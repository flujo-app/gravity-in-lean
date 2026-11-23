// The one-team trial: one container, a lead and nine workers, on the smooth-flow statement.
//   node trial.mjs <minutes>
// It deploys the team, watches it, writes status.json every 30 seconds, and ends the trial by itself
// when the time is up or when a file named STOP appears in the run folder. At the end it asks every
// agent to stop, copies the branches out as one git bundle, and stops the container.
// It does not remove the container or its volume: `node finish.mjs` does that after a look.
import { execFile } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { ROOT, REPOSITORY, REVISION, IMAGE, MODEL, githubToken, makeFleet, sleep, stamp, traces, enrolled } from './common.mjs';

const minutes = Number(process.argv[2]);
if (!Number.isFinite(minutes) || minutes < 1 || minutes > 240) throw new Error('Give the length of the trial in minutes (1 to 240).');
const RUN = process.argv[3] ?? 'trial1';
const directory = join(ROOT, 'runs', RUN);
mkdirSync(directory, { recursive: true });
const docker = async args => (await promisify(execFile)('docker', args, { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024, windowsHide: true })).stdout;
const fleet = makeFleet(directory);
const runId = `gravity-flows-${RUN}`;
const plan = { runId, app: runId, workerProgram: 'claude',
  repository: REPOSITORY, repositoryRevision: REVISION,
  machines: 1, agentsPerMachine: 10, cpus: 7, memoryMb: 18432,
  model: MODEL, subagentModel: MODEL, reasoningEffort: 'high',
  goal: readFileSync(new URL('./goal-flows.md', import.meta.url), 'utf8') };
const agents = Array.from({ length: plan.agentsPerMachine }, (_, index) => `m0-a${index}`);
const container = `factory-${runId}-m0`;

const started = Date.now();
const say = text => console.log(`${stamp()} +${Math.round((Date.now() - started) / 1000)}s ${text}`);
/** What the team has used and done so far, from the trace records. */
function summary(observation) {
  const all = traces(directory), perAgent = {};
  for (const id of agents) perAgent[id] = { turnsStarted: 0, turnsEnded: 0, tokens: null, toolCalls: 0 };
  for (const event of all) {
    const agent = perAgent[event.source]; if (!agent) continue;
    if (event.kind === 'native.turn.started') agent.turnsStarted++;
    if (event.kind === 'native.turn.completed') agent.turnsEnded++;
    if (event.kind === 'thread/tokenUsage/updated') agent.tokens = event.body.tokenUsage?.total ?? event.body.total ?? event.body;
    if (event.kind === 'item/completed' && event.body.item?.type === 'toolCall') agent.toolCalls++;
  }
  const retries = all.filter(event => event.kind === 'model/retry').length;
  const failures = all.filter(event => /continuation\.failed|claude\.stderr|turn\.failed|session_unavailable/.test(event.kind)).slice(-5)
    .map(event => ({ kind: event.kind, source: event.source, body: JSON.stringify(event.body).slice(0, 240) }));
  return { at: stamp(), minutes: Math.round((Date.now() - started) / 6000) / 10, traceRecords: all.length, modelRetries: retries,
    claims: (observation?.claims ?? []).map(claim => ({ resource: claim.resource, owner: claim.owner, status: claim.status, updated: new Date(claim.updated).toISOString() })),
    perAgent, lastFailures: failures };
}

try {
  say(`deploying ${runId}: 1 container, ${plan.agentsPerMachine} agents, model ${MODEL}, effort ${plan.reasoningEffort}, for ${minutes} minutes`);
  await fleet.deploy(plan, { image: IMAGE, prebuild: true, githubToken: githubToken() });
  say('deployed; waiting for agents');
  await enrolled(fleet, directory, agents);
  const begun = Date.now(), deadline = begun + minutes * 60000;
  writeFileSync(join(directory, 'begun.txt'), new Date(begun).toISOString());
  say('all agents enrolled; the clock starts now');
  let last = 0, reason = 'time is up';
  for (;;) {
    let observation = null;
    try { observation = await fleet.observe({ maxPages: 25 }); } catch (error) { say(`observe failed: ${error.message}`); }
    if (Date.now() - last >= 30000) {
      last = Date.now();
      const status = summary(observation);
      writeFileSync(join(directory, 'status.json'), JSON.stringify(status, null, 1));
      const sum = name => Object.values(status.perAgent).reduce((total, agent) => total + (agent.tokens?.[name] ?? 0), 0);
      status.tokens = { input: sum('inputTokens'), cachedInput: sum('cachedInputTokens'), output: sum('outputTokens') };
      writeFileSync(join(directory, 'status.json'), JSON.stringify(status, null, 1));
      say(`claims ${status.claims.length}; turns ${Object.values(status.perAgent).map(agent => `${agent.turnsEnded}/${agent.turnsStarted}`).join(' ')}; tokens in ${status.tokens.input} (cached ${status.tokens.cachedInput}) out ${status.tokens.output}; retries ${status.modelRetries}`);
    }
    if (existsSync(join(directory, 'STOP'))) { reason = 'a STOP file appeared'; break; }
    if (Date.now() >= deadline) break;
    await sleep(10000);
  }
  say(`ending the trial: ${reason}`);
  writeFileSync(join(directory, 'ended.txt'), `${stamp()} ${reason}\n`);
  try { await fleet.quiesce({ timeoutMs: 180000, attempt: `end-${Date.now().toString(36)}` }); say('every agent has stopped'); }
  catch (error) { say(`quiesce did not finish cleanly: ${error.message}`); }
  try { const observation = await fleet.observe({ maxPages: 25 }); writeFileSync(join(directory, 'status.json'), JSON.stringify(summary(observation), null, 1)); } catch { /* keep the last status */ }
  // Copy out the branches, the queue's log and the size of every work folder, while the container still runs.
  try {
    await docker(['exec', container, '/bin/sh', '-c', 'cd /data/repository 2>/dev/null || cd "$(git -C /data/worktrees/m0-a0 rev-parse --git-common-dir)/.." && git bundle create /data/flows.bundle --all 2>&1 | tail -2; (cat /data/gravity-build.log 2>/dev/null || cat /tmp/gravity-in-lean-build.log 2>/dev/null) > /data/queue.log; git branch --all --format="%(refname:short) %(objectname:short) %(committerdate:iso8601) %(subject)" > /data/branches.txt']);
    for (const name of ['flows.bundle', 'queue.log', 'branches.txt']) await docker(['cp', `${container}:/data/${name}`, join(directory, name)]);
    say('copied out: flows.bundle, queue.log, branches.txt');
  } catch (error) { say(`copying out failed: ${error.message}`); process.exitCode = 1; }
  try { await fleet.stop(); say('container stopped (not removed)'); } catch (error) { say(`stop failed: ${error.message}`); process.exitCode = 1; }
} catch (error) {
  console.error(`FAIL ${error.message}`);
  process.exitCode = 1;
} finally {
  await fleet.disconnect().catch(() => {});
}
