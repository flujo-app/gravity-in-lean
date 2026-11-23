// A small check before the real trial: one container, two agents, one short job for one of them.
// It shows that the worker image, the private clone, Lean, the build queue and the model name work.
//   node smoke.mjs [--keep]
import { mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { ROOT, REPOSITORY, REVISION, IMAGE, MODEL, githubToken, makeFleet, sleep, stamp, traces, enrolled } from './common.mjs';

const directory = join(ROOT, 'runs', 'smoke1');
mkdirSync(directory, { recursive: true });
const fleet = makeFleet(directory);
const plan = { runId: 'gravity-smoke-1', app: 'gravity-smoke-1', workerProgram: 'claude',
  repository: REPOSITORY, repositoryRevision: REVISION,
  machines: 1, agentsPerMachine: 2, cpus: 6, memoryMb: 8192,
  model: MODEL, subagentModel: MODEL, reasoningEffort: 'low',
  supervision: 'operator', monitorIntervalMs: 4000,
  goal: 'Check of the set-up. Wait for operator messages.' };

const message = `This is a check of the set-up. Do exactly the following in your work folder, with shell commands, and nothing else.
1. Run: pwd; git rev-parse HEAD; git status --short | wc -l; git config user.name; which lean lake; echo "LOCK=$GRAVITY_BUILD_LOCK PACKAGES=$GRAVITY_PACKAGES HOME=$HOME"; nproc; free -g | head -2
2. Run: scripts/setup-worktree.sh
3. Create the file GravityInLean/Flows/Smoke.lean with exactly these three lines:
import Mathlib.Analysis.ODE.Gronwall

example : (1 : ℝ) + 1 = 2 := by norm_num
4. Run: scripts/queued-build.sh lake build GravityInLean.Flows.Smoke 2>&1 | tail -5; echo "EXIT=\${PIPESTATUS[0]}"
5. Run: cat /data/gravity-build.log 2>/dev/null || cat /tmp/gravity-in-lean-build.log
6. Run: git branch --list | head -5; git worktree list | head -5; git remote -v | sed 's#//[^@]*@#//#' | head -2
7. Delete GravityInLean/Flows/Smoke.lean again.
8. If step 4 ended with "Build completed successfully", call the FACTORY board tool factory_claim with resource "task:smoke-ok".
Then answer with the raw output of steps 1, 2, 4, 5 and 6, and stop.`;

const started = Date.now();
const say = text => console.log(`${stamp()} +${Math.round((Date.now() - started) / 1000)}s ${text}`);
try {
  say('deploying');
  await fleet.deploy(plan, { image: IMAGE, prebuild: true, githubToken: githubToken() });
  say('deployed; waiting for agents');
  await enrolled(fleet, directory, ['m0-a0', 'm0-a1']);
  say('agents enrolled');
  const after = traces(directory).at(-1)?.seq ?? 0;
  await fleet.command('m0-a1', { id: 'smoke-1', message });
  const deadline = Date.now() + 1500000;
  let ended;
  while (!ended) {
    const observation = await fleet.observe({ maxPages: 25 });
    const fresh = traces(directory).filter(event => event.seq > after && event.source === 'm0-a1');
    ended = fresh.find(event => event.kind === 'native.turn.completed');
    if (ended) {
      say(`turn ended: ${ended.body.turn?.status}`);
      const configured = fresh.filter(event => event.kind === 'session/configured').at(-1)?.body;
      say(`session: ${JSON.stringify(configured)}`);
      const usage = fresh.filter(event => event.kind === 'thread/tokenUsage/updated').at(-1)?.body;
      say(`token use: ${JSON.stringify(usage)}`);
      const text = fresh.filter(event => event.kind === 'item/completed' && event.body.item?.type === 'agentMessage').map(event => event.body.item.text).join('\n');
      console.log('----- agent report -----\n' + text + '\n------------------------');
      say(`claims: ${JSON.stringify((observation.claims ?? []).map(claim => ({ resource: claim.resource, owner: claim.owner })))}`);
      const errors = traces(directory).filter(event => /stderr|error|failed/i.test(event.kind)).slice(-5);
      if (errors.length) say(`error traces: ${JSON.stringify(errors).slice(0, 1500)}`);
    } else if (Date.now() >= deadline) throw new Error('The agent did not end its turn in time.');
    else await sleep(4000);
  }
} catch (error) {
  console.error(`FAIL ${error.message}`);
  const tail = traces(directory).slice(-8).map(event => ({ kind: event.kind, source: event.source, body: JSON.stringify(event.body).slice(0, 300) }));
  console.error(JSON.stringify(tail, null, 1));
  process.exitCode = 1;
} finally {
  if (!process.argv.includes('--keep')) {
    try { await fleet.retire(); say('retired: container, volume and network removed'); }
    catch (error) { console.error(`retire failed: ${error.message}`); process.exitCode = 1; }
  }
  await fleet.disconnect().catch(() => {});
}
