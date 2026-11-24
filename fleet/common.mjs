// Shared pieces for the gravity-in-lean fleet scripts. Secrets are read here and never printed.
import { execFileSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { FactoryDockerLiteFleet, ClaudeSubscriptionBroker } from 'flujo-factory';

// Where the runs are kept: a private folder outside the repository. It holds the fleet's journals
// and, until a run is removed, its staged logins.
export const ROOT = required('GRAVITY_FLEET_ROOT');
export const REPOSITORY = 'flujo-app/gravity-in-lean';
// The commit the team starts from: any commit that is on GitHub. Set GRAVITY_REVISION to its full
// name (`git rev-parse origin/main`).
export const REVISION = required('GRAVITY_REVISION');
export const IMAGE = 'gravity-worker:lean-4.36.0-r2';
export const MODEL = 'claude-fable-5-2';
// The one address that commits of a team may carry (GitHub's no-reply address of the account).
// scripts/setup-worktree.sh sets it in every worker's copy; trial.mjs checks it on collection.
export const COMMIT_ADDRESS = process.env.GRAVITY_GIT_EMAIL ?? '300233937+flujo-app@users.noreply.github.com';

function required(name) {
  const value = process.env[name];
  if (!value) throw new Error(`Set ${name} first (see fleet/README.md).`);
  return value.replaceAll('\\', '/');
}
export const githubToken = () => execFileSync('gh', ['auth', 'token'], { encoding: 'utf8', windowsHide: true }).trim();
export const makeFleet = directory => new FactoryDockerLiteFleet({ directory,
  auth: new ClaudeSubscriptionBroker({ tokenFile: required('CLAUDE_TOKEN_FILE') }) });

export const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
export const stamp = () => new Date().toISOString();
export function traces(directory) {
  const file = join(directory, 'traces.jsonl');
  if (!existsSync(file)) return [];
  const out = [];
  for (const line of readFileSync(file, 'utf8').split('\n')) {
    if (!line.trim()) continue;
    try { out.push(JSON.parse(line)); } catch { /* a line still being written */ }
  }
  return out;
}
/** Waits until every listed agent has enrolled on the board. */
export async function enrolled(fleet, directory, agentIds, timeoutMs = 1800000) {
  const deadline = Date.now() + timeoutMs;
  for (;;) {
    try { await fleet.observe({ maxPages: 25 }); } catch { /* the board is not up yet */ }
    const seen = new Set(traces(directory).filter(event => event.kind === 'agent.enrolled').map(event => event.body.agentId));
    if (agentIds.every(id => seen.has(id))) return;
    if (Date.now() >= deadline) throw new Error('Agents did not all enrol in time.');
    await sleep(3000);
  }
}
