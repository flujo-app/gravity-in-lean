// Removes a finished run's container, volume and network, and its staged secrets.
//   node finish.mjs <run folder name>
// Run it only after flows.bundle has been copied out and checked: the volume holds the agents' work.
import { existsSync } from 'node:fs';
import { join } from 'node:path';
import { ROOT, makeFleet, stamp } from './common.mjs';

const run = process.argv[2];
if (!run) throw new Error('Name the run folder.');
const directory = join(ROOT, 'runs', run);
if (!existsSync(join(directory, 'fleet.json'))) throw new Error(`No fleet journal in ${directory}.`);
const fleet = makeFleet(directory);
try {
  await fleet.retire();
  console.log(`${stamp()} retired ${run}: container, volume and network removed`);
} finally {
  await fleet.disconnect().catch(() => {});
}
