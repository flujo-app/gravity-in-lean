# A team of workers on this repository

Everything needed to let a FACTORY team (one lead, nine workers, in one Docker container on this
PC) work on a statement of this project. Used for the first trial on 23 November 2026; what it
showed is in [PLAN.md](../PLAN.md), "What the first team trial showed".

| File | What it is |
|---|---|
| `Dockerfile` | The worker image: Node, Lean 4.36.0, and the ready-built standard library. |
| `goal-flows.md`, `goal-turns.md`, `goal-birkhoff.md`, `goal-exactly-when.md`, `goal-checks.md` | The briefs for the five jobs: what to prove, a route, the rules, how turns work. |
| `image-check.sh` | Checks the image the way an agent uses it: only the search path and the home folder are set. |
| `common.mjs` | Shared settings: which commit, which image, which model. |
| `smoke.mjs` | A small check before a real run: one container, two agents, one short job. |
| `trial.mjs` | The run itself. Deploys the team, watches it, stops it after a set time or when a file named `STOP` appears in the run folder, and copies the branches out as one git bundle. |
| `finish.mjs` | Removes a finished run's container, volume, network and staged logins. |

## To run it

Needs Docker, Node 24, the GitHub command line tool (logged in), and FACTORY 0.11.0 installed in
a private folder outside this repository:

```sh
mkdir my-fleet && cd my-fleet
npm install https://github.com/flujo-app/FACTORY/releases/download/v0.11.0/flujo-factory-0.11.0.tgz
cp <this repository>/fleet/*.mjs <this repository>/fleet/goal-flows.md .
```

Three settings, as environment variables:

- `GRAVITY_FLEET_ROOT`: that private folder. Runs are kept in `runs/` inside it.
- `GRAVITY_REVISION`: the commit the team starts from, by its full name. It must be on GitHub.
- `CLAUDE_TOKEN_FILE`: a file holding a token from `claude setup-token`. Never commit it.

Then:

```sh
# once: the worker image (about 12 minutes the first time, 11.5 GB)
mkdir ctx && cp <this repository>/{lean-toolchain,lakefile.toml,lake-manifest.json} ctx/
docker build -f <this repository>/fleet/Dockerfile -t gravity-worker:lean-4.36.0-r2 ctx

node smoke.mjs            # a small check; removes itself
node trial.mjs 90 trial1 goal-flows.md   # the team, for at most 90 minutes, on that brief
node finish.mjs trial1    # after the bundle in runs/trial1/flows.bundle has been checked
```

The scripts read the two logins themselves and never print them. A run folder holds staged
logins until `finish.mjs` has run, so keep it private and remove it afterwards.

## What an agent's commands can rely on

Measured on 23 November 2026 with FACTORY 0.11.0: an agent's commands get the search path and
the home folder (`/data`) from the image, and no other setting. So the image puts Lean itself
first on the search path, and `scripts/setup-worktree.sh` looks for the ready-built library at
the fixed place `/opt/gravity/.lake/packages`. The first small check found three faults of this
kind before any real work was started; `image-check.sh` now tests for them without a model.

## What comes back

The team's branches arrive as a git bundle. Nothing is taken on the team's word: the supervisor
fetches the bundle, looks at what changed, builds the whole project through the queue, and adds
the new theorem to `Audit.lean` together with a line that checks it proves the statement that
was fixed beforehand.
