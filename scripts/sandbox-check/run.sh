#!/usr/bin/env bash
# Lake's two sandboxed checks, on a clean Linux container (paper Section 9, items 3 and 4):
#
#   lake check --paranoid        builds the default targets (GravityInLean, Audit) inside Lake's
#                                sandbox, exports every declaration in scope (mathlib and Lean's
#                                own library included: about 3.1 GB) and runs the export through
#                                Lean's kernel and the five other checkers that ship with Lean.
#   lake comparator --paranoid   builds comparator/Challenge.lean (every statement that Audit.lean
#                                checks, with a hole for each proof) and Audit.lean inside the
#                                sandbox, and accepts only if each named result has exactly the
#                                challenge's statement, uses no axiom beyond the three standard
#                                ones, and passes the same six checkers.
#
# Usage: scripts/sandbox-check/run.sh [git ref] [comparator]   (default ref: main)
#        With "comparator", only the second check runs. The workflow "Compare statements" runs
#        the same on GitHub's machines.
#
# Needs Docker and a network. On the PC of the paper (8 cores) the first check took 2 h 21 min
# and the second 9 minutes. On the whole export, nanoda 0.4.17 used all 24 GB of memory plus
# about 30 GB of swap and then crashed with a stack overflow, so `lake check` ends with
# "nanoda exited with 134"; the other five checkers accept. Without nanoda the peak was 19 GB.
# Removes its container when done; the image stays (docker rmi gravity-sandbox-check:lean-4.36.0).
set -uo pipefail

REF="${1:-main}"
ONLY="${2:-}"
HERE="$(cd "$(dirname "$0")" && pwd)"
IMAGE=gravity-sandbox-check:lean-4.36.0
NAME=gravity-sandbox-check

docker build -t "$IMAGE" "$HERE" || exit 1

# The sandbox (bwrap) makes its own namespaces. Docker's default system-call filter forbids that,
# so it is turned off for this one container. Nothing else is loosened: no added capabilities,
# not privileged, and everything runs as an ordinary user.
docker run -d --name "$NAME" --security-opt seccomp=unconfined "$IMAGE" sleep infinity || exit 1
trap 'docker rm -f "$NAME" >/dev/null' EXIT

docker exec "$NAME" bash -uc "
  git clone -q https://github.com/flujo-app/gravity-in-lean.git && cd gravity-in-lean || exit 1
  git checkout -q '$REF' || exit 1
  git log -1 --format='checking %H %s'
  # mathlib's prebuilt files. This step runs outside Lake's sandbox; it fetches mathlib's own
  # build results, whose declarations the checkers below check again one by one.
  lake exe cache get || exit 1
  # No lake build here: the project's own code is built only inside the sandbox.
  if [ '$ONLY' != comparator ]; then
    /usr/bin/time -v lake check --paranoid; echo \"lake check: exit \$?\"
  fi
  if [ -f comparator.json ]; then
    /usr/bin/time -v lake comparator --paranoid; echo \"lake comparator: exit \$?\"
  fi
"
