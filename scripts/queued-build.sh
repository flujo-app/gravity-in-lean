#!/usr/bin/env bash
# One Lean build at a time per machine.
#
# Use this instead of calling `lake build` directly whenever more than one worker may be
# building on the same machine (or in the same container):
#
#   scripts/queued-build.sh                          # the whole project: `lake build`
#   scripts/queued-build.sh lake build GravityInLean.Curved.Basic
#
# It waits until no other build is running, runs the command, and writes one line to a log:
# who built, how long they waited, how long the build took, and how it ended.
#
# Settings (all optional, as environment variables):
#   GRAVITY_BUILD_LOCK     the lock, a folder that exists while a build runs
#                          (default: <temp folder>/gravity-in-lean-build.lock)
#   GRAVITY_BUILD_LOG      the log file (default: next to the lock, ending in .log)
#   GRAVITY_BUILD_WHO      a name for the log (default: user and process number)
#   GRAVITY_BUILD_MAX_AGE  seconds after which a lock counts as abandoned (default: 1800)
#
# Workers that should queue together must use the same lock. On one PC that is the default. In
# containers, point GRAVITY_BUILD_LOCK at a folder that all of them can see.

set -u

LOCK_DIR="${GRAVITY_BUILD_LOCK:-${TMPDIR:-/tmp}/gravity-in-lean-build.lock}"
LOG="${GRAVITY_BUILD_LOG:-${LOCK_DIR%.lock}.log}"
WHO="${GRAVITY_BUILD_WHO:-$(whoami 2>/dev/null || echo unknown)@$$}"
MAX_AGE="${GRAVITY_BUILD_MAX_AGE:-1800}"

if [ "$#" -eq 0 ]; then
  set -- lake build
fi

start_wait=$(date +%s)

# Creating a folder either works or fails as one step, so only one waiter can win.
while ! mkdir "$LOCK_DIR" 2>/dev/null; do
  if [ -f "$LOCK_DIR/since" ]; then
    since=$(cat "$LOCK_DIR/since" 2>/dev/null || echo 0)
    now=$(date +%s)
    case "$since" in
      ''|*[!0-9]*) since=0 ;;
    esac
    if [ "$since" -gt 0 ] && [ $((now - since)) -gt "$MAX_AGE" ]; then
      echo "queued-build: removing a lock that is older than ${MAX_AGE}s" >&2
      rm -rf "$LOCK_DIR"
      continue
    fi
  fi
  sleep 1
done

date +%s > "$LOCK_DIR/since"
echo "$WHO" > "$LOCK_DIR/who"
trap 'rm -rf "$LOCK_DIR"' EXIT
trap 'exit 130' INT TERM

start_build=$(date +%s)
"$@"
code=$?
end=$(date +%s)

echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) who=$WHO waited=$((start_build - start_wait))s built=$((end - start_build))s exit=$code cmd=$*" >> "$LOG"

exit "$code"
