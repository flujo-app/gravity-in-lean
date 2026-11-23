#!/usr/bin/env bash
# Runs inside the worker image, with only the few settings a FACTORY agent's commands get
# (search path and home folder). Shows that a fresh copy of the repository can be set up and
# that one file builds through the queue, without Lean or the library being downloaded.
set -u
mkdir -p /data
exec env -i PATH="$PATH" HOME=/data bash -c '
  set -u
  echo "lean: $(which lean)  lake: $(which lake)"
  lean --version
  git config --global --add safe.directory "*"
  git clone -q /src /data/repository && cd /data/repository
  git worktree add -q --detach /data/worktrees/m0-a1 "$0" && cd /data/worktrees/m0-a1
  ls -l scripts/*.sh | cut -c1-10,40-
  scripts/setup-worktree.sh
  scripts/setup-worktree.sh
  mkdir -p GravityInLean/Flows
  printf "import Mathlib.Analysis.ODE.Gronwall\n\nexample : (1 : ℝ) + 1 = 2 := by norm_num\n" > GravityInLean/Flows/Smoke.lean
  start=$(date +%s)
  scripts/queued-build.sh lake build GravityInLean.Flows.Smoke 2>&1 | tail -2
  echo "one file through the queue: $(( $(date +%s) - start ))s"
  printf "import Mathlib.Analysis.ODE.Gronwall\n\nexample : (2 : ℝ) + 2 = 4 := by norm_num\n" > /tmp/Scratch.lean
  start=$(date +%s)
  scripts/queued-build.sh lake env lean /tmp/Scratch.lean 2>&1 | tail -2
  echo "scratch file through the queue: $(( $(date +%s) - start ))s"
  cat /tmp/gravity-in-lean-build.log
  echo "second copy of Lean in the home folder: $([ -e /data/.elan ] && echo YES || echo no)"
  echo "library is a link: $([ -L .lake/packages ] && echo yes || echo NO)"
' "$1"
