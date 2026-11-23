#!/usr/bin/env bash
# Make a fresh copy of this repository ready to build: give it the ready-built standard library.
#
#   scripts/setup-worktree.sh
#
# If GRAVITY_PACKAGES points at a folder that already holds the standard library (the worker
# image sets it), that folder is linked in, which takes no time and no disk space. Otherwise the
# ready-built library is downloaded (about 3.4 GB). It is never built from source.

set -eu

cd "$(dirname "$0")/.."
mkdir -p .lake

if [ -e .lake/packages ]; then
  echo "setup-worktree: the standard library is already in place"
  exit 0
fi

if [ -n "${GRAVITY_PACKAGES:-}" ] && [ -d "$GRAVITY_PACKAGES/mathlib" ]; then
  ln -s "$GRAVITY_PACKAGES" .lake/packages
  echo "setup-worktree: linked the shared standard library from $GRAVITY_PACKAGES"
else
  lake exe cache get
fi
