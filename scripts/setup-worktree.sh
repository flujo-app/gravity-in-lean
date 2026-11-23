#!/usr/bin/env bash
# Make a fresh copy of this repository ready to build: give it the ready-built standard library.
#
#   scripts/setup-worktree.sh
#
# If a folder with the ready-built standard library is at hand, it is linked in, which takes no
# time and no disk space. The folder is $GRAVITY_PACKAGES, or else /opt/gravity/.lake/packages,
# where the worker image keeps it. Otherwise the ready-built library is downloaded (about
# 3.4 GB). It is never built from source. Running this again is safe: a download that was cut
# short goes on where it stopped.

set -eu

cd "$(dirname "$0")/.."
mkdir -p .lake

PACKAGES="${GRAVITY_PACKAGES:-/opt/gravity/.lake/packages}"

if [ -L .lake/packages ]; then
  echo "setup-worktree: the shared standard library is already linked in"
  exit 0
fi

if [ ! -e .lake/packages ] && [ -d "$PACKAGES/mathlib" ]; then
  ln -s "$PACKAGES" .lake/packages
  echo "setup-worktree: linked the shared standard library from $PACKAGES"
  exit 0
fi

lake exe cache get
