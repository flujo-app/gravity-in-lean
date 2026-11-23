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
#
# Inside the worker image there is a second saving. The first copy of the repository that is set
# up builds the whole project once (through the queue) and keeps the result in a shared folder;
# every later copy at the same commit takes it from there. Without this, ten workers would each
# build the same files again, one after the other. The shared folder is $GRAVITY_PREBUILT, or
# else /data/gravity-prebuilt when the worker image's library is in use.

set -eu

cd "$(dirname "$0")/.."
mkdir -p .lake

PACKAGES="${GRAVITY_PACKAGES:-/opt/gravity/.lake/packages}"

if [ -L .lake/packages ]; then
  echo "setup-worktree: the shared standard library is already linked in"
elif [ ! -e .lake/packages ] && [ -d "$PACKAGES/mathlib" ]; then
  ln -s "$PACKAGES" .lake/packages
  echo "setup-worktree: linked the shared standard library from $PACKAGES"
else
  lake exe cache get
  exit 0
fi

# The project's own build, shared between copies at the same commit.
PREBUILT="${GRAVITY_PREBUILT:-}"
if [ -z "$PREBUILT" ] && [ -d /opt/gravity/.lake/packages ] && [ -d /data ]; then
  PREBUILT=/data/gravity-prebuilt
fi
if [ -n "$PREBUILT" ] && [ ! -e .lake/build ]; then
  commit=$(git rev-parse HEAD)
  shared="$PREBUILT/$commit"
  if [ ! -e "$shared/done" ]; then
    # Inside the queue, so that only one copy builds; the others find the result when their turn comes.
    SHARED="$shared" scripts/queued-build.sh sh -c '
      [ -e "$SHARED/done" ] && exit 0
      lake build || exit 1
      mkdir -p "$SHARED" && rm -rf "$SHARED/build" && cp -a .lake/build "$SHARED/build" && touch "$SHARED/done"
    ' || { echo "setup-worktree: the shared build failed; this copy will build for itself" >&2; exit 0; }
  fi
  if [ ! -e .lake/build ]; then
    cp -a "$shared/build" .lake/build
    echo "setup-worktree: took the project's build from $shared"
  else
    echo "setup-worktree: built the project once and shared it in $shared"
  fi
fi
