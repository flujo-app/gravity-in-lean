# The worker image for a FACTORY team that works on this repository:
# Node (for FACTORY and Claude Code), Lean, and the ready-built standard library.
#
# Build it from a folder that holds only the three files copied below, so that the 3.4 GB of
# build files in `.lake` are not sent to Docker:
#
#   mkdir ctx && cp lean-toolchain lakefile.toml lake-manifest.json ctx/
#   docker build -f fleet/Dockerfile -t gravity-worker:lean-4.36.0 ctx
FROM node:24.22.1-bookworm-slim

RUN apt-get update \
 && apt-get install -y --no-install-recommends curl git ca-certificates python3 \
 && rm -rf /var/lib/apt/lists/*

# Lean. Agents run with HOME=/data, so nothing they need may live under /root.
ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
 && sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain leanprover/lean4:v4.36.0 \
 && rm /tmp/elan-init.sh

# The standard library, ready-built, once for all workers that use this image.
# `scripts/setup-worktree.sh` links it into each worker's own copy of the repository.
WORKDIR /opt/gravity
COPY lean-toolchain lakefile.toml lake-manifest.json ./
RUN lake exe cache get \
 && chmod -R a+rwX /opt/gravity /opt/elan

ENV GRAVITY_PACKAGES=/opt/gravity/.lake/packages
# All workers in one container queue their builds on this lock (see scripts/queued-build.sh).
ENV GRAVITY_BUILD_LOCK=/data/gravity-build.lock
WORKDIR /data
