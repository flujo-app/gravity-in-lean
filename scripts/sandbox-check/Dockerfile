# A plain Linux machine for Lake's sandboxed checks (`lake check --paranoid` and
# `lake comparator --paranoid`), which need `bwrap` and so cannot run on Windows.
# Debian 12, Lean 4.36.0 through elan, bubblewrap, git. See run.sh next to this file.
FROM debian:bookworm-slim

RUN apt-get update \
 && apt-get install -y --no-install-recommends bubblewrap git curl ca-certificates time procps \
 && rm -rf /var/lib/apt/lists/* \
 && mkdir -p /run/user /work \
 && useradd -m -u 1000 checker \
 && chown checker:checker /work

# Not root: the sandbox runs as an ordinary user.
USER checker
WORKDIR /home/checker
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh \
 && sh elan-init.sh -y --no-modify-path --default-toolchain leanprover/lean4:v4.36.0 \
 && rm elan-init.sh
ENV PATH=/home/checker/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
RUN elan toolchain install leanprover/lean4:v4.36.0 && lean --version
WORKDIR /work
