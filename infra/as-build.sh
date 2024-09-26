#!/usr/bin/env bash
# Build example files with LLVM assembler (compatible with GNU assembler)

set -euxo pipefail
docker exec rsas-builder-1 make "$@"
