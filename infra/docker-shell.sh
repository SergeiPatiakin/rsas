#!/usr/bin/env bash
# Start shell on development docker container

set -euxo pipefail
docker exec -it -w /build rsas-builder-1 bash
