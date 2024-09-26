#!/usr/bin/env bash
# Create docker container for rsas development

set -euxo pipefail
docker create --platform linux/amd64 \
    --restart always \
    --mount type=bind,source="$(pwd)"/build,target=/build \
    --mount type=bind,source="$(pwd)"/as-examples,target=/as-examples \
    --name rsas-builder-1 \
    -w /as-examples rsas-builder \
    sleep 100000d
