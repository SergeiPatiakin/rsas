#!/usr/bin/env bash
# Build docker image for rsas development

set -euxo pipefail
docker build  --platform linux/amd64 infra -t rsas-builder
