#!/usr/bin/env bash
# Build example files with rsas

set -euxo pipefail
cargo run as-examples/hello-main.s && mv a.out build/rsas-hello-main.o
cargo run as-examples/hello-module.s && mv a.out build/rsas-hello-module.o
cargo run as-examples/cat.s && mv a.out build/rsas-cat.o
docker exec -it -w /build rsas-builder-1 ld -o rsas-hello rsas-hello-main.o rsas-hello-module.o
docker exec -it -w /build rsas-builder-1 ld -o rsas-cat rsas-cat.o
