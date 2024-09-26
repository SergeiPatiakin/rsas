# rsas
- rsas is a toy assembler targeting x64 Linux

## Usage
- `rsas source.s` will assemble `source.s` into a Linux ELF64 object file at `a.out`

## Trying it out
- Assemble, link and demo a simple cat implementation on a Linux x64 host
```sh
cargo install --path .

rsas as-examples/cat.s
ld -o rsas-cat a.out

echo 'aaa' > a.txt
echo 'bbb' > b.txt
./rsas-cat a.txt b.txt
# Output:
# aaa
# bbb
```

## Features
- AT&T assembly syntax
- No Cargo dependencies
- Supports global and local symbols
- Supports multiple types of relocations
