// Progbits section
#[derive(Debug)]
struct ProgbitsSectionBody {
    content: Vec<u8>,
    is_writable: bool,
    is_executable: bool,
}

// Strtab section
#[derive(Debug)]
struct StrtabSectionBody {
    strings: Vec<Vec<u8>>,
}

// Relocation section
#[derive(Debug)]
struct Rela {
    addend: i64,
    symbol_index: u32,
    type_: u32,
    reference_offset: u64, // Offset of reference to this symbol in this section
}

#[derive(Debug)]
struct RelaSectionBody {
    referenced_section_index: u16, // Section index of section to which the relocations apply
    relocations: Vec<Rela>,
}

// Symtab section
#[derive(Clone, Debug)]
struct Symbol {
    binding: &'static str,
    _type: &'static str,
    name_strtab_index: u32,
    value: u64,
    section_index: u16,
}

#[derive(Debug)]
struct SymtabSectionBody {
    symbols: Vec<Symbol>,
    num_local_symbols: u32,
}

// Sections union
#[derive(Debug)]
enum SectionType {
    NullSection,
    ProgbitsSection(ProgbitsSectionBody),
    StrtabSection(StrtabSectionBody),
    RelaSection(RelaSectionBody),
    SymtabSection(SymtabSectionBody),
}

#[derive(Debug)]
struct Section {
    name_strtab_index: u32,
    offset: u32,
    length: u32,
    section_type: SectionType,
}

#[derive(Debug)]
struct ObjectFile {
    sections: Vec<Section>
}

fn extract_hex_literal(source: &[u8], pair: &Pair) -> u64 {
    assert_eq!(pair.token_type, "hex_literal");
    assert!(pair.children.len() >= 2);
    let mut result: u64 = 0;
    for pos in (pair.children[1].start)..pair.end {
        result <<= 4;
        result += match source[pos] {
            b'0'..=b'9' => (source[pos] - b'0') as u64,
            b'a'..=b'f' => (source[pos] - b'a' + 10) as u64,
            b'A'..=b'F' => (source[pos] - b'A' + 10) as u64,
            _ => panic!(),
        };
    }
    match pair.children[0].token_type {
        "null" => result,
        "single_char" => 0xffff_ffff_ffff_ffff - result + 1,
        _ => panic!("Unknown sign"),
    }
}

fn extract_string_literal(source: &[u8], pair: &Pair) -> Vec<u8> {
    assert_eq!(pair.token_type, "string_literal");
    let mut result: Vec<u8> = Vec::new();
    for pair in &pair.children {
        assert_eq!(pair.token_type, "string_literal_charrep");
        assert_eq!(pair.children.len(), 1);
        let charrep = pair;
        assert_eq!(charrep.children.len(), 1);
        let charrep_child = &charrep.children[0];
        if charrep_child.token_type == "single_char" {
            assert_eq!(charrep_child.end - charrep_child.start, 1);
            let escaped_char = match source[charrep_child.start] {
                b'\\' => b'\\',
                b'\"' => b'\"',
                b'n' => b'\n',
                _ => panic!("Unknown escape char: {}", source[charrep_child.start]),
            };
            result.push(escaped_char);
        } else if charrep_child.token_type == "string_literal_normal_char" {
            let normal_char = source[charrep_child.start];
            result.push(normal_char);
        } else {
            panic!("Unexpected child type for string_literal_charrep");
        }
    }
    result
}

// Returns the index of an item in a vector
// If the item cannot be found, it is added to the vector
fn find_or_add(bag: &mut Vec<Vec<u8>>, item: &Vec<u8>) -> usize {
    match bag.iter().position(|x| x == item) {
        Some(pos) => pos,
        None => {
            bag.push(item.clone());
            return bag.len() - 1;
        }
    }
}

#[derive(Debug, PartialEq)]
struct IntermediateSymbolDef {
    binding: &'static str,
    section_offset: u64,
    symbol_name: Vec<u8>,
}

#[derive(Debug)]
struct IntermediateSymbolRef {
    section_offset: u64,
    symbol_name: Vec<u8>,
    ref_type: &'static str,
}

struct IntermediateSection {
    section_name: Vec<u8>,
    prog_bits: Vec<u8>,
    symbol_defs: Vec<IntermediateSymbolDef>,
    symbol_refs: Vec<IntermediateSymbolRef>,
}

struct IntermediateObjectFile {
    sections: Vec<IntermediateSection>,
}

#[derive(Debug)]
struct RmOperandBody<'a> {
    pair: &'a Pair,
    mode: u8,
    rm: u8,
    displacement: Option<i32>,
    displacement_symbol_ref: Option<IntermediateSymbolRef>,
}

#[derive(Debug)]
struct ImmOperandBody<'a> {
    pair: &'a Pair,
    immediate_value: u32,
    immediate_symbol_ref: Option<IntermediateSymbolRef>,
}

#[derive(Debug)]
enum ProcessedOperand<'a> {
    RmOperand(RmOperandBody<'a>),
    ImmOperand(ImmOperandBody<'a>),
}
use ProcessedOperand::*;

// Parse an instruction statement node which is expected to have no operands
fn process_no_operands(
    instruction_stmt: &Pair,
    source:  &[u8],
) {
    assert_eq!(instruction_stmt.token_type, "instruction_stmt");
    assert_eq!(instruction_stmt.children.len(), 1);
}

// Parse an instruction statement node which is expected to have 1 operand
fn process_singleton_operands<'a>(
    instruction_stmt: &'a Pair,
    source:  &[u8],
) -> ProcessedOperand<'a> {
    assert_eq!(instruction_stmt.token_type, "instruction_stmt");
    assert_eq!(instruction_stmt.children.len(), 2);
    assert_eq!(instruction_stmt.children[1].token_type, "operands");
    let operands_pair = &instruction_stmt.children[1];
    assert_eq!(operands_pair.children.len(), 1);
    assert_eq!(operands_pair.children[0].token_type, "operand");
    assert_eq!(operands_pair.children[0].children.len(), 1);
    let operand = &operands_pair.children[0].children[0];
    process_operand(operand, source, false)
}

fn process_singleton_rel32_operands<'a>(
    instruction_stmt: &'a Pair,
    source:  &[u8],
) -> ProcessedOperand<'a> {
    assert_eq!(instruction_stmt.token_type, "instruction_stmt");
    assert_eq!(instruction_stmt.children.len(), 2);
    assert_eq!(instruction_stmt.children[1].token_type, "operands");
    let operands_pair = &instruction_stmt.children[1];
    assert_eq!(operands_pair.children.len(), 1);
    assert_eq!(operands_pair.children[0].token_type, "operand");
    assert_eq!(operands_pair.children[0].children.len(), 1);
    let operand = &operands_pair.children[0].children[0];
    process_operand(operand, source, true)
}

// Parse an instruction statement node which is expected to have 2 operands
fn process_two_operands<'a>(
    instruction_stmt: &'a Pair,
    source:  &[u8],
) -> (ProcessedOperand<'a>, ProcessedOperand<'a>) {
    assert_eq!(instruction_stmt.token_type, "instruction_stmt");
    assert_eq!(instruction_stmt.children.len(), 2);
    assert_eq!(instruction_stmt.children[1].token_type, "operands");
    let operands_pair = &instruction_stmt.children[1];
    assert_eq!(operands_pair.children.len(), 2);
    assert_eq!(operands_pair.children[0].token_type, "operand");
    assert_eq!(operands_pair.children[0].children.len(), 1);
    let first_operand = &operands_pair.children[0].children[0];
    assert_eq!(operands_pair.children[1].token_type, "operand");
    assert_eq!(operands_pair.children[1].children.len(), 1);
    let second_operand = &operands_pair.children[1].children[0];
    (process_operand(&first_operand, source, false), process_operand(&second_operand, source, false))
}

// Returns rm
fn process_register(mode: u8, register: &Pair, source: &[u8]) -> u8 {
    assert_eq!(register.children.len(), 1);
    assert_eq!(register.children[0].token_type, "identifier");
    let register_identifier = &register.children[0];
    let rm: u8 = match &source[register_identifier.start..register_identifier.end] {
        b"rax" => 0,
        b"rcx" => 1,
        b"rdx" => 2,
        b"rbx" => 3,
        b"rsp" => 4,
        b"rbp" => 5,
        b"rsi" => 6,
        b"rdi" => 7,
        x => panic!("Unknown register {:?}", x),
    };
    assert!(mode < 4);
    assert!(rm < 8);
    if mode == 0b10 && rm == 4 {
        panic!("rsp-relative indirect addressing is unimplemented");
    }
    rm
}

fn process_operand<'a>(
    operand: &'a Pair,
    source: &[u8],
    is_rel32: bool,
) -> ProcessedOperand<'a>{
    if operand.token_type == "register" {
        let mode = 0b11;
        let rm = process_register(mode, operand, source);
        RmOperand(RmOperandBody {
            pair: operand,
            mode,
            rm,
            displacement: None,
            displacement_symbol_ref: None,
        })
    } else if operand.token_type == "indirect_register_expr" {
        assert_eq!(operand.children.len(), 2);
        assert_eq!(operand.children[1].token_type, "register");
        let mode = 0b10;
        let rm = process_register(mode, &operand.children[1], source);
        let displacement: i32 = if operand.children[0].token_type == "null" {
            0
        } else if operand.children[0].token_type == "hex_literal" {
            extract_hex_literal(source, &operand.children[0]) as i32
        } else {
            panic!("Unknown child of indirect_register_expr");
        };
        RmOperand( RmOperandBody {
            pair: operand,
            mode,
            rm,
            displacement: Some(displacement),
            displacement_symbol_ref: None,
        })
    } else if !is_rel32 && operand.token_type == "identifier" {
        let mode: u8 = 0b00;
        let rm: u8 = 4;
        let identifier = operand;
        let name = &source[identifier.start..identifier.end].to_vec();
        let symbol_ref = Some(IntermediateSymbolRef {
            section_offset: 0, // temporary
            symbol_name: name.to_vec(),
            ref_type: "R_X86_64_32",
        });
        RmOperand( RmOperandBody {
            pair: operand,
            mode,
            rm,
            displacement: Some(0),
            displacement_symbol_ref: symbol_ref,
        })
    } else if is_rel32 && operand.token_type == "identifier" {
        let identifier = operand;
        let name = &source[identifier.start..identifier.end].to_vec();
        let symbol_ref = Some(IntermediateSymbolRef {
            section_offset: 0, // temporary
            symbol_name: name.to_vec(),
            ref_type: "R_X86_64_PC32",
        });
        ImmOperand( ImmOperandBody {
            pair: operand,
            immediate_value: 0,
            immediate_symbol_ref: symbol_ref,
        })
    } else if operand.token_type == "immediate" {
        assert_eq!(operand.children.len(), 1);
        assert_eq!(operand.children[0].token_type, "hex_literal");
        let src_hex_literal = &operand.children[0];
        let value = extract_hex_literal(source, &src_hex_literal) as u32;
        ImmOperand( ImmOperandBody {
            pair: operand,
            immediate_value: value,
            immediate_symbol_ref: None,
        })
    } else if operand.token_type == "address_immediate" {
        assert_eq!(operand.children.len(), 1);
        assert_eq!(operand.children[0].token_type, "identifier");
        let identifier = &operand.children[0];
        let name = &source[identifier.start..identifier.end].to_vec();
        let symbol_ref = Some(IntermediateSymbolRef {
            section_offset: 0, // temporary
            symbol_name: name.to_vec(),
            ref_type: "R_X86_64_32",
        });
        ImmOperand( ImmOperandBody {
            pair: operand,
            immediate_value: 0,
            immediate_symbol_ref: symbol_ref,
        })
    } else {
        panic!("Unknown operand type: \"{}\"", operand.token_type);
    }
}

fn emit_instruction(
    mut opcode: Vec<u8>,
    mode_reg_rm: Option<(u8, u8, u8)>,
    displacement: Option<i32>,
    displacement_relocation: Option<IntermediateSymbolRef>,
    immediate: Option<i32>,
    immediate_relocation: Option<IntermediateSymbolRef>,
    current_section: &mut IntermediateSection,
    source: &[u8],
) {
    current_section.prog_bits.append(&mut vec![0x48]); // REX prefix
    current_section.prog_bits.append(&mut opcode); // opcode
    
    if let Some((mode, reg, rm)) = mode_reg_rm {
        assert!(mode < 4);
        assert!(rm < 8);
        let modrm: u8 = (mode << 6) + (reg << 3) + rm;
        current_section.prog_bits.append(&mut vec![modrm]); // modrm
        if mode == 0b00 && rm == 4 {
            current_section.prog_bits.append(&mut vec![0x25]); // SIB. Hack
        }
    }
    
    if let Some(displacement) = displacement {
        current_section.prog_bits.append(&mut displacement.to_le_bytes().to_vec()); // disp32
    }

    if let Some(mut relocation) = displacement_relocation {
        relocation.section_offset = current_section.prog_bits.len() as u64 - 4;
        current_section.symbol_refs.push(relocation);
    }

    if let Some(immediate) = immediate {
        current_section.prog_bits.append(&mut immediate.to_le_bytes().to_vec()); // imm32
    }

    if let Some(mut relocation) = immediate_relocation {
        relocation.section_offset = current_section.prog_bits.len() as u64 - 4;
        current_section.symbol_refs.push(relocation);
    }
}

fn build_intermediate_object_file(source: &[u8]) -> IntermediateObjectFile {
    let parse_tree = parse_file(source, 0).unwrap();
    if parse_tree.end != source.len() {
        panic!("Unrecognized chars at position {}", parse_tree.end);
    }
    let mut sections: Vec<IntermediateSection> = Vec::new();
    let mut current_section_idx: Option<usize> = None;
    let mut global_symbol_names: Vec<Vec<u8>> = Vec::new();
    
    for pair in parse_tree.children {
        assert_eq!(pair.token_type, "line");
        assert!(pair.children.len() == 2);
        if pair.children[0].token_type == "label" {
            let label = &pair.children[0];
            assert!(!label.children.is_empty());
            assert_eq!(label.children[0].token_type, "identifier");
            let identifier = &label.children[0];

            let current_section = &mut sections[current_section_idx.expect("No section selected")];
            current_section.symbol_defs.push(IntermediateSymbolDef {
                binding: "local",
                section_offset: current_section.prog_bits.len() as u64,
                symbol_name: source[identifier.start..identifier.end].to_vec(),
            })
        }

        if pair.children[1].token_type == "null" {
            continue;
        }
        assert_eq!(pair.children[1].token_type, "stmt");
        let stmt = &pair.children[1];
        assert_eq!(stmt.children.len(), 1);
        if stmt.children[0].token_type == "directive_stmt" {
            let directive_stmt = &stmt.children[0];

            assert_eq!(directive_stmt.children[0].token_type, "directive");
            let directive = &directive_stmt.children[0];
            
            assert_eq!(directive.children.len(), 1);
            assert_eq!(directive.children[0].token_type, "identifier");

            let identifier = &directive.children[0];
            let identifier_content = &source[identifier.start..identifier.end];

            match identifier_content {
                b"text" => {
                    match sections.iter().position(|section| section.section_name == b".text") {
                        Some(idx) => {
                            current_section_idx = Some(idx);
                        },
                        None => {
                            current_section_idx = Some(sections.len());
                            sections.push(IntermediateSection {
                                section_name: b".text".to_vec(),
                                prog_bits: Vec::new(),
                                symbol_defs: Vec::new(),
                                symbol_refs: Vec::new(),
                            });
                        }
                    }
                },
                b"data" => {
                    match sections.iter().position(|section| section.section_name == b".data") {
                        Some(idx) => {
                            current_section_idx = Some(idx);
                        },
                        None => {
                            current_section_idx = Some(sections.len());
                            sections.push(IntermediateSection {
                                section_name: b".data".to_vec(),
                                prog_bits: Vec::new(),
                                symbol_defs: Vec::new(),
                                symbol_refs: Vec::new(),
                            });
                        }
                    }
                },
                b"byte" => {
                    let current_section = &mut sections[current_section_idx.expect("No section selected")];
                    assert!(directive_stmt.children.len() == 2);
                    assert_eq!(directive_stmt.children[1].token_type, "directive_args");
                    let directive_args = &directive_stmt.children[1];
                    for directive_arg in &directive_args.children {
                        let directive_arg_value = match directive_arg.children[0].token_type {
                            "hex_literal" => extract_hex_literal(source, &directive_arg.children[0]),
                            _ => panic!("Unsupported directive arg"),
                        };
                        current_section.prog_bits.push(directive_arg_value as u8);
                    }
                },
                b"dword" => {
                    let current_section = &mut sections[current_section_idx.expect("No section selected")];
                    assert!(directive_stmt.children.len() == 2);
                    assert_eq!(directive_stmt.children[1].token_type, "directive_args");
                    let directive_args = &directive_stmt.children[1];
                    for directive_arg in &directive_args.children {
                        let directive_arg_value = match directive_arg.children[0].token_type {
                            "hex_literal" => extract_hex_literal(source, &directive_arg.children[0]),
                            "identifier" => {
                                current_section.symbol_refs.push(IntermediateSymbolRef {
                                    section_offset: current_section.prog_bits.len() as u64,
                                    symbol_name: source[directive_arg.children[0].start..directive_arg.children[0].end].to_vec(),
                                    ref_type: "R_X86_64_32",
                                });
                                0
                            },
                            _ => panic!("Unknown directive arg"),
                        };
                        current_section.prog_bits.append(&mut (directive_arg_value as u32).to_le_bytes().to_vec());
                    }
                },
                b"quad" => {
                    let current_section = &mut sections[current_section_idx.expect("No section selected")];
                    assert!(directive_stmt.children.len() == 2);
                    assert_eq!(directive_stmt.children[1].token_type, "directive_args");
                    let directive_args = &directive_stmt.children[1];
                    for directive_arg in &directive_args.children {
                        let directive_arg_value = match directive_arg.children[0].token_type {
                            "hex_literal" => extract_hex_literal(source, &directive_arg.children[0]),
                            "identifier" => {
                                current_section.symbol_refs.push(IntermediateSymbolRef {
                                    section_offset: current_section.prog_bits.len() as u64,
                                    symbol_name: source[directive_arg.children[0].start..directive_arg.children[0].end].to_vec(),
                                    ref_type: "R_X86_64_64",
                                });
                                0
                            },
                            _ => panic!("Unknown directive arg"),
                        };
                        current_section.prog_bits.append(&mut (directive_arg_value as u64).to_le_bytes().to_vec());
                    }
                },
                b"global" => {
                    assert_eq!(directive_stmt.children.len(), 2);
                    let global_stmt_args = &directive_stmt.children[1];
                    if global_stmt_args.children.len() != 1 {
                        panic!("Expected 1 argument for .global directive");
                    }
                    let global_stmt_arg = &global_stmt_args.children[0];
                    assert_eq!(global_stmt_arg.token_type, "directive_arg");
                    assert_eq!(global_stmt_arg.children.len(), 1);
                    if global_stmt_arg.children[0].token_type != "identifier" {
                        panic!("Expected identifier for .global directive");
                    }
                    let identifier = &global_stmt_arg.children[0];
                    let x = source[identifier.start..identifier.end].to_vec();
                    global_symbol_names.push(x);
                },
                b"asciz" => {
                    assert_eq!(directive_stmt.children.len(), 2);
                    let asciiz_stmt_args = &directive_stmt.children[1];
                    if asciiz_stmt_args.children.len() != 1 {
                        panic!("Expected 1 argument for .asciiz directive");
                    }
                    let asciiz_stmt_arg = &asciiz_stmt_args.children[0];
                    assert_eq!(asciiz_stmt_arg.token_type, "directive_arg");
                    assert_eq!(asciiz_stmt_arg.children.len(), 1);
                    if asciiz_stmt_arg.children[0].token_type != "string_literal" {
                        panic!("Expected string literal for .asciiz directive");
                    }
                    let string_literal = &asciiz_stmt_arg.children[0];
                    let mut string_literal_content = extract_string_literal(source, string_literal);
                    string_literal_content.push(0);
                    let current_section = &mut sections[current_section_idx.expect("No section selected")];
                    current_section.prog_bits.append(&mut string_literal_content);
                },
                b"skip" => {
                    assert_eq!(directive_stmt.children.len(), 2);
                    let skip_stmt_args = &directive_stmt.children[1];
                    if skip_stmt_args.children.len() != 1 {
                        panic!("Expected 1 argument for .skip directive");
                    }
                    let skip_stmt_arg = &skip_stmt_args.children[0];
                    assert_eq!(skip_stmt_arg.token_type, "directive_arg");
                    assert_eq!(skip_stmt_arg.children.len(), 1);
                    if skip_stmt_arg.children[0].token_type != "hex_literal" {
                        panic!("Expected hex literal for .skip directive");
                    }
                    let hex_literal = &skip_stmt_arg.children[0];
                    let hex_literal_value = extract_hex_literal(source, hex_literal);
                    let current_section = &mut sections[current_section_idx.expect("No section selected")];
                    for _ in 0..hex_literal_value {
                        current_section.prog_bits.push(0);
                    }
                },
                _ => panic!("Unknown directive"),
            }
        } else if stmt.children[0].token_type == "instruction_stmt" {
            let instruction_stmt = &stmt.children[0];
            let instruction = &instruction_stmt.children[0];
            let instruction_content = &source[instruction.start..instruction.end];
            let current_section = &mut sections[current_section_idx.expect("No section selected")];
            match instruction_content {
                b"movq" => {
                    let x = process_two_operands(instruction_stmt, source);
                    match process_two_operands(instruction_stmt, source) {
                        (ImmOperand(src), RmOperand(dest)) =>
                            // MOV r/m64, imm32 (intel)
                            emit_instruction(vec![0xc7], Some((dest.mode, 0x0, dest.rm)), dest.displacement, dest.displacement_symbol_ref, Some(src.immediate_value as i32), src.immediate_symbol_ref, current_section, source),
                        (RmOperand(src), RmOperand(dest)) =>
                            if dest.mode == 0b11 {
                                // MOV r64, r/m64 (intel)
                                emit_instruction(vec![0x8b], Some((src.mode, dest.rm, src.rm)), src.displacement, src.displacement_symbol_ref, None, None, current_section, source);
                            } else if src.mode == 0b11 {
                                // MOV r/m64, r64 (intel)
                                emit_instruction(vec![0x89], Some((dest.mode, src.rm, dest.rm)), dest.displacement, dest.displacement_symbol_ref, None, None, current_section, source);
                            } else {
                                panic!("Cannot have two memory operands");
                            }
                        _ => panic!("Unsupported operand type"),
                    }
                },

                b"addq" => {
                    match process_two_operands(instruction_stmt, source) {
                        (ImmOperand(src), RmOperand(dest)) =>
                            // ADD r/m64, imm32 (intel)
                            emit_instruction(vec![0x81], Some((dest.mode, 0x0, dest.rm)), dest.displacement, dest.displacement_symbol_ref, Some(src.immediate_value as i32), src.immediate_symbol_ref, current_section, source),
                        (RmOperand(src), RmOperand(dest)) =>
                            if dest.mode == 0b11 {
                                // ADD r64, r/m64 (intel)
                                emit_instruction(vec![0x03], Some((src.mode, dest.rm, src.rm)), src.displacement, src.displacement_symbol_ref, None, None, current_section, source);
                            } else if src.mode == 0b11 {
                                // ADD r/m64, r64 (intel)
                                emit_instruction(vec![0x01], Some((dest.mode, src.rm, dest.rm)), dest.displacement, dest.displacement_symbol_ref, None, None, current_section, source);
                            } else {
                                panic!("Cannot have two memory operands");
                            }
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"orq" => {
                    match process_two_operands(instruction_stmt, source) {
                        (ImmOperand(src), RmOperand(dest)) =>
                            emit_instruction(vec![0x81], Some((dest.mode, 0x1, dest.rm)), dest.displacement, dest.displacement_symbol_ref, Some(src.immediate_value as i32), src.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                // ADC (add with carry) is 81 /2
                // SBB (subtract with borrow) is 81 /3
                b"andq" => {
                    match process_two_operands(instruction_stmt, source) {
                        (ImmOperand(src), RmOperand(dest)) =>
                            emit_instruction(vec![0x81], Some((dest.mode, 0x4, dest.rm)), dest.displacement, dest.displacement_symbol_ref, Some(src.immediate_value as i32), src.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"subq" => {
                    match process_two_operands(instruction_stmt, source) {
                        (ImmOperand(src), RmOperand(dest)) =>
                            emit_instruction(vec![0x81], Some((dest.mode, 0x5, dest.rm)), dest.displacement, dest.displacement_symbol_ref, Some(src.immediate_value as i32), src.immediate_symbol_ref, current_section, source),
                        (RmOperand(src), RmOperand(dest)) =>
                            if dest.mode == 0b11 {
                                // SUB r64, r/m64 (intel)
                                emit_instruction(vec![0x2b], Some((src.mode, dest.rm, src.rm)), src.displacement, src.displacement_symbol_ref, None, None, current_section, source);
                            } else if src.mode == 0b11 {
                                // SUB r/m64, r64 (intel)
                                emit_instruction(vec![0x29], Some((dest.mode, src.rm, dest.rm)), dest.displacement, dest.displacement_symbol_ref, None, None, current_section, source);
                            } else {
                                panic!("Cannot have two memory operands");
                            }
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"xorq" => {
                    match process_two_operands(instruction_stmt, source) {
                        (ImmOperand(src), RmOperand(dest)) =>
                            emit_instruction(vec![0x81], Some((dest.mode, 0x6, dest.rm)), dest.displacement, dest.displacement_symbol_ref, Some(src.immediate_value as i32), src.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"cmpq" => {
                    match process_two_operands(instruction_stmt, source) {
                        (ImmOperand(src), RmOperand(dest)) =>
                            emit_instruction(vec![0x81], Some((dest.mode, 0x7, dest.rm)), dest.displacement, dest.displacement_symbol_ref, Some(src.immediate_value as i32), src.immediate_symbol_ref, current_section, source),
                        (RmOperand(src), RmOperand(dest)) =>
                            if src.mode != 0b11 && dest.mode == 0b11 {
                                // CMP r64, r/m64 (intel)
                                emit_instruction(vec![0x3b], Some((src.mode, dest.rm, src.rm)), src.displacement, src.displacement_symbol_ref, None, None, current_section, source);
                            } else if src.mode == 0b11 && dest.mode != 0b11 {
                                // CMP r/m64, r64 (intel)
                                emit_instruction(vec![0x39], Some((dest.mode, src.rm, dest.rm)), dest.displacement, dest.displacement_symbol_ref, None, None, current_section, source);
                            } else {
                                panic!("Cannot have two memory operands");
                            }
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"testq" => {
                    match process_two_operands(instruction_stmt, source) {
                        (ImmOperand(src), RmOperand(dest)) =>
                            emit_instruction(vec![0xf7], Some((dest.mode, 0x0, dest.rm)), dest.displacement, dest.displacement_symbol_ref, Some(src.immediate_value as i32), src.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"call" | b"callq" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0xe8], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jmp" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0xe9], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jz" | b"je" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x84], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jnz" | b"jne" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x85], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jg" | b"jnle" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x8f], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jge" | b"jnl" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x8d], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jl" | b"jnge" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x8c], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jle" | b"jng" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x8e], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"ja" | b"jnbe" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x87], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jae" | b"jnb" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x83], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jb" | b"jnae" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x82], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"jbe" | b"jna" => {
                    match process_singleton_rel32_operands(instruction_stmt, source) {
                        ImmOperand(o) => emit_instruction(vec![0x0f, 0x86], None, None, None, Some(o.immediate_value as i32), o.immediate_symbol_ref, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"pushq" => {
                    match process_singleton_operands(instruction_stmt, source) {
                        RmOperand(o) => emit_instruction(vec![0xff], Some((o.mode, 0x6, o.rm)), o.displacement, o.displacement_symbol_ref, None, None, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"popq" => {
                    match process_singleton_operands(instruction_stmt, source) {
                        RmOperand(o) => emit_instruction(vec![0x8f], Some((o.mode, 0x0, o.rm)), o.displacement, o.displacement_symbol_ref, None, None, current_section, source),
                        _ => panic!("Unsupported operand type"),
                    }
                },
                b"syscall" => {
                    process_no_operands(instruction_stmt, source);
                    emit_instruction(vec![0x0f, 0x05], None, None, None, None, None, current_section, source);
                },
                b"retq" => {
                    process_no_operands(instruction_stmt, source);
                    emit_instruction(vec![0xc3], None, None, None, None, None, current_section, source);
                },
                unknown => {
                    panic!("Unknown instruction: {}", String::from_utf8_lossy(unknown));
                },
            }
        } else {
            panic!("Unimplemented statement type");
        }
    }
    for section in sections.iter_mut() {
        for symbol in section.symbol_defs.iter_mut() {
            if global_symbol_names.iter().any(|name| name == &symbol.symbol_name) {
                symbol.binding = "global";
            }
        }
    }

    IntermediateObjectFile {
        sections,
    }
}
fn build_object_file(intermediate_object_file: IntermediateObjectFile) -> ObjectFile {
    let mut strings: Vec<Vec<u8>> = Vec::new();

    let mut sections: Vec<Section> = Vec::new();
    let mut symbols: Vec<Symbol> = vec![];

    sections.push(Section {
        name_strtab_index: 0,
        offset: 0,
        length: 0,
        section_type: SectionType::NullSection,
    });

    for intermediate_section in &intermediate_object_file.sections {
        let section_name_idx = find_or_add(&mut strings, &intermediate_section.section_name) as u32;
        sections.push(
            Section {
                name_strtab_index: section_name_idx,
                offset: 0, // temporary
                length: 0, // temporary
                section_type: SectionType::ProgbitsSection(
                    ProgbitsSectionBody {
                        content: intermediate_section.prog_bits.clone(),
                        is_executable: intermediate_section.section_name == b".text",
                        is_writable: intermediate_section.section_name == b".data",
                    }
                ),
            },
        );
        symbols.push(Symbol {
            binding: "local",
            _type: "section",
            name_strtab_index: section_name_idx,
            value: 0,
            section_index: sections.len() as u16 - 1,
        });
        for symbol_def in &intermediate_section.symbol_defs {
            let name_strtab_index = find_or_add(&mut strings, &symbol_def.symbol_name) as u32;
            symbols.push(Symbol {
                binding: symbol_def.binding,
                _type: "notype",
                name_strtab_index,
                value: symbol_def.section_offset,
                section_index: sections.len() as u16 - 1,
            });
        }
    }

    let mut sorted_symbols: Vec<Symbol> = vec![];
    let mut num_local_symbols: u32 = 0;
    for symbol in &symbols {
        if symbol.binding == "local" {
            sorted_symbols.push(symbol.clone());
            num_local_symbols += 1;
        }
    }
    for symbol in &symbols {
        if symbol.binding == "global" {
            sorted_symbols.push(symbol.clone());
        }
    }
    drop(symbols);

    for section in &intermediate_object_file.sections {
        for symbol_ref in &section.symbol_refs {
            let ref_name_strtab_index = find_or_add(&mut strings, &symbol_ref.symbol_name) as u32;
            // O(n^2), can be improved to O(n)
            if !sorted_symbols.iter().any(|s| s.name_strtab_index == ref_name_strtab_index) {
                // Insert an undefined-section symbol
                sorted_symbols.push(Symbol {
                    binding: "global",
                    _type: "notype",
                    name_strtab_index: ref_name_strtab_index,
                    value: 0,
                    section_index: 0,
                });
            }
        }
    }
    
    // for each section:
    for (section_idx, section) in intermediate_object_file.sections.iter().enumerate() {
        // initialize a relocation list for this section
        let mut relocations: Vec<Rela> = Vec::new();
        // for each symbol ref:
        for symbol_ref in &section.symbol_refs {
            // find whether we have a symbol def in `symbols` with the same name
            let symbol_strtab_index = find_or_add(&mut strings, &symbol_ref.symbol_name) as u32;
            let maybe_symbol_index = sorted_symbols
                .iter()
                .position(|s| s.name_strtab_index == symbol_strtab_index);
            if let Some(symbol_index) = maybe_symbol_index {
                let symbol = &sorted_symbols[symbol_index];
                if symbol.binding == "global" {
                    // if we have one and it's global, add a reloc to the symbol name
                    relocations.push(Rela {
                        addend: if symbol_ref.ref_type == "R_X86_64_PC32" { -4 } else { 0 }, // Hack
                        symbol_index: symbol_index as u32 + 1,
                        type_: match symbol_ref.ref_type {
                            "R_X86_64_32" => 10,
                            "R_X86_64_64" => 1,
                            "R_X86_64_PC32" => 2,
                            _ => panic!("Unknown relocation type"),
                        },
                        reference_offset: symbol_ref.section_offset,
                    });
                } else if symbol.binding == "local" {
                    // if we have one and it's local, add a reloc to the section name with an addend
                    let referenced_section_index = symbol.section_index;
                    let referenced_section_name_strtab_index = sections[referenced_section_index as usize].name_strtab_index;
                    let referenced_section_symbol_index = sorted_symbols
                        .iter()
                        .position(|s| s.name_strtab_index == referenced_section_name_strtab_index)
                        .unwrap();
                    relocations.push(Rela {
                        addend: if symbol_ref.ref_type == "R_X86_64_PC32" { symbol.value as i64 - 4 } else { symbol.value as i64 }, // Hack
                        symbol_index: referenced_section_symbol_index as u32 + 1,
                        type_: match symbol_ref.ref_type {
                            "R_X86_64_32" => 10,
                            "R_X86_64_64" => 1,
                            "R_X86_64_PC32" => 2,
                            _ => panic!("Unknown relocation type"),
                        },
                        reference_offset: symbol_ref.section_offset,
                    });
                } else {
                    panic!("Symbol binding not implemented")
                }
            } else {
                panic!("Undefined symbol");
            }
        }
        let rela_section_name = format!(".rela{}", String::from_utf8_lossy(&section.section_name)).into_bytes();
        let rela_section_name_strtab_index = find_or_add(&mut strings, &rela_section_name) as u32;

        // add a relocation section with the intermediate relocation list
        sections.push(Section {
            name_strtab_index: rela_section_name_strtab_index,
            offset: 0, // temporary
            length: 0, // temporary
            section_type: SectionType::RelaSection(RelaSectionBody {
                referenced_section_index: section_idx as u16 + 1,
                relocations,
            }),
        });
    }

    let lit_symtab_idx = find_or_add(&mut strings, &b".symtab".to_vec()) as u32;
    sections.push(Section {
        name_strtab_index: lit_symtab_idx,
        offset: 0, // temporary
        length: 0, // temporary
        section_type: SectionType::SymtabSection(SymtabSectionBody {
            symbols: sorted_symbols,
            num_local_symbols,
        }),
    });

    let lit_strtab_idx = find_or_add(&mut strings, &b".strtab".to_vec()) as u32;
    sections.push(Section {
        name_strtab_index: lit_strtab_idx,
        offset: 0, // temporary
        length: 0, // temporary
        section_type: SectionType::StrtabSection(
            StrtabSectionBody { strings }
        ),
    });

    let mut object_file = ObjectFile { sections };

    object_file
}

fn build_file_content(mut object_file: ObjectFile) -> Vec<u8> {
    let strtab_index = object_file.sections.iter().position(|section| {
        match section.section_type {
            SectionType::StrtabSection(_) => true,
            _ => false,
        }
    }).unwrap() as u16;

    let mut content: Vec<u8> = Vec::new();
    // e_ident[16]; /* ELF identification */
    content.append(&mut vec![0x7f, 0x45, 0x4c, 0x46, 0x02, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
    // e_type; /* Object file type */
    content.append(&mut vec![0x01, 0x00].to_vec());
    // e_machine; /* Machine type */
    content.append(&mut vec![0x3e, 0x00]);
    // e_version; /* Object file version */
    content.append(&mut vec![0x01, 0x00, 0x00, 0x00]);
    // e_entry; /* Entry point address */
    content.append(&mut vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
    // e_phoff; /* Program header offset */
    content.append(&mut vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
    // e_shoff; /* Section header offset */
    content.append(&mut vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
    // e_flags; /* Processor-specific flags */
    content.append(&mut vec![0x00, 0x00, 0x00, 0x00]);
    // e_ehsize; /* ELF header size */
    content.append(&mut vec![0x40, 0x00]);
    // e_phentsize; /* Size of program header entry */
    content.append(&mut vec![0x00, 0x00]);
    // e_phnum; /* Number of program header entries */
    content.append(&mut vec![0x00, 0x00]);
    // e_shentsize; /* Size of section header entry */
    content.append(&mut vec![0x40, 0x00]);
    // e_shnum; /* Number of section header entries */
    content.append(&mut (object_file.sections.len() as u16).to_le_bytes().to_vec());
    // e_shstrndx; /* Section name string table index */
    content.append(&mut strtab_index.to_le_bytes().to_vec());

    // Convert strtab indexes to strtab offsets
    let mut strtab_offsets: Vec<u32> = Vec::new();
    if let SectionType::StrtabSection(body) = &object_file.sections[strtab_index as usize].section_type {
        let mut offset = 1; // Account for initial 0x00 at start of strtab
        for string in body.strings.iter() {
            strtab_offsets.push(offset);
            offset += string.len() as u32 + 1; // Account for null terminator
        }
    } else {
        panic!("Inconsistent strtab_index");
    }


    for section in object_file.sections.iter_mut() {
        match &section.section_type {
            SectionType::NullSection => {
                // No-op
            },
            SectionType::ProgbitsSection(body) => {
                section.offset = content.len() as u32;
                content.append(&mut body.content.clone());
                section.length = content.len() as u32 - section.offset;
            },
            SectionType::StrtabSection(body) => {
                section.offset = content.len() as u32;
                content.push(0x00);
                for string in body.strings.iter() {
                    content.append(&mut string.clone());
                    content.push(0);
                }
                section.length = content.len() as u32 - section.offset;
            },
            SectionType::SymtabSection(body) => {
                section.offset = content.len() as u32;
                // Null symbol
                for _ in 0..0x18 {
                    content.push(0x00);
                }
                for symbol in body.symbols.iter() {
                    content.append(&mut (strtab_offsets[symbol.name_strtab_index as usize]).to_le_bytes().to_vec());
                    let binding: u8 = match symbol.binding {
                        "local" => 0x0,
                        "global" => 0x1,
                        _ => panic!("Unknown symbol type"),
                    };
                    let _type: u8 = match symbol._type {
                        "notype" => 0x0,
                        "section" => 0x3,
                        _ => panic!("Unknown symbol type"),
                    };
                    content.append(&mut vec![binding << 4 + _type]); // binding = ST_GLOBAL, type = NO_TYPE
                    content.append(&mut vec![0x00]); // Reserved, must be zero
                    content.append(&mut symbol.section_index.to_le_bytes().to_vec());
                    content.append(&mut symbol.value.to_le_bytes().to_vec());
                    content.append(&mut vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]); // Value
                }
                section.length = content.len() as u32 - section.offset;
            }
            SectionType::RelaSection(body) => {
                section.offset = content.len() as u32;
                for rela in body.relocations.iter() {
                    let r_info: u64 = (rela.symbol_index as u64) << 32 | rela.type_ as u64;
                    content.append(&mut rela.reference_offset.to_le_bytes().to_vec());
                    content.append(&mut r_info.to_le_bytes().to_vec());
                    content.append(&mut rela.addend.to_le_bytes().to_vec());
                }
                section.length = content.len() as u32 - section.offset;
            },
        }
    }

    let shoff_array = (content.len() as u64).to_le_bytes();
    content[0x28..0x30].copy_from_slice(&shoff_array);

    for section in &object_file.sections {
        // sh_name; /* Section name */
        match section.section_type {
            SectionType::NullSection => {
                content.append(&mut vec![0x00, 0x00, 0x00, 0x00]);
            },
            _ => {
                content.append(&mut strtab_offsets[section.name_strtab_index as usize].to_le_bytes().to_vec());
            },
        }
        // sh_type; /* Section type */
        match section.section_type {
            SectionType::NullSection => {
                content.append(&mut vec![0x00, 0x00, 0x00, 0x00]);
            },
            SectionType::ProgbitsSection(_) => {
                content.append(&mut vec![0x01, 0x00, 0x00, 0x00]);
            },
            SectionType::StrtabSection(_) => {
                content.append(&mut vec![0x03, 0x00, 0x00, 0x00]);
            },
            SectionType::SymtabSection(_) => {
                content.append(&mut vec![0x02, 0x00, 0x00, 0x00]);
            },
            SectionType::RelaSection(_) => {
                content.append(&mut vec![0x04, 0x00, 0x00, 0x00]);
            },
            _ => todo!("Other section types"),
        }
        // sh_flags; /* Section attributes */
        match &section.section_type {
            SectionType::ProgbitsSection(body) => {
                let flags: u64 = (body.is_writable as u64) // SHF_WRITE
                    | 0x2 // SHF_ALLOC
                    | ((body.is_executable as u64) << 2); // SHF_EXECINSTR
                content.append(&mut flags.to_le_bytes().to_vec());
            },
            _ => {
                content.append(&mut vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            },
        }
        // sh_addr; /* Virtual address in memory */
        content.append(&mut vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
        // sh_offset; /* Offset in file */
        content.append(&mut (section.offset as u64).to_le_bytes().to_vec());
        // sh_size; /* Size of section */
        content.append(&mut (section.length as u64).to_le_bytes().to_vec());
        // sh_link; /* Link to other section */
        match &section.section_type {
            SectionType::SymtabSection(_) => {
                content.append(&mut (strtab_index as u32).to_le_bytes().to_vec());
            },
            SectionType::RelaSection(_) => {
                let symtab_section_index = &object_file.sections.len() - 2;
                content.append(&mut (symtab_section_index as u32).to_le_bytes().to_vec());
            }
            _ => {
                content.append(&mut vec![0x00, 0x00, 0x00, 0x00]);
            },
        }
        // sh_info; /* Miscellaneous information */
        match &section.section_type {
            SectionType::SymtabSection(symtab_body) => {
                let mut v = (symtab_body.num_local_symbols + 1).to_le_bytes().to_vec();
                content.append(&mut v);
            },
            SectionType::RelaSection(body) => {
                content.append(&mut (body.referenced_section_index as u32).to_le_bytes().to_vec());
            }
            _ => {
                content.append(&mut vec![0x00, 0x00, 0x00, 0x00]);
            },
        }
        // sh_addralign; /* Address alignment boundary */
        content.append(&mut vec![0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
        // sh_entsize; /* Size of entries, if section has table */
        match section.section_type {
            SectionType::SymtabSection(_) => {
                content.append(&mut vec![0x18, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            },
            SectionType::RelaSection(_) => {
                content.append(&mut vec![0x18, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            }
            _ => {
                content.append(&mut vec![0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
            },
        }
    }
    content
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 2);
    let file_path = &args[1];
    let source = std::fs::read(file_path).unwrap();
    let intermediate_object_file = build_intermediate_object_file(&source[..]);
    let object_file = build_object_file(intermediate_object_file);
    let content = build_file_content(object_file);
    // write to file
    std::fs::write("a.out", content).unwrap();
}

#[derive(Debug, PartialEq)]
struct Pair {
    token_type: &'static str,
    start: usize,
    end: usize,
    children: Vec<Pair>
}

fn parse_single_char(char: u8, s: &[u8], start: usize) -> Option<Pair> {
    if start >= s.len() {
        return None
    }
    if s[start] == char {
        return Some(Pair {
            start,
            end: start + 1,
            token_type: "single_char",
            children: Vec::new(),
        })
    }
    None
}

fn parse_oneormore_space(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos: usize = start;
    loop {
        match parse_single_char(b' ', s, pos) {
            Some(pair) => {
                pos = pair.end;
            }
            None => { break; }
        }
    }
    if pos > start {
        Some(Pair {
            start,
            end: pos,
            token_type: "oneormore_space",
            children: Vec::new(),
        })
    } else {
        None
    }
}

fn parse_zeroormore_space(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos: usize = start;
    loop {
        match parse_single_char(b' ', s, pos) {
            Some(pair) => {
                pos = pair.end;
            }
            None => { break; }
        }
    }
    Some(Pair {
        start,
        end: pos,
        token_type: "zeroormore_space",
        children: Vec::new(),
    })
}

fn parse_single_hex_digit(s: &[u8], start: usize) -> Option<Pair> {
    if start >= s.len() {
        return None
    }
    if
        s[start] >= b'0' && s[start] <= b'9' ||
        s[start] >= b'a' && s[start] <= b'f' ||
        s[start] >= b'A' && s[start] <= b'F'
    {
        return Some(Pair {
            start,
            end: start + 1,
            token_type: "single_hex_digit",
            children: Vec::new(),
        })
    }
    None
}

fn parse_identifier_start_char(s: &[u8], start: usize) -> Option<Pair> {
    if start >= s.len() {
        return None
    }
    if
        s[start] >= b'a' && s[start] <= b'z' ||
        s[start] >= b'A' && s[start] <= b'Z' ||
        s[start] == b'_'
    {
        return Some(Pair {
            start,
            end: start + 1,
            token_type: "identifier_start_char",
            children: Vec::new(),
        })
    }
    None
}

fn parse_identifier_continuation_char(s: &[u8], start: usize) -> Option<Pair> {
    if start >= s.len() {
        return None
    }
    if
        s[start] >= b'a' && s[start] <= b'z' ||
        s[start] >= b'A' && s[start] <= b'Z' ||
        s[start] >= b'0' && s[start] <= b'9' ||
        s[start] == b'_'
    {
        return Some(Pair {
            start,
            end: start + 1,
            token_type: "identifier_continuation_char",
            children: Vec::new(),
        })
    }
    None
}

fn parse_not_newline_char(s: &[u8], start: usize) -> Option<Pair> {
    if start >= s.len() {
        return None
    }
    if s[start] != b'\n' {
        return Some(Pair {
            start,
            end: start + 1,
            token_type: "not_whitespace_char",
            children: Vec::new(),
        })
    }
    None
}

fn parse_string_literal_normal_char(s: &[u8], start: usize) -> Option<Pair> {
    if start >= s.len() {
        return None
    }
    if s[start] != b'\n' && s[start] != b'"' && s[start] != b'\\' {
        return Some(Pair {
            start,
            end: start + 1,
            token_type: "string_literal_normal_char",
            children: Vec::new(),
        })
    }
    None
}

fn parse_hex_literal(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos: usize = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_single_char(b'-', s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        }
        None => {
            children.push(Pair {
                start: pos,
                end: pos,
                token_type: "null",
                children: vec![],
            });
        }
    }
    match parse_single_char(b'0', s, pos) {
        Some(pair) => {
            pos = pair.end;
        }
        None => { return None }
    }
    match parse_single_char(b'x', s, pos) {
        Some(pair) => {
            pos = pair.end;
        }
        None => { return None }
    }
    loop {
        match parse_single_hex_digit(s, pos) {
            Some(pair) => {
                pos = pair.end;
                children.push(pair);
            }
            None => { break; }
        }
    }
    if pos > start {
        Some(Pair {
            start,
            end: pos,
            token_type: "hex_literal",
            children,
        })
    } else {
        None
    }
}

fn parse_string_literal_charrep(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos: usize = start;
    match parse_single_char(b'\\', s, pos) {
        Some(pair) => {
            pos = pair.end;
            if let Some(pair) = parse_single_char(b'\\', s, pos) {
                pos = pair.end;
                return Some(Pair {
                    start: start,
                    end: pair.end,
                    token_type: "string_literal_charrep",
                    children: vec![pair],
                });
            }
            if let Some(pair) = parse_single_char(b'"', s, pos) {
                pos = pair.end;
                return Some(Pair {
                    start,
                    end: pair.end,
                    token_type: "string_literal_charrep",
                    children: vec![pair],
                });
            }
            if let Some(pair) = parse_single_char(b'n', s, pos) {
                pos = pair.end;
                return Some(Pair {
                    start,
                    end: pair.end,
                    token_type: "string_literal_charrep",
                    children: vec![pair],
                });
            }
            return None;
        },
        None => {
            match parse_string_literal_normal_char(s, pos) {
                Some(pair) => {
                    pos = pair.end;
                    return Some(Pair {
                        start: pair.start,
                        end: pair.end,
                        token_type: "string_literal_charrep",
                        children: vec![pair],
                    });
                }
                None => { return None }
            }
        }
    };
}

fn parse_string_literal(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos: usize = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_single_char(b'"', s, pos) {
        Some(pair) => {
            pos = pair.end;
        }
        None => { return None }
    }
    loop {
        match parse_string_literal_charrep(s, pos) {
            Some(pair) => {
                pos = pair.end;
                children.push(pair);
            }
            None => { break; }
        }
    }
    match parse_single_char(b'"', s, pos) {
        Some(pair) => {
            pos = pair.end;
        }
        None => { return None }
    }
    Some(Pair {
        start,
        end: pos,
        token_type: "string_literal",
        children,
    })
}

fn parse_identifier(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_identifier_start_char(s, pos) {
        None => { return None },
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
    }
    loop {
        match parse_identifier_continuation_char(s, pos) {
            Some(pair) => {
                pos = pair.end;
                children.push(pair);
            }
            None => { break; }
        }
    }
    Some(Pair {
        start,
        end: pos,
        token_type: "identifier",
        children,
    })
}

fn parse_directive(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut child: Pair;
    match parse_single_char(b'.', s, start) {
        Some(pair) => { pos = pair.end },
        None => { return None },
    };
    match parse_identifier(s, pos) {
        Some(pair) => {
            pos = pair.end;
            child = pair;
        },
        None => { return None }
    };
    Some( Pair {
        start,
        end: pos,
        token_type: "directive",
        children: vec![child],
    })
}

fn parse_label(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_identifier(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        }
        None => { return None },
    }
    match parse_single_char(b':', s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
            return Some(Pair {
                start,
                end: pos,
                token_type: "label",
                children,
            })            
        },
        None => { return None }
    }
}

fn parse_directive_arg(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_hex_literal(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
            return Some(Pair {
                start,
                end: pos,
                token_type: "directive_arg",
                children,
            })
        }
        None => {},
    }
    match parse_string_literal(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
            return Some(Pair {
                start,
                end: pos,
                token_type: "directive_arg",
                children,
            })
        }
        None => {},
    }
    match parse_identifier(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
            return Some(Pair {
                start,
                end: pos,
                token_type: "directive_arg",
                children,
            })
        }
        None => {},
    }
    None
}

fn parse_directive_args(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_directive_arg(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
        None => { return None }
    };
    loop {
        match parse_zeroormore_space(s, pos) {
            Some(pair) => { pos = pair.end },
            None => panic!(),
        };
        match parse_single_char(b',', s, pos) {
            Some(pair) => { pos = pair.end },
            None => { break; }
        };
        match parse_zeroormore_space(s, pos) {
            Some(pair) => { pos = pair.end },
            None => panic!(),
        };
        match parse_directive_arg(s, pos) {
            Some(pair) => {
                pos = pair.end;
                children.push(pair);
            }
            None => { break; }
        }
    }
    Some(Pair {
        start,
        end: children.last().unwrap().end,
        token_type: "directive_args",
        children,
    })
}

fn parse_directive_stmt(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_directive(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
        None => { return None }
    };
    match parse_zeroormore_space(s, pos) {
        Some(pair) => { pos = pair.end },
        None => panic!(),
    };
    match parse_directive_args(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
        None => {},
    };
    Some(Pair {
        start,
        end: pos,
        token_type: "directive_stmt",
        children,
    })
}

fn parse_register(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut child: Pair;
    match parse_single_char(b'%', s, pos) {
        Some(pair) => {
            pos = pair.end;
        },
        None => { return None; },
    };
    match parse_identifier(s, pos) {
        Some(pair) => {
            pos = pair.end;
            child = pair;
        },
        None => { return None }
    }
    Some(Pair {
        start,
        end: pos,
        token_type: "register",
        children: vec![child],
    })
}

fn parse_indirect_register_expr(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = vec![];
    match parse_hex_literal(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
        None => {
            children.push(Pair {
                start: pos,
                end: pos,
                token_type: "null",
                children: vec![],
            });
        }
    };
    match parse_single_char(b'(', s, pos) {
        Some(pair) => { pos = pair.end; },
        None => { return None; }
    };

    let space = parse_zeroormore_space(s, pos).unwrap();
    pos = space.end;

    match parse_register(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
        None => { return None; }
    }

    let space = parse_zeroormore_space(s, pos).unwrap();
    pos = space.end;

    match parse_single_char(b')', s, pos) {
        Some(pair) => { pos = pair.end; },
        None => { return None; }
    };
    Some(Pair {
        start,
        end: pos,
        token_type: "indirect_register_expr",
        children,
    })
}

fn parse_immediate(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut child: Pair;
    match parse_single_char(b'$', s, pos) {
        Some(pair) => {
            pos = pair.end;
        },
        None => { return None; },
    };
    match parse_hex_literal(s, pos) {
        Some(pair) => {
            pos = pair.end;
            child = pair;
        },
        None => { return None }
    }
    Some(Pair {
        start,
        end: pos,
        token_type: "immediate",
        children: vec![child],
    })
}

fn parse_address_immediate(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut child: Pair;
    match parse_single_char(b'$', s, pos) {
        Some(pair) => {
            pos = pair.end;
        },
        None => { return None; },
    };
    match parse_identifier(s, pos) {
        Some(pair) => {
            pos = pair.end;
            child = pair;
        },
        None => { return None }
    }
    Some(Pair {
        start,
        end: pos,
        token_type: "address_immediate",
        children: vec![child],
    })
}

fn parse_operand(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut child: Pair;
    if let Some(pair) = parse_register(s, pos) {
        // return pair?
        pos = pair.end;
        return Some(Pair {
            start,
            end: pos,
            token_type: "operand",
            children: vec![pair],
        })
    }
    if let Some(pair) = parse_indirect_register_expr(s, pos) {
        // return pair?
        pos = pair.end;
        return Some(Pair {
            start,
            end: pos,
            token_type: "operand",
            children: vec![pair],
        })
    }
    if let Some(pair) = parse_immediate(s, pos) {
        // return pair?
        pos = pair.end;
        return Some(Pair {
            start,
            end: pos,
            token_type: "operand",
            children: vec![pair],
        })
    }
    if let Some(pair) = parse_address_immediate(s, pos) {
        // return pair?
        pos = pair.end;
        return Some(Pair {
            start,
            end: pos,
            token_type: "operand",
            children: vec![pair],
        })
    }
    if let Some(pair) = parse_identifier(s, pos) {
        // return pair?
        pos = pair.end;
        return Some(Pair {
            start,
            end: pos,
            token_type: "operand",
            children: vec![pair],
        })
    }
    
    None
}

fn parse_operands(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_operand(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
        None => { return None }
    };
    loop {
        match parse_zeroormore_space(s, pos) {
            Some(pair) => { pos = pair.end },
            None => panic!(),
        };
        match parse_single_char(b',', s, pos) {
            Some(pair) => { pos = pair.end },
            None => { break; }
        };
        match parse_zeroormore_space(s, pos) {
            Some(pair) => { pos = pair.end },
            None => panic!(),
        };
        match parse_operand(s, pos) {
            Some(pair) => {
                pos = pair.end;
                children.push(pair);
            }
            None => { break; }
        }
    }
    Some(Pair {
        start,
        end: children.last().unwrap().end,
        token_type: "operands",
        children,
    })
}

fn parse_instruction_stmt(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_identifier(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
        None => { return None }
    };
    match parse_zeroormore_space(s, pos) {
        Some(pair) => { pos = pair.end },
        None => panic!(),
    };
    match parse_operands(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
        None => {},
    };
    Some(Pair {
        start,
        end: pos,
        token_type: "instruction_stmt",
        children,
    })
}

fn parse_stmt(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut child: Pair;
    if let Some(pair) = parse_directive_stmt(s, pos) {
        // return pair?
        pos = pair.end;
        return Some(Pair {
            start,
            end: pos,
            token_type: "stmt",
            children: vec![pair],
        })
    }
    if let Some(pair) = parse_instruction_stmt(s, pos) {
        // return pair?
        pos = pair.end;
        return Some(Pair {
            start,
            end: pos,
            token_type: "stmt",
            children: vec![pair],
        })
    }
    None
}

fn parse_comment(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    match parse_single_char(b'/', s, pos) {
        Some(pair) => { pos = pair.end;},
        None => { return None }
    };
    match parse_single_char(b'/', s, pos) {
        Some(pair) => { pos = pair.end;},
        None => { return None }
    };
    loop {
        match parse_not_newline_char(s, pos) {
            Some(pair) => { pos = pair.end; },
            None => { break; }
        }
    }
    Some(Pair {
        start,
        end: pos,
        token_type: "comment",
        children: vec![],
    })
}

fn parse_line(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = Vec::new();
    match parse_zeroormore_space(s, pos) {
        Some(pair) => { pos = pair.end },
        None => panic!(),
    };
    match parse_label(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        }
        None => {
            children.push(Pair {
                start: pos,
                end: pos,
                token_type: "null",
                children: vec![],
            })
        },
    }
    match parse_zeroormore_space(s, pos) {
        Some(pair) => { pos = pair.end },
        None => panic!(),
    };
    match parse_stmt(s, pos) {
        Some(pair) => {
            pos = pair.end;
            children.push(pair);
        },
        None => {
            children.push(Pair {
                start: pos,
                end: pos,
                token_type: "null",
                children: vec![],
            })
        }
    };
    match parse_zeroormore_space(s, pos) {
        Some(pair) => { pos = pair.end },
        None => panic!(),
    };
    match parse_comment(s, pos) {
        Some(pair) => { pos = pair.end; },
        None => {},
    }
    match parse_single_char(b'\n', s, pos) {
        Some(pair) => { pos = pair.end },
        None => { return None },
    };
    Some(Pair {
        start,
        end: pos,
        token_type: "line",
        children,
    })
}

fn parse_file(s: &[u8], start: usize) -> Option<Pair> {
    let mut pos = start;
    let mut children: Vec<Pair> = Vec::new();
    loop {
        match parse_line(s, pos) {
            Some(pair) => {
                pos = pair.end;
                children.push(pair);
            },
            None => { break; }
        };
    }
    match parse_zeroormore_space(s, pos) {
        Some(pair) => { pos = pair.end },
        None => panic!(),
    };
    Some(Pair {
        start,
        end: pos,
        token_type: "file",
        children,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_assemble_instructions() {
        let raw_bytes: &[u8] = br#"
        .text
        .global _start
        _start:
            movq $0x1001, %rax
            movq $0x1002, %rcx
            movq $data_label_1, %rax
            movq $data_label_1, data_label_2
            movq $undefined_label, %rax
            movq $0x1003, 0x8(%rax)
            movq 0x01020304(%rax), %rcx
            movq %rax, %rcx
            movq %rcx, 0x01020304(%rax)
            
            addq $0x1101, %rax
            addq 0x01020304(%rax), %rcx
            addq %rcx, 0x01020304(%rax)
            cmpq $0x1102, %rax
            
            pushq %rax
            popq %rcx

            callq text_label
            jmp text_label
            jz text_label
            jnz text_label
            syscall
        text_label:
            retq

        .data
            .quad 0x2001
            .skip 0x8
        data_label_1:
            .quad 0x2002
        data_label_2:
            .asciz "Hello \"quoted\" World\n"
        "#;
        let r = build_intermediate_object_file(raw_bytes);
        assert_eq!(r.sections[0].section_name, b".text");
        assert_eq!(r.sections[0].prog_bits, vec![
            // movq
            0x48, 0xc7, 0xc0, 0x01, 0x10, 0x00, 0x00,
            0x48, 0xc7, 0xc1, 0x02, 0x10, 0x00, 0x00,
            0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00,
            0x48, 0xc7, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00,
            0x48, 0xc7, 0x80, 0x08, 0x00, 0x00, 0x00, 0x03, 0x10, 0x00, 0x00,
            0x48, 0x8b, 0x88, 0x04, 0x03, 0x02, 0x01,
            0x48, 0x8b, 0xc8,
            0x48, 0x89, 0x88, 0x04, 0x03, 0x02, 0x01,

            // addq, cmpq
            0x48, 0x81, 0xc0, 0x01, 0x11, 0x00, 0x00,
            0x48, 0x03, 0x88, 0x04, 0x03, 0x02, 0x01,
            0x48, 0x01, 0x88, 0x04, 0x03, 0x02, 0x01,
            0x48, 0x81, 0xf8, 0x02, 0x11, 0x00, 0x00,

            // pushq, popq
            0x48, 0xff, 0xf0,
            0x48, 0x8f, 0xc1,

            // call and jump
            0x48, 0xe8, 0x00, 0x00, 0x00, 0x00,
            0x48, 0xe9, 0x00, 0x00, 0x00, 0x00,
            0x48, 0x0f, 0x84, 0x00, 0x00, 0x00, 0x00,
            0x48, 0x0f, 0x85, 0x00, 0x00, 0x00, 0x00,
            0x48, 0x0f, 0x05,

            // retq
            0x48, 0xc3,
        ]);

        assert_eq!(r.sections[1].section_name, b".data");
        let mut expected_data_progbits = vec![
            0x01, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x02, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        expected_data_progbits.append(&mut b"Hello \"quoted\" World\n\0".to_vec());
        assert_eq!(r.sections[1].prog_bits, expected_data_progbits);
        
        // Smoke test
        let r2 = build_object_file(r);
        let r3 = build_file_content(r2);
    }

    // one character and zero-or-one character rules
    #[test]
    fn test_single_char() {
        let r = parse_single_char(b' ', b" a", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 1, token_type: "single_char", children: Vec::new()}));
        let r = parse_single_char(b' ', b"a ", 0);
        assert_eq!(r, None);
        let r = parse_single_char(b' ', b" a", 2);
        assert_eq!(r, None);
    }
    #[test]
    fn test_oneormore_space() {
        let r = parse_oneormore_space(b"   a", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 3, token_type: "oneormore_space", children: Vec::new()}));
        let r = parse_oneormore_space(b"a   ", 0);
        assert_eq!(r, None);
    }
    #[test]
    fn test_zeroormore_space() {
        let r = parse_zeroormore_space(b"   a", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 3, token_type: "zeroormore_space", children: Vec::new()}));
        let r = parse_zeroormore_space(b"a   ", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 0, token_type: "zeroormore_space", children: Vec::new()}));
    }

    #[test]
    fn test_string_literal () {
        let r = parse_string_literal(b"\"abc\"", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 5, token_type: "string_literal", children: vec![
            Pair { token_type: "string_literal_charrep", start: 1, end: 2, children: vec![
                Pair { token_type: "string_literal_normal_char", start: 1, end: 2, children: vec![] }
            ]},
            Pair { token_type: "string_literal_charrep", start: 2, end: 3, children: vec![
                Pair { token_type: "string_literal_normal_char", start: 2, end: 3, children: vec![] }
            ]},
            Pair { token_type: "string_literal_charrep", start: 3, end: 4, children: vec![
                Pair { token_type: "string_literal_normal_char", start: 3, end: 4, children: vec![] }
            ]},
        ]}));
        let r = parse_string_literal(b"\"a\\\\c\"", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 6, token_type: "string_literal", children: vec![
            Pair { token_type: "string_literal_charrep", start: 1, end: 2, children: vec![
                Pair { token_type: "string_literal_normal_char", start: 1, end: 2, children: vec![] }
            ]},
            Pair { token_type: "string_literal_charrep", start: 2, end: 4, children: vec![
                Pair { token_type: "single_char", start: 3, end: 4, children: vec![] }
            ]},
            Pair { token_type: "string_literal_charrep", start: 4, end: 5, children: vec![
                Pair { token_type: "string_literal_normal_char", start: 4, end: 5, children: vec![] }
            ]},
        ]}));
    }

    #[test]
    fn test_identifier_start_char () {
        let r = parse_identifier_start_char(b"a", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 1, token_type: "identifier_start_char", children: Vec::new()}));
        let r = parse_identifier_start_char(b"A", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 1, token_type: "identifier_start_char", children: Vec::new()}));
        let r = parse_identifier_start_char(b"_", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 1, token_type: "identifier_start_char", children: Vec::new()}));
        let r = parse_identifier_start_char(b"0", 0);
        assert_eq!(r, None);
        let r = parse_identifier_start_char(b" ", 0);
        assert_eq!(r, None);
        let r = parse_identifier_start_char(b"", 0);
        assert_eq!(r, None);
    }
    #[test]
    fn test_identifier() {
        let r = parse_identifier(b"a", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 1, token_type: "identifier", children: vec![
            Pair { start: 0, end: 1, token_type: "identifier_start_char", children: Vec::new() }
        ]}));
        let r = parse_identifier(b"a0", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 2, token_type: "identifier", children: vec![
            Pair { start: 0, end: 1, token_type: "identifier_start_char", children: Vec::new() },
            Pair { start: 1, end: 2, token_type: "identifier_continuation_char", children: Vec::new() },
        ]}));
        let r = parse_identifier(b"aa0", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 3, token_type: "identifier", children: vec![
            Pair { start: 0, end: 1, token_type: "identifier_start_char", children: Vec::new() },
            Pair { start: 1, end: 2, token_type: "identifier_continuation_char", children: Vec::new() },
            Pair { start: 2, end: 3, token_type: "identifier_continuation_char", children: Vec::new() },
        ]}));
    }
    #[test]
    fn test_label() {
        let r = parse_label(b"abc:", 0);
        assert_eq!(r, Some(
            Pair { start: 0, end: 4, token_type: "label", children: vec![
                Pair { start: 0, end: 3, token_type: "identifier", children: vec![
                    Pair { start: 0, end: 1, token_type: "identifier_start_char", children: Vec::new() },
                    Pair { start: 1, end: 2, token_type: "identifier_continuation_char", children: Vec::new() },
                    Pair { start: 2, end: 3, token_type: "identifier_continuation_char", children: Vec::new() },
                ]},
                Pair { start: 3, end: 4, token_type: "single_char", children: vec![] },
            ]}
        ));
    }

    #[test]
    fn test_register() {
        let r = parse_register(b"%rax", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 4, token_type: "register", children: vec![
            Pair { start: 1, end: 4, token_type: "identifier", children: vec![
                Pair { start: 1, end: 2, token_type: "identifier_start_char", children: Vec::new() },
                Pair { start: 2, end: 3, token_type: "identifier_continuation_char", children: Vec::new() },
                Pair { start: 3, end: 4, token_type: "identifier_continuation_char", children: Vec::new() },
            ] },
        ]}))
    }

    #[test]
    fn test_directive() {
        let r = parse_directive(b".a0", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 3, token_type: "directive", children: vec![
            Pair { start: 1, end: 3, token_type: "identifier", children: vec![
                Pair { start: 1, end: 2, token_type: "identifier_start_char", children: Vec::new() },
                Pair { start: 2, end: 3, token_type: "identifier_continuation_char", children: Vec::new() },
            ]}
        ]}));
    }
    #[test]
    fn test_directive_stmt() {
        let r = parse_directive_stmt(b".b 0x3", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 6, token_type: "directive_stmt", children: vec![
            Pair { start: 0, end: 2, token_type: "directive", children: vec![
                Pair { start: 1, end: 2, token_type: "identifier", children: vec![
                    Pair { start: 1, end: 2, token_type: "identifier_start_char", children: Vec::new() },
                ]},
            ]},
            Pair { start: 3, end: 6, token_type: "directive_args", children: vec![
                Pair { start: 3, end: 6, token_type: "directive_arg", children: vec![
                    Pair { start: 3, end: 6, token_type: "hex_literal", children: vec![
                        Pair { start: 3, end: 3, token_type: "null", children: Vec::new() },
                        Pair { start: 5, end: 6, token_type: "single_hex_digit", children: Vec::new() },
                    ]},
                ]}
            ]}
        ]}));
    }

    #[test]
    fn test_comment() {
        let r = parse_comment(b"//foo", 0);
        assert_eq!(r, Some(Pair { start: 0, end: 5, token_type: "comment", children: vec![]}));
        let r = parse_comment(b" //foo", 0);
        assert_eq!(r, None);
        let r = parse_comment(b"/ /foo", 0);
        assert_eq!(r, None);
    }

    #[test]
    fn test_line() {
        let r = parse_line(b" .b 0x3 \n", 0);
        assert_eq!(r, Some(
            Pair { start: 0, end: 9, token_type: "line", children: vec![
                Pair { start: 1, end: 1, token_type: "null", children: vec![] },
                Pair { start: 1, end: 7, token_type: "stmt", children: vec![
                    Pair { start: 1, end: 7, token_type: "directive_stmt", children: vec![
                        Pair { start: 1, end: 3, token_type: "directive", children: vec![
                            Pair { start: 2, end: 3, token_type: "identifier", children: vec![
                                Pair { start: 2, end: 3, token_type: "identifier_start_char", children: Vec::new() },
                            ]},
                        ]},
                        Pair { start: 4, end: 7, token_type: "directive_args", children: vec![
                            Pair { start: 4, end: 7, token_type: "directive_arg", children: vec![
                                Pair { start: 4, end: 7, token_type: "hex_literal", children: vec![
                                    Pair { start: 4, end: 4, token_type: "null", children: Vec::new() },
                                    Pair { start: 6, end: 7, token_type: "single_hex_digit", children: Vec::new() },
                                ]},
                            ]},
                        ]},
                    ]}
                ]},
            ]}
        ));
    }
    #[test]
    fn test_file() {
        let r = parse_file(b".b 0x1\n.b 0x2\n", 0);
        assert_eq!(r, Some(
            Pair { start: 0, end: 14, token_type: "file", children: vec![
                Pair { start: 0, end: 7, token_type: "line", children: vec![
                    Pair { start: 0, end: 0, token_type: "null", children: vec![] },
                    Pair { start: 0, end: 6, token_type: "stmt", children: vec![
                        Pair { start: 0, end: 6, token_type: "directive_stmt", children: vec![
                            Pair { start: 0, end: 2, token_type: "directive", children: vec![
                                Pair { start: 1, end: 2, token_type: "identifier", children: vec![
                                    Pair { start: 1, end: 2, token_type: "identifier_start_char", children: Vec::new() },
                                ]},
                            ]},
                            Pair { start: 3, end: 6, token_type: "directive_args", children: vec![
                                Pair { start: 3, end: 6, token_type: "directive_arg", children: vec![
                                    Pair { start: 3, end: 6, token_type: "hex_literal", children: vec![
                                        Pair { start: 3, end: 3, token_type: "null", children: Vec::new() },
                                        Pair { start: 5, end: 6, token_type: "single_hex_digit", children: Vec::new() },
                                    ]},
                                ]},
                            ]},
                        ]}
                    ]},
                ]},
                Pair { start: 7, end: 14, token_type: "line", children: vec![
                    Pair { start: 7, end: 7, token_type: "null", children: vec![] },
                    Pair { start: 7, end: 13, token_type: "stmt", children: vec![
                        Pair { start: 7, end: 13, token_type: "directive_stmt", children: vec![
                            Pair { start: 7, end: 9, token_type: "directive", children: vec![
                                Pair { start: 8, end: 9, token_type: "identifier", children: vec![
                                    Pair { start: 8, end: 9, token_type: "identifier_start_char", children: Vec::new() },
                                ]},
                            ]},
                            Pair { start: 10, end: 13, token_type: "directive_args", children: vec![
                                Pair { start: 10, end: 13, token_type: "directive_arg", children: vec![
                                    Pair { start: 10, end: 13, token_type: "hex_literal", children: vec![
                                        Pair { start: 10, end: 10, token_type: "null", children: Vec::new() },
                                        Pair { start: 12, end: 13, token_type: "single_hex_digit", children: Vec::new() },
                                    ]},
                                ]},
                            ]},
                        ]}
                    ]}
                ]},
            ]}
        ));
    }
}
