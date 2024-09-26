.text

// void hello_module_subroutine()
.global hello_module_subroutine
hello_module_subroutine:
    movq $0x1, %rax                                          // write(
    movq $0x1, %rdi                                          //   1,
    movq $hello_module_msg, %rsi                             //   foo_hello_msg,
    movq $0x19, %rdx                                         //   25
    syscall                                                  // )

    retq                                                     // return;

.data
hello_module_msg:                                            // Local symbol
  .asciz "Hello Module Subroutine!\n"
