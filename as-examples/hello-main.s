.text
.global _start
_start:

main_loop:
    movq $0x1, %rax                                          // write(
    movq $0x1, %rdi                                          //   1,
    movq $local_hello_msg, %rsi                              //   local_hello_msg,
    movq $0x13, %rdx                                         //   19
    syscall                                                  // )

    movq $0x1, %rax                                          // write(
    movq $0x1, %rdi                                          //   1,
    movq $global_hello_msg, %rsi                             //   global_hello_msg,
    movq $0x14, %rdx                                         //   20
    syscall                                                  // )

    callq local_subroutine                                   // local_subroutine();
    callq hello_module_subroutine                            // hello_module_subroutine();

    movq $0x3c, %rax                                         // exit(
    movq $0x0, %rdi                                          //   0
    syscall                                                  // )

// void local_subroutine()
local_subroutine:
    movq $0x1, %rax                                          // write(
    movq $0x1, %rdi                                          //   1,
    movq $local_subroutine_hello_msg, %rsi                   //   local_subroutine_hello_msg,
    movq $0x19, %rdx                                         //   25
    syscall                                                  // )

    retq                                                     // return;

.data
    .quad 0x0                                                // Dummy
local_hello_msg:                                             // Local symbol
    .asciz "Hello Local World!\n"
.global global_hello_msg
global_hello_msg:                                            // Global symbol
    .asciz "Hello Global World!\n"
local_subroutine_hello_msg:
    .asciz "Hello Local Subroutine!\n"
