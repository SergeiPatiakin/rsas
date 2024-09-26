.text

.global _start
_start:
    movq %rsp, %rdx
    movq (%rdx), %rdi                                       // main(argc, argv);
    movq %rdx, %rsi
    addq $0x8, %rsi
    callq main
    
    movq $0x3c, %rax                                        // exit(
    movq $0x0, %rdi                                         //   0
    syscall                                                 // )

//
// void main(u64 argc, char** argv)
//
main:
    pushq %rbp
    movq %rsp, %rbp
    subq $0x38, %rsp                                        //
                                                            // 8 bytes for in_fd at -0x8(%rbp)
                                                            // 8 bytes for chunk_bytes_read at -0x10(%rbp)
                                                            // 8 bytes for call_bytes_written at -0x18(%rbp)
                                                            // 8 bytes for chunk_bytes_written at -0x20(%rbp)
                                                            // 8 bytes for argn at -0x28(%rbp)
                                                            // 8 bytes for argc at -0x30(%rbp)
                                                            // 8 bytes for argv at -0x38(%rbp)
    movq %rdi, -0x30(%rbp)
    movq %rsi, -0x38(%rbp)

    cmpq $0x2, %rdi                                         // if (argc < 2)
    jge main_argc_ok
    movq $errmsg_noargs, %rdi                               //   panic(errmsg_noargs);
    call panic
main_argc_ok:
    movq $0x1, -0x28(%rbp)                                  // argn = 1;

main_read_file:
    movq -0x30(%rbp), %rdi
    movq -0x38(%rbp), %rsi

    cmpq %rdi, -0x28(%rbp)                                  // while (argn < argc) {
    jge main_finished

    movq $0x2, %rax                                         //   in_fd = open(
    movq -0x28(%rbp), %rcx
    addq %rcx, %rcx
    addq %rcx, %rcx
    addq %rcx, %rcx
    addq %rcx, %rsi
    movq (%rsi), %rdi                                       //     argv[argn],
    movq $0x2, %rsi                                         //     O_RDWR,
    movq $0x0, %rdx                                         //     0 // mode
    syscall
    movq %rax, -0x8(%rbp)                                   //   );
    movq %rax, %rdi
    call assert_syscall_success                             //   assert_syscall_success(in_fd);

main_read_chunk:
                                                            //   while(true) {

    movq $0x0, %rax                                         //     chunk_bytes_read = read(
    movq -0x8(%rbp), %rdi                                   //        in_fd,
    movq $content_buffer, %rsi                              //        content_buffer,
    movq $0x1000, %rdx                                      //         0x1000
    syscall                                                 //     );
    movq %rax, -0x10(%rbp)
    movq %rax, %rdi
    call assert_syscall_success                             //     assert_syscall_success(chunk_bytes_read);

    cmpq $0x0, -0x10(%rbp)                                  //     if (chunk_bytes_read == 0) break;
    jz main_file_finished

    movq $0x0, -0x18(%rbp)                                  //     chunk_bytes_written = 0;
main_write_more:
    movq -0x10(%rbp), %rdx                                  //     while(chunk_bytes_to_write = chunk_bytes_read - chunk_bytes_written) {
    subq -0x18(%rbp), %rdx
    cmpq $0x0, %rdx
    jz main_chunk_finished

    movq $0x1, %rax                                         //       call_bytes_written = write(
    movq $0x1, %rdi                                         //         1,
    movq $content_buffer, %rsi                              //         content_buffer + chunk_bytes_written,
    addq -0x18(%rbp), %rsi
                                                            //         chunk_bytes_to_write
    syscall                                                 //       );
    movq %rax, -0x18(%rbp)
    movq %rax, %rdi
    call assert_syscall_success                             //       assert_syscall_success(bytes_written);
    jmp main_write_more                                     //     }
main_chunk_finished:
    jmp main_read_chunk                                     //   }
main_file_finished:
    addq $0x1, -0x28(%rbp)                                  //   argn += 1;
    jmp main_read_file                                      // }
main_finished:
    movq %rbp, %rsp                                         // return;
    popq %rbp
    retq

//
// u64 strlen (char* s)
//
strlen:
    movq $0x0, %rax                                         // u64 i = 0;
strlen_loop:                                                // while (true) {
    movq %rdi, %rsi                                         //   char* c = s + i;
    addq %rax, %rsi
    testq $0xff, (%rsi)                                     //   if (!*c) {
    jz strlen_end                                           //     break;
    addq $0x1, %rax                                         //   }
    jmp strlen_loop                                         // }
strlen_end:
    retq                                                    // return i;

//
// void assert_syscall_success (i64 syscall_result)
//
assert_syscall_success:
    pushq %rbp
    movq %rsp, %rbp
    subq $0x10, %rsp                                        // syscall_result at -0x8(%rbp)
                                                            // i at -0x10(%rbp)
    movq %rdi, -0x8(%rbp)
    movq $0x0, -0x10(%rbp)

    // -1 to -4095 means error, anything else means success
    cmpq $-0xfff, %rdi                                      // if (syscall_result < -4095)
    jl assert_syscall_success_ok                            //   return;
    cmpq $0x0, %rdi                                         // if (syscall_result >= 0)
    jge assert_syscall_success_ok                           //   return;

    movq $errmsg_syscall, %rdi                              //   panic(errmsg_syscall);
    call panic

assert_syscall_success_ok:
    movq %rbp, %rsp
    popq %rbp
    retq

//
// void panic (char* errmsg)
//
panic:
    pushq %rbp
    movq %rsp, %rbp
    subq $0x8, %rsp                                         // errmsg at -0x8(%rbp)
    movq %rdi, -0x8(%rbp)
    call strlen
    movq %rax, %rcx
    
    movq $0x1, %rax                                         // write(
    movq $0x2, %rdi                                         //   2,
    movq -0x8(%rbp), %rsi                                   //   errmsg,
    movq %rcx, %rdx                                         //   errmsg_len
    syscall                                                 // )

    movq $0x1, %rax                                         // write(
    movq $0x2, %rdi                                         //   2,
    movq $newline_char, %rsi                                //   newline_char,
    movq $0x1, %rdx                                         //   1
    syscall                                                 // )

    movq $0x3c, %rax                                        // exit(
    movq $0x1, %rdi                                         //   1
    syscall                                                 // )

.data
errmsg_noargs:
    .asciz "No args provided"
errmsg_enoent:
    .asciz "No such file or directory"
errmsg_syscall:
    .asciz "Syscall error"
newline_char:
    .byte 0x0A
content_buffer:
    .skip 0x1000
