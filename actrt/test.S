.data
.align 8
lit_0: .quad 0
.align 4
lit_2: .float 1
.align 4
lit_3: .float 1
.align 4
lit_5: .float 1
.align 4
lit_1: .float 15
.align 1
lit_4: .asciz "I am done with my work here"
.text
.globl _start
_start:
jmp rest_3
init_4:
push %rbp
mov %rsp, %rbp
sub $8, %rsp
mov lit_0(%rip), %rdi
mov %rdi, -8(%rbp)
movss lit_1(%rip), %xmm0
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_gc_number
mov %rax, %rsi
mov -8(%rbp), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call send_actor
movss lit_2(%rip), %xmm0
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_gc_number
leave
ret
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_undefined
leave
ret
update_5:
push %rbp
mov %rsp, %rbp
sub $72, %rsp
mov %rdi, -8(%rbp)
mov %rsi, -16(%rbp)
mov -8(%rbp), %rax
mov %rax, -24(%rbp)
movss lit_3(%rip), %xmm0
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_gc_number
mov %rax, -32(%rbp)
mov -24(%rbp), %rdi
mov -32(%rbp), %rsi
and $0xFFFFFFFFFFFFFFF0, %rsp
call eval_le
mov %rax, %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call eval_conditional
test %rax, %rax
jz otherwise_1
then_0:
lea lit_4(%rip), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_gc_string
leave
ret
jmp rest_2
otherwise_1:
mov lit_0(%rip), %rdi
mov %rdi, -40(%rbp)
mov -8(%rbp), %rax
mov %rax, -48(%rbp)
movss lit_5(%rip), %xmm0
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_gc_number
mov %rax, -56(%rbp)
mov -48(%rbp), %rdi
mov -56(%rbp), %rsi
and $0xFFFFFFFFFFFFFFF0, %rsp
call eval_minus
mov %rax, %rsi
mov -40(%rbp), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call send_actor
mov -8(%rbp), %rax
mov %rax, -64(%rbp)
mov -16(%rbp), %rax
mov %rax, -72(%rbp)
mov -64(%rbp), %rdi
mov -72(%rbp), %rsi
and $0xFFFFFFFFFFFFFFF0, %rsp
call eval_mul
leave
ret
rest_2:
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_undefined
leave
ret
rest_3:
lea init_4(%rip), %rdi
lea update_5(%rip), %rsi
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_actor
mov %rax, lit_0(%rip)
and $0xFFFFFFFFFFFFFFF0, %rsp
call start_runtime

