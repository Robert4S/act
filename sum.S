
.data
.align 4
lit_1: .float 100
.align 4
lit_3: .float 0
.align 8
lit_0: .quad 0
.align 4
lit_2: .float 0
.align 1
lit_4: .asciz "I am done with my work here"
.align 4
lit_5: .float 1
.text
.globl _start
_start:
jmp rest_3
init_4:
push %rbp
mov %rsp, %rbp
sub $24, %rsp
mov %rdi, -8(%rbp)
mov lit_0(%rip), %rax
mov %rax, -16(%rbp)
mov -8(%rbp), %rdi
movss lit_1(%rip), %xmm0 
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_gc_number 
mov %rax, -24(%rbp)
mov -8(%rbp), %rdi
mov -16(%rbp), %rsi
mov -24(%rbp), %rdx
and $0xFFFFFFFFFFFFFFF0, %rsp
mov -8(%rbp), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call send_actor
mov -8(%rbp), %rdi
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
sub $136, %rsp
mov %rdi, -24(%rbp)
mov %rsi, -8(%rbp)
mov %rdx, -16(%rbp)
mov -24(%rbp), %rax
mov %rax, -32(%rbp)
mov -24(%rbp), %rax
mov %rax, -48(%rbp)
mov -8(%rbp), %rax
mov %rax, -56(%rbp)
mov -24(%rbp), %rdi
movss lit_3(%rip), %xmm0 
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_gc_number 
mov %rax, -64(%rbp)
mov -48(%rbp), %rdi
mov -56(%rbp), %rsi
mov -64(%rbp), %rdx
and $0xFFFFFFFFFFFFFFF0, %rsp
mov -24(%rbp), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call eval_le
mov %rax, -40(%rbp)
mov -32(%rbp), %rdi
mov -40(%rbp), %rsi
and $0xFFFFFFFFFFFFFFF0, %rsp
mov -24(%rbp), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call eval_conditional
test %rax, %rax
jz otherwise_1
then_0:
mov -24(%rbp), %rdi
lea lit_4(%rip), %rsi 
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_gc_string 
leave
ret
jmp rest_2
otherwise_1:
mov -24(%rbp), %rax
mov %rax, -72(%rbp)
mov lit_0(%rip), %rax
mov %rax, -80(%rbp)
mov -24(%rbp), %rax
mov %rax, -96(%rbp)
mov -8(%rbp), %rax
mov %rax, -104(%rbp)
mov -24(%rbp), %rdi
movss lit_5(%rip), %xmm0 
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_gc_number 
mov %rax, -112(%rbp)
mov -96(%rbp), %rdi
mov -104(%rbp), %rsi
mov -112(%rbp), %rdx
and $0xFFFFFFFFFFFFFFF0, %rsp
mov -24(%rbp), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call eval_minus
mov %rax, -88(%rbp)
mov -72(%rbp), %rdi
mov -80(%rbp), %rsi
mov -88(%rbp), %rdx
and $0xFFFFFFFFFFFFFFF0, %rsp
mov -24(%rbp), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call send_actor
mov -24(%rbp), %rax
mov %rax, -120(%rbp)
mov -8(%rbp), %rax
mov %rax, -128(%rbp)
mov -16(%rbp), %rax
mov %rax, -136(%rbp)
mov -120(%rbp), %rdi
mov -128(%rbp), %rsi
mov -136(%rbp), %rdx
and $0xFFFFFFFFFFFFFFF0, %rsp
mov -24(%rbp), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call eval_plus
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
call make_actor_global
mov %rax, lit_0(%rip)
mov lit_0(%rip), %rdi
and $0xFFFFFFFFFFFFFFF0, %rsp
call make_static
and $0xFFFFFFFFFFFFFFF0, %rsp
call start_runtime