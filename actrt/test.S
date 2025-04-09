.data
lit_3: .float 6.28
lit_1: .quad 1
lit_6: .asciz "hello_world!"
lit_0: .float 2.73
lit_2: .float 3.141
lit_4: .quad 0
lit_5: .float 2.5
.text
.globl _start
_start:
push %rbp
mov %rsp, %rbp
sub $8, %rsp
jmp rest_6
init_7:
push %rbp
mov %rsp, %rbp
sub $0, %rsp
movss lit_0(%rip), %xmm0
call make_gc_number
leave
ret
call make_undefined
leave
ret
update_8:
push %rbp
mov %rsp, %rbp
sub $24, %rsp
mov %rdi, -8(%rbp)
mov %rsi, -16(%rbp)
mov lit_1(%rip), %rdi
call make_gc_bool
mov %rax, %rdi
call eval_conditional
test %rax, %rax
jz otherwise_1
then_0:
movss lit_2(%rip), %xmm0
call make_gc_number
mov %rax, -24(%rbp)
jmp rest_2
otherwise_1:
movss lit_3(%rip), %xmm0
call make_gc_number
mov %rax, -24(%rbp)
mov -24(%rbp), %rax
leave
ret
rest_2:
mov lit_4(%rip), %rdi
call make_gc_bool
mov %rax, %rdi
call eval_conditional
test %rax, %rax
jz otherwise_4
then_3:
movss lit_5(%rip), %xmm0
call make_gc_number
leave
ret
jmp rest_5
otherwise_4:
mov lit_6(%rip), %rdi
call make_gc_string
leave
ret
rest_5:
call make_undefined
leave
ret
rest_6:
lea init_7(%rip), %rdi
lea update_8(%rip), %rsi
call make_actor
mov %rax, -8(%rbp)
call start_runtime
