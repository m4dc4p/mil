.global _top
.section data
topv1:
        .asciz "b"
topv2:
        .asciz "c"
topv3:
        .asciz "d"
f3v1:
        .asciz "a"

.section text
_top:
        subl $24, %esp          # r6 = esp, r5 = 4(esp), r4 = 8(esp)
                                # r3 = 12(esp), r2 = 16(esp), r1 = 20(esp)
                                # r0 = 24(esp)
### Alloc f1 0 r0
        pushl $f1
        call _alloc
        movl %eax, 24(%esp)     # eax = r0 : | f1 |
### Set "r1" "b"
        movl $topv1, 20(%esp)   # r1 = "b"
### Set "r2" "c"
        movl $topv2, 16(%esp)   # r2 = "c"
### Set "r3" "d"
        movl $topv3, 12(%esp)   # r3 = "d"
### Enter "r0" "r1" "r4"
        ## Prelude
        movl 20(%esp), %eax      
        pushl %eax              # r1 as arg
        movl 28(%esp), %eax     # r0 now at 24(esp) + 4
        pushl %eax              # r4 as clo
        call *(%esp)            # enter closure
        ## Postlude
        movl %eax, 16(%esp)     # r4 at 8(esp) + 8
        addl $8, %esp           # remove arg & clo
### Enter "r4" "r2" "r5"
        ## Prelude
        movl 16(%esp), %eax     
        pushl %eax              # r2 as arg
        movl 12(%esp), %eax     # r4 now at 8(esp) + 4
        pushl %eax
        call *(%esp)
        ## Postlude
        movl %eax, 12(%esp)      # r5 at 4(esp) + 4
        addl $8, %esp           # remove arg & clo
### Enter "r5" "r3" "r6"
        ## Prelude
        movl 12(%esp), %eax
        pushl %eax              # r3 as arg
        movl 8(%esp), %eax      # r5 now at 4(esp) + 4
        pushl %eax              # r5 as clo
        call *(%esp)
        ## Postlude
        movl %eax, 8(%esp)      # r6 now at (esp) + 8
        addl $8, %esp           # remove arg & clo
### Copy "r6" "result"
        movl (%esp), %eax
### Halt
        addl $24, %esp           # Clean up stack
        ret
        
### EntryPoint (f1, 0)
        .long 0
f1:     ## Prologue
        pushl %ebp
        movl %esp, %ebp
        subl $4, %esp           # r0 at esp
### Alloc f2 1 r0
        pushl $f2
        call _alloc
                                #              __________
        movl %eax, (%esp)       # *esp = r0 : | f2 | . |
                                #              ----------
### Store arg (r0, 0)
        movl (%esp), %eax       # r0 in eax
        movl 12(%ebp), %ecx     # arg in ecx
        movl %ecx, 4(%eax)      # r0[0] = arg
### Ret r0
        movl (%esp), %eax       # &r0 in eax
        subl $4, %esp           # remove r0 from stack
        ## Epilogue
        popl %ebp
        ret

### EntryPoint (f2, 1)
        .long 1
f2:     ## Prologue
        pushl %ebp
        movl %esp, %ebp
        subl $8, %esp           # r0 at 4(esp), r1 at esp
### Alloc f3 2 r0
        pushl $f3
        call _alloc
        movl %eax, 4(%esp)      # *(esp + 4) = r0 : | f3 | . | . |
### Load (clo, 0) r1
        movl 8(%ebp), %eax      # &clo = *(ebp + 8)
        movl 4(%eax), %ecx      # ecx = clo[0]
        movl %ecx, (%esp)       # *esp = r1 = (clo, 0) 
### Store r1 (r0, 0)
        movl (%esp), %eax       # *esp = eax = r1
        movl 4(%esp), %ecx      # ecx = *(esp + 4) = r0
        movl %eax, 4(%ecx)      # r0[0] = r1
### Store arg (r0, 1)
        movl 12(%ebp), %eax     # eax = arg
        movl 4(%esp), %ecx      # ecx = *(esp + 4) = r0
        movl %eax, 8(%ecx)      # r0[1] = arg
### Ret r0
        movl 4(%esp), %eax      # eax = r0
        addl $8, %esp           # remove r1, r0 from stack
        ## Epilogue
        popl %ebp
        ret

### EntryPoint (f3, 2)
        .long 2
f3:     ## Prologue
        pushl %ebp
        movl %esp, %ebp
        subl $12, %esp          # r0 at 8(esp), r1 at 4(esp), r2 at esp
### Load (clo, 0) r0
        movl 8(%ebp), %eax
        movl 4(%eax), %ecx
        movl %ecx, 8(%esp)
### Load (clo, 1) r1
        movl 8(%ebp), %eax
        movl 8(%eax), %ecx
        movl %ecx, 4(%esp)
### Set "r2" "a"
        movl $f3v1, (%esp)
### Ret r2
        movl (%esp), %eax
        addl $12, %esp          # Remove r2, r1, r0 from stack
        ## Epilogue
        popl %ebp
        ret
        