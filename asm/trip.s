# Handmade assembly code for naive closure-based execution of a
# simple functional program.
#
# Tested on Linux:
#   gcc -o trip trip.s runtime.c
#

# data Triple a b c = MkTrip a b c

	.globl	MkTrip3, MkTrip2, MkTrip1, MkTrip0, MkTrip
	.long	3	# MkTrip values contain 3 fields
MkTrip3:		# .. error code .. I'm a data constructor ...

# constructs MkTrip object from closure with a, b and c in arg
	.long	2	# MkTrip2 closures have 2 fields
MkTrip2:
	pushl	%ebp	# prologue
	movl	%esp, %ebp

	# arg should be at 12(%ebp)
	# clo should be at 8(%ebp)

	pushl	$MkTrip3 # allocate new MkTrip3 object
	call	alloc
	addl	$4, %esp

	# eax points to new MkTrip3 object

	movl	8(%ebp), %ebx

	# ebx points to old closure

	movl	4(%ebx), %ecx	# copy "a" field from closure
	movl	%ecx, 4(%eax)

	movl	8(%ebx), %ecx	# copy "b" field from closure
	movl	%ecx, 8(%eax)

	movl	12(%ebp), %ecx	# copy "c" field from arg
	movl	%ecx, 12(%eax)

        movl	%ebp, %esp
	popl	%ebp
	ret

# constructs MkTrip2 object from closure with a and b in arg
	.long	1	# MkTrip1 closures have 1 fields
MkTrip1:
	pushl	%ebp	# prologue
	movl	%esp, %ebp

	# arg should be at 12(%ebp)
	# clo should be at 8(%ebp)

	pushl	$MkTrip2 # allocate new MkTrip2 object
	call	alloc
	addl	$4, %esp

	# eax points to new MkTrip2 object

	movl	8(%ebp), %ebx

	# ebx points to old closure

	movl	4(%ebx), %ecx	# copy "a" field from closure
	movl	%ecx, 4(%eax)

	movl	12(%ebp), %ecx	# copy "b" field from arg
	movl	%ecx, 8(%eax)

        movl	%ebp, %esp
	popl	%ebp
	ret

# constructs MkTrip1 object from a in arg
	.long	0	# MkTrip0 closures have no fields
MkTrip0:
	pushl	%ebp	# prologue
	movl	%esp, %ebp

	# arg should be at 12(%ebp)
	# clo should be at 8(%ebp)

	pushl	$MkTrip1 # allocate new MkTrip1 object
	call	alloc
	addl	$4, %esp

	# eax points to new MkTrip2 object

	movl	12(%ebp), %ecx	# copy "a" field from arg
	movl	%ecx, 4(%eax)

        movl	%ebp, %esp
	popl	%ebp
	ret

	# closure for MkTrip function:
MkTrip:	.long	MkTrip0

# So how do we construct a Triple now?
# 
# 	movl	$MkTrip, %eax
# 
# 	pushl	$1
# 	pushl	%eax
# 	movl	(%eax), %ebx
# 	call	*%ebx
# 	addl	$8, %esp
# 
# 	# eax now points to (MkTrip 1) closure
# 
# 	pushl	$2
# 	pushl	%eax
# 	movl	(%eax), %ebx
# 	call	*%ebx
# 	addl	$8, %esp
# 
# 	# eax now points to (MkTrip 1 2) closure
# 
# 	pushl	$3
# 	pushl	%eax
# 	movl	(%eax), %ebx
# 	call	*%ebx
# 	addl	$8, %esp
# 
# 	# eax now points to (MkTrip 1 2 3) value
# 
# Maybe we can assume that eax always points to the closure on
# entry to closure code, so we don't need to push it on the stack?
# 

# f x y = MkTrip x x y

	.globl	f1, f0, f
	.long	1
	# runs f with x in closure and y in arg
f1:	pushl   %ebp	# prologue
	movl	%esp, %ebp

	# arg should be at 12(%ebp)
	# clo should be at 8(%ebp)

	movl	$MkTrip, %eax

	# apply MkTrip to x:
	movl	8(%ebp), %ebx	# get closure in %ebx
	pushl	4(%ebx)		# push argument x
	pushl	%eax
	movl	(%eax), %ebx
	call	*%ebx
	addl	$8, %esp

	# apply (MkTrip x) to x
	movl	8(%ebp), %ebx	# get closure in %ebx
	pushl	4(%ebx)		# push argument x
	pushl	%eax
	movl	(%eax), %ebx
	call	*%ebx
	addl	$8, %esp

	# apply (MkTrip x x) to y
	movl	12(%ebp), %ebx	# get closure in %ebx
	pushl	%ebx		# push argument y
	pushl	%eax
	movl	(%eax), %ebx
	call	*%ebx
	addl	$8, %esp

        movl	%ebp, %esp
	popl	%ebp
	ret

	.long	0
	# constructs a closure for f x with x in arg
f0:	pushl	%ebp	# prologue
	movl	%esp, %ebp

	# arg should be at 12(%ebp)
	# clo should be at 8(%ebp)

	pushl	$f1 # allocate new f1 closure
	call	alloc
	addl	$4, %esp

	movl	12(%ebp), %ecx	# copy arg into closure
	movl	%ecx, 4(%eax)

        movl	%ebp, %esp
	popl	%ebp
	ret

	# closure for f function:
f:	.long	f0


# top = f 1 2
	.globl	top0, top
	.long	0
top0:	pushl	%ebp
	movl	%esp, %ebp

	movl	$f, %eax

	pushl	$1
	pushl	%eax
	movl	(%eax), %ebx
	call	*%ebx
	addl	$8, %esp

	pushl	$2
	pushl	%eax
	movl	(%eax), %ebx
	call	*%ebx
	addl	$8, %esp

        movl	%ebp, %esp
	popl	%ebp
	ret

	# closure for top function:
top:	.long	top0

