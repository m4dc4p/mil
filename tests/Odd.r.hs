AllocD "reg.Nat.Z" "Even.Nat.Z" 0
AllocC "reg.Nat.S.1" "Nat.S" 0
AllocC "reg.Even.even.1" "Even.even" 0
AllocC "reg.Even.odd.1" "Even.odd" 0
Enter "reg.Nat.S.1" "reg.Nat.Z" "reg.top.1"
Enter "reg.Nat.S.1" "reg.top.1" "reg.top.2"
Enter "reg.Even.odd.1" "reg.top.2" "reg.top.3"
Copy "reg.top.3" "result"
Halt
EntryPoint "Nat.S"
AllocD "reg.Nat.S" "Even.Nat.S" 1
Store "arg" ("reg.Nat.S", 0)
Ret "reg.Nat.S"
Lab "TopFail"
Error "Match failure!"
EntryPoint "Even.odd"
FailT "arg" "Even.Nat.S" "lab.odd.Z"
Load ("arg", 0) "reg.Even.odd.n"
AllocC "reg.Even.odd.1" "Even.even" 0
Enter "reg.Even.odd.1" "reg.Even.odd.n" "reg.Even.odd.2"
Ret "reg.Even.odd.2"
Lab "lab.odd.Z"
FailT "arg" "Even.Nat.Z" "TopFail"
AllocD "reg.Even.odd.3" "Even.Bool.False" 0
Ret "reg.Even.odd.3"
EntryPoint "Even.even"
FailT "arg" "Even.Nat.S" "lab.even.Z"
Load ("arg", 0) "reg.Even.even.n"
AllocC "reg.Even.even.1" "Even.odd" 0
Enter "reg.Even.even.1" "reg.Even.even.n" "reg.Even.even.2"
Ret "reg.Even.even.2"
Lab "lab.even.Z"
FailT "arg" "Even.Nat.Z" "TopFail"
AllocD "reg.Even.even.3" "Even.Bool.True" 0
Ret "reg.Even.even.3"
