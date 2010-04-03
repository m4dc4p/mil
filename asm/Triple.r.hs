AllocC "Triple1" 0 "_Triple"
Set "a" "r0"
Set "b" "r1"
Set "c" "r2"
Enter "_Triple" "r0" "r3"
Enter "r3" "r1" "r4"
Enter "r4" "r2" "r5"
Copy "r5" "result"
EntryPoint "Triple" 2
Load ("clo", 0) "r0"
Load ("clo", 1) "r1"
AllocD "Triple" 3 "r2"
Store "r0" ("r2", 0)
Store "r1" ("r2", 1)
Store "arg" ("r2", 2)
Ret "r2"
EntryPoint "Triple2" 1
Load ("clo", 0) "r0"
AllocC "Triple" 2 "r1"
Store "r0" ("r1", 0)
Store "arg" ("r2", 1)
Ret "r1"
EntryPoint "Triple1" 0
AllocC "Triple2" 1 "r0"
Store "arg" ("r0", 0)
Ret "r0"
