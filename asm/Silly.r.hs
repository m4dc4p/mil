Alloc "f1" 0 "r0"
Set "r1" "b" 
Set "r2" "c"
Set "r3" "d"
Enter "r0" "r1" "r4"
Enter "r4" "r2" "r5"
Enter "r5" "r3" "r6"
Copy "r6" "result"
Halt

EntryPoint ("f1", 0)
AllocC "f2" 1 "r0"
Store "arg" ("r0", 0)
Ret "r0"

EntryPoint ("f2", 1)
Alloc "f3" 2 "r0"
Load ("clo", 0) "r1" 
Store "r1" ("r0", 0)
Store "arg" ("r0", 1)
Ret "r0"

EntryPoint ("f3", 2)
Load ("clo", 0) "r0"
Load ("clo", 1) "r1"
Set "r2" "a"
Ret "r2"