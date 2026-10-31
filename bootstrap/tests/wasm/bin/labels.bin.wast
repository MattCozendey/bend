(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return (invoke "block") (i32.const 0x1))
(assert_return (invoke "loop1") (i32.const 0x5))
(assert_return (invoke "loop2") (i32.const 0x8))
(assert_return (invoke "loop3") (i32.const 0x1))
(assert_return (invoke "loop4" (i32.const 0x8)) (i32.const 0x10))
(assert_return (invoke "loop5") (i32.const 0x2))
(assert_return (invoke "loop6") (i32.const 0x3))
(assert_return (invoke "if") (i32.const 0x5))
(assert_return (invoke "if2") (i32.const 0x5))
(assert_return (invoke "switch" (i32.const 0x0)) (i32.const 0x32))
(assert_return (invoke "switch" (i32.const 0x1)) (i32.const 0x14))
(assert_return (invoke "switch" (i32.const 0x2)) (i32.const 0x14))
(assert_return (invoke "switch" (i32.const 0x3)) (i32.const 0x3))
(assert_return (invoke "switch" (i32.const 0x4)) (i32.const 0x32))
(assert_return (invoke "switch" (i32.const 0x5)) (i32.const 0x32))
(assert_return (invoke "return" (i32.const 0x0)) (i32.const 0x0))
(assert_return (invoke "return" (i32.const 0x1)) (i32.const 0x2))
(assert_return (invoke "return" (i32.const 0x2)) (i32.const 0x2))
(assert_return (invoke "br_if0") (i32.const 0x1d))
(assert_return (invoke "br_if1") (i32.const 0x1))
(assert_return (invoke "br_if2") (i32.const 0x1))
(assert_return (invoke "br_if3") (i32.const 0x2))
(assert_return (invoke "br") (i32.const 0x1))
(assert_return (invoke "shadowing") (i32.const 0x1))
(assert_return (invoke "redefinition") (i32.const 0x5))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\91\80\80\80\00"
    "\01\8b\80\80\80\00\00\02\40\41\01\0d\00\8c\01\0b"
    "\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\94\80\80\80\00"
    "\01\8e\80\80\80\00\00\02\40\43\00\00\00\00\41\01"
    "\0d\00\0b\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\94\80\80\80\00"
    "\01\8e\80\80\80\00\00\02\40\43\00\00\00\00\41\01"
    "\0d\00\0b\0b"
  )
  "type mismatch"
)
