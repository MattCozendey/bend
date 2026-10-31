(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\82\80\80\80\00\01\00\05\83\80\80\80"
  "\00\01\00\00\07\88\80\80\80\00\01\04\73\69\7a\65"
  "\00\00\0a\8a\80\80\80\00\01\84\80\80\80\00\00\3f"
  "\00\0b"
)
(module instance)
(assert_return (invoke "size") (i32.const 0x0))
(assert_return (invoke "grow" (i32.const 0x1)))
(assert_return (invoke "size") (i32.const 0x1))
(assert_return (invoke "grow" (i32.const 0x4)))
(assert_return (invoke "size") (i32.const 0x5))
(assert_return (invoke "grow" (i32.const 0x0)))
(assert_return (invoke "size") (i32.const 0x5))
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\82\80\80\80\00\01\00\05\83\80\80\80"
  "\00\01\00\01\07\88\80\80\80\00\01\04\73\69\7a\65"
  "\00\00\0a\8a\80\80\80\00\01\84\80\80\80\00\00\3f"
  "\00\0b"
)
(module instance)
(assert_return (invoke "size") (i32.const 0x1))
(assert_return (invoke "grow" (i32.const 0x1)))
(assert_return (invoke "size") (i32.const 0x2))
(assert_return (invoke "grow" (i32.const 0x4)))
(assert_return (invoke "size") (i32.const 0x6))
(assert_return (invoke "grow" (i32.const 0x0)))
(assert_return (invoke "size") (i32.const 0x6))
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\82\80\80\80\00\01\00\05\84\80\80\80"
  "\00\01\01\00\02\07\88\80\80\80\00\01\04\73\69\7a"
  "\65\00\00\0a\8a\80\80\80\00\01\84\80\80\80\00\00"
  "\3f\00\0b"
)
(module instance)
(assert_return (invoke "size") (i32.const 0x0))
(assert_return (invoke "grow" (i32.const 0x3)))
(assert_return (invoke "size") (i32.const 0x0))
(assert_return (invoke "grow" (i32.const 0x1)))
(assert_return (invoke "size") (i32.const 0x1))
(assert_return (invoke "grow" (i32.const 0x0)))
(assert_return (invoke "size") (i32.const 0x1))
(assert_return (invoke "grow" (i32.const 0x4)))
(assert_return (invoke "size") (i32.const 0x1))
(assert_return (invoke "grow" (i32.const 0x1)))
(assert_return (invoke "size") (i32.const 0x2))
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
  "\00\01\7f\03\82\80\80\80\00\01\00\05\84\80\80\80"
  "\00\01\01\03\08\07\88\80\80\80\00\01\04\73\69\7a"
  "\65\00\00\0a\8a\80\80\80\00\01\84\80\80\80\00\00"
  "\3f\00\0b"
)
(module instance)
(assert_return (invoke "size") (i32.const 0x3))
(assert_return (invoke "grow" (i32.const 0x1)))
(assert_return (invoke "size") (i32.const 0x4))
(assert_return (invoke "grow" (i32.const 0x3)))
(assert_return (invoke "size") (i32.const 0x7))
(assert_return (invoke "grow" (i32.const 0x0)))
(assert_return (invoke "size") (i32.const 0x7))
(assert_return (invoke "grow" (i32.const 0x2)))
(assert_return (invoke "size") (i32.const 0x7))
(assert_return (invoke "grow" (i32.const 0x1)))
(assert_return (invoke "size") (i32.const 0x8))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\8a\80\80\80\00\01\84\80\80\80\00\00"
    "\3f\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7d\03\82\80\80\80\00\01\00\05\83\80\80\80"
    "\00\01\00\01\0a\8a\80\80\80\00\01\84\80\80\80\00"
    "\00\3f\00\0b"
  )
  "type mismatch"
)
