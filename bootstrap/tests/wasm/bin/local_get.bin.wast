(module definition binary
  "\00\61\73\6d\01\00\00\00\01\8a\80\80\80\00\02\60"
  "\00\01\7f\60\01\7f\01\7f\03\83\80\80\80\00\02\00"
  "\01\07\a3\80\80\80\00\02\0e\74\79\70\65\2d\6c\6f"
  "\63\61\6c\2d\69\33\32\00\00\0e\74\79\70\65\2d\70"
  "\61\72\61\6d\2d\69\33\32\00\01\0a\95\80\80\80\00"
  "\02\86\80\80\80\00\01\01\7f\20\00\0b\84\80\80\80"
  "\00\00\20\00\0b"
)
(module instance)
(assert_return (invoke "type-local-i32") (i32.const 0x0))
(assert_return (invoke "type-local-i64") (i64.const 0x0))
(assert_return (invoke "type-local-f32") (f32.const 0x0p+0))
(assert_return (invoke "type-local-f64") (f64.const 0x0p+0))
(assert_return (invoke "type-param-i32" (i32.const 0x2)) (i32.const 0x2))
(assert_return (invoke "type-param-i64" (i64.const 0x3)) (i64.const 0x3))
(assert_return
  (invoke "type-param-f32" (f32.const 0x1.1999_9ap+2))
  (f32.const 0x1.1999_9ap+2)
)
(assert_return
  (invoke "type-param-f64" (f64.const 0x1.6p+2))
  (f64.const 0x1.6p+2)
)
(assert_return (invoke "as-block-value" (i32.const 0x6)) (i32.const 0x6))
(assert_return (invoke "as-loop-value" (i32.const 0x7)) (i32.const 0x7))
(assert_return (invoke "as-br-value" (i32.const 0x8)) (i32.const 0x8))
(assert_return (invoke "as-br_if-value" (i32.const 0x9)) (i32.const 0x9))
(assert_return (invoke "as-br_if-value-cond" (i32.const 0xa)) (i32.const 0xa))
(assert_return (invoke "as-br_table-value" (i32.const 0x1)) (i32.const 0x2))
(assert_return (invoke "as-return-value" (i32.const 0x0)) (i32.const 0x0))
(assert_return (invoke "as-if-then" (i32.const 0x1)) (i32.const 0x1))
(assert_return (invoke "as-if-else" (i32.const 0x0)) (i32.const 0x0))
(assert_return
  (invoke "type-mixed"
    (i64.const 0x1)
    (f32.const 0x1.1999_9ap+1)
    (f64.const 0x1.a666_6666_6666_6p+1)
    (i32.const 0x4)
    (i32.const 0x5)
  )
)
(assert_return
  (invoke "read"
    (i64.const 0x1)
    (f32.const 0x1p+1)
    (f64.const 0x1.a666_6666_6666_6p+1)
    (i32.const 0x4)
    (i32.const 0x5)
  )
  (f64.const 0x1.1666_6666_6666_6p+5)
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7e\03\82\80\80\80\00\01\00\0a\8c\80\80\80"
    "\00\01\86\80\80\80\00\01\01\7f\20\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7f\03\82\80\80\80\00\01\00\0a\8d\80\80\80"
    "\00\01\87\80\80\80\00\01\01\7d\20\00\45\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\00\01\7c\03\82\80\80\80\00\01\00\0a\8f\80\80\80"
    "\00\01\89\80\80\80\00\02\01\7c\01\7e\20\01\9a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\01\7f\01\7e\03\82\80\80\80\00\01\00\0a\8a\80\80"
    "\80\00\01\84\80\80\80\00\00\20\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\01\7d\01\7f\03\82\80\80\80\00\01\00\0a\8b\80\80"
    "\80\00\01\85\80\80\80\00\00\20\00\45\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\87\80\80\80\00\01\60"
    "\02\7c\7e\01\7c\03\82\80\80\80\00\01\00\0a\8b\80"
    "\80\80\00\01\85\80\80\80\00\00\20\01\9a\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8c\80\80\80\00"
    "\01\86\80\80\80\00\01\01\7f\20\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8c\80\80\80\00"
    "\01\86\80\80\80\00\01\01\7e\20\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8c\80\80\80\00"
    "\01\86\80\80\80\00\01\01\7d\20\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8c\80\80\80\00"
    "\01\86\80\80\80\00\01\01\7c\20\00\0b"
  )
  "type mismatch"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\8f\80\80\80\00"
    "\01\89\80\80\80\00\02\01\7f\01\7e\20\03\1a\0b"
  )
  "unknown local"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\0a\92\80\80\80\00"
    "\01\8c\80\80\80\00\02\01\7f\01\7e\20\f7\a4\ea\06"
    "\1a\0b"
  )
  "unknown local"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\02\7f\7e\00\03\82\80\80\80\00\01\00\0a\8b\80\80"
    "\80\00\01\85\80\80\80\00\00\20\02\1a\0b"
  )
  "unknown local"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
    "\02\7f\7e\00\03\82\80\80\80\00\01\00\0a\8f\80\80"
    "\80\00\01\89\80\80\80\00\00\20\f7\f2\ce\d4\02\1a"
    "\0b"
  )
  "unknown local"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\01\7f\00\03\82\80\80\80\00\01\00\0a\8f\80\80\80"
    "\00\01\89\80\80\80\00\02\01\7f\01\7e\20\03\1a\0b"
  )
  "unknown local"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\85\80\80\80\00\01\60"
    "\01\7e\00\03\82\80\80\80\00\01\00\0a\92\80\80\80"
    "\00\01\8c\80\80\80\00\02\01\7f\01\7e\20\f7\a8\99"
    "\66\1a\0b"
  )
  "unknown local"
)
