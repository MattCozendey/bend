(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
  "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
  "\01\00\00\0a\8f\80\80\80\00\01\89\80\80\80\00\00"
  "\41\00\41\01\3a\00\00\0b"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
  "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
  "\01\00\00\0a\8f\80\80\80\00\01\89\80\80\80\00\00"
  "\41\00\41\01\36\02\00\0b"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\00"
)
(module instance)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2c\01\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2d\01\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2e\02\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2f\02\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\28\03\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\30\01\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\31\01\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\32\02\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\33\02\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\34\03\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\35\03\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\29\04\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2a\03\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2b\04\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2c\01\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2d\01\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2e\02\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2f\02\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\28\03\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\30\01\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\31\01\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\32\02\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\33\02\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\34\03\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\35\03\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\29\04\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2a\03\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\2b\04\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8f\80\80\80\00\01\89\80\80\80\00\00"
    "\41\00\41\00\3a\01\00\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8f\80\80\80\00\01\89\80\80\80\00\00"
    "\41\00\41\00\3b\02\00\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8f\80\80\80\00\01\89\80\80\80\00\00"
    "\41\00\41\00\36\03\00\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8f\80\80\80\00\01\89\80\80\80\00\00"
    "\41\00\42\00\3c\01\00\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8f\80\80\80\00\01\89\80\80\80\00\00"
    "\41\00\42\00\3d\02\00\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8f\80\80\80\00\01\89\80\80\80\00\00"
    "\41\00\42\00\3e\03\00\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\8f\80\80\80\00\01\89\80\80\80\00\00"
    "\41\00\42\00\37\04\00\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\92\80\80\80\00\01\8c\80\80\80\00\00"
    "\41\00\43\00\00\00\00\38\03\00\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\00\0a\96\80\80\80\00\01\90\80\80\80\00\00"
    "\41\00\44\00\00\00\00\00\00\00\00\39\04\00\0b"
  )
  "alignment must not be larger than natural"
)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\01"
)
(module instance)
(assert_return (invoke "f32_align_switch" (i32.const 0x0)) (f32.const 0x1.4p+3))
(assert_return (invoke "f32_align_switch" (i32.const 0x1)) (f32.const 0x1.4p+3))
(assert_return (invoke "f32_align_switch" (i32.const 0x2)) (f32.const 0x1.4p+3))
(assert_return (invoke "f32_align_switch" (i32.const 0x3)) (f32.const 0x1.4p+3))
(assert_return (invoke "f64_align_switch" (i32.const 0x0)) (f64.const 0x1.4p+3))
(assert_return (invoke "f64_align_switch" (i32.const 0x1)) (f64.const 0x1.4p+3))
(assert_return (invoke "f64_align_switch" (i32.const 0x2)) (f64.const 0x1.4p+3))
(assert_return (invoke "f64_align_switch" (i32.const 0x3)) (f64.const 0x1.4p+3))
(assert_return (invoke "f64_align_switch" (i32.const 0x4)) (f64.const 0x1.4p+3))
(assert_return
  (invoke "i32_align_switch" (i32.const 0x0) (i32.const 0x0))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x0) (i32.const 0x1))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x1) (i32.const 0x0))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x1) (i32.const 0x1))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x2) (i32.const 0x0))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x2) (i32.const 0x1))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x2) (i32.const 0x2))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x3) (i32.const 0x0))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x3) (i32.const 0x1))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x3) (i32.const 0x2))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x4) (i32.const 0x0))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x4) (i32.const 0x1))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x4) (i32.const 0x2))
  (i32.const 0xa)
)
(assert_return
  (invoke "i32_align_switch" (i32.const 0x4) (i32.const 0x4))
  (i32.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x0) (i32.const 0x0))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x0) (i32.const 0x1))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x1) (i32.const 0x0))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x1) (i32.const 0x1))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x2) (i32.const 0x0))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x2) (i32.const 0x1))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x2) (i32.const 0x2))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x3) (i32.const 0x0))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x3) (i32.const 0x1))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x3) (i32.const 0x2))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x4) (i32.const 0x0))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x4) (i32.const 0x1))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x4) (i32.const 0x2))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x4) (i32.const 0x4))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x5) (i32.const 0x0))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x5) (i32.const 0x1))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x5) (i32.const 0x2))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x5) (i32.const 0x4))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x6) (i32.const 0x0))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x6) (i32.const 0x1))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x6) (i32.const 0x2))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x6) (i32.const 0x4))
  (i64.const 0xa)
)
(assert_return
  (invoke "i64_align_switch" (i32.const 0x6) (i32.const 0x8))
  (i64.const 0xa)
)
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
  "\01\7f\01\7f\03\82\80\80\80\00\01\00\05\83\80\80"
  "\80\00\01\00\01\07\88\80\80\80\00\01\04\6c\6f\61"
  "\64\00\00\0a\8d\80\80\80\00\01\87\80\80\80\00\00"
  "\20\00\28\02\00\0b"
)
(module instance)
(assert_trap
  (invoke "store" (i32.const 0xfffc) (i64.const 0xffff_ffff_ffff_ffff))
  "out of bounds memory access"
)
(assert_return (invoke "load" (i32.const 0xfffc)) (i32.const 0x0))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\28\1f\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\28\20\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\28\21\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\8e\80\80\80\00\01\88\80\80\80\00\00"
    "\41\00\28\3f\00\1a\0b"
  )
  "alignment must not be larger than natural"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\8d\80\80\80\00\01\87\80\80\80\00\00"
    "\41\00\28\01\1a\0b"
  )
  "type mismatch"
)
(assert_malformed
  (module binary
    "\00\61\73\6d\01\00\00\00\01\04\01\60\00\00\03\02"
    "\01\00\05\03\01\00\01\0a\0b\01\09\00\41\00\28\80"
    "\01\00\1a\0b"
  )
  "malformed memop flags"
)
(assert_malformed
  (module binary
    "\00\61\73\6d\01\00\00\00\01\04\01\60\00\00\03\02"
    "\01\00\05\03\01\00\01\0a\0b\01\09\00\41\00\28\80"
    "\02\00\1a\0b"
  )
  "malformed memop flags"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\97\80\80\80\00\01\91\80\80\80\00\00"
    "\41\00\28\02\ff\ff\ff\ff\ff\ff\ff\ff\ff\01\1a\0b"
  )
  "offset out of range"
)
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\97\80\80\80\00\01\91\80\80\80\00\00"
    "\41\00\28\3f\ff\ff\ff\ff\ff\ff\ff\ff\ff\01\1a\0b"
  )
  "alignment must not be larger than natural"
)
