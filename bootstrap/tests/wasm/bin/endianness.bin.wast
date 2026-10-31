(module definition binary
  "\00\61\73\6d\01\00\00\00\01\8b\80\80\80\00\02\60"
  "\01\7f\01\7f\60\02\7f\7f\00\03\83\80\80\80\00\02"
  "\01\00\05\83\80\80\80\00\01\00\01\0a\b4\80\80\80"
  "\00\02\96\80\80\80\00\00\20\00\20\01\3a\00\00\20"
  "\00\41\01\6a\20\01\41\08\76\3a\00\00\0b\93\80\80"
  "\80\00\00\20\00\2d\00\00\20\00\41\01\6a\2d\00\00"
  "\41\08\74\72\0b"
)
(module instance)
(assert_return
  (invoke "i32_load16_s" (i32.const 0xffff_ffff))
  (i32.const 0xffff_ffff)
)
(assert_return
  (invoke "i32_load16_s" (i32.const 0xffff_ef6e))
  (i32.const 0xffff_ef6e)
)
(assert_return (invoke "i32_load16_s" (i32.const 0x2a)) (i32.const 0x2a))
(assert_return (invoke "i32_load16_s" (i32.const 0x3210)) (i32.const 0x3210))
(assert_return
  (invoke "i32_load16_u" (i32.const 0xffff_ffff))
  (i32.const 0xffff)
)
(assert_return
  (invoke "i32_load16_u" (i32.const 0xffff_ef6e))
  (i32.const 0xef6e)
)
(assert_return (invoke "i32_load16_u" (i32.const 0x2a)) (i32.const 0x2a))
(assert_return (invoke "i32_load16_u" (i32.const 0xcafe)) (i32.const 0xcafe))
(assert_return
  (invoke "i32_load" (i32.const 0xffff_ffff))
  (i32.const 0xffff_ffff)
)
(assert_return
  (invoke "i32_load" (i32.const 0xfd78_a84e))
  (i32.const 0xfd78_a84e)
)
(assert_return
  (invoke "i32_load" (i32.const 0x287_57b2))
  (i32.const 0x287_57b2)
)
(assert_return
  (invoke "i32_load" (i32.const 0xabad_1dea))
  (i32.const 0xabad_1dea)
)
(assert_return
  (invoke "i64_load16_s" (i64.const 0xffff_ffff_ffff_ffff))
  (i64.const 0xffff_ffff_ffff_ffff)
)
(assert_return
  (invoke "i64_load16_s" (i64.const 0xffff_ffff_ffff_ef6e))
  (i64.const 0xffff_ffff_ffff_ef6e)
)
(assert_return (invoke "i64_load16_s" (i64.const 0x2a)) (i64.const 0x2a))
(assert_return (invoke "i64_load16_s" (i64.const 0x3210)) (i64.const 0x3210))
(assert_return
  (invoke "i64_load16_u" (i64.const 0xffff_ffff_ffff_ffff))
  (i64.const 0xffff)
)
(assert_return
  (invoke "i64_load16_u" (i64.const 0xffff_ffff_ffff_ef6e))
  (i64.const 0xef6e)
)
(assert_return (invoke "i64_load16_u" (i64.const 0x2a)) (i64.const 0x2a))
(assert_return (invoke "i64_load16_u" (i64.const 0xcafe)) (i64.const 0xcafe))
(assert_return
  (invoke "i64_load32_s" (i64.const 0xffff_ffff_ffff_ffff))
  (i64.const 0xffff_ffff_ffff_ffff)
)
(assert_return
  (invoke "i64_load32_s" (i64.const 0xffff_ffff_fd78_a84e))
  (i64.const 0xffff_ffff_fd78_a84e)
)
(assert_return
  (invoke "i64_load32_s" (i64.const 0x287_57b2))
  (i64.const 0x287_57b2)
)
(assert_return
  (invoke "i64_load32_s" (i64.const 0x1234_5678))
  (i64.const 0x1234_5678)
)
(assert_return
  (invoke "i64_load32_u" (i64.const 0xffff_ffff_ffff_ffff))
  (i64.const 0xffff_ffff)
)
(assert_return
  (invoke "i64_load32_u" (i64.const 0xffff_ffff_fd78_a84e))
  (i64.const 0xfd78_a84e)
)
(assert_return
  (invoke "i64_load32_u" (i64.const 0x287_57b2))
  (i64.const 0x287_57b2)
)
(assert_return
  (invoke "i64_load32_u" (i64.const 0xabad_1dea))
  (i64.const 0xabad_1dea)
)
(assert_return
  (invoke "i64_load" (i64.const 0xffff_ffff_ffff_ffff))
  (i64.const 0xffff_ffff_ffff_ffff)
)
(assert_return
  (invoke "i64_load" (i64.const 0xffff_ffff_fd78_a84e))
  (i64.const 0xffff_ffff_fd78_a84e)
)
(assert_return
  (invoke "i64_load" (i64.const 0xabad_1dea))
  (i64.const 0xabad_1dea)
)
(assert_return
  (invoke "i64_load" (i64.const 0xabad_cafe_dead_1dea))
  (i64.const 0xabad_cafe_dead_1dea)
)
(assert_return (invoke "f32_load" (f32.const -0x1p+0)) (f32.const -0x1p+0))
(assert_return
  (invoke "f32_load" (f32.const 0x1.945b_6cp-7))
  (f32.const 0x1.945b_6cp-7)
)
(assert_return
  (invoke "f32_load" (f32.const 0x1.0926_cap+12))
  (f32.const 0x1.0926_cap+12)
)
(assert_return
  (invoke "f32_load" (f32.const 0x1.ffff_fep+127))
  (f32.const 0x1.ffff_fep+127)
)
(assert_return (invoke "f64_load" (f64.const -0x1p+0)) (f64.const -0x1p+0))
(assert_return
  (invoke "f64_load" (f64.const 0x1.34a4_584f_4c6e_7p+10))
  (f64.const 0x1.34a4_584f_4c6e_7p+10)
)
(assert_return
  (invoke "f64_load" (f64.const 0x1.9e4c_9b26_c7ea_ep+18))
  (f64.const 0x1.9e4c_9b26_c7ea_ep+18)
)
(assert_return
  (invoke "f64_load" (f64.const 0x1.ffff_ffff_ffff_fp+1023))
  (f64.const 0x1.ffff_ffff_ffff_fp+1023)
)
(assert_return
  (invoke "i32_store16" (i32.const 0xffff_ffff))
  (i32.const 0xffff)
)
(assert_return
  (invoke "i32_store16" (i32.const 0xffff_ef6e))
  (i32.const 0xef6e)
)
(assert_return (invoke "i32_store16" (i32.const 0x2a)) (i32.const 0x2a))
(assert_return (invoke "i32_store16" (i32.const 0xcafe)) (i32.const 0xcafe))
(assert_return
  (invoke "i32_store" (i32.const 0xffff_ffff))
  (i32.const 0xffff_ffff)
)
(assert_return
  (invoke "i32_store" (i32.const 0xffff_ef6e))
  (i32.const 0xffff_ef6e)
)
(assert_return
  (invoke "i32_store" (i32.const 0x287_57b2))
  (i32.const 0x287_57b2)
)
(assert_return
  (invoke "i32_store" (i32.const 0xdead_cafe))
  (i32.const 0xdead_cafe)
)
(assert_return
  (invoke "i64_store16" (i64.const 0xffff_ffff_ffff_ffff))
  (i64.const 0xffff)
)
(assert_return
  (invoke "i64_store16" (i64.const 0xffff_ffff_ffff_ef6e))
  (i64.const 0xef6e)
)
(assert_return (invoke "i64_store16" (i64.const 0x2a)) (i64.const 0x2a))
(assert_return (invoke "i64_store16" (i64.const 0xcafe)) (i64.const 0xcafe))
(assert_return
  (invoke "i64_store32" (i64.const 0xffff_ffff_ffff_ffff))
  (i64.const 0xffff_ffff)
)
(assert_return
  (invoke "i64_store32" (i64.const 0xffff_ffff_ffff_ef6e))
  (i64.const 0xffff_ef6e)
)
(assert_return
  (invoke "i64_store32" (i64.const 0x287_57b2))
  (i64.const 0x287_57b2)
)
(assert_return
  (invoke "i64_store32" (i64.const 0xdead_cafe))
  (i64.const 0xdead_cafe)
)
(assert_return
  (invoke "i64_store" (i64.const 0xffff_ffff_ffff_ffff))
  (i64.const 0xffff_ffff_ffff_ffff)
)
(assert_return
  (invoke "i64_store" (i64.const 0xffff_ffff_fd78_a84e))
  (i64.const 0xffff_ffff_fd78_a84e)
)
(assert_return
  (invoke "i64_store" (i64.const 0xabad_1dea))
  (i64.const 0xabad_1dea)
)
(assert_return
  (invoke "i64_store" (i64.const 0xabad_cafe_dead_1dea))
  (i64.const 0xabad_cafe_dead_1dea)
)
(assert_return (invoke "f32_store" (f32.const -0x1p+0)) (f32.const -0x1p+0))
(assert_return
  (invoke "f32_store" (f32.const 0x1.945b_6cp-7))
  (f32.const 0x1.945b_6cp-7)
)
(assert_return
  (invoke "f32_store" (f32.const 0x1.0926_cap+12))
  (f32.const 0x1.0926_cap+12)
)
(assert_return
  (invoke "f32_store" (f32.const 0x1.ffff_fep+127))
  (f32.const 0x1.ffff_fep+127)
)
(assert_return (invoke "f64_store" (f64.const -0x1p+0)) (f64.const -0x1p+0))
(assert_return
  (invoke "f64_store" (f64.const 0x1.34a4_584f_4c6e_7p+10))
  (f64.const 0x1.34a4_584f_4c6e_7p+10)
)
(assert_return
  (invoke "f64_store" (f64.const 0x1.9e4c_9b26_c7ea_ep+18))
  (f64.const 0x1.9e4c_9b26_c7ea_ep+18)
)
(assert_return
  (invoke "f64_store" (f64.const 0x1.ffff_ffff_ffff_fp+1023))
  (f64.const 0x1.ffff_ffff_ffff_fp+1023)
)
