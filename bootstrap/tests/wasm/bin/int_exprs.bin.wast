(module definition binary
  "\00\61\73\6d\01\00\00\00\01\87\80\80\80\00\01\60"
  "\02\7f\7f\01\7f\03\82\80\80\80\00\01\00\07\9c\80"
  "\80\80\00\01\18\69\33\32\2e\6e\6f\5f\66\6f\6c\64"
  "\5f\63\6d\70\5f\75\5f\6f\66\66\73\65\74\00\00\0a"
  "\93\80\80\80\00\01\8d\80\80\80\00\00\20\00\41\01"
  "\6a\20\01\41\01\6a\49\0b"
)
(module instance)
(assert_return
  (invoke "i32.no_fold_cmp_s_offset" (i32.const 0x7fff_ffff) (i32.const 0x0))
  (i32.const 0x1)
)
(assert_return
  (invoke "i32.no_fold_cmp_u_offset" (i32.const 0xffff_ffff) (i32.const 0x0))
  (i32.const 0x1)
)
(assert_return
  (invoke "i64.no_fold_cmp_s_offset"
    (i64.const 0x7fff_ffff_ffff_ffff)
    (i64.const 0x0)
  )
  (i32.const 0x1)
)
(assert_return
  (invoke "i64.no_fold_cmp_u_offset"
    (i64.const 0xffff_ffff_ffff_ffff)
    (i64.const 0x0)
  )
  (i32.const 0x1)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return
  (invoke "i64.no_fold_wrap_extend_s" (i64.const 0x10_2030_4050_6070))
  (i64.const 0x4050_6070)
)
(assert_return
  (invoke "i64.no_fold_wrap_extend_s" (i64.const 0xa0_b0c0_d0e0_f0a0))
  (i64.const 0xffff_ffff_d0e0_f0a0)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return
  (invoke "i64.no_fold_wrap_extend_u" (i64.const 0x10_2030_4050_6070))
  (i64.const 0x4050_6070)
)
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
  "\01\7f\01\7f\03\82\80\80\80\00\01\00\07\99\80\80"
  "\80\00\01\15\69\33\32\2e\6e\6f\5f\66\6f\6c\64\5f"
  "\73\68\6c\5f\73\68\72\5f\75\00\00\0a\90\80\80\80"
  "\00\01\8a\80\80\80\00\00\20\00\41\01\74\41\01\76"
  "\0b"
)
(module instance)
(assert_return
  (invoke "i32.no_fold_shl_shr_s" (i32.const 0x8000_0000))
  (i32.const 0x0)
)
(assert_return
  (invoke "i32.no_fold_shl_shr_u" (i32.const 0x8000_0000))
  (i32.const 0x0)
)
(assert_return
  (invoke "i64.no_fold_shl_shr_s" (i64.const 0x8000_0000_0000_0000))
  (i64.const 0x0)
)
(assert_return
  (invoke "i64.no_fold_shl_shr_u" (i64.const 0x8000_0000_0000_0000))
  (i64.const 0x0)
)
(module definition binary
  "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
  "\01\7f\01\7f\03\82\80\80\80\00\01\00\07\99\80\80"
  "\80\00\01\15\69\33\32\2e\6e\6f\5f\66\6f\6c\64\5f"
  "\73\68\72\5f\75\5f\73\68\6c\00\00\0a\90\80\80\80"
  "\00\01\8a\80\80\80\00\00\20\00\41\01\76\41\01\74"
  "\0b"
)
(module instance)
(assert_return (invoke "i32.no_fold_shr_s_shl" (i32.const 0x1)) (i32.const 0x0))
(assert_return (invoke "i32.no_fold_shr_u_shl" (i32.const 0x1)) (i32.const 0x0))
(assert_return (invoke "i64.no_fold_shr_s_shl" (i64.const 0x1)) (i64.const 0x0))
(assert_return (invoke "i64.no_fold_shr_u_shl" (i64.const 0x1)) (i64.const 0x0))
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return (invoke "i32.no_fold_div_s_mul" (i32.const 0x1)) (i32.const 0x0))
(assert_return (invoke "i32.no_fold_div_u_mul" (i32.const 0x1)) (i32.const 0x0))
(assert_return (invoke "i64.no_fold_div_s_mul" (i64.const 0x1)) (i64.const 0x0))
(assert_return (invoke "i64.no_fold_div_u_mul" (i64.const 0x1)) (i64.const 0x0))
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_trap
  (invoke "i32.no_fold_div_s_self" (i32.const 0x0))
  "integer divide by zero"
)
(assert_trap
  (invoke "i32.no_fold_div_u_self" (i32.const 0x0))
  "integer divide by zero"
)
(assert_trap
  (invoke "i64.no_fold_div_s_self" (i64.const 0x0))
  "integer divide by zero"
)
(assert_trap
  (invoke "i64.no_fold_div_u_self" (i64.const 0x0))
  "integer divide by zero"
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_trap
  (invoke "i32.no_fold_rem_s_self" (i32.const 0x0))
  "integer divide by zero"
)
(assert_trap
  (invoke "i32.no_fold_rem_u_self" (i32.const 0x0))
  "integer divide by zero"
)
(assert_trap
  (invoke "i64.no_fold_rem_s_self" (i64.const 0x0))
  "integer divide by zero"
)
(assert_trap
  (invoke "i64.no_fold_rem_u_self" (i64.const 0x0))
  "integer divide by zero"
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return
  (invoke "i32.no_fold_mul_div_s" (i32.const 0x8000_0000))
  (i32.const 0x0)
)
(assert_return
  (invoke "i32.no_fold_mul_div_u" (i32.const 0x8000_0000))
  (i32.const 0x0)
)
(assert_return
  (invoke "i64.no_fold_mul_div_s" (i64.const 0x8000_0000_0000_0000))
  (i64.const 0x0)
)
(assert_return
  (invoke "i64.no_fold_mul_div_u" (i64.const 0x8000_0000_0000_0000))
  (i64.const 0x0)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return
  (invoke "i32.no_fold_div_s_2" (i32.const 0xffff_fff5))
  (i32.const 0xffff_fffb)
)
(assert_return
  (invoke "i64.no_fold_div_s_2" (i64.const 0xffff_ffff_ffff_fff5))
  (i64.const 0xffff_ffff_ffff_fffb)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return
  (invoke "i32.no_fold_rem_s_2" (i32.const 0xffff_fff5))
  (i32.const 0xffff_ffff)
)
(assert_return
  (invoke "i64.no_fold_rem_s_2" (i64.const 0xffff_ffff_ffff_fff5))
  (i64.const 0xffff_ffff_ffff_ffff)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_trap (invoke "i32.div_s_0" (i32.const 0x47)) "integer divide by zero")
(assert_trap (invoke "i32.div_u_0" (i32.const 0x47)) "integer divide by zero")
(assert_trap (invoke "i64.div_s_0" (i64.const 0x47)) "integer divide by zero")
(assert_trap (invoke "i64.div_u_0" (i64.const 0x47)) "integer divide by zero")
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return (invoke "i32.div_s_3" (i32.const 0x47)) (i32.const 0x17))
(assert_return
  (invoke "i32.div_s_3" (i32.const 0x6000_0000))
  (i32.const 0x2000_0000)
)
(assert_return (invoke "i32.div_u_3" (i32.const 0x47)) (i32.const 0x17))
(assert_return
  (invoke "i32.div_u_3" (i32.const 0xc000_0000))
  (i32.const 0x4000_0000)
)
(assert_return (invoke "i64.div_s_3" (i64.const 0x47)) (i64.const 0x17))
(assert_return
  (invoke "i64.div_s_3" (i64.const 0x3000_0000_0000_0000))
  (i64.const 0x1000_0000_0000_0000)
)
(assert_return (invoke "i64.div_u_3" (i64.const 0x47)) (i64.const 0x17))
(assert_return
  (invoke "i64.div_u_3" (i64.const 0xc000_0000_0000_0000))
  (i64.const 0x4000_0000_0000_0000)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return (invoke "i32.div_s_5" (i32.const 0x47)) (i32.const 0xe))
(assert_return
  (invoke "i32.div_s_5" (i32.const 0x5000_0000))
  (i32.const 0x1000_0000)
)
(assert_return (invoke "i32.div_u_5" (i32.const 0x47)) (i32.const 0xe))
(assert_return
  (invoke "i32.div_u_5" (i32.const 0xa000_0000))
  (i32.const 0x2000_0000)
)
(assert_return (invoke "i64.div_s_5" (i64.const 0x47)) (i64.const 0xe))
(assert_return
  (invoke "i64.div_s_5" (i64.const 0x5000_0000_0000_0000))
  (i64.const 0x1000_0000_0000_0000)
)
(assert_return (invoke "i64.div_u_5" (i64.const 0x47)) (i64.const 0xe))
(assert_return
  (invoke "i64.div_u_5" (i64.const 0xa000_0000_0000_0000))
  (i64.const 0x2000_0000_0000_0000)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return (invoke "i32.div_s_7" (i32.const 0x47)) (i32.const 0xa))
(assert_return
  (invoke "i32.div_s_7" (i32.const 0x7000_0000))
  (i32.const 0x1000_0000)
)
(assert_return (invoke "i32.div_u_7" (i32.const 0x47)) (i32.const 0xa))
(assert_return
  (invoke "i32.div_u_7" (i32.const 0xe000_0000))
  (i32.const 0x2000_0000)
)
(assert_return (invoke "i64.div_s_7" (i64.const 0x47)) (i64.const 0xa))
(assert_return
  (invoke "i64.div_s_7" (i64.const 0x7000_0000_0000_0000))
  (i64.const 0x1000_0000_0000_0000)
)
(assert_return (invoke "i64.div_u_7" (i64.const 0x47)) (i64.const 0xa))
(assert_return
  (invoke "i64.div_u_7" (i64.const 0xe000_0000_0000_0000))
  (i64.const 0x2000_0000_0000_0000)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return (invoke "i32.rem_s_3" (i32.const 0x47)) (i32.const 0x2))
(assert_return (invoke "i32.rem_s_3" (i32.const 0x6000_0000)) (i32.const 0x0))
(assert_return (invoke "i32.rem_u_3" (i32.const 0x47)) (i32.const 0x2))
(assert_return (invoke "i32.rem_u_3" (i32.const 0xc000_0000)) (i32.const 0x0))
(assert_return (invoke "i64.rem_s_3" (i64.const 0x47)) (i64.const 0x2))
(assert_return
  (invoke "i64.rem_s_3" (i64.const 0x3000_0000_0000_0000))
  (i64.const 0x0)
)
(assert_return (invoke "i64.rem_u_3" (i64.const 0x47)) (i64.const 0x2))
(assert_return
  (invoke "i64.rem_u_3" (i64.const 0xc000_0000_0000_0000))
  (i64.const 0x0)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return (invoke "i32.rem_s_5" (i32.const 0x47)) (i32.const 0x1))
(assert_return (invoke "i32.rem_s_5" (i32.const 0x5000_0000)) (i32.const 0x0))
(assert_return (invoke "i32.rem_u_5" (i32.const 0x47)) (i32.const 0x1))
(assert_return (invoke "i32.rem_u_5" (i32.const 0xa000_0000)) (i32.const 0x0))
(assert_return (invoke "i64.rem_s_5" (i64.const 0x47)) (i64.const 0x1))
(assert_return
  (invoke "i64.rem_s_5" (i64.const 0x5000_0000_0000_0000))
  (i64.const 0x0)
)
(assert_return (invoke "i64.rem_u_5" (i64.const 0x47)) (i64.const 0x1))
(assert_return
  (invoke "i64.rem_u_5" (i64.const 0xa000_0000_0000_0000))
  (i64.const 0x0)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_return (invoke "i32.rem_s_7" (i32.const 0x47)) (i32.const 0x1))
(assert_return (invoke "i32.rem_s_7" (i32.const 0x7000_0000)) (i32.const 0x0))
(assert_return (invoke "i32.rem_u_7" (i32.const 0x47)) (i32.const 0x1))
(assert_return (invoke "i32.rem_u_7" (i32.const 0xe000_0000)) (i32.const 0x0))
(assert_return (invoke "i64.rem_s_7" (i64.const 0x47)) (i64.const 0x1))
(assert_return
  (invoke "i64.rem_s_7" (i64.const 0x7000_0000_0000_0000))
  (i64.const 0x0)
)
(assert_return (invoke "i64.rem_u_7" (i64.const 0x47)) (i64.const 0x1))
(assert_return
  (invoke "i64.rem_u_7" (i64.const 0xe000_0000_0000_0000))
  (i64.const 0x0)
)
(module definition binary "\00\61\73\6d\01\00\00\00")
(module instance)
(assert_trap
  (invoke "i32.no_fold_div_neg1" (i32.const 0x8000_0000))
  "integer overflow"
)
(assert_trap
  (invoke "i64.no_fold_div_neg1" (i64.const 0x8000_0000_0000_0000))
  "integer overflow"
)
