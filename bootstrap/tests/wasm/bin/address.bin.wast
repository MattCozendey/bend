(module definition binary
  "\00\61\73\6d\01\00\00\00\01\86\80\80\80\00\01\60"
  "\01\7f\01\7f\03\8b\80\80\80\00\0a\00\00\00\00\00"
  "\00\00\00\00\00\05\83\80\80\80\00\01\00\01\07\ef"
  "\80\80\80\00\0a\08\38\75\5f\67\6f\6f\64\31\00\00"
  "\08\38\75\5f\67\6f\6f\64\32\00\01\08\38\75\5f\67"
  "\6f\6f\64\33\00\02\08\38\75\5f\67\6f\6f\64\34\00"
  "\03\08\38\75\5f\67\6f\6f\64\35\00\04\08\33\32\5f"
  "\67\6f\6f\64\31\00\05\08\33\32\5f\67\6f\6f\64\32"
  "\00\06\08\33\32\5f\67\6f\6f\64\33\00\07\08\33\32"
  "\5f\67\6f\6f\64\34\00\08\08\33\32\5f\67\6f\6f\64"
  "\35\00\09\0a\f9\80\80\80\00\0a\87\80\80\80\00\00"
  "\20\00\2d\00\00\0b\87\80\80\80\00\00\20\00\2d\00"
  "\00\0b\87\80\80\80\00\00\20\00\2d\00\01\0b\87\80"
  "\80\80\00\00\20\00\2d\00\02\0b\87\80\80\80\00\00"
  "\20\00\2d\00\19\0b\87\80\80\80\00\00\20\00\28\02"
  "\00\0b\87\80\80\80\00\00\20\00\28\00\00\0b\87\80"
  "\80\80\00\00\20\00\28\00\01\0b\87\80\80\80\00\00"
  "\20\00\28\01\02\0b\87\80\80\80\00\00\20\00\28\02"
  "\19\0b\0b\a0\80\80\80\00\01\00\41\00\0b\1a\61\62"
  "\63\64\65\66\67\68\69\6a\6b\6c\6d\6e\6f\70\71\72"
  "\73\74\75\76\77\78\79\7a"
)
(module instance)
(assert_return (invoke "8u_good1" (i32.const 0x0)) (i32.const 0x61))
(assert_return (invoke "8u_good2" (i32.const 0x0)) (i32.const 0x61))
(assert_return (invoke "8u_good3" (i32.const 0x0)) (i32.const 0x62))
(assert_return (invoke "8u_good4" (i32.const 0x0)) (i32.const 0x63))
(assert_return (invoke "8u_good5" (i32.const 0x0)) (i32.const 0x7a))
(assert_return (invoke "8s_good1" (i32.const 0x0)) (i32.const 0x61))
(assert_return (invoke "8s_good2" (i32.const 0x0)) (i32.const 0x61))
(assert_return (invoke "8s_good3" (i32.const 0x0)) (i32.const 0x62))
(assert_return (invoke "8s_good4" (i32.const 0x0)) (i32.const 0x63))
(assert_return (invoke "8s_good5" (i32.const 0x0)) (i32.const 0x7a))
(assert_return (invoke "16u_good1" (i32.const 0x0)) (i32.const 0x6261))
(assert_return (invoke "16u_good2" (i32.const 0x0)) (i32.const 0x6261))
(assert_return (invoke "16u_good3" (i32.const 0x0)) (i32.const 0x6362))
(assert_return (invoke "16u_good4" (i32.const 0x0)) (i32.const 0x6463))
(assert_return (invoke "16u_good5" (i32.const 0x0)) (i32.const 0x7a))
(assert_return (invoke "16s_good1" (i32.const 0x0)) (i32.const 0x6261))
(assert_return (invoke "16s_good2" (i32.const 0x0)) (i32.const 0x6261))
(assert_return (invoke "16s_good3" (i32.const 0x0)) (i32.const 0x6362))
(assert_return (invoke "16s_good4" (i32.const 0x0)) (i32.const 0x6463))
(assert_return (invoke "16s_good5" (i32.const 0x0)) (i32.const 0x7a))
(assert_return (invoke "32_good1" (i32.const 0x0)) (i32.const 0x6463_6261))
(assert_return (invoke "32_good2" (i32.const 0x0)) (i32.const 0x6463_6261))
(assert_return (invoke "32_good3" (i32.const 0x0)) (i32.const 0x6564_6362))
(assert_return (invoke "32_good4" (i32.const 0x0)) (i32.const 0x6665_6463))
(assert_return (invoke "32_good5" (i32.const 0x0)) (i32.const 0x7a))
(assert_return (invoke "8u_good1" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8u_good2" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8u_good3" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8u_good4" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8u_good5" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8s_good1" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8s_good2" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8s_good3" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8s_good4" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8s_good5" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16u_good1" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16u_good2" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16u_good3" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16u_good4" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16u_good5" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16s_good1" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16s_good2" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16s_good3" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16s_good4" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "16s_good5" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "32_good1" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "32_good2" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "32_good3" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "32_good4" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "32_good5" (i32.const 0xffe3)) (i32.const 0x0))
(assert_return (invoke "8u_good1" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "8u_good2" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "8u_good3" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "8u_good4" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "8u_good5" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "8s_good1" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "8s_good2" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "8s_good3" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "8s_good4" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "8s_good5" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16u_good1" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16u_good2" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16u_good3" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16u_good4" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16u_good5" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16s_good1" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16s_good2" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16s_good3" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16s_good4" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "16s_good5" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "32_good1" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "32_good2" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "32_good3" (i32.const 0xffe4)) (i32.const 0x0))
(assert_return (invoke "32_good4" (i32.const 0xffe4)) (i32.const 0x0))
(assert_trap
  (invoke "32_good5" (i32.const 0xffe4))
  "out of bounds memory access"
)
(assert_trap
  (invoke "8u_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "8s_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "16u_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "16s_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "32_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "32_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap (invoke "8u_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "8s_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "16u_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "16s_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "32_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "8u_bad" (i32.const 0x1)) "out of bounds memory access")
(assert_trap (invoke "8s_bad" (i32.const 0x1)) "out of bounds memory access")
(assert_trap (invoke "16u_bad" (i32.const 0x1)) "out of bounds memory access")
(assert_trap (invoke "16s_bad" (i32.const 0x1)) "out of bounds memory access")
(assert_trap (invoke "32_bad" (i32.const 0x1)) "out of bounds memory access")
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\01\84\80\80\80\00\01\60"
    "\00\00\03\82\80\80\80\00\01\00\05\83\80\80\80\00"
    "\01\00\01\0a\92\80\80\80\00\01\8c\80\80\80\00\00"
    "\41\00\28\02\80\80\80\80\10\1a\0b"
  )
  "offset out of range"
)
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\01\0b\a0\80\80\80\00\01\00\41\00\0b\1a\61\62\63"
  "\64\65\66\67\68\69\6a\6b\6c\6d\6e\6f\70\71\72\73"
  "\74\75\76\77\78\79\7a"
)
(module instance)
(assert_return (invoke "8u_good1" (i32.const 0x0)) (i64.const 0x61))
(assert_return (invoke "8u_good2" (i32.const 0x0)) (i64.const 0x61))
(assert_return (invoke "8u_good3" (i32.const 0x0)) (i64.const 0x62))
(assert_return (invoke "8u_good4" (i32.const 0x0)) (i64.const 0x63))
(assert_return (invoke "8u_good5" (i32.const 0x0)) (i64.const 0x7a))
(assert_return (invoke "8s_good1" (i32.const 0x0)) (i64.const 0x61))
(assert_return (invoke "8s_good2" (i32.const 0x0)) (i64.const 0x61))
(assert_return (invoke "8s_good3" (i32.const 0x0)) (i64.const 0x62))
(assert_return (invoke "8s_good4" (i32.const 0x0)) (i64.const 0x63))
(assert_return (invoke "8s_good5" (i32.const 0x0)) (i64.const 0x7a))
(assert_return (invoke "16u_good1" (i32.const 0x0)) (i64.const 0x6261))
(assert_return (invoke "16u_good2" (i32.const 0x0)) (i64.const 0x6261))
(assert_return (invoke "16u_good3" (i32.const 0x0)) (i64.const 0x6362))
(assert_return (invoke "16u_good4" (i32.const 0x0)) (i64.const 0x6463))
(assert_return (invoke "16u_good5" (i32.const 0x0)) (i64.const 0x7a))
(assert_return (invoke "16s_good1" (i32.const 0x0)) (i64.const 0x6261))
(assert_return (invoke "16s_good2" (i32.const 0x0)) (i64.const 0x6261))
(assert_return (invoke "16s_good3" (i32.const 0x0)) (i64.const 0x6362))
(assert_return (invoke "16s_good4" (i32.const 0x0)) (i64.const 0x6463))
(assert_return (invoke "16s_good5" (i32.const 0x0)) (i64.const 0x7a))
(assert_return (invoke "32u_good1" (i32.const 0x0)) (i64.const 0x6463_6261))
(assert_return (invoke "32u_good2" (i32.const 0x0)) (i64.const 0x6463_6261))
(assert_return (invoke "32u_good3" (i32.const 0x0)) (i64.const 0x6564_6362))
(assert_return (invoke "32u_good4" (i32.const 0x0)) (i64.const 0x6665_6463))
(assert_return (invoke "32u_good5" (i32.const 0x0)) (i64.const 0x7a))
(assert_return (invoke "32s_good1" (i32.const 0x0)) (i64.const 0x6463_6261))
(assert_return (invoke "32s_good2" (i32.const 0x0)) (i64.const 0x6463_6261))
(assert_return (invoke "32s_good3" (i32.const 0x0)) (i64.const 0x6564_6362))
(assert_return (invoke "32s_good4" (i32.const 0x0)) (i64.const 0x6665_6463))
(assert_return (invoke "32s_good5" (i32.const 0x0)) (i64.const 0x7a))
(assert_return
  (invoke "64_good1" (i32.const 0x0))
  (i64.const 0x6867_6665_6463_6261)
)
(assert_return
  (invoke "64_good2" (i32.const 0x0))
  (i64.const 0x6867_6665_6463_6261)
)
(assert_return
  (invoke "64_good3" (i32.const 0x0))
  (i64.const 0x6968_6766_6564_6362)
)
(assert_return
  (invoke "64_good4" (i32.const 0x0))
  (i64.const 0x6a69_6867_6665_6463)
)
(assert_return (invoke "64_good5" (i32.const 0x0)) (i64.const 0x7a))
(assert_return (invoke "8u_good1" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8u_good2" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8u_good3" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8u_good4" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8u_good5" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8s_good1" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8s_good2" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8s_good3" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8s_good4" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8s_good5" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16u_good1" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16u_good2" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16u_good3" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16u_good4" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16u_good5" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16s_good1" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16s_good2" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16s_good3" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16s_good4" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "16s_good5" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32u_good1" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32u_good2" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32u_good3" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32u_good4" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32u_good5" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32s_good1" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32s_good2" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32s_good3" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32s_good4" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "32s_good5" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "64_good1" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "64_good2" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "64_good3" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "64_good4" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "64_good5" (i32.const 0xffdf)) (i64.const 0x0))
(assert_return (invoke "8u_good1" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "8u_good2" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "8u_good3" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "8u_good4" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "8u_good5" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "8s_good1" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "8s_good2" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "8s_good3" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "8s_good4" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "8s_good5" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16u_good1" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16u_good2" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16u_good3" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16u_good4" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16u_good5" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16s_good1" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16s_good2" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16s_good3" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16s_good4" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "16s_good5" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32u_good1" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32u_good2" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32u_good3" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32u_good4" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32u_good5" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32s_good1" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32s_good2" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32s_good3" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32s_good4" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "32s_good5" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "64_good1" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "64_good2" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "64_good3" (i32.const 0xffe0)) (i64.const 0x0))
(assert_return (invoke "64_good4" (i32.const 0xffe0)) (i64.const 0x0))
(assert_trap
  (invoke "64_good5" (i32.const 0xffe0))
  "out of bounds memory access"
)
(assert_trap
  (invoke "8u_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "8s_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "16u_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "16s_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "32u_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "32s_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "64_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap (invoke "8u_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "8s_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "16u_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "16s_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "32u_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "32s_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "64_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "8u_bad" (i32.const 0x1)) "out of bounds memory access")
(assert_trap (invoke "8s_bad" (i32.const 0x1)) "out of bounds memory access")
(assert_trap (invoke "16u_bad" (i32.const 0x1)) "out of bounds memory access")
(assert_trap (invoke "16s_bad" (i32.const 0x1)) "out of bounds memory access")
(assert_trap (invoke "32u_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "32s_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "64_bad" (i32.const 0x1)) "out of bounds memory access")
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\01\0b\92\80\80\80\00\01\00\41\00\0b\0c\00\00\00"
  "\00\00\00\a0\7f\01\00\d0\7f"
)
(module instance)
(assert_return (invoke "32_good1" (i32.const 0x0)) (f32.const 0x0p+0))
(assert_return (invoke "32_good2" (i32.const 0x0)) (f32.const 0x0p+0))
(assert_return (invoke "32_good3" (i32.const 0x0)) (f32.const 0x0p+0))
(assert_return (invoke "32_good4" (i32.const 0x0)) (f32.const 0x0p+0))
(assert_return (invoke "32_good5" (i32.const 0x0)) (f32.const nan:0x50_0001))
(assert_return (invoke "32_good1" (i32.const 0xfff4)) (f32.const 0x0p+0))
(assert_return (invoke "32_good2" (i32.const 0xfff4)) (f32.const 0x0p+0))
(assert_return (invoke "32_good3" (i32.const 0xfff4)) (f32.const 0x0p+0))
(assert_return (invoke "32_good4" (i32.const 0xfff4)) (f32.const 0x0p+0))
(assert_return (invoke "32_good5" (i32.const 0xfff4)) (f32.const 0x0p+0))
(assert_return (invoke "32_good1" (i32.const 0xfff5)) (f32.const 0x0p+0))
(assert_return (invoke "32_good2" (i32.const 0xfff5)) (f32.const 0x0p+0))
(assert_return (invoke "32_good3" (i32.const 0xfff5)) (f32.const 0x0p+0))
(assert_return (invoke "32_good4" (i32.const 0xfff5)) (f32.const 0x0p+0))
(assert_trap
  (invoke "32_good5" (i32.const 0xfff5))
  "out of bounds memory access"
)
(assert_trap
  (invoke "32_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "32_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap (invoke "32_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "32_bad" (i32.const 0x1)) "out of bounds memory access")
(module definition binary
  "\00\61\73\6d\01\00\00\00\05\83\80\80\80\00\01\00"
  "\01\0b\a0\80\80\80\00\01\00\41\00\0b\1a\00\00\00"
  "\00\00\00\00\00\00\00\00\00\00\00\00\00\f4\7f\01"
  "\00\00\00\00\00\fc\7f"
)
(module instance)
(assert_return (invoke "64_good1" (i32.const 0x0)) (f64.const 0x0p+0))
(assert_return (invoke "64_good2" (i32.const 0x0)) (f64.const 0x0p+0))
(assert_return (invoke "64_good3" (i32.const 0x0)) (f64.const 0x0p+0))
(assert_return (invoke "64_good4" (i32.const 0x0)) (f64.const 0x0p+0))
(assert_return
  (invoke "64_good5" (i32.const 0x0))
  (f64.const nan:0xc_0000_0000_0001)
)
(assert_return (invoke "64_good1" (i32.const 0xffe6)) (f64.const 0x0p+0))
(assert_return (invoke "64_good2" (i32.const 0xffe6)) (f64.const 0x0p+0))
(assert_return (invoke "64_good3" (i32.const 0xffe6)) (f64.const 0x0p+0))
(assert_return (invoke "64_good4" (i32.const 0xffe6)) (f64.const 0x0p+0))
(assert_return (invoke "64_good5" (i32.const 0xffe6)) (f64.const 0x0p+0))
(assert_return (invoke "64_good1" (i32.const 0xffe7)) (f64.const 0x0p+0))
(assert_return (invoke "64_good2" (i32.const 0xffe7)) (f64.const 0x0p+0))
(assert_return (invoke "64_good3" (i32.const 0xffe7)) (f64.const 0x0p+0))
(assert_return (invoke "64_good4" (i32.const 0xffe7)) (f64.const 0x0p+0))
(assert_trap
  (invoke "64_good5" (i32.const 0xffe7))
  "out of bounds memory access"
)
(assert_trap
  (invoke "64_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap
  (invoke "64_good3" (i32.const 0xffff_ffff))
  "out of bounds memory access"
)
(assert_trap (invoke "64_bad" (i32.const 0x0)) "out of bounds memory access")
(assert_trap (invoke "64_bad" (i32.const 0x1)) "out of bounds memory access")
