import FV.Link.TypedStockShared
import FV.Backend.Lowering.StockMemorySinkExtNI
import FVTest.Link.DeadCleanupWitness

/-! # A real vtable-site function under the R4 typed route (#753)

`%_RNxC4toml12H3aIpUwLG79T` is a function of serde_json's `compiletest` executable (its dependency `toml`, debug,
cg_clif's unoptimised dump `_RNxC4toml12H3aIpUwLG79T.unopt.clif` as `cargo fv --lean-link --verified` compiled it).
It was one of #753's left-out functions (CallRegs1's site file: `__fv_d39255307351__RNxC4toml12H3aIpUwLG79T`,
`callRegs/blrRegs`, A1 shape). Two vtable
calls `call_indirect sig26, v197(v269, v198)` and `sig34`, with `sig26 = sig34 = (i64, i64)` (x0,
x1), go through `readonly` vtable loads. The function declares, non-colocated (called through the
GOT), `%_RNxC10serde_core11Hp7uFPr4pJE(i64 sret, i64)` (x8, x0), two other `sret` functions, `memcpy`,
`_Unwind_Resume` and `panic_in_cleanup` (12 GOT calls). It also makes 28 colocated calls (13 of
them `try_call`s with landing pads) and reads three data objects (`symbol_value`).

The program here is `%_RNxC4toml12H3aIpUwLG79T` with that GOT callee, given an `sret` body (its own CLIF is not in
the dump). The other callees and the data objects are outside the program, at addresses of the
outside code. The Stock route is `lean-link`'s first, `Stock.MemorySinkExt.lowerValidated`.

* **Before R4** the typed checks failed at the vtable sites (`stockFails`: `callRegs/blrRegs`):
  `okBTS` is false.
* **Since R4** they hold (`okBTSR`), `attemptT` writes the executable, and `attemptT_correct`
  applies to `%_RNxC4toml12H3aIpUwLG79T` (`correct_applies`). Its conclusion is about every run of the function:
  through its vtable `blr`s, its GOT calls and its `bl`s.

Decided by `native_decide` (witness only): `lake build FVTest.Link.CallRegsR4RealWitness`. -/

namespace E2E.CallRegsR4RealWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend Backend.Proof Backend.Proof.Driver
open E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
open E2E.DeadCleanupExecutableWitness (placeholder)

/-- cg_clif's dump of `_RNxC4toml12H3aIpUwLG79T` (serde_json 1.0.154's `compiletest`, crate `toml`, debug). -/
def srcG : String := "set regalloc_algorithm=backtracking
set opt_level=none
set tls_model=elf_gd
set stack_switch_model=none
set libcall_call_conv=isa_default
set probestack_size_log2=12
set probestack_strategy=inline
set bb_padding_log2_minus_one=0
set log2_min_function_alignment=0
set regalloc_checker=0
set regalloc_verbose_logs=0
set enable_alias_analysis=1
set enable_verifier=0
set is_pic=1
set use_colocated_libcalls=0
set enable_nan_canonicalization=0
set enable_pinned_reg=0
set enable_llvm_abi_extensions=1
set enable_multi_ret_implicit_sret=0
set unwind_info=1
set preserve_frame_pointers=1
set machine_code_cfg_info=0
set enable_probestack=1
set enable_heap_access_spectre_mitigation=1
set enable_table_access_spectre_mitigation=1
set enable_incremental_compilation_cache_checks=0
set enable_compact_unwind_abi=0
target aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0

function %_RNxC4toml12H3aIpUwLG79T(i64, i64, i64, i8 uext, i64, i64) -> i64 system_v {
    ss0 = explicit_slot 8, align = 8
    ss1 = explicit_slot 16, align = 8
    ss2 = explicit_slot 16, align = 8
    ss3 = explicit_slot 16, align = 8
    ss4 = explicit_slot 8, align = 8
    ss5 = explicit_slot 72, align = 8
    ss6 = explicit_slot 40, align = 8
    ss7 = explicit_slot 72, align = 8
    ss8 = explicit_slot 32, align = 8
    ss9 = explicit_slot 40, align = 8
    ss10 = explicit_slot 32, align = 8
    ss11 = explicit_slot 56, align = 8
    ss12 = explicit_slot 16, align = 8
    ss13 = explicit_slot 40, align = 8
    ss14 = explicit_slot 72, align = 8
    ss15 = explicit_slot 8, align = 8
    ss16 = explicit_slot 32, align = 8
    ss17 = explicit_slot 8, align = 8
    ss18 = explicit_slot 8, align = 8
    ss19 = explicit_slot 16, align = 8
    ss20 = explicit_slot 88, align = 8
    ss21 = explicit_slot 88, align = 8
    ss22 = explicit_slot 16, align = 8
    ss23 = explicit_slot 88, align = 8
    ss24 = explicit_slot 88, align = 8
    ss25 = explicit_slot 24, align = 8
    ss26 = explicit_slot 24, align = 8
    ss27 = explicit_slot 16, align = 8
    ss28 = explicit_slot 8, align = 8
    ss29 = explicit_slot 16, align = 8
    ss30 = explicit_slot 16, align = 8
    ss31 = explicit_slot 16, align = 8
    ss32 = explicit_slot 32, align = 8
    ss33 = explicit_slot 56, align = 8
    gv0 = symbol colocated %c_Ldata132
    gv1 = symbol colocated %c_Ldata133
    gv2 = symbol colocated %c_Ldata134
    sig0 = (i64, i64) -> i64, i64 system_v
    sig1 = (i64, i64) -> i64, i64 system_v
    sig2 = (i64) -> i64 system_v
    sig3 = (i64 sret, i64) system_v
    sig4 = (i64 sret, i64, i64) system_v
    sig5 = (i64) -> i64 system_v
    sig6 = (i64, i64, i64) -> i64 system_v
    sig7 = (i64 sret) system_v
    sig8 = (i64, i8 uext) system_v
    sig9 = (i64, i8 uext) system_v
    sig10 = (i64, i8 uext) system_v
    sig11 = (i64) -> i64, i64 system_v
    sig12 = (i64, i64, i64) -> i64 system_v
    sig13 = (i64 sret, i64, i64, i64) system_v
    sig14 = (i64, i64, i64) -> i64 system_v
    sig15 = (i64, i64) -> i64 system_v
    sig16 = (i64, i64, i64) -> i64 system_v
    sig17 = (i64) -> i64 system_v
    sig18 = (i64) -> i64 system_v
    sig19 = (i64, i64) -> i64 system_v
    sig20 = (i64) -> i64 system_v
    sig21 = (i64) -> i64, i64 system_v
    sig22 = (i64) -> i8 uext system_v
    sig23 = (i64) -> i64, i64 system_v
    sig24 = (i64 sret, i64, i64) system_v
    sig25 = (i64 sret, i64, i64, i64) system_v
    sig26 = (i64, i64) system_v
    sig27 = (i64) -> i64, i64 system_v
    sig28 = (i64 sret, i64) system_v
    sig29 = (i64, i64) -> i64, i64 system_v
    sig30 = (i64 sret, i64, i64) system_v
    sig31 = (i64 sret, i64) system_v
    sig32 = (i64 sret, i64) system_v
    sig33 = (i64 sret, i64, i64, i64) system_v
    sig34 = (i64, i64) system_v
    sig35 = (i64) system_v
    sig36 = (i64) system_v
    sig37 = () system_v
    sig38 = (i64) system_v
    sig39 = () system_v
    sig40 = (i64) system_v
    sig41 = () system_v
    fn0 = colocated %_RNxC4toml12H33a80mHdtsj(i64, i64) -> i64, i64 system_v
    fn1 = colocated %_RNxC4toml12HfpciWSTobpl(i64, i64) -> i64, i64 system_v
    fn2 = colocated %_RNxC4toml12Hb3Hdm2BsiHy(i64) -> i64 system_v
    fn3 = colocated %_RNxC4toml12H9cGRmKLY4JS(i64 sret, i64) system_v
    fn4 = colocated %_RNxC4toml12H1GvBPtBRYZY(i64 sret, i64, i64) system_v
    fn5 = colocated %_RNxC4toml12H1nofZt6HE0T(i64) -> i64 system_v
    fn6 = %memcpy(i64, i64, i64) -> i64 system_v
    fn7 = colocated %_RNxC4toml12HjHYCJmCK4B7(i64 sret) system_v
    fn8 = colocated %_RNxC4toml12HjiKBW8D45gQ(i64, i8 uext) system_v
    fn9 = colocated %_RNxC4toml12H3SXvXJWPxUp(i64, i8 uext) system_v
    fn10 = colocated %_RNxC4toml12HbNplun0jt5v(i64, i8 uext) system_v
    fn11 = colocated %_RNxC4toml12H9wlH7wbHhnp(i64) -> i64, i64 system_v
    fn12 = %memcpy(i64, i64, i64) -> i64 system_v
    fn13 = colocated %_RNxC4toml12H5CBAnzRRPZp(i64 sret, i64, i64, i64) system_v
    fn14 = %memcpy(i64, i64, i64) -> i64 system_v
    fn15 = colocated %_RNxC4toml12HaO7KVmyDQNW(i64, i64) -> i64 system_v
    fn16 = %memcpy(i64, i64, i64) -> i64 system_v
    fn17 = colocated %_RNxC4toml12H5xWFa7tOaZV(i64) -> i64 system_v
    fn18 = colocated %_RNxC4toml12Ham7uXG6cCKR(i64) -> i64 system_v
    fn19 = colocated %_RNxC4toml12HjGzJUiKEXCD(i64, i64) -> i64 system_v
    fn20 = colocated %_RNxC4toml12H5xWFa7tOaZV(i64) -> i64 system_v
    fn21 = colocated %_RNxC4toml12HebzLc3YzCLA(i64) -> i64, i64 system_v
    fn22 = colocated %_RNxC4toml12HjK9NAveAOIT(i64) -> i8 uext system_v
    fn23 = colocated %_RNxC4toml12HebzLc3YzCLA(i64) -> i64, i64 system_v
    fn24 = %_RNxC11toml_parser12H2wB6GoetCjG(i64 sret, i64, i64) system_v
    fn25 = %_RNxC11toml_parser12Hf8kKoWwrbUB(i64 sret, i64, i64, i64) system_v
    fn26 = colocated %_RNxC4toml12HkXkEmn2jWQf(i64) -> i64, i64 system_v
    fn27 = %_RNxC10serde_core11Hp7uFPr4pJE(i64 sret, i64) system_v
    fn28 = colocated %_RNxC4toml12HhbBepeUuFHB(i64, i64) -> i64, i64 system_v
    fn29 = colocated %_RNxC4toml12HiH2NdChIXsp(i64 sret, i64, i64) system_v
    fn30 = colocated %_RNxC4toml12H4ltlCc3orqz(i64 sret, i64) system_v
    fn31 = colocated %_RNxC4toml12HfHyvvgmhaHo(i64 sret, i64) system_v
    fn32 = %_RNxC11toml_parser12Hf8kKoWwrbUB(i64 sret, i64, i64, i64) system_v
    fn33 = %_Unwind_Resume(i64) system_v
    fn34 = colocated %_RNxC4toml12HkVHeodXMmkZ(i64) system_v
    fn35 = %_RNvNtCsazjiGSRkgVH_4core9panicking16panic_in_cleanup() system_v
    fn36 = colocated %_RNxC4toml12H8PWWiEpbUkA(i64) system_v
    fn37 = %_RNvNtCsazjiGSRkgVH_4core9panicking16panic_in_cleanup() system_v
    fn38 = colocated %_RNxC4toml12HkMjg9NTCdWU(i64) system_v
    fn39 = %_RNvNtCsazjiGSRkgVH_4core9panicking16panic_in_cleanup() system_v

block0(v0: i64, v1: i64, v2: i64, v3: i8, v4: i64, v5: i64):
    nop
    jump block1

block1:
    nop
    v6 = iconst.i8 0
    v7 = iconst.i8 0
    v8 = iconst.i8 0
    nop
    v11, v12 = call fn0(v1, v2)
    v13 = stack_addr.i64 ss2
    store.i64 notrap v11, v13
    v14 = stack_addr.i64 ss2+8
    store.i64 notrap v12, v14
    jump block2

block2:
    nop
    v15 = stack_addr.i64 ss2
    v16 = load.i64 notrap v15
    v17 = stack_addr.i64 ss2+8
    v18 = load.i64 notrap v17
    nop
    v19, v20 = call fn1(v16, v18)
    v21 = stack_addr.i64 ss1
    store.i64 notrap v19, v21
    v22 = stack_addr.i64 ss1+8
    store.i64 notrap v20, v22
    jump block3

block3:
    nop
    v23 = stack_addr.i64 ss1
    v24 = load.i64 notrap v23
    v25 = stack_addr.i64 ss1+8
    v26 = load.i64 notrap v25
    v27 = stack_addr.i64 ss3
    store.i64 notrap v24, v27
    v28 = stack_addr.i64 ss3+8
    store.i64 notrap v26, v28
    jump block4(v0, v3, v4, v5)

block4(v266: i64, v267: i8, v269: i64, v271: i64):
    nop
    v29 = stack_addr.i64 ss3
    nop
    v30 = call fn2(v29)
    v31 = stack_addr.i64 ss4
    store.i64 notrap v30, v31
    jump block5

block5:
    nop
    v32 = stack_addr.i64 ss4
    v33 = load.i64 notrap v32
    v34 = iconst.i64 0
    v35 = icmp.i64 eq v33, v34
    v36 = iconst.i64 0
    v37 = iconst.i64 1
    v38 = select.i64 v35, v36, v37
    v39 = iconst.i64 4294967295
    v40 = icmp.i64 ugt v38, v39
    brif.i8 v40, block6, block53

block53:
    v41 = ireduce.i32 v38
    br_table v41, block6, [block8, block7]

block6 cold:
    nop
    trap user1

block7:
    nop
    v42 = stack_addr.i64 ss4
    v43 = load.i64 notrap v42
    v45 = stack_addr.i64 ss6
    nop
    call fn3(v45, v43)
    jump block9

block8:
    nop
    v47 = stack_addr.i64 ss0
    store.i64 notrap v266, v47
    v48 = stack_addr.i64 ss0
    v49 = load.i64 notrap v48
    return v49

block9:
    nop
    v51 = stack_addr.i64 ss5
    v52 = stack_addr.i64 ss6
    nop
    call fn4(v51, v266, v52)
    jump block10

block10:
    nop
    v53 = stack_addr.i64 ss5
    v54 = load.i64 notrap v53
    v55 = iconst.i64 -2
    v56 = icmp.i64 eq v54, v55
    v57 = iconst.i64 1
    v58 = iconst.i64 0
    v59 = select.i64 v56, v57, v58
    v60 = iconst.i64 4294967295
    v61 = icmp.i64 ugt v59, v60
    brif.i8 v61, block6, block54

block54:
    v62 = ireduce.i32 v59
    br_table v62, block6, [block12, block11]

block11:
    nop
    v63 = stack_addr.i64 ss5+8
    v64 = stack_addr.i64 ss16
    v65 = load.i64 notrap aligned v63
    v66 = load.i64 notrap aligned v63+8
    v67 = load.i64 notrap aligned v63+16
    v68 = load.i64 notrap aligned v63+24
    store.i64 notrap aligned v65, v64
    store.i64 notrap aligned v66, v64+8
    store.i64 notrap aligned v67, v64+16
    store.i64 notrap aligned v68, v64+24
    v69 = stack_addr.i64 ss16
    v70 = stack_addr.i64 ss32
    v71 = load.i64 notrap aligned v69
    v72 = load.i64 notrap aligned v69+8
    v73 = load.i64 notrap aligned v69+16
    v74 = load.i64 notrap aligned v69+24
    store.i64 notrap aligned v71, v70
    store.i64 notrap aligned v72, v70+8
    store.i64 notrap aligned v73, v70+16
    store.i64 notrap aligned v74, v70+24
    v75 = stack_addr.i64 ss32
    nop
    v76 = call fn5(v75)
    jump block23

block12:
    nop
    v77 = iconst.i8 1
    v78 = stack_addr.i64 ss5
    v79 = stack_addr.i64 ss7
    v80 = iconst.i64 72
    v81 = call fn6(v79, v78, v80)
    v82 = stack_addr.i64 ss8
    nop
    try_call fn7(v82), sig7, block55, [ tag0: block56(exn0) ]

block56(v83: i64) cold:
    jump block52(v77, v83)

block55:
    nop
    jump block13

block13:
    nop
    v84 = iconst.i8 1
    v85 = stack_addr.i64 ss8
    v86 = iconst.i8 1
    nop
    try_call fn8(v85, v86), sig8, block57, [ tag0: block58(exn0) ]

block58(v87: i64) cold:
    jump block50(v84, v77, v87)

block57:
    nop
    jump block14

block14:
    nop
    v88 = stack_addr.i64 ss8
    nop
    try_call fn9(v88, v267), sig9, block59, [ tag0: block60(exn0) ]

block60(v90: i64) cold:
    jump block50(v84, v77, v90)

block59:
    nop
    jump block15

block15:
    nop
    v91 = stack_addr.i64 ss8
    v92 = iconst.i8 1
    nop
    try_call fn10(v91, v92), sig10, block61, [ tag0: block62(exn0) ]

block62(v93: i64) cold:
    jump block50(v84, v77, v93)

block61:
    nop
    jump block16

block16:
    nop
    v94 = iconst.i8 0
    v95 = stack_addr.i64 ss8
    v96 = stack_addr.i64 ss10
    v97 = load.i64 notrap aligned v95
    v98 = load.i64 notrap aligned v95+8
    v99 = load.i64 notrap aligned v95+16
    v100 = load.i64 notrap aligned v95+24
    store.i64 notrap aligned v97, v96
    store.i64 notrap aligned v98, v96+8
    store.i64 notrap aligned v99, v96+16
    store.i64 notrap aligned v100, v96+24
    v101 = iconst.i8 1
    v102 = stack_addr.i64 ss10
    v103 = stack_addr.i64 ss9+8
    v104 = load.i64 notrap aligned v102
    v105 = load.i64 notrap aligned v102+8
    v106 = load.i64 notrap aligned v102+16
    v107 = load.i64 notrap aligned v102+24
    store.i64 notrap aligned v104, v103
    store.i64 notrap aligned v105, v103+8
    store.i64 notrap aligned v106, v103+16
    store.i64 notrap aligned v107, v103+24
    v108 = iconst.i8 6
    v109 = stack_addr.i64 ss9
    store.i8 notrap v108, v109
    nop
    try_call fn11(v43), sig11, block63(ret0, ret1), [ tag0: block64(exn0) ]

block64(v111: i64) cold:
    jump block48(v101, v77, v111)

block63(v112: i64, v113: i64):
    nop
    v114 = stack_addr.i64 ss12
    store.i64 notrap v112, v114
    v115 = stack_addr.i64 ss12+8
    store.i64 notrap v113, v115
    jump block17

block17:
    nop
    v116 = iconst.i8 0
    v117 = stack_addr.i64 ss9
    v118 = stack_addr.i64 ss13
    v119 = iconst.i64 40
    v120 = call fn12(v118, v117, v119)
    v121 = stack_addr.i64 ss11
    v122 = stack_addr.i64 ss12
    v123 = load.i64 notrap v122
    v124 = stack_addr.i64 ss12+8
    v125 = load.i64 notrap v124
    v126 = stack_addr.i64 ss13
    nop
    try_call fn13(v121, v123, v125, v126), sig13, block65, [ tag0: block66(exn0) ]

block66(v127: i64) cold:
    jump block48(v116, v77, v127)

block65:
    nop
    jump block18

block18:
    nop
    v128 = iconst.i8 0
    v129 = stack_addr.i64 ss7
    v130 = stack_addr.i64 ss14
    v131 = iconst.i64 72
    v132 = call fn14(v130, v129, v131)
    v133 = stack_addr.i64 ss14
    v134 = stack_addr.i64 ss11
    v135 = stack_addr.i64 ss33
    v136 = iconst.i64 56
    v137 = call fn16(v135, v134, v136)
    v138 = stack_addr.i64 ss33
    nop
    try_call fn15(v133, v138), sig15, block67(ret0), [ tag0: block68(exn0) ]

block68(v139: i64) cold:
    jump block48(v116, v128, v139)

block67(v140: i64):
    nop
    jump block19

block19:
    nop
    nop
    try_call fn17(v140), sig17, block69(ret0), [ tag0: block70(exn0) ]

block70(v142: i64) cold:
    jump block48(v116, v128, v142)

block69(v143: i64):
    nop
    jump block20

block20:
    nop
    nop
    try_call fn18(v143), sig18, block71(ret0), [ tag0: block72(exn0) ]

block72(v145: i64) cold:
    jump block48(v116, v128, v145)

block71(v146: i64):
    nop
    v147 = stack_addr.i64 ss15
    store.i64 notrap v146, v147
    jump block21

block21:
    nop
    v148 = symbol_value.i64 gv0
    v149 = stack_addr.i64 ss15
    v150 = load.i64 notrap v149
    nop
    try_call fn19(v150, v148), sig19, block73(ret0), [ tag0: block74(exn0) ]

block74(v151: i64) cold:
    jump block48(v116, v128, v151)

block73(v152: i64):
    nop
    jump block22

block22:
    nop
    v153 = iconst.i8 0
    v154 = iconst.i8 0
    v156 = iconst.i8 0
    jump block44(v152)

block23:
    nop
    nop
    v158 = call fn20(v76)
    v159 = stack_addr.i64 ss17
    store.i64 notrap v158, v159
    jump block24

block24:
    nop
    v160 = stack_addr.i64 ss17
    v161 = load.i64 notrap v160
    v162 = load.i8 notrap v161
    v163 = uextend.i64 v162
    v164 = iconst.i64 6
    v165 = icmp.i64 eq v163, v164
    brif.i8 v165, block26, block25

block25:
    nop
    nop
    v167, v168 = call fn21(v43)
    v169 = stack_addr.i64 ss22
    store.i64 notrap v167, v169
    v170 = stack_addr.i64 ss22+8
    store.i64 notrap v168, v170
    jump block35

block26:
    nop
    v171 = stack_addr.i64 ss17
    v172 = load.i64 notrap v171
    v173 = iconst.i64 8
    v174 = iadd.i64 v172, v173
    v175 = stack_addr.i64 ss18
    store.i64 notrap v174, v175
    brif.i8 v267, block27, block34

block27:
    nop
    v177 = stack_addr.i64 ss18
    v178 = load.i64 notrap v177
    nop
    v179 = call fn22(v178)
    jump block28

block28:
    nop
    brif.i8 v179, block34, block29

block29:
    nop
    nop
    v182, v183 = call fn23(v43)
    v184 = stack_addr.i64 ss19
    store.i64 notrap v182, v184
    v185 = stack_addr.i64 ss19+8
    store.i64 notrap v183, v185
    jump block30

block30:
    nop
    v186 = symbol_value.i64 gv1
    v187 = iconst.i64 13
    v188 = stack_addr.i64 ss21
    nop
    call fn24(v188, v186, v187)
    jump block31

block31:
    nop
    v189 = stack_addr.i64 ss20
    v190 = stack_addr.i64 ss21
    v191 = stack_addr.i64 ss19
    v192 = load.i64 notrap v191
    v193 = stack_addr.i64 ss19+8
    v194 = load.i64 notrap v193
    nop
    call fn25(v189, v190, v192, v194)
    jump block32

block32:
    nop
    nop
    v197 = load.i64 notrap aligned readonly v271+24
    v198 = stack_addr.i64 ss20
    nop
    call_indirect sig26, v197(v269, v198)
    jump block33

block33:
    nop
    v199 = iconst.i64 0
    v200 = stack_addr.i64 ss0
    store.i64 notrap v199, v200
    v201 = stack_addr.i64 ss0
    v202 = load.i64 notrap v201
    return v202

block34:
    nop
    v203 = stack_addr.i64 ss18
    v204 = load.i64 notrap v203
    jump block44(v204)

block35:
    nop
    v205 = stack_addr.i64 ss17
    v206 = load.i64 notrap v205
    nop
    v207, v208 = call fn26(v206)
    v209 = stack_addr.i64 ss29
    store.i64 notrap v207, v209
    v210 = stack_addr.i64 ss29+8
    store.i64 notrap v208, v210
    jump block36

block36:
    nop
    v211 = stack_addr.i64 ss29
    v212 = stack_addr.i64 ss28
    store.i64 notrap v211, v212
    v213 = stack_addr.i64 ss28
    v214 = load.i64 notrap v213
    v215 = stack_addr.i64 ss31
    nop
    call fn27(v215, v214)
    jump block37

block37:
    nop
    v216 = iconst.i64 0
    v217 = iconst.i64 16
    v218 = imul.i64 v216, v217
    v219 = stack_addr.i64 ss30
    v220 = iadd.i64 v219, v218
    v221 = stack_addr.i64 ss31
    v222 = load.i64 notrap aligned v221
    v223 = load.i64 notrap aligned v221+8
    store.i64 notrap aligned v222, v220
    store.i64 notrap aligned v223, v220+8
    v224 = symbol_value.i64 gv2
    v225 = stack_addr.i64 ss30
    nop
    v226, v227 = call fn28(v224, v225)
    v228 = stack_addr.i64 ss27
    store.i64 notrap v226, v228
    v229 = stack_addr.i64 ss27+8
    store.i64 notrap v227, v229
    jump block38

block38:
    nop
    v230 = stack_addr.i64 ss26
    v231 = stack_addr.i64 ss27
    v232 = load.i64 notrap v231
    v233 = stack_addr.i64 ss27+8
    v234 = load.i64 notrap v233
    nop
    call fn29(v230, v232, v234)
    jump block39

block39:
    nop
    v235 = stack_addr.i64 ss25
    v236 = stack_addr.i64 ss26
    nop
    call fn30(v235, v236)
    jump block40

block40:
    nop
    v237 = stack_addr.i64 ss24
    v238 = stack_addr.i64 ss25
    nop
    call fn31(v237, v238)
    jump block41

block41:
    nop
    v239 = stack_addr.i64 ss23
    v240 = stack_addr.i64 ss24
    v241 = stack_addr.i64 ss22
    v242 = load.i64 notrap v241
    v243 = stack_addr.i64 ss22+8
    v244 = load.i64 notrap v243
    nop
    call fn32(v239, v240, v242, v244)
    jump block42

block42:
    nop
    nop
    v247 = load.i64 notrap aligned readonly v271+24
    v248 = stack_addr.i64 ss23
    nop
    call_indirect sig34, v247(v269, v248)
    jump block43

block43:
    nop
    v249 = iconst.i64 0
    v250 = stack_addr.i64 ss0
    store.i64 notrap v249, v250
    v251 = stack_addr.i64 ss0
    v252 = load.i64 notrap v251
    return v252

block44(v253: i64):
    nop
    jump block4(v253, v267, v269, v271)

block45:
    nop
    v254 = stack_addr.i64 ss0
    v255 = load.i64 notrap v254
    return v255

block46(v256: i64) cold:
    nop
    call fn33(v256)
    trap user1

block47 cold:
    nop
    v257 = stack_addr.i64 ss9
    try_call fn34(v257), sig36, block50(v94, v280, v282), [ tag0: block76(exn0) ]

block76(v258: i64) cold:
    nop
    call fn35()
    trap user1

block48(v259: i8, v280: i8, v282: i64) cold:
    nop
    brif.i8 v259, block47, block50(v94, v280, v282)

block49 cold:
    nop
    v260 = stack_addr.i64 ss8
    try_call fn36(v260), sig38, block52(v279, v281), [ tag0: block78(exn0) ]

block78(v261: i64) cold:
    nop
    call fn37()
    trap user1

block50(v262: i8, v279: i8, v281: i64) cold:
    nop
    brif.i8 v262, block49, block52(v279, v281)

block51 cold:
    nop
    v263 = stack_addr.i64 ss7
    try_call fn38(v263), sig40, block46(v277), [ tag0: block80(exn0) ]

block80(v264: i64) cold:
    nop
    call fn39()
    trap user1

block52(v265: i8, v277: i64) cold:
    nop
    brif.i8 v265, block51, block46(v277)
}
"

/-- The GOT-declared `sret` callee of the vtable-site function. Its signature is the declared one;
the body stores the argument through the `sret` pointer. -/
def srcS : String := "function %_RNxC10serde_core11Hp7uFPr4pJE(i64 sret, i64) system_v {
block0(v0: i64, v1: i64):
    store notrap aligned v1, v0
    return
}
"

/-- `lean-link`'s first Stock route. -/
def lower : ProductionLowering := Stock.MemorySinkExt.lowerValidated

/-- The callees and data objects of `_RNxC4toml12H3aIpUwLG79T` outside the program, at outside-code addresses. -/
def outsideSyms : List (String × Nat) := [
    ("c_Ldata132", 0x100000),
    ("c_Ldata133", 0x100040),
    ("c_Ldata134", 0x100080),
    ("_RNxC4toml12H33a80mHdtsj", 0x1000c0),
    ("_RNxC4toml12HfpciWSTobpl", 0x100100),
    ("_RNxC4toml12Hb3Hdm2BsiHy", 0x100140),
    ("_RNxC4toml12H9cGRmKLY4JS", 0x100180),
    ("_RNxC4toml12H1GvBPtBRYZY", 0x1001c0),
    ("_RNxC4toml12H1nofZt6HE0T", 0x100200),
    ("memcpy", 0x100240),
    ("_RNxC4toml12HjHYCJmCK4B7", 0x100280),
    ("_RNxC4toml12HjiKBW8D45gQ", 0x1002c0),
    ("_RNxC4toml12H3SXvXJWPxUp", 0x100300),
    ("_RNxC4toml12HbNplun0jt5v", 0x100340),
    ("_RNxC4toml12H9wlH7wbHhnp", 0x100380),
    ("_RNxC4toml12H5CBAnzRRPZp", 0x1003c0),
    ("_RNxC4toml12HaO7KVmyDQNW", 0x100400),
    ("_RNxC4toml12H5xWFa7tOaZV", 0x100440),
    ("_RNxC4toml12Ham7uXG6cCKR", 0x100480),
    ("_RNxC4toml12HjGzJUiKEXCD", 0x1004c0),
    ("_RNxC4toml12HebzLc3YzCLA", 0x100500),
    ("_RNxC4toml12HjK9NAveAOIT", 0x100540),
    ("_RNxC11toml_parser12H2wB6GoetCjG", 0x100580),
    ("_RNxC11toml_parser12Hf8kKoWwrbUB", 0x1005c0),
    ("_RNxC4toml12HkXkEmn2jWQf", 0x100600),
    ("_RNxC4toml12HhbBepeUuFHB", 0x100640),
    ("_RNxC4toml12HiH2NdChIXsp", 0x100680),
    ("_RNxC4toml12H4ltlCc3orqz", 0x1006c0),
    ("_RNxC4toml12HfHyvvgmhaHo", 0x100700),
    ("_Unwind_Resume", 0x100740),
    ("_RNxC4toml12HkVHeodXMmkZ", 0x100780),
    ("_RNvNtCsazjiGSRkgVH_4core9panicking16panic_in_cleanup", 0x1007c0),
    ("_RNxC4toml12H8PWWiEpbUkA", 0x100800),
    ("_RNxC4toml12HkMjg9NTCdWU", 0x100840)]

def spec : LinkSpec :=
  ({ funcs := [{ clif := srcS, ra := "{}" }, { clif := srcG, ra := "{}" }], names := [], sizes := [],
     outside := outsideSyms, symNames := [], R := 0x1000000 } : LinkSpec).placedProductionWith lower true

def file0 : ByteArray :=
  placeholder spec.R spec.size (spec.addrs.map fun p => (BinCheck.symName p.1, p.2))

def input : SemanticStackBound.CompilerInput := SemanticCompilerWith.input lower spec true
def res : Res := spec.input0.resultsProductionWith lower true

/-- The prepared code of `_RNxC4toml12H3aIpUwLG79T` has `blr` sites through a register no GOT load defines (the
vtable calls), passing in x0, x1. -/
def vtableSitesN : Nat :=
  (input.results.filterMap fun row => match row.2 with
    | .error _ => none
    | .ok a => if row.1.name == "_RNxC4toml12H3aIpUwLG79T" then some a else none).foldl (fun n a =>
      n + (a.vcp.blocks.toList.flatMap fun vb => vb.insts.toList.filter fun i => match i with
        | .call info => match info.dest with
          | .reg (.vreg t _) => (E2E.gotOf a.vcp t).isNone && info.uses.map (·.2) == [.x 0, .x 1]
          | _ => false
        | _ => false).length) 0

def checks : Bool :=
  vtableSitesN == 2 && !SemanticStackBound.okBTS input && SemanticStackBound.okBTSR input &&
    (TypedStockShared.stockFails spec res).any (fun e => e.1 == "_RNxC4toml12H3aIpUwLG79T" && e.2.contains "callRegs/blrRegs") &&
    (TypedStockShared.stockFailsR spec res).isEmpty &&
    (SemanticCompilerWith.attemptT lower spec file0).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide -- witness: native_decide

theorem parts : vtableSitesN = 2 ∧ SemanticStackBound.okBTS input = false ∧
    SemanticStackBound.okBTSR input = true ∧
    (∃ e ∈ TypedStockShared.stockFails spec res, e.1 = "_RNxC4toml12H3aIpUwLG79T" ∧ "callRegs/blrRegs" ∈ e.2) ∧
    ∃ file, SemanticCompilerWith.attemptT lower spec file0 = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.any_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨hv, hb⟩, hr⟩, ⟨e, he, hn, hc⟩⟩, -⟩, ha⟩ := h
  refine ⟨hv, hb, hr, ⟨e, he, hn, hc⟩, ?_⟩
  cases r : SemanticCompilerWith.attemptT lower spec file0 with
  | error m => rw [r] at ha; cases ha
  | ok file => exact ⟨file, rfl⟩

/-- **`attemptT_correct` applies to the real vtable-site function**: every run of it, through its
vtable `blr`s, its GOT calls and its `bl`s, is refined by the executable's. -/
theorem correct_applies : ∃ file g,
    SemanticCompilerWith.attemptT lower spec file0 = .ok file ∧
    (prog input).func? "_RNxC4toml12H3aIpUwLG79T" = some g ∧
    ∀ (B : BaseEnv), BaseOk (sys input B) → HooksSim input B →
    ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls input input.results) g →
    ∀ (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State},
    (imageOf file).Intact r →
    OutsideCall input (BinCheck.roByte input spec.data) g
      (SemanticStackBound.stackFn input g) r args cs.mem →
    ClifRun input B g r args cs →
    TrapsExplicit (Clif.linkEnvN (prog input) B.env M) (prog input).bare cs →
    ExecBytes.ExecRefinesT (art input g).fb (art input g).base (xreg 30 r) (step input B file) r
      (RelocAtWithResults input input.results) (Clif.runLoop B.env (prog input) (M + 1) cs) := by
  obtain ⟨-, -, -, -, ⟨file, hf⟩⟩ := parts
  have hs : ((prog input).func? "_RNxC4toml12H3aIpUwLG79T").isSome = true := by native_decide -- witness: native_decide
  obtain ⟨g, eg⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨file, g, hf, eg, fun B hB hH hc M r args cs hX ho hr htr =>
    SemanticCompilerWith.attemptT_correct hf B hB hH eg hc M hX ho hr htr⟩

end E2E.CallRegsR4RealWitness
