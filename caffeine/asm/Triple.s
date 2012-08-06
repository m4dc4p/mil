.data
	.align 4
.globl _Main_lvl_closure
_Main_lvl_closure:
	.long	_base_GHCziNum_Szh_static_info
	.long	0
.data
	.align 4
.globl _Main_a_closure
_Main_a_closure:
	.long	_Main_a_info
.text
	.align 4,0x90
	.long	65539
	.long	0
	.long	15
.globl _Main_a_info
_Main_a_info:
	movl $_Main_lvl_closure+1,%esi
	jmp *(%ebp)
.section .data
	.align 4
.globl _Main_a1_srt
_Main_a1_srt:
	.long	_base_GHCziTopHandler_a7_closure
.data
	.align 4
.globl _Main_a1_closure
_Main_a1_closure:
	.long	_Main_a1_info
	.long	0
.text
	.align 4,0x90
	.long	_Main_a1_srt-(_Main_a1_info)+0
	.long	65539
	.long	0
	.long	65551
.globl _Main_a1_info
_Main_a1_info:
	leal -4(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcyE
	movl $_Main_a_closure+1,-4(%ebp)
	addl $-4,%ebp
	jmp _base_GHCziTopHandler_a7_info
.LcyE:
	movl $_Main_a1_closure,%esi
	jmp *-4(%ebx)
.data
	.align 4
.globl _Main_a2_closure
_Main_a2_closure:
	.long	_base_GHCziBase_Izh_static_info
	.long	0
.data
	.align 4
.globl _Main_main_closure
_Main_main_closure:
	.long	_Main_main_info
.text
	.align 4,0x90
	.long	65539
	.long	0
	.long	15
.globl _Main_main_info
_Main_main_info:
	jmp _Main_a_info
.section .data
	.align 4
.globl _Main_zdf1_srt
_Main_zdf1_srt:
	.long	_base_GHCziShow_showListzuzu_closure
.data
	.align 4
.globl _Main_zdf1_closure
_Main_zdf1_closure:
	.long	_Main_zdf1_info
	.long	0
.text
	.align 4,0x90
	.long	2
	.long	19
_sxk_info:
	leal -24(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .Lczr
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 12(%esi),%eax
	movl %eax,-12(%ebp)
	movl $_stg_INTLIKE_closure+217,-16(%ebp)
	movl $_stg_ap_pp_info,-20(%ebp)
	movl 8(%esi),%eax
	movl %eax,-24(%ebp)
	addl $-24,%ebp
	jmp _base_GHCziShow_showsPrec_info
.Lczr:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	1
	.long	17
_sxm_info:
	leal -16(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LczG
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 8(%esi),%eax
	movl %eax,-12(%ebp)
	movl $_base_GHCziBase_zi_closure+3,%esi
	movl $_base_GHCziShow_showSpace_closure+1,-16(%ebp)
	addl $-16,%ebp
	jmp _stg_ap_pp_fast
.LczG:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	2
	.long	19
_sxe_info:
	leal -24(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LczV
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 12(%esi),%eax
	movl %eax,-12(%ebp)
	movl $_stg_INTLIKE_closure+217,-16(%ebp)
	movl $_stg_ap_pp_info,-20(%ebp)
	movl 8(%esi),%eax
	movl %eax,-24(%ebp)
	addl $-24,%ebp
	jmp _base_GHCziShow_showsPrec_info
.LczV:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	2
	.long	19
_sxo_info:
	leal -16(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcAb
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 12(%esi),%eax
	movl %eax,-12(%ebp)
	movl 8(%esi),%eax
	movl %eax,-16(%ebp)
	movl $_base_GHCziBase_zi_closure+3,%esi
	addl $-16,%ebp
	jmp _stg_ap_pp_fast
.LcAb:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	1
	.long	17
_sxq_info:
	leal -16(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcAq
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 8(%esi),%eax
	movl %eax,-12(%ebp)
	movl $_base_GHCziBase_zi_closure+3,%esi
	movl $_base_GHCziShow_showSpace_closure+1,-16(%ebp)
	addl $-16,%ebp
	jmp _stg_ap_pp_fast
.LcAq:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	2
	.long	19
_sx8_info:
	leal -24(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcAF
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 12(%esi),%eax
	movl %eax,-12(%ebp)
	movl $_stg_INTLIKE_closure+217,-16(%ebp)
	movl $_stg_ap_pp_info,-20(%ebp)
	movl 8(%esi),%eax
	movl %eax,-24(%ebp)
	addl $-24,%ebp
	jmp _base_GHCziShow_showsPrec_info
.LcAF:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	2
	.long	19
_sxs_info:
	leal -16(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcAV
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 12(%esi),%eax
	movl %eax,-12(%ebp)
	movl 8(%esi),%eax
	movl %eax,-16(%ebp)
	movl $_base_GHCziBase_zi_closure+3,%esi
	addl $-16,%ebp
	jmp _stg_ap_pp_fast
.LcAV:
	jmp *-8(%ebx)
.section .rodata
	.align 4
_cB5_str:
	.byte	84
	.byte	114
	.byte	105
	.byte	112
	.byte	108
	.byte	101
	.byte	32
	.byte	0
.text
	.align 4,0x90
	.long	0
	.long	16
_sx0_info:
	leal -12(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcBd
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl $_cB5_str,-12(%ebp)
	addl $-12,%ebp
	jmp _base_GHCziBase_unpackCStringzh_info
.LcBd:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	1
	.long	17
_sx2_info:
	leal -12(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcBq
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 8(%esi),%eax
	movl %eax,-12(%ebp)
	movl $_base_GHCziShow_showString_closure+2,%esi
	addl $-12,%ebp
	jmp _stg_ap_p_fast
.LcBq:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	2
	.long	19
_sxu_info:
	leal -16(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcBF
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 12(%esi),%eax
	movl %eax,-12(%ebp)
	movl 8(%esi),%eax
	movl %eax,-16(%ebp)
	movl $_base_GHCziBase_zi_closure+3,%esi
	addl $-16,%ebp
	jmp _stg_ap_pp_fast
.LcBF:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	1
	.long	34
_swY_info:
	movl %esi,(%ebp)
	jmp _base_GHCziShow_showParen_info
.text
	.align 4,0x90
	.long	4
	.long	34
_sz1_info:
	addl $140,%edi
	cmpl 92(%ebx),%edi
	ja .LcCd
	movl $_sxk_info,-136(%edi)
	movl 4(%ebp),%eax
	movl %eax,-128(%edi)
	movl 11(%esi),%eax
	movl %eax,-124(%edi)
	movl $_sxm_info,-120(%edi)
	leal -136(%edi),%eax
	movl %eax,-112(%edi)
	movl $_sxe_info,-108(%edi)
	movl 8(%ebp),%eax
	movl %eax,-100(%edi)
	movl 7(%esi),%eax
	movl %eax,-96(%edi)
	movl $_sxo_info,-92(%edi)
	leal -108(%edi),%eax
	movl %eax,-84(%edi)
	leal -120(%edi),%eax
	movl %eax,-80(%edi)
	movl $_sxq_info,-76(%edi)
	leal -92(%edi),%eax
	movl %eax,-68(%edi)
	movl $_sx8_info,-64(%edi)
	movl 16(%ebp),%eax
	movl %eax,-56(%edi)
	movl 3(%esi),%eax
	movl %eax,-52(%edi)
	movl $_sxs_info,-48(%edi)
	leal -64(%edi),%eax
	movl %eax,-40(%edi)
	leal -76(%edi),%eax
	movl %eax,-36(%edi)
	movl $_sx0_info,-32(%edi)
	movl $_sx2_info,-24(%edi)
	leal -32(%edi),%eax
	movl %eax,-16(%edi)
	movl $_sxu_info,-12(%edi)
	leal -24(%edi),%eax
	movl %eax,-4(%edi)
	leal -48(%edi),%eax
	movl %eax,(%edi)
	leal -12(%edi),%eax
	movl %eax,16(%ebp)
	movl $_stg_INTLIKE_closure+217,8(%ebp)
	movl 12(%ebp),%eax
	movl %eax,4(%ebp)
	movl $_stg_ap_pp_info,(%ebp)
	movl $_base_GHCziBase_zdf1_closure,-4(%ebp)
	movl $_swY_info,12(%ebp)
	addl $-4,%ebp
	jmp _base_GHCziBase_zgze_info
.LcCd:
	movl $140,112(%ebx)
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	131084
	.long	3
	.long	9
_sxw_info:
	leal -16(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcCI
	movl 10(%esi),%eax
	movl %eax,-8(%ebp)
	movl 6(%esi),%eax
	movl %eax,-4(%ebp)
	movl 4(%ebp),%eax
	movl 2(%esi),%ecx
	movl %ecx,4(%ebp)
	movl %eax,%esi
	movl $_sz1_info,-12(%ebp)
	addl $-12,%ebp
	testl $3,%esi
	jne _sz1_info
	jmp *(%esi)
.LcCI:
	jmp *-4(%ebx)
.text
	.align 4,0x90
	.long	65541
	.long	1
	.long	10
_sxC_info:
	leal -4(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcCZ
	movl 3(%esi),%esi
	movl $_Main_a2_closure+1,-4(%ebp)
	addl $-4,%ebp
	jmp _sxw_info
.LcCZ:
	jmp *-4(%ebx)
.text
	.align 4,0x90
	.long	_Main_zdf1_srt-(_sxL_info)+0
	.long	131084
	.long	1
	.long	65546
_sxL_info:
	leal -4(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcDc
	movl 2(%esi),%eax
	movl %eax,-4(%ebp)
	addl $-4,%ebp
	jmp _base_GHCziShow_showListzuzu_info
.LcDc:
	jmp *-4(%ebx)
.text
	.align 4,0x90
	.long	1
	.long	17
_sxP_info:
	leal -12(%ebp),%eax
	cmpl 84(%ebx),%eax
	jb .LcDq
	movl $_stg_upd_frame_info,-8(%ebp)
	movl %esi,-4(%ebp)
	movl 8(%esi),%eax
	movl %eax,-12(%ebp)
	addl $-12,%ebp
	jmp _base_GHCziShow_zddmshow_info
.LcDq:
	jmp *-8(%ebx)
.text
	.align 4,0x90
	.long	_Main_zdf1_srt-(_Main_zdf1_info)+0
	.long	196628
	.long	0
	.long	65551
.globl _Main_zdf1_info
_Main_zdf1_info:
	addl $60,%edi
	cmpl 92(%ebx),%edi
	ja .LcDI
	movl $_sxw_info,-56(%edi)
	movl (%ebp),%eax
	movl %eax,-52(%edi)
	movl 4(%ebp),%eax
	movl %eax,-48(%edi)
	movl 8(%ebp),%eax
	movl %eax,-44(%edi)
	movl $_sxC_info,-40(%edi)
	leal -54(%edi),%eax
	movl %eax,-36(%edi)
	movl $_sxL_info,-32(%edi)
	leal -39(%edi),%eax
	movl %eax,-28(%edi)
	movl $_base_GHCziShow_ZCDShow_con_info,-24(%edi)
	leal -54(%edi),%eax
	movl %eax,-20(%edi)
	leal -8(%edi),%eax
	movl %eax,-16(%edi)
	leal -30(%edi),%eax
	movl %eax,-12(%edi)
	movl $_sxP_info,-8(%edi)
	leal -23(%edi),%eax
	movl %eax,(%edi)
	leal -23(%edi),%esi
	addl $12,%ebp
	jmp *(%ebp)
.LcDI:
	movl $60,112(%ebx)
	movl $_Main_zdf1_closure,%esi
	jmp *-4(%ebx)
.section .data
	.align 4
.globl _ZCMain_main_srt
_ZCMain_main_srt:
	.long	_base_GHCziTopHandler_a7_closure
.data
	.align 4
.globl _ZCMain_main_closure
_ZCMain_main_closure:
	.long	_ZCMain_main_info
	.long	0
.text
	.align 4,0x90
	.long	_ZCMain_main_srt-(_ZCMain_main_info)+0
	.long	65539
	.long	0
	.long	65551
.globl _ZCMain_main_info
_ZCMain_main_info:
	jmp _Main_a1_info
.data
	.align 4
.globl _Main_Triple_closure
_Main_Triple_closure:
	.long	_Main_Triple_info
.text
	.align 4,0x90
	.long	196628
	.long	0
	.long	15
.globl _Main_Triple_info
_Main_Triple_info:
	addl $16,%edi
	cmpl 92(%ebx),%edi
	ja .LcEn
	movl $_Main_Triple_con_info,-12(%edi)
	movl (%ebp),%eax
	movl %eax,-8(%edi)
	movl 4(%ebp),%eax
	movl %eax,-4(%edi)
	movl 8(%ebp),%eax
	movl %eax,(%edi)
	leal -11(%edi),%esi
	addl $12,%ebp
	jmp *(%ebp)
.LcEn:
	movl $16,112(%ebx)
	movl $_Main_Triple_closure,%esi
	jmp *-4(%ebx)
.section .rodata
	.align 4
_cEy_str:
	.byte	109
	.byte	97
	.byte	105
	.byte	110
	.byte	58
	.byte	77
	.byte	97
	.byte	105
	.byte	110
	.byte	46
	.byte	84
	.byte	114
	.byte	105
	.byte	112
	.byte	108
	.byte	101
	.byte	0
.text
	.align 4,0x90
	.long	_cEy_str-(_Main_Triple_con_info)+0
	.long	3
	.long	1
.globl _Main_Triple_con_info
_Main_Triple_con_info:
	incl %esi
	jmp *(%ebp)
.section .rodata
	.align 4
_cEH_str:
	.byte	109
	.byte	97
	.byte	105
	.byte	110
	.byte	58
	.byte	77
	.byte	97
	.byte	105
	.byte	110
	.byte	46
	.byte	84
	.byte	114
	.byte	105
	.byte	112
	.byte	108
	.byte	101
	.byte	0
.text
	.align 4,0x90
	.long	_cEH_str-(_Main_Triple_static_info)+0
	.long	3
	.long	7
.globl _Main_Triple_static_info
_Main_Triple_static_info:
	incl %esi
	jmp *(%ebp)
.data
	.align 4
__module_registered:
	.long	0
.text
	.align 4,0x90
.globl ___stginit_Main_
___stginit_Main_:
	cmpl $0,__module_registered
	jne .LcEW
.LcEX:
	movl $1,__module_registered
	addl $-4,%ebp
	movl $___stginit_base_Prelude_,(%ebp)
	addl $-4,%ebp
	movl $___stginit_base_GHCziTopHandler_,(%ebp)
.LcEW:
	addl $4,%ebp
	jmp *-4(%ebp)
.text
	.align 4,0x90
.globl ___stginit_Main
___stginit_Main:
	jmp ___stginit_Main_
.text
	.align 4,0x90
.globl ___stginit_ZCMain
___stginit_ZCMain:
	addl $4,%ebp
	jmp *-4(%ebp)
.ident "GHC 6.8.3"
