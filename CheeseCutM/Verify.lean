module

public import CheeseCutM

/-!
# Axiom Verification Audit for `CheeseCutM`

Prints the Lean 4 kernel axioms used by every single public `theorem` and `lemma` in
`CheeseCutM` (164/164 = 100% coverage across all modules). A clean audit must show ONLY
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — NEVER `sorryAx`,
`Lean.ofReduceBool`, `Lean.trustCompiler`, or any custom axiom.
-/

-- Core natural-number counting (CoreCount.lean — 22 public declarations)
#print axioms CheeseCutM.Core.rsum_succ
#print axioms CheeseCutM.Core.rsum_congr
#print axioms CheeseCutM.Core.rsum_add
#print axioms CheeseCutM.Core.rsum_split
#print axioms CheeseCutM.Core.rsum_window
#print axioms CheeseCutM.Core.rsum_up
#print axioms CheeseCutM.Core.rsum_down
#print axioms CheeseCutM.Core.layerCount_eq_rsum_M
#print axioms CheeseCutM.Core.layerCount_alg_end
#print axioms CheeseCutM.Core.layerCount_alg_mid
#print axioms CheeseCutM.Core.layerCount_closed
#print axioms CheeseCutM.Core.pair_count
#print axioms CheeseCutM.Core.tripleT_eq
#print axioms CheeseCutM.Core.tripleX_eq
#print axioms CheeseCutM.Core.tripleY_eq
#print axioms CheeseCutM.Core.G_four
#print axioms CheeseCutM.Core.G_le
#print axioms CheeseCutM.Core.G_eq
#print axioms CheeseCutM.Core.b1_inv
#print axioms CheeseCutM.Core.b2_inv
#print axioms CheeseCutM.Core.b3_inv
#print axioms CheeseCutM.Core.order_cases

-- Real-geometry definitions, symmetries, and Bárány–Frankl lower bound (Defs.lean — 30 public declarations)
#print axioms CheeseCutM.F_small_values
#print axioms CheeseCutM.T2_nat
#print axioms CheeseCutM.four_mul_T2
#print axioms CheeseCutM.T2_sub_two
#print axioms CheeseCutM.D_eq_Tstar
#print axioms CheeseCutM.F_le_diag
#print axioms CheeseCutM.isNormal_iff
#print axioms CheeseCutM.mem_cells
#print axioms CheeseCutM.mem_cutSet
#print axioms CheeseCutM.card_cells
#print axioms CheeseCutM.cutCount_le_cube
#print axioms CheeseCutM.bddAbove_counts
#print axioms CheeseCutM.cuts_iff_range
#print axioms CheeseCutM.meets_iff_nonneg
#print axioms CheeseCutM.normal_pos
#print axioms CheeseCutM.isNormal_of_pos_sum
#print axioms CheeseCutM.cutCount_eq_of_maps
#print axioms CheeseCutM.cutCount_flip1
#print axioms CheeseCutM.cutCount_flip2
#print axioms CheeseCutM.cutCount_flip3
#print axioms CheeseCutM.cutCount_swap13
#print axioms CheeseCutM.cutCount_swap23
#print axioms CheeseCutM.cutCount_swap12
#print axioms CheeseCutM.cutCount_scale
#print axioms CheeseCutM.cutCount_neg
#print axioms CheeseCutM.cutCount_mirror
#print axioms CheeseCutM.wlog_ordered_nonneg
#print axioms CheeseCutM.gCount_eq_core
#print axioms CheeseCutM.barany_frankl_lower_bound
#print axioms CheeseCutM.F_le_maxCutCount

-- Foundation: diagonal lines, Lemma T, Theorem U, Corollary U2, Reduction R (Phase4.lean — 16 public declarations)
#print axioms CheeseCutM.card_starts
#print axioms CheeseCutM.lines_bound
#print axioms CheeseCutM.cutCount_le_starts
#print axioms CheeseCutM.mem_triNat_iff
#print axioms CheeseCutM.tri_eq_triNat
#print axioms CheeseCutM.tri_lb
#print axioms CheeseCutM.tri_lb_sym
#print axioms CheeseCutM.lemmaT_le
#print axioms CheeseCutM.column_bound
#print axioms CheeseCutM.exists_central
#print axioms CheeseCutM.rad_pos
#print axioms CheeseCutM.rad_sq
#print axioms CheeseCutM.u2_sorted_cone
#print axioms CheeseCutM.theoremU_bound
#print axioms CheeseCutM.perturb_strict_ordered
#print axioms CheeseCutM.reduction_R

-- Lemma P, Corollary P1, and Lemma C (Pairing.lean — 25 public declarations)
#print axioms CheeseCutM.rowCard_eq_pos
#print axioms CheeseCutM.rowCard_eq_zero
#print axioms CheeseCutM.sum_rowCard_le_Delta
#print axioms CheeseCutM.Lval_le_cap
#print axioms CheeseCutM.tent_sum
#print axioms CheeseCutM.rowCard_pair_ge
#print axioms CheeseCutM.lemma_P_pairing_bound
#print axioms CheeseCutM.Gval_of_full
#print axioms CheeseCutM.cor_P1_full
#print axioms CheeseCutM.cor_P1_full_of_lt
#print axioms CheeseCutM.cor_P1_full_mono
#print axioms CheeseCutM.cor_P1_not_full
#print axioms CheeseCutM.cor_P1_quad_bound
#print axioms CheeseCutM.alpha_add_beta1
#print axioms CheeseCutM.alpha_add_beta2
#print axioms CheeseCutM.alpha_add_beta3
#print axioms CheeseCutM.x_ordered
#print axioms CheeseCutM.G1_le_pair
#print axioms CheeseCutM.G2_le_pair
#print axioms CheeseCutM.G3_le_pair
#print axioms CheeseCutM.G1_le_B1
#print axioms CheeseCutM.G2_le_B2
#print axioms CheeseCutM.G3_le_B3
#print axioms CheeseCutM.lemma_P_sum_B
#print axioms CheeseCutM.lemma_C_coupling

-- Lemma H and Proposition V (VertexPrinciple.lean — 12 public declarations)
#print axioms CheeseCutM.exists_vertex_dominated
#print axioms CheeseCutM.lemma_H_vertex_principle
#print axioms CheeseCutM.KForm_nonDegen
#print axioms CheeseCutM.inK_iff_KForm
#print axioms CheeseCutM.eval_hpForm0
#print axioms CheeseCutM.eval_hpForm1
#print axioms CheeseCutM.eval_hpForm2
#print axioms CheeseCutM.hpForm_iff_le_Lval
#print axioms CheeseCutM.arrLines_nonDegen
#print axioms CheeseCutM.arrLines_sides
#print axioms CheeseCutM.arrVal_mono
#print axioms CheeseCutM.prop_V_arr_verify_sound

-- Theorem A for n ≥ 700 (TheoremA.lean — 5 public declarations)
#print axioms CheeseCutM.identity_A0
#print axioms CheeseCutM.estimate_e5_alg
#print axioms CheeseCutM.concave_quad_min
#print axioms CheeseCutM.theorem_A_ge_700
#print axioms CheeseCutM.theorem_A_upper_bound_ge_700

-- Headline Theorem M (Main.lean — 5 public declarations)
#print axioms CheeseCutM.maxCutCount_eq_of_bounds
#print axioms CheeseCutM.theoremM_ge_700
#print axioms CheeseCutM.maxCutCount_eq_F_ge_700
#print axioms CheeseCutM.barany_frankl_plus_two_refuted_ge_700
#print axioms CheeseCutM.theoremM_all_n

-- Small-n closure, 2D law, arithmetic planes, and 4D n=3 surprise (SmallNAndDim.lean — 49 public declarations)
#print axioms CheeseCutM.cutCount_one_witness
#print axioms CheeseCutM.maxCutCount_one
#print axioms CheeseCutM.maxCutCount_one_ne_F
#print axioms CheeseCutM.cutCount_two_le_seven
#print axioms CheeseCutM.cutCount_two_witness
#print axioms CheeseCutM.maxCutCount_two
#print axioms CheeseCutM.maxCutCount_two_ne_F
#print axioms CheeseCutM.cutCount_two_unperturbed_central
#print axioms CheeseCutM.cutCount_three_le_nineteen
#print axioms CheeseCutM.cutCount_three_ahsme_bisector
#print axioms CheeseCutM.maxCutCount_three
#print axioms CheeseCutM.cutCount_four_le_thirtyfive
#print axioms CheeseCutM.maxCutCount_four
#print axioms CheeseCutM.F_even
#print axioms CheeseCutM.F_odd
#print axioms CheeseCutM.F_first_diff_even
#print axioms CheeseCutM.F_first_diff_odd
#print axioms CheeseCutM.F_second_diff_odd_center
#print axioms CheeseCutM.F_second_diff_even_center
#print axioms CheeseCutM.F_second_diff_int
#print axioms CheeseCutM.D_even
#print axioms CheeseCutM.D_odd
#print axioms CheeseCutM.D_closed_quarter
#print axioms CheeseCutM.mem_cutSet2D
#print axioms CheeseCutM.meets2D_iff_nonneg
#print axioms CheeseCutM.cutCount2D_le
#print axioms CheeseCutM.cutCount2D_witness
#print axioms CheeseCutM.maxCutCount2D_eq
#print axioms CheeseCutM.stdArithPlaneZ_iff_andresVoxel
#print axioms CheeseCutM.cutSet_subset_stdArithPlaneZ
#print axioms CheeseCutM.cutSet_eq_stdArithPlaneZ_half
#print axioms CheeseCutM.mem_cells4D
#print axioms CheeseCutM.card_cells4D
#print axioms CheeseCutM.meets4D_iff_nonneg
#print axioms CheeseCutM.cutCount4D_diag_three_max
#print axioms CheeseCutM.cutCount4D_bf_three_max
#print axioms CheeseCutM.cutCount4D_tilted_surprise_three
#print axioms CheeseCutM.perturb_strict_ordered_ne
#print axioms CheeseCutM.reduction_R_general
#print axioms CheeseCutM.checkCertN_sound
#print axioms CheeseCutM.cutCount_le_F_3_to_32
#print axioms CheeseCutM.cutCount_le_F_3_to_15
#print axioms CheeseCutM.maxCutCount_eq_F_3_to_32
#print axioms CheeseCutM.maxCutCount_five_and_six
#print axioms CheeseCutM.maxCutCount_ten
#print axioms CheeseCutM.theoremU_bound_all_ge_2
#print axioms CheeseCutM.theoremM_all_n_from_arr_33_699
#print axioms CheeseCutM.stdArithPlane_card_le_F_uncond
#print axioms CheeseCutM.F_eq_mDiag_add_sub_three
