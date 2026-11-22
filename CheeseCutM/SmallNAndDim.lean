module

public import CheeseCutM.Main

import Mathlib.Tactic

/-!
# Small-`n` Sharpness, Pure-Kernel `3 ≤ n ≤ 32` Closure, 2D Law, Arithmetic Planes, and 4D Surprise

Strengthens the `CheeseCutM` formalization across dimensions `d = 2, 3, 4` and small box sizes:
* **Boundary exceptions & small-`n` exact values in `ℝ³`:**
  - `maxCutCount_one` (`m(1) = 1 ≠ F(1) = 0`) and `maxCutCount_two` (`m(2) = 7 ≠ F(2) = 6`),
    together with `cutCount_two_unperturbed_central` (`x + y + z = 3` cuts only `6` open cubes).
  - `maxCutCount_three` (`m(3) = 19 = F(3)`) and `cutCount_three_ahsme_bisector` (`x + y + z = 9/2`
    cuts `19` open cubes, matching 1995 AHSME Problem 30).
  - `maxCutCount_four` (`m(4) = 35 = F(4)`), proved unconditionally over `ℝ` via Bárány–Frankl's
    corner-chain deficit argument on `lines_bound`.
* **Pure-kernel 2D Farkas-BSP verifier & unconditional `3 ≤ n ≤ 32` closure:**
  - `perturb_strict_ordered_ne`, `reduction_R_general`, and `checkCertN_sound` discharge all
    `5 ≤ n ≤ 32` in Lean 4's pure kernel (`decide` on exact `ℕ` Farkas-BSP trees, zero
    `native_decide`, zero external C code), proving `cutCount_le_F_3_to_32`, `cutCount_le_F_3_to_15`
    (completely eliminating the `h_small_3_15` hypothesis of `Main.theoremM_all_n`),
    `maxCutCount_eq_F_3_to_32`, `maxCutCount_five_and_six`, `maxCutCount_ten` (`m(10) = 230`,
    resolving Bárány–Frankl's printed *"unknown"*), `theoremU_bound_all_ge_2` (`∀ n ≥ 2`), and
    `theoremM_all_n_from_arr_33_699`.
* **Parity, alternating `(6, 3)` second differences, linear tilt gain, and deficit identities:**
  - `F_even`, `F_odd`, `F_first_diff_even`, `F_first_diff_odd`, `F_second_diff_odd_center`,
    `F_second_diff_even_center`, `F_second_diff_int`, `D_even`, `D_odd`, `D_closed_quarter`, and
    `F_eq_mDiag_add_sub_three` (`F(n) = m_diag(n) + (n - 3)` for every `n ≥ 3`).
* **Exact 2D cheese-cut theorem over `ℝ²`:**
  - `maxCutCount2D_eq` (`m₂(n) = 2n - 1` for every `n ≥ 1`).
* **Reveillès–Andres standard arithmetic plane equivalence (`Andres 2003, Props. 3 & 5(b)`):**
  - `stdArithPlaneZ_iff_andresVoxel`, `cutSet_subset_stdArithPlaneZ`,
    `cutSet_eq_stdArithPlaneZ_half`, and `stdArithPlane_card_le_F_uncond`.
* **4D real-geometry definitions (`Fin 4 → ℝ`) & the `n = 3` surprise (`63 > 62 > 61`):**
  - `meets4D_iff_nonneg`, `cutCount4D_diag_three_max` (`≤ 61` for all `t`, `61` at `t = 13/2`,
    `51` at unperturbed `t = 6`), `cutCount4D_bf_three_max` (`≤ 62` for all `t`, `62` at `t = 25/2`
    and `t = 29/2`), and `cutCount4D_tilted_surprise_three` (`x₁ + 2x₂ + 2x₃ + 2x₄ = 21/2` cuts
    `63` open 4-cubes, so `63 ≤ maxCutCount4D 3`).
-/

@[expose] public section

namespace CheeseCutM

open Finset

noncomputable section

/-! ### Section 1: Small-`n` exact `maxCutCount` theorems (`n = 1, 2, 3, 4`) and boundary traps -/

/-- The plane `x = 1/2` cuts the unique open unit cube `(0, 0, 0)` of `[0, 1]³`. -/
theorem cutCount_one_witness : cutCount 1 1 0 0 (1 / 2) = 1 := by
  apply le_antisymm
  · simpa using cutCount_le_cube 1 1 0 0 (1 / 2)
  · unfold cutCount
    have hmem : ((0, 0, 0) : Cell) ∈ cutSet 1 1 0 0 (1 / 2) := by
      rw [mem_cutSet]
      refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩, ?_⟩
      refine ⟨(1 / 2, 1 / 2, 1 / 2), Set.mem_inter ?_ ?_⟩
      · simp [plane]
      · simp [OpenCube]; norm_num
    exact Finset.card_pos.2 ⟨(0, 0, 0), hmem⟩

/-- **`m(1) = 1` (`maxCutCount_one`):** Unconditional exact value at `n = 1`. -/
theorem maxCutCount_one : maxCutCount 1 = 1 := by
  apply maxCutCount_eq_of_bounds
  · intro a b c t _
    simpa using cutCount_le_cube 1 a b c t
  · refine ⟨1, 0, 0, 1 / 2, ?_, cutCount_one_witness⟩
    rw [isNormal_iff]; norm_num

/-- Sharpness of `n ≥ 3` at `n = 1`: `maxCutCount 1 = 1 ≠ 0 = F 1`. -/
theorem maxCutCount_one_ne_F : maxCutCount 1 ≠ F 1 := by
  rw [maxCutCount_one]
  have hF : F 1 = 0 := by decide
  omega

/-- Every nonzero real plane cuts at most `7` open unit cubes of `[0, 2]³`. -/
theorem cutCount_two_le_seven (a b c t : ℝ) (hv : IsNormal a b c) :
    cutCount 2 a b c t ≤ 7 := by
  obtain ⟨a', b', c', t', ha, hab, hbc, hsum, heq⟩ := wlog_ordered_nonneg 2 a b c t hv
  rw [heq]
  have hle := cutCount_le_starts (n := 2) (a := a') (b := b') (c := c') (t := t')
    ha (by linarith) (by linarith) (by linarith)
  have hst : (starts 2).card + 1 ≤ 8 := card_starts 1
  omega

/-- The perturbed central diagonal plane `x + y + z = 7/2` cuts `7` open unit cubes of `[0, 2]³`. -/
theorem cutCount_two_witness : cutCount 2 1 1 1 (7 / 2) = 7 := by
  unfold cutCount
  have h0 : ((0, 0, 0) : Cell) ∈ cells 2 :=
    mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
  have hset : cutSet 2 1 1 1 (7 / 2) = (cells 2).erase (0, 0, 0) := by
    ext z
    rw [mem_cutSet, Finset.mem_erase]
    constructor
    · rintro ⟨hz, hm⟩
      have hm' := (meets_iff_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) z).1 hm
      refine ⟨?_, hz⟩
      intro hz0
      subst hz0
      simp [dot] at hm'
      linarith
    · rintro ⟨hne, hz⟩
      refine ⟨hz, (meets_iff_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) z).2 ?_⟩
      have hzc := mem_cells.1 hz
      have hpos : 1 ≤ z.1 + z.2.1 + z.2.2 := by
        by_contra h0'
        apply hne
        exact Prod.ext (by dsimp only; omega)
          (Prod.ext (by dsimp only; omega) (by dsimp only; omega))
      have hhi : z.1 + z.2.1 + z.2.2 ≤ 3 := by omega
      have hpos_r : (1 : ℝ) ≤ (z.1 : ℝ) + z.2.1 + z.2.2 := by exact_mod_cast hpos
      have hhi_r : (z.1 : ℝ) + z.2.1 + z.2.2 ≤ 3 := by exact_mod_cast hhi
      unfold dot
      constructor <;> linarith
  rw [hset, Finset.card_erase_of_mem h0, card_cells 2]
  norm_num

/-- **`m(2) = 7` (`maxCutCount_two`):** Unconditional exact value at `n = 2`. -/
theorem maxCutCount_two : maxCutCount 2 = 7 := by
  apply maxCutCount_eq_of_bounds cutCount_two_le_seven
  refine ⟨1, 1, 1, 7 / 2, ?_, cutCount_two_witness⟩
  rw [isNormal_iff]; norm_num

/-- Sharpness of `n ≥ 3` at `n = 2`: `maxCutCount 2 = 7 ≠ 6 = F 2`. -/
theorem maxCutCount_two_ne_F : maxCutCount 2 ≠ F 2 := by
  rw [maxCutCount_two]
  have hF : F 2 = 6 := by decide
  omega

/-- **Unperturbed central-plane trap at `n = 2`:** The exact central plane `x + y + z = 3`
passes through the interior grid vertex `(1, 1, 1)` and cuts only `6` open unit cubes (missing
both `(0, 0, 0)` and `(1, 1, 1)`), strictly fewer than `m(2) = 7`. -/
theorem cutCount_two_unperturbed_central : cutCount 2 1 1 1 3 = 6 := by
  unfold cutCount
  have h0 : ((0, 0, 0) : Cell) ∈ cells 2 :=
    mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
  have h1 : ((1, 1, 1) : Cell) ∈ (cells 2).erase (0, 0, 0) := by
    rw [Finset.mem_erase]
    exact ⟨by decide, mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩⟩
  have hset : cutSet 2 1 1 1 3 = ((cells 2).erase (0, 0, 0)).erase (1, 1, 1) := by
    ext z
    rw [mem_cutSet, Finset.mem_erase, Finset.mem_erase]
    constructor
    · rintro ⟨hz, hm⟩
      have hm' := (meets_iff_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) z).1 hm
      unfold dot at hm'
      refine ⟨?_, ?_, hz⟩
      · intro heq; subst heq; norm_num at hm'
      · intro heq; subst heq; norm_num at hm'
    · rintro ⟨hne1, hne0, hz⟩
      refine ⟨hz, (meets_iff_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) z).2 ?_⟩
      have hzc := mem_cells.1 hz
      have hlo : 1 ≤ z.1 + z.2.1 + z.2.2 := by
        by_contra hc; apply hne0
        exact Prod.ext (by dsimp only; omega)
          (Prod.ext (by dsimp only; omega) (by dsimp only; omega))
      have hhi : z.1 + z.2.1 + z.2.2 ≤ 2 := by
        by_contra hc; apply hne1
        exact Prod.ext (by dsimp only; omega)
          (Prod.ext (by dsimp only; omega) (by dsimp only; omega))
      have hlo_r : (1 : ℝ) ≤ (z.1 : ℝ) + z.2.1 + z.2.2 := by exact_mod_cast hlo
      have hhi_r : (z.1 : ℝ) + z.2.1 + z.2.2 ≤ 2 := by exact_mod_cast hhi
      unfold dot
      constructor <;> linarith
  rw [hset, Finset.card_erase_of_mem h1, Finset.card_erase_of_mem h0, card_cells 2]
  norm_num

/-- Every nonzero real plane cuts at most `19 = F(3)` open unit cubes of `[0, 3]³`. -/
theorem cutCount_three_le_nineteen (a b c t : ℝ) (hv : IsNormal a b c) :
    cutCount 3 a b c t ≤ 19 := by
  obtain ⟨a', b', c', t', ha, hab, hbc, hsum, heq⟩ := wlog_ordered_nonneg 3 a b c t hv
  rw [heq]
  have hle := cutCount_le_starts (n := 3) (a := a') (b := b') (c := c') (t := t')
    ha (by linarith) (by linarith) (by linarith)
  have hst : (starts 3).card + 8 ≤ 27 := card_starts 2
  omega

/-- **1995 AHSME Problem 30 plane:** The perpendicular bisector `x + y + z = 9/2` of the main
diagonal of `[0, 3]³` cuts exactly `19` open unit cubes. -/
theorem cutCount_three_ahsme_bisector : cutCount 3 1 1 1 (9 / 2) = 19 := by
  unfold cutCount
  have hsub : (cells 3).filter (fun z : Cell => 2 ≤ sigma z ∧ sigma z ≤ 4) =
      cutSet 3 1 1 1 (9 / 2) := by
    ext z
    rw [Finset.mem_filter, mem_cutSet]
    refine and_congr_right fun _ => ?_
    rw [meets_iff_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    unfold dot sigma
    constructor
    · rintro ⟨h1, h2⟩
      have h1r : (2 : ℝ) ≤ (z.1 : ℝ) + z.2.1 + z.2.2 := by exact_mod_cast h1
      have h2r : (z.1 : ℝ) + z.2.1 + z.2.2 ≤ 4 := by exact_mod_cast h2
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      have hlt5 : z.1 + z.2.1 + z.2.2 ≤ 4 := by
        by_contra hc
        have h5 : (5 : ℝ) ≤ (z.1 : ℝ) + z.2.1 + z.2.2 := by
          exact_mod_cast (show 5 ≤ z.1 + z.2.1 + z.2.2 by omega)
        linarith
      have hge2 : 2 ≤ z.1 + z.2.1 + z.2.2 := by
        by_contra hc
        have h1' : (z.1 : ℝ) + z.2.1 + z.2.2 ≤ 1 := by
          exact_mod_cast (show z.1 + z.2.1 + z.2.2 ≤ 1 by omega)
        linarith
      exact ⟨hge2, hlt5⟩
  rw [← hsub]
  decide

/-- **`m(3) = 19 = F(3)` (`maxCutCount_three`):** Unconditional exact value at `n = 3`. -/
theorem maxCutCount_three : maxCutCount 3 = 19 ∧ maxCutCount 3 = F 3 := by
  have hF3 : F 3 = 19 := by decide
  have hm : maxCutCount 3 = F 3 := by
    apply maxCutCount_eq_of_bounds
    · intro a b c t hv
      rw [hF3]
      exact cutCount_three_le_nineteen a b c t hv
    · exact barany_frankl_lower_bound 3 (by omega)
  exact ⟨hm.trans hF3, hm⟩

/-- **Unconditional upper bound at `n = 4` (Bárány–Frankl Lemma 7):**
Every nonzero real plane cuts at most `35 = F(4)` open unit cubes of `[0, 4]³`. -/
theorem cutCount_four_le_thirtyfive (a b c t : ℝ) (hv : IsNormal a b c) :
    cutCount 4 a b c t ≤ 35 := by
  obtain ⟨a', b', c', t', ha, hab, hbc, hsum, heq⟩ := wlog_ordered_nonneg 4 a b c t hv
  rw [heq]
  have hb : 0 ≤ b' := by linarith
  have hc : 0 ≤ c' := by linarith
  have hW : 0 < a' + b' + c' := by linarith
  have hlines := lines_bound (n := 4) (t := t') ha hb hc hW
  have hst : (starts 4).card + 27 ≤ 64 := card_starts 3
  have mA1 : t' ≤ 3 * (b' + c') → 1 ≤ (missA1 4 a' b' c' t').card := fun ht => by
    refine Finset.card_pos.2 ⟨(0, 3, 3), Finset.mem_filter.2 ?_⟩
    refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩,
      rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
    unfold dot; push_cast; linarith
  have mA2 : t' ≤ 3 * (a' + c') → 1 ≤ (missA2 4 a' b' c' t').card := fun ht => by
    refine Finset.card_pos.2 ⟨(3, 0, 3), Finset.mem_filter.2 ?_⟩
    refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩,
      rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
    unfold dot; push_cast; linarith
  have mB1 : 3 * a' + 1 ≤ t' → 1 ≤ (missB1 4 a' b' c' t').card := fun ht => by
    refine Finset.card_pos.2 ⟨(3, 0, 0), Finset.mem_filter.2 ?_⟩
    refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩,
      Or.inl rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
    unfold dot; push_cast; linarith
  have mB2 : 3 * b' + 1 ≤ t' → 1 ≤ (missB2 4 a' b' c' t').card := fun ht => by
    refine Finset.card_pos.2 ⟨(0, 3, 0), Finset.mem_filter.2 ?_⟩
    refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩,
      Or.inl rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
    unfold dot; push_cast; linarith
  have hmiss2 : 2 ≤ (missA1 4 a' b' c' t').card + (missA2 4 a' b' c' t').card +
      (missB1 4 a' b' c' t').card + (missB2 4 a' b' c' t').card := by
    by_cases hb3 : b' ≤ 1 / 3
    · have h1 : 1 ≤ (missA1 4 a' b' c' t').card + (missB1 4 a' b' c' t').card := by
        by_cases ht1 : t' ≤ 3 * (b' + c')
        · have := mA1 ht1; omega
        · have := mB1 (by linarith); omega
      have h2 : 1 ≤ (missA2 4 a' b' c' t').card + (missB2 4 a' b' c' t').card := by
        by_cases ht2 : t' ≤ 3 * (a' + c')
        · have := mA2 ht2; omega
        · have := mB2 (by linarith); omega
      omega
    · push Not at hb3
      have hc3 : 1 / 3 < c' := by linarith
      by_cases ht_lo : t' ≤ 3 * (a' + c')
      · have h1 := mA1 (by linarith)
        have h2 := mA2 ht_lo
        omega
      · by_cases ht_hi : 3 * b' + 1 ≤ t'
        · have h1 := mB1 (by linarith)
          have h2 := mB2 ht_hi
          omega
        · have h1 := mA1 (by linarith)
          have h2 := mB1 (by linarith)
          omega
  omega

/-- **`m(4) = 35 = F(4)` (`maxCutCount_four`):** Unconditional exact value at `n = 4`. -/
theorem maxCutCount_four : maxCutCount 4 = 35 ∧ maxCutCount 4 = F 4 := by
  have hF4 : F 4 = 35 := by decide
  have hm : maxCutCount 4 = F 4 := by
    apply maxCutCount_eq_of_bounds
    · intro a b c t hv
      rw [hF4]
      exact cutCount_four_le_thirtyfive a b c t hv
    · exact barany_frankl_lower_bound 4 (by omega)
  exact ⟨hm.trans hF4, hm⟩

/-! ### Section 2: Parity closed forms, alternating `(6, 3)` second differences, and `D(n)` -/

/-- Even-`n` closed form of `F`: for `k ≥ 2`, `F(2k) = 9k² + 2k - 5 = 9(2k)²/4 + (2k) - 5`. -/
theorem F_even (k : ℕ) (hk : 2 ≤ k) : F (2 * k) = 9 * k ^ 2 + 2 * k - 5 := by
  unfold F
  have h17 : 17 ≤ 9 * (2 * k) ^ 2 + 4 * (2 * k) := by nlinarith
  have h5 : 5 ≤ 9 * k ^ 2 + 2 * k := by nlinarith
  have hnum : 9 * (2 * k) ^ 2 + 4 * (2 * k) - 17 = 4 * (9 * k ^ 2 + 2 * k - 5) + 3 := by
    zify [h17, h5]; ring
  rw [hnum]; omega

/-- Odd-`n` closed form of `F`: for `k ≥ 1`, `F(2k + 1) = 9k² + 11k - 1`. -/
theorem F_odd (k : ℕ) (hk : 1 ≤ k) : F (2 * k + 1) = 9 * k ^ 2 + 11 * k - 1 := by
  unfold F
  have h17 : 17 ≤ 9 * (2 * k + 1) ^ 2 + 4 * (2 * k + 1) := by nlinarith
  have h1 : 1 ≤ 9 * k ^ 2 + 11 * k := by nlinarith
  have hnum : 9 * (2 * k + 1) ^ 2 + 4 * (2 * k + 1) - 17 = 4 * (9 * k ^ 2 + 11 * k - 1) := by
    zify [h17, h1]; ring
  rw [hnum]; omega

/-- First difference of `F` from `2k` to `2k + 1` (`k ≥ 2`): `F(2k + 1) - F(2k) = 9k + 4`. -/
theorem F_first_diff_even (k : ℕ) (hk : 2 ≤ k) :
    F (2 * k + 1) - F (2 * k) = 9 * k + 4 := by
  rw [F_odd k (by omega), F_even k hk]
  have h5 : 5 ≤ 9 * k ^ 2 + 2 * k := by nlinarith
  have h1 : 1 ≤ 9 * k ^ 2 + 11 * k := by nlinarith
  have hle : 9 * k ^ 2 + 2 * k - 5 ≤ 9 * k ^ 2 + 11 * k - 1 := by omega
  zify [h5, h1, hle]; ring

/-- First difference of `F` from `2k + 1` to `2k + 2` (`k ≥ 1`): `F(2k + 2) - F(2k + 1) = 9k + 7`. -/
theorem F_first_diff_odd (k : ℕ) (hk : 1 ≤ k) :
    F (2 * k + 2) - F (2 * k + 1) = 9 * k + 7 := by
  have heq : 2 * k + 2 = 2 * (k + 1) := by ring
  rw [heq, F_even (k + 1) (by omega), F_odd k hk]
  have h5 : 5 ≤ 9 * (k + 1) ^ 2 + 2 * (k + 1) := by nlinarith
  have h1 : 1 ≤ 9 * k ^ 2 + 11 * k := by nlinarith
  have hle : 9 * k ^ 2 + 11 * k - 1 ≤ 9 * (k + 1) ^ 2 + 2 * (k + 1) - 5 := by
    zify [h5, h1]; nlinarith
  zify [h5, h1, hle]; ring

/-- Subtraction-free second difference of `F` centered at odd `2k + 1` (`k ≥ 1`):
`F(2k + 2) + F(2k) = 2 F(2k + 1) + 3`. -/
theorem F_second_diff_odd_center (k : ℕ) (hk : 1 ≤ k) :
    F (2 * k + 2) + F (2 * k) = 2 * F (2 * k + 1) + 3 := by
  by_cases hk1 : k = 1
  · subst hk1; decide
  · have hk2 : 2 ≤ k := by omega
    have heq : 2 * k + 2 = 2 * (k + 1) := by ring
    rw [heq, F_even (k + 1) (by omega), F_even k hk2, F_odd k hk]
    have h1 : 5 ≤ 9 * (k + 1) ^ 2 + 2 * (k + 1) := by nlinarith
    have h2 : 5 ≤ 9 * k ^ 2 + 2 * k := by nlinarith
    have h3 : 1 ≤ 9 * k ^ 2 + 11 * k := by nlinarith
    zify [h1, h2, h3]; ring

/-- Subtraction-free second difference of `F` centered at even `2k` (`k ≥ 2`):
`F(2k + 1) + F(2k - 1) = 2 F(2k) + 6`. -/
theorem F_second_diff_even_center (k : ℕ) (hk : 2 ≤ k) :
    F (2 * k + 1) + F (2 * k - 1) = 2 * F (2 * k) + 6 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
  have hodd_prev : 2 * (m + 2) - 1 = 2 * (m + 1) + 1 := by omega
  rw [hodd_prev, F_odd (m + 2) (by omega), F_odd (m + 1) (by omega), F_even (m + 2) (by omega)]
  have h1 : 1 ≤ 9 * (m + 2) ^ 2 + 11 * (m + 2) := by nlinarith
  have h2 : 1 ≤ 9 * (m + 1) ^ 2 + 11 * (m + 1) := by nlinarith
  have h3 : 5 ≤ 9 * (m + 2) ^ 2 + 2 * (m + 2) := by nlinarith
  zify [h1, h2, h3]; ring

/-- Period-2 alternating second-difference law of `F` over `ℤ`: for all `n ≥ 2`,
`F(n + 2) - 2 F(n + 1) + F(n) = 3` if `n` is even and `6` if `n` is odd (summing to `9`,
matching the quadratic leading term `(9/4) n²`). -/
theorem F_second_diff_int (n : ℕ) (hn : 2 ≤ n) :
    (F (n + 2) : ℤ) - 2 * (F (n + 1) : ℤ) + (F n : ℤ) = if Even n then 3 else 6 := by
  by_cases hev : Even n
  · rw [ite_eq_left hev]
    rcases hev with ⟨k, rfl⟩
    have hk : 1 ≤ k := by omega
    have h := F_second_diff_odd_center k hk
    have h1 : k + k = 2 * k := by ring
    rw [h1] at *
    have hz : ((F (2 * k + 2) + F (2 * k) : ℕ) : ℤ) = ((2 * F (2 * k + 1) + 3 : ℕ) : ℤ) :=
      congrArg Nat.cast h
    push_cast at hz
    linarith
  · rw [ite_eq_right hev]
    rcases Nat.not_even_iff_odd.1 hev with ⟨k, rfl⟩
    have hk : 1 ≤ k := by omega
    have h := F_second_diff_even_center (k + 1) (by omega)
    have e1 : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    have e2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e3 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e1, e2, e3] at h
    have hz : ((F (2 * k + 1 + 2) + F (2 * k + 1) : ℕ) : ℤ) =
        ((2 * F (2 * k + 1 + 1) + 6 : ℕ) : ℤ) := congrArg Nat.cast h
    push_cast at hz
    linarith

/-- Subtraction-safe even-`n` closed form of the diagonal-line deficit:
`D(2k) = 3k² + 6 - 8k` for all `k ≥ 2`. -/
theorem D_even (k : ℕ) (hk : 2 ≤ k) : D (2 * k) = 3 * k ^ 2 + 6 - 8 * k := by
  by_cases hk2 : k = 2
  · subst hk2; decide
  · unfold D
    rw [F_even k hk]
    have hk3 : 3 ≤ k := by omega
    have h1 : 3 * (2 * k) ≤ 3 * (2 * k) ^ 2 := by nlinarith
    have h2 : 5 ≤ 9 * k ^ 2 + 2 * k := by nlinarith
    have h3 : 9 * k ^ 2 + 2 * k - 5 ≤ 3 * (2 * k) ^ 2 - 3 * (2 * k) + 1 := by
      zify [h1, h2]; nlinarith
    have h4 : 8 * k ≤ 3 * k ^ 2 + 6 := by nlinarith
    zify [h1, h2, h3, h4]; ring

/-- Subtraction-safe odd-`n` closed form of the diagonal-line deficit:
`D(2k + 1) = 3k² + 2 - 5k` for all `k ≥ 1`. -/
theorem D_odd (k : ℕ) (hk : 1 ≤ k) : D (2 * k + 1) = 3 * k ^ 2 + 2 - 5 * k := by
  by_cases hk1 : k = 1
  · subst hk1; decide
  · unfold D
    rw [F_odd k hk]
    have hk2 : 2 ≤ k := by omega
    have h1 : 3 * (2 * k + 1) ≤ 3 * (2 * k + 1) ^ 2 := by nlinarith
    have h2 : 1 ≤ 9 * k ^ 2 + 11 * k := by nlinarith
    have h3 : 9 * k ^ 2 + 11 * k - 1 ≤ 3 * (2 * k + 1) ^ 2 - 3 * (2 * k + 1) + 1 := by
      zify [h1, h2]; nlinarith
    have h4 : 5 * k ≤ 3 * k ^ 2 + 2 := by nlinarith
    zify [h1, h2, h3, h4]; ring

/-- Single parity-free closed form for `D(n)` (`n ≥ 3`), matching OEIS `A397990(n - 3)`:
`D(n) = ⌊(3(n - 3)² + 2(n - 3) + 3)/4⌋ = ⌈(n - 3)(n - 2)/2 + (n - 3)²/4⌉`. -/
theorem D_closed_quarter (n : ℕ) (hn : 3 ≤ n) :
    D n = (3 * (n - 3) ^ 2 + 2 * (n - 3) + 3) / 4 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : 2 ≤ k := by omega
    by_cases hk2 : k = 2
    · subst hk2; decide
    · have h2k : k + k = 2 * k := by ring
      rw [h2k, D_even k hk]
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 3 := ⟨k - 3, by omega⟩
      have heq1 : 2 * (m + 3) - 3 = 2 * m + 3 := by omega
      rw [heq1]
      have hsub : 8 * (m + 3) ≤ 3 * (m + 3) ^ 2 + 6 := by nlinarith
      have hnum : 3 * (2 * m + 3) ^ 2 + 2 * (2 * m + 3) + 3 =
          4 * (3 * (m + 3) ^ 2 + 6 - 8 * (m + 3)) := by zify [hsub]; ring
      rw [hnum]; omega
  · have hk : 1 ≤ k := by omega
    by_cases hk1 : k = 1
    · subst hk1; decide
    · rw [D_odd k hk]
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
      have heq1 : 2 * (m + 2) + 1 - 3 = 2 * m + 2 := by omega
      rw [heq1]
      have hsub : 5 * (m + 2) ≤ 3 * (m + 2) ^ 2 + 2 := by nlinarith
      have hnum : 3 * (2 * m + 2) ^ 2 + 2 * (2 * m + 2) + 3 =
          4 * (3 * (m + 2) ^ 2 + 2 - 5 * (m + 2)) + 3 := by zify [hsub]; ring
      rw [hnum]; omega

/-! ### Section 3: Exact 2D Cheese-Cut Theorem (`m₂(n) = 2n - 1` for all `n ≥ 1`) -/

/-- A planar grid cell indexed by its lower-left corner `(i, j) ∈ ℕ²`. -/
abbrev Cell2D := ℕ × ℕ

/-- The line `a x + b y = t` in `ℝ²`. -/
def line2D (a b t : ℝ) : Set (ℝ × ℝ) := {p | a * p.1 + b * p.2 = t}

/-- The open unit square `(i, i + 1) × (j, j + 1)` in `ℝ²`. -/
def OpenSquare (z : Cell2D) : Set (ℝ × ℝ) :=
  {p | (z.1 : ℝ) < p.1 ∧ p.1 < (z.1 : ℝ) + 1 ∧ (z.2 : ℝ) < p.2 ∧ p.2 < (z.2 : ℝ) + 1}

/-- The line `a x + b y = t` cuts (meets the interior of) `OpenSquare z`. -/
def Meets2D (a b t : ℝ) (z : Cell2D) : Prop := (line2D a b t ∩ OpenSquare z).Nonempty

/-- `(a, b)` is a nonzero normal vector in `ℝ²`. -/
def IsNormal2D (a b : ℝ) : Prop := (a, b) ≠ (0, 0)

/-- The `n²` unit square indices `{0, …, n - 1}²`. -/
def cells2D (n : ℕ) : Finset Cell2D := range n ×ˢ range n

open Classical in
/-- The finite set of open unit squares in `[0, n]²` cut by `a x + b y = t`. -/
def cutSet2D (n : ℕ) (a b t : ℝ) : Finset Cell2D := (cells2D n).filter (Meets2D a b t)

/-- Number of open unit squares of `[0, n]²` cut by `a x + b y = t`. -/
def cutCount2D (n : ℕ) (a b t : ℝ) : ℕ := (cutSet2D n a b t).card

/-- `m₂(n)`: maximum number of open unit squares of `[0, n]²` cut by a single line. -/
def maxCutCount2D (n : ℕ) : ℕ :=
  sSup {k | ∃ a b t : ℝ, IsNormal2D a b ∧ cutCount2D n a b t = k}

lemma mem_cutSet2D {n : ℕ} {a b t : ℝ} {z : Cell2D} :
    z ∈ cutSet2D n a b t ↔ z ∈ cells2D n ∧ Meets2D a b t z := by
  unfold cutSet2D
  classical exact Finset.mem_filter

/-- Open-interval characterization of `Meets2D` for nonnegative normals `a, b ≥ 0` with `a + b > 0`. -/
theorem meets2D_iff_nonneg {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hW : 0 < a + b) (z : Cell2D) :
    Meets2D a b t z ↔
      a * (z.1 : ℝ) + b * (z.2 : ℝ) < t ∧ t < a * (z.1 : ℝ) + b * (z.2 : ℝ) + (a + b) := by
  constructor
  · rintro ⟨p, hp, hq⟩
    simp only [line2D, OpenSquare, Set.mem_ofPred_eq] at hp hq
    obtain ⟨x1, x2, y1, y2⟩ := hq
    by_cases ha0 : a = 0
    · have hb0 : 0 < b := by linarith
      subst ha0; constructor <;> nlinarith
    · have ha0' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    let q : ℝ := (t - (a * (z.1 : ℝ) + b * (z.2 : ℝ))) / (a + b)
    have hq0 : 0 < q := div_pos (by linarith) hW
    have hq1 : q < 1 := (div_lt_one hW).2 (by linarith)
    have hqW : q * (a + b) = t - (a * (z.1 : ℝ) + b * (z.2 : ℝ)) :=
      div_mul_cancel₀ _ (ne_of_gt hW)
    refine ⟨((z.1 : ℝ) + q, (z.2 : ℝ) + q), Set.mem_inter ?_ ?_⟩
    · simp only [line2D, Set.mem_ofPred_eq]; linarith
    · simp only [OpenSquare, Set.mem_ofPred_eq]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma cutCount2D_flip1 (n : ℕ) (a b t : ℝ) :
    cutCount2D n a b t = cutCount2D n (-a) b (t - (n : ℝ) * a) := by
  unfold cutCount2D
  apply Finset.card_nbij' (fun z : Cell2D => (n - 1 - z.1, z.2))
    (fun z : Cell2D => (n - 1 - z.1, z.2))
  · intro z hz
    obtain ⟨hzc, p, hp, x1, x2, y1, y2⟩ := mem_cutSet2D.1 (Finset.mem_coe.1 hz)
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
    refine Finset.mem_coe.2 (mem_cutSet2D.2 ⟨?_, ((n : ℝ) - p.1, p.2), ?_, ?_⟩)
    · rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨by dsimp only; omega, hzc.2⟩
    · simp only [line2D, Set.mem_ofPred_eq] at hp ⊢; linarith
    · have hc : ((n - 1 - z.1 : ℕ) : ℝ) + (z.1 : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast (show n - 1 - z.1 + z.1 + 1 = n by omega)
      simp only [OpenSquare, Set.mem_ofPred_eq]; exact ⟨by linarith, by linarith, y1, y2⟩
  · intro z hz
    obtain ⟨hzc, p, hp, x1, x2, y1, y2⟩ := mem_cutSet2D.1 (Finset.mem_coe.1 hz)
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
    refine Finset.mem_coe.2 (mem_cutSet2D.2 ⟨?_, ((n : ℝ) - p.1, p.2), ?_, ?_⟩)
    · rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨by dsimp only; omega, hzc.2⟩
    · simp only [line2D, Set.mem_ofPred_eq] at hp ⊢; linarith
    · have hc : ((n - 1 - z.1 : ℕ) : ℝ) + (z.1 : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast (show n - 1 - z.1 + z.1 + 1 = n by omega)
      simp only [OpenSquare, Set.mem_ofPred_eq]; exact ⟨by linarith, by linarith, y1, y2⟩
  · intro z hz
    have hzc := (mem_cutSet2D.1 (Finset.mem_coe.1 hz)).1
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
    exact Prod.ext (by dsimp only; omega) rfl
  · intro z hz
    have hzc := (mem_cutSet2D.1 (Finset.mem_coe.1 hz)).1
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
    exact Prod.ext (by dsimp only; omega) rfl

private lemma cutCount2D_flip2 (n : ℕ) (a b t : ℝ) :
    cutCount2D n a b t = cutCount2D n a (-b) (t - (n : ℝ) * b) := by
  unfold cutCount2D
  apply Finset.card_nbij' (fun z : Cell2D => (z.1, n - 1 - z.2))
    (fun z : Cell2D => (z.1, n - 1 - z.2))
  · intro z hz
    obtain ⟨hzc, p, hp, x1, x2, y1, y2⟩ := mem_cutSet2D.1 (Finset.mem_coe.1 hz)
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
    refine Finset.mem_coe.2 (mem_cutSet2D.2 ⟨?_, (p.1, (n : ℝ) - p.2), ?_, ?_⟩)
    · rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨hzc.1, by dsimp only; omega⟩
    · simp only [line2D, Set.mem_ofPred_eq] at hp ⊢; linarith
    · have hc : ((n - 1 - z.2 : ℕ) : ℝ) + (z.2 : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast (show n - 1 - z.2 + z.2 + 1 = n by omega)
      simp only [OpenSquare, Set.mem_ofPred_eq]; exact ⟨x1, x2, by linarith, by linarith⟩
  · intro z hz
    obtain ⟨hzc, p, hp, x1, x2, y1, y2⟩ := mem_cutSet2D.1 (Finset.mem_coe.1 hz)
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
    refine Finset.mem_coe.2 (mem_cutSet2D.2 ⟨?_, (p.1, (n : ℝ) - p.2), ?_, ?_⟩)
    · rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨hzc.1, by dsimp only; omega⟩
    · simp only [line2D, Set.mem_ofPred_eq] at hp ⊢; linarith
    · have hc : ((n - 1 - z.2 : ℕ) : ℝ) + (z.2 : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast (show n - 1 - z.2 + z.2 + 1 = n by omega)
      simp only [OpenSquare, Set.mem_ofPred_eq]; exact ⟨x1, x2, by linarith, by linarith⟩
  · intro z hz
    have hzc := (mem_cutSet2D.1 (Finset.mem_coe.1 hz)).1
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
    exact Prod.ext rfl (by dsimp only; omega)
  · intro z hz
    have hzc := (mem_cutSet2D.1 (Finset.mem_coe.1 hz)).1
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
    exact Prod.ext rfl (by dsimp only; omega)

/-- **2D Cheese-Cut Upper Bound:** For every `n ≥ 1`, any nonzero line in `ℝ²` cuts at most
`2n - 1` open unit squares of `[0, n]²`. -/
theorem cutCount2D_le (n : ℕ) (hn : 1 ≤ n) (a b t : ℝ) (hv : IsNormal2D a b) :
    cutCount2D n a b t ≤ 2 * n - 1 := by
  classical
  obtain ⟨t1, e1⟩ : ∃ t1, cutCount2D n a b t = cutCount2D n |a| b t1 := by
    rcases le_total 0 a with h | h
    · exact ⟨t, by rw [abs_of_nonneg h]⟩
    · exact ⟨t - (n : ℝ) * a, by rw [abs_of_nonpos h]; exact cutCount2D_flip1 n a b t⟩
  obtain ⟨t2, e2⟩ : ∃ t2, cutCount2D n |a| b t1 = cutCount2D n |a| |b| t2 := by
    rcases le_total 0 b with h | h
    · exact ⟨t1, by rw [abs_of_nonneg h]⟩
    · exact ⟨t1 - (n : ℝ) * b, by rw [abs_of_nonpos h]; exact cutCount2D_flip2 n |a| b t1⟩
  rw [e1, e2]
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hW : 0 < |a| + |b| := by
    by_contra hle; push Not at hle
    exact hv (Prod.ext (abs_eq_zero.1 (by linarith)) (abs_eq_zero.1 (by linarith)))
  let starts2 : Finset Cell2D := (cells2D n).filter (fun z => z.1 = 0 ∨ z.2 = 0)
  have hstarts_le : starts2.card ≤ 2 * n - 1 := by
    obtain ⟨h, rfl⟩ : ∃ h : ℕ, n = h + 1 := ⟨n - 1, by omega⟩
    have hpart : starts2.card + ((cells2D (h + 1)).filter (fun z => ¬(z.1 = 0 ∨ z.2 = 0))).card =
        (cells2D (h + 1)).card := Finset.card_filter_add_card_filter_not _
    have hinj : (cells2D h).card ≤
        ((cells2D (h + 1)).filter (fun z => ¬(z.1 = 0 ∨ z.2 = 0))).card := by
      apply Finset.card_le_card_of_injOn (fun z : Cell2D => (z.1 + 1, z.2 + 1))
      · intro z hz
        have hzc := Finset.mem_product.1 (Finset.mem_coe.1 hz)
        rw [Finset.mem_range, Finset.mem_range] at hzc
        refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨?_, by dsimp only; omega⟩)
        rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · intro z _ z' _ heq
        simp only [Prod.mk.injEq] at heq; exact Prod.ext (by omega) (by omega)
    have c1 : (cells2D (h + 1)).card = (h + 1) ^ 2 := by
      simp [cells2D, Finset.card_product]; ring
    have c2 : (cells2D h).card = h ^ 2 := by
      simp [cells2D, Finset.card_product]; ring
    have hsq : (h + 1) ^ 2 = h ^ 2 + 2 * h + 1 := by ring
    omega
  refine le_trans ?_ hstarts_le
  unfold cutCount2D
  apply Finset.card_le_card_of_injOn (fun z : Cell2D => (z.1 - min z.1 z.2, z.2 - min z.1 z.2))
  · intro z hz
    have hzc := (mem_cutSet2D.1 (Finset.mem_coe.1 hz)).1
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨?_, by dsimp only; omega⟩)
    rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · intro z hz z' hz' heq
    have hm1 := (meets2D_iff_nonneg ha hb hW z).1 (mem_cutSet2D.1 (Finset.mem_coe.1 hz)).2
    have hm2 := (meets2D_iff_nonneg ha hb hW z').1 (mem_cutSet2D.1 (Finset.mem_coe.1 hz')).2
    simp only [Prod.mk.injEq] at heq
    let m := min z.1 z.2
    let m' := min z'.1 z'.2
    have hz_eq : |a| * (z.1 : ℝ) + |b| * (z.2 : ℝ) =
        |a| * ((z.1 - m : ℕ) : ℝ) + |b| * ((z.2 - m : ℕ) : ℝ) + (m : ℝ) * (|a| + |b|) := by
      rw [Nat.cast_sub (min_le_left _ _), Nat.cast_sub (min_le_right _ _)]; ring
    have hz'_eq : |a| * (z'.1 : ℝ) + |b| * (z'.2 : ℝ) =
        |a| * ((z'.1 - m' : ℕ) : ℝ) + |b| * ((z'.2 - m' : ℕ) : ℝ) + (m' : ℝ) * (|a| + |b|) := by
      rw [Nat.cast_sub (min_le_left _ _), Nat.cast_sub (min_le_right _ _)]; ring
    have heq1 : ((z.1 - m : ℕ) : ℝ) = ((z'.1 - m' : ℕ) : ℝ) := by exact_mod_cast heq.1
    have heq2 : ((z.2 - m : ℕ) : ℝ) = ((z'.2 - m' : ℕ) : ℝ) := by exact_mod_cast heq.2
    have hmeq : m = m' := by
      rcases lt_trichotomy m m' with hlt | h0 | hgt
      · exfalso
        have hl : (m : ℝ) + 1 ≤ (m' : ℝ) := by exact_mod_cast hlt
        nlinarith [mul_nonneg (sub_nonneg.2 hl) hW.le]
      · exact h0
      · exfalso
        have hl : (m' : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hgt
        nlinarith [mul_nonneg (sub_nonneg.2 hl) hW.le]
    have : min z.1 z.2 = min z'.1 z'.2 := hmeq
    exact Prod.ext (by omega) (by omega)

/-- **2D Cheese-Cut Witness:** For every `n ≥ 1`, there exists a nonzero line cutting exactly
`2n - 1` open unit squares of `[0, n]²` (specifically `(n - 1) x + n y = (n - 1) n + 1/2`
for `n ≥ 2`, and `x = 1/2` for `n = 1`). -/
theorem cutCount2D_witness (n : ℕ) (hn : 1 ≤ n) :
    ∃ a b t : ℝ, IsNormal2D a b ∧ cutCount2D n a b t = 2 * n - 1 := by
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨1, 0, 1 / 2, by unfold IsNormal2D; norm_num, ?_⟩
    apply le_antisymm
    · exact cutCount2D_le 1 (by omega) 1 0 (1 / 2) (by unfold IsNormal2D; norm_num)
    · unfold cutCount2D
      refine Finset.card_pos.2 ⟨(0, 0), mem_cutSet2D.2 ⟨?_, ?_⟩⟩
      · simp [cells2D]
      · rw [meets2D_iff_nonneg (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · obtain ⟨h, rfl⟩ : ∃ h : ℕ, n = h + 1 := ⟨n - 1, by omega⟩
    have hh : 1 ≤ h := by omega
    refine ⟨(h : ℝ), (h : ℝ) + 1, ((h * (h + 1) : ℕ) : ℝ) + 1 / 2, ?_, ?_⟩
    · unfold IsNormal2D
      intro hc; simp only [Prod.mk.injEq] at hc
      have : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
      linarith
    · classical
      unfold cutCount2D
      let L1 : Finset Cell2D := (range (h + 1)).image (fun j => (h - j, j))
      let L2 : Finset Cell2D := (range h).image (fun j => (h - 1 - j, j))
      have hdisj : Disjoint L1 L2 := by
        rw [Finset.disjoint_left]
        intro z h1 h2
        obtain ⟨j1, hj1, rfl⟩ := Finset.mem_image.1 h1
        obtain ⟨j2, hj2, heq⟩ := Finset.mem_image.1 h2
        rw [Finset.mem_range] at hj1 hj2
        simp only [Prod.mk.injEq] at heq
        omega
      have hinj1 : Function.Injective (fun j : ℕ => (h - j, j)) := by
        intro j1 j2 heq; simp only [Prod.mk.injEq] at heq; exact heq.2
      have hinj2 : Function.Injective (fun j : ℕ => (h - 1 - j, j)) := by
        intro j1 j2 heq; simp only [Prod.mk.injEq] at heq; exact heq.2
      have hcard1 : L1.card = h + 1 := by rw [Finset.card_image_of_injective _ hinj1, Finset.card_range]
      have hcard2 : L2.card = h := by rw [Finset.card_image_of_injective _ hinj2, Finset.card_range]
      have hset : cutSet2D (h + 1) (h : ℝ) ((h : ℝ) + 1) (((h * (h + 1) : ℕ) : ℝ) + 1 / 2) =
          L1 ∪ L2 := by
        have h0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
        ext z
        rw [mem_cutSet2D, meets2D_iff_nonneg h0 (by linarith) (by linarith), Finset.mem_union]
        have hdot : (h : ℝ) * (z.1 : ℝ) + ((h : ℝ) + 1) * (z.2 : ℝ) =
            ((h * (z.1 + z.2) + z.2 : ℕ) : ℝ) := by push_cast; ring
        rw [hdot]
        constructor
        · rintro ⟨hzc, hlo, hhi⟩
          rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hzc
          have kle : h * (z.1 + z.2) + z.2 ≤ h * (h + 1) := by
            by_contra hc
            have : ((h * (h + 1) : ℕ) : ℝ) + 1 ≤ ((h * (z.1 + z.2) + z.2 : ℕ) : ℝ) := by
              exact_mod_cast (show h * (h + 1) + 1 ≤ h * (z.1 + z.2) + z.2 by omega)
            linarith
          have kge : h * (h - 1) ≤ h * (z.1 + z.2) + z.2 := by
            by_contra hc
            have hsub : h * (h - 1) + 2 * h + 1 = h * (h + 1) + 1 := by
              zify [hh]; ring
            have : ((h * (z.1 + z.2) + z.2 : ℕ) : ℝ) + (2 * (h : ℝ) + 1) ≤
                ((h * (h + 1) : ℕ) : ℝ) := by
              have hnat : h * (z.1 + z.2) + z.2 + (2 * h + 1) ≤ h * (h + 1) := by omega
              exact_mod_cast hnat
            linarith
          have hsum_cases : z.1 + z.2 = h ∨ z.1 + z.2 = h - 1 := by
            rcases (show z.1 + z.2 + 2 ≤ h ∨ z.1 + z.2 = h - 1 ∨ z.1 + z.2 = h ∨
              h + 1 ≤ z.1 + z.2 by omega) with c | c | c | c
            · exfalso
              have h2 : 2 ≤ h := by omega
              have m := Nat.mul_le_mul_left h c
              have e : h * (z.1 + z.2 + 2) = h * (z.1 + z.2) + 2 * h := by ring
              have e2 : h * (h - 1) + h = h * h := by zify [hh]; ring
              nlinarith
            · exact Or.inr c
            · exact Or.inl c
            · exfalso
              have m := Nat.mul_le_mul_left h c
              omega
          rcases hsum_cases with hs | hs
          · exact Or.inl (Finset.mem_image.2 ⟨z.2, Finset.mem_range.2 hzc.2,
              Prod.ext (by omega) rfl⟩)
          · exact Or.inr (Finset.mem_image.2 ⟨z.2, Finset.mem_range.2 (by omega),
              Prod.ext (by omega) rfl⟩)
        · rintro (h1 | h2)
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h1
            rw [Finset.mem_range] at hj
            refine ⟨?_, ?_, ?_⟩
            · rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range]
              exact ⟨by dsimp only; omega, hj⟩
            · have hle : h * (h - j + j) + j ≤ h * (h + 1) := by
                have e : h - j + j = h := by omega
                rw [e]
                have : h * (h + 1) = h * h + h := by ring
                omega
              have hr : ((h * (h - j + j) + j : ℕ) : ℝ) ≤ ((h * (h + 1) : ℕ) : ℝ) := by
                exact_mod_cast hle
              linarith
            · have hge : h * h ≤ h * (h - j + j) + j := by
                have e : h - j + j = h := by omega
                rw [e]; omega
              have heq_mul : ((h * (h + 1) : ℕ) : ℝ) = ((h * h : ℕ) : ℝ) + (h : ℝ) := by
                push_cast; ring
              have hr : ((h * h : ℕ) : ℝ) ≤ ((h * (h - j + j) + j : ℕ) : ℝ) := by
                exact_mod_cast hge
              linarith
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h2
            rw [Finset.mem_range] at hj
            refine ⟨?_, ?_, ?_⟩
            · rw [cells2D, Finset.mem_product, Finset.mem_range, Finset.mem_range]
              exact ⟨by dsimp only; omega, by omega⟩
            · have hle : h * (h - 1 - j + j) + j ≤ h * (h + 1) := by
                have e : h - 1 - j + j = h - 1 := by omega
                rw [e]
                have : h * (h - 1) + h ≤ h * (h + 1) := by zify [hh]; nlinarith
                omega
              have hr : ((h * (h - 1 - j + j) + j : ℕ) : ℝ) ≤ ((h * (h + 1) : ℕ) : ℝ) := by
                exact_mod_cast hle
              linarith
            · have he : h - 1 - j + j = h - 1 := by omega
              rw [he]
              have heq_mul : ((h * (h + 1) : ℕ) : ℝ) = ((h * (h - 1) : ℕ) : ℝ) + 2 * (h : ℝ) := by
                zify [hh]; ring
              have hr : ((h * (h - 1) : ℕ) : ℝ) ≤ ((h * (h - 1) + j : ℕ) : ℝ) := by
                exact_mod_cast (Nat.le_add_right _ _)
              linarith
      rw [hset, Finset.card_union_of_disjoint hdisj, hcard1, hcard2]
      omega

/-- **Exact 2D Cheese-Cut Law (`maxCutCount2D_eq`):**
For every `n ≥ 1`, `maxCutCount2D n = 2n - 1`. -/
theorem maxCutCount2D_eq (n : ℕ) (hn : 1 ≤ n) : maxCutCount2D n = 2 * n - 1 := by
  obtain ⟨a0, b0, t0, hv0, hcnt0⟩ := cutCount2D_witness n hn
  have hne : {k | ∃ a b t : ℝ, IsNormal2D a b ∧ cutCount2D n a b t = k}.Nonempty :=
    ⟨2 * n - 1, a0, b0, t0, hv0, hcnt0⟩
  have hbdd : BddAbove {k | ∃ a b t : ℝ, IsNormal2D a b ∧ cutCount2D n a b t = k} := by
    refine ⟨2 * n - 1, ?_⟩
    rintro k ⟨a, b, t, hv, rfl⟩
    exact cutCount2D_le n hn a b t hv
  apply le_antisymm
  · apply csSup_le hne
    rintro k ⟨a, b, t, hv, rfl⟩
    exact cutCount2D_le n hn a b t hv
  · exact le_csSup hbdd ⟨a0, b0, t0, hv0, hcnt0⟩

/-! ### Section 4: Reveillès–Andres Standard Arithmetic Plane Equivalence -/

/-- Reveillès (1991) analytical standard arithmetic plane of integer normal `(a, b, c) ∈ ℕ³`
and shift `m ∈ ℤ`: `{z ∈ ℕ³ : m ≤ a z₁ + b z₂ + c z₃ < m + (a + b + c)}`. -/
def stdArithPlaneZ (a b c : ℕ) (m : ℤ) (z : Cell) : Prop :=
  m ≤ ((a * z.1 + b * z.2.1 + c * z.2.2 : ℕ) : ℤ) ∧
    ((a * z.1 + b * z.2.1 + c * z.2.2 : ℕ) : ℤ) < m + ((a + b + c : ℕ) : ℤ)

instance instDecidablePredStdArithPlaneZ (a b c : ℕ) (m : ℤ) :
    DecidablePred (stdArithPlaneZ a b c m) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Andres (2003, Propositions 3 & 5(b)) centered-voxel standard arithmetic plane for
Euclidean plane `a X + b Y + c Z = B` (with voxel centers `z + (1/2, 1/2, 1/2)` and `a, b, c ≥ 0`). -/
def andresVoxelPlane (a b c : ℝ) (B : ℝ) (z : Cell) : Prop :=
  B - (a + b + c) / 2 ≤ a * ((z.1 : ℝ) + 1 / 2) + b * ((z.2.1 : ℝ) + 1 / 2) +
    c * ((z.2.2 : ℝ) + 1 / 2) ∧
  a * ((z.1 : ℝ) + 1 / 2) + b * ((z.2.1 : ℝ) + 1 / 2) + c * ((z.2.2 : ℝ) + 1 / 2) <
    B + (a + b + c) / 2

/-- **Equivalence of Reveillès's `S`-window and Andres's centered-voxel standard model:**
At `B = m + (a + b + c)`, `stdArithPlaneZ a b c m z` holds iff `andresVoxelPlane a b c B z` holds. -/
theorem stdArithPlaneZ_iff_andresVoxel (a b c : ℕ) (m : ℤ) (z : Cell) :
    stdArithPlaneZ a b c m z ↔
      andresVoxelPlane (a : ℝ) (b : ℝ) (c : ℝ) ((m : ℝ) + ((a + b + c : ℕ) : ℝ)) z := by
  unfold stdArithPlaneZ andresVoxelPlane
  have hcast : (((a * z.1 + b * z.2.1 + c * z.2.2 : ℕ) : ℤ) : ℝ) =
      (a : ℝ) * (z.1 : ℝ) + (b : ℝ) * (z.2.1 : ℝ) + (c : ℝ) * (z.2.2 : ℝ) := by
    push_cast; ring
  constructor
  · rintro ⟨h1, h2⟩
    have h1r : (m : ℝ) ≤ (((a * z.1 + b * z.2.1 + c * z.2.2 : ℕ) : ℤ) : ℝ) := by exact_mod_cast h1
    have h2r : (((a * z.1 + b * z.2.1 + c * z.2.2 : ℕ) : ℤ) : ℝ) <
        (m : ℝ) + ((a + b + c : ℕ) : ℝ) := by exact_mod_cast h2
    rw [hcast] at h1r h2r
    push_cast at h2r ⊢
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    push_cast at h1 h2
    have h1r : (m : ℝ) ≤ (((a * z.1 + b * z.2.1 + c * z.2.2 : ℕ) : ℤ) : ℝ) := by
      rw [hcast]; linarith
    have h2r : (((a * z.1 + b * z.2.1 + c * z.2.2 : ℕ) : ℤ) : ℝ) <
        ((m + ((a + b + c : ℕ) : ℤ) : ℤ) : ℝ) := by
      rw [hcast]; push_cast; linarith
    exact ⟨by exact_mod_cast h1r, by exact_mod_cast h2r⟩

/-- **Every real offset of an integer normal is contained in a standard arithmetic plane:**
For any nonzero `(a, b, c) ∈ ℕ³` and ANY `t ∈ ℝ`, setting `m = ⌈t⌉ - (a + b + c)`, every cell cut
by `a x + b y + c z = t` lies in `stdArithPlaneZ a b c m`. -/
theorem cutSet_subset_stdArithPlaneZ (n a b c : ℕ) (hS : 0 < a + b + c) (t : ℝ) :
    cutSet n (a : ℝ) (b : ℝ) (c : ℝ) t ⊆
      (cells n).filter (stdArithPlaneZ a b c (⌈t⌉ - ((a + b + c : ℕ) : ℤ))) := by
  have hWr : (0 : ℝ) < (a : ℝ) + (b : ℝ) + (c : ℝ) := by exact_mod_cast hS
  intro z hz
  rw [mem_cutSet, meets_iff_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) (Nat.cast_nonneg c) hWr]
    at hz
  rw [Finset.mem_filter]
  refine ⟨hz.1, ?_⟩
  unfold stdArithPlaneZ
  set V : ℤ := ((a * z.1 + b * z.2.1 + c * z.2.2 : ℕ) : ℤ)
  have hVr : (V : ℝ) = dot (a : ℝ) (b : ℝ) (c : ℝ) z := by
    dsimp [V]; unfold dot; push_cast; ring
  have hlt : V < ⌈t⌉ := by
    by_contra hge
    push Not at hge
    have : (⌈t⌉ : ℝ) ≤ (V : ℝ) := by exact_mod_cast hge
    linarith [Int.le_ceil t, hz.2.1]
  have hge : ⌈t⌉ ≤ V + ((a + b + c : ℕ) : ℤ) := by
    apply Int.ceil_le.2
    rw [Int.cast_add, hVr]
    push_cast
    exact hz.2.2.le
  exact ⟨by omega, by omega⟩

/-- **Every standard arithmetic plane is realized by a half-integer Euclidean slice:**
At `t = m + (a + b + c) - 1/2`, `cutSet n a b c t` equals `(cells n).filter (stdArithPlaneZ a b c m)`
verbatim. -/
theorem cutSet_eq_stdArithPlaneZ_half (n a b c : ℕ) (hS : 0 < a + b + c) (m : ℤ) :
    cutSet n (a : ℝ) (b : ℝ) (c : ℝ) ((m : ℝ) + ((a + b + c : ℕ) : ℝ) - 1 / 2) =
      (cells n).filter (stdArithPlaneZ a b c m) := by
  have hWr : (0 : ℝ) < (a : ℝ) + (b : ℝ) + (c : ℝ) := by exact_mod_cast hS
  ext z
  rw [mem_cutSet, meets_iff_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) (Nat.cast_nonneg c) hWr,
    Finset.mem_filter]
  refine and_congr_right fun _ => ?_
  unfold stdArithPlaneZ
  set V : ℤ := ((a * z.1 + b * z.2.1 + c * z.2.2 : ℕ) : ℤ)
  have hVr : (V : ℝ) = dot (a : ℝ) (b : ℝ) (c : ℝ) z := by
    dsimp [V]; unfold dot; push_cast; ring
  rw [← hVr]
  constructor
  · rintro ⟨h1, h2⟩
    have hm_le : m ≤ V := by
      by_contra hc; push Not at hc
      have : (V : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hc
      push_cast at h2; linarith
    have hV_lt : V < m + ((a + b + c : ℕ) : ℤ) := by
      by_contra hc; push Not at hc
      have : (m : ℝ) + ((a + b + c : ℕ) : ℝ) ≤ (V : ℝ) := by exact_mod_cast hc
      linarith
    exact ⟨hm_le, hV_lt⟩
  · rintro ⟨h1, h2⟩
    have h1r : (m : ℝ) ≤ (V : ℝ) := by exact_mod_cast h1
    have h2r : (V : ℝ) + 1 ≤ (m : ℝ) + ((a + b + c : ℕ) : ℝ) := by
      exact_mod_cast (show V + 1 ≤ m + ((a + b + c : ℕ) : ℤ) by omega)
    push_cast at h2r ⊢
    constructor <;> linarith

/-! ### Section 5: 4D Real Geometry (`Fin 4 → ℝ`) & the `n = 3` Surprise (`63 > 62 > 61`, `ZO02`) -/

/-- A point in `ℝ⁴`. -/
abbrev Pt4D := Fin 4 → ℝ

/-- A 4D grid cell indexed by its lower corner `z : Fin 4 → ℕ`. -/
abbrev Cell4D := Fin 4 → ℕ

/-- Explicit constructor for a 4-vector `Fin 4 → α`. -/
def vec4 {α : Type*} (a b c d : α) : Fin 4 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d

private lemma sum_fin4 (f : Fin 4 → ℝ) :
    (∑ i : Fin 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  have h : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [h]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  ring

/-- The hyperplane `∑ᵢ vᵢ pᵢ = t` in `ℝ⁴`. -/
def hyperplane4D (v : Pt4D) (t : ℝ) : Set Pt4D :=
  {p | (∑ i : Fin 4, v i * p i) = t}

/-- The open unit 4-cube `∏ᵢ (zᵢ, zᵢ + 1)` in `ℝ⁴`. -/
def OpenCube4D (z : Cell4D) : Set Pt4D :=
  {p | ∀ i : Fin 4, (z i : ℝ) < p i ∧ p i < (z i : ℝ) + 1}

/-- The hyperplane `v · x = t` cuts (meets the interior of) `OpenCube4D z`. -/
def Meets4D (v : Pt4D) (t : ℝ) (z : Cell4D) : Prop :=
  (hyperplane4D v t ∩ OpenCube4D z).Nonempty

/-- `v` is a nonzero normal vector in `ℝ⁴`. -/
def IsNormal4D (v : Pt4D) : Prop := v ≠ 0

/-- Embedding of `ℕ × ℕ × ℕ × ℕ` onto `Fin 4 → ℕ`. -/
def tupleToCell4D : (ℕ × ℕ × ℕ × ℕ) ↪ Cell4D where
  toFun q := vec4 q.1 q.2.1 q.2.2.1 q.2.2.2
  inj' := by
    intro q1 q2 heq
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have h2 := congrFun heq 2
    have h3 := congrFun heq 3
    dsimp [vec4] at h0 h1 h2 h3
    exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))

@[simp] private lemma tupleToCell4D_apply (q : ℕ × ℕ × ℕ × ℕ) :
    tupleToCell4D q = vec4 q.1 q.2.1 q.2.2.1 q.2.2.2 := rfl

/-- The `n⁴` open unit 4-cube indices `{0, …, n - 1}⁴` as `Fin 4 → ℕ`. -/
def cells4D (n : ℕ) : Finset Cell4D :=
  (range n ×ˢ range n ×ˢ range n ×ˢ range n).map tupleToCell4D

lemma mem_cells4D {n : ℕ} {z : Cell4D} :
    z ∈ cells4D n ↔ ∀ i : Fin 4, z i < n := by
  unfold cells4D
  rw [Finset.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩ i
    simp only [Finset.mem_product, Finset.mem_range] at hq
    fin_cases i <;> dsimp [tupleToCell4D, vec4] <;> omega
  · intro hz
    refine ⟨(z 0, z 1, z 2, z 3), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨hz 0, hz 1, hz 2, hz 3⟩
    · funext i
      fin_cases i <;> rfl

lemma card_cells4D (n : ℕ) : (cells4D n).card = n ^ 4 := by
  unfold cells4D
  rw [Finset.card_map, Finset.card_product, Finset.card_product, Finset.card_product,
    Finset.card_range]
  ring

open Classical in
/-- Finite set of open unit 4-cubes of `[0, n]⁴` cut by `v · x = t`. -/
def cutSet4D (n : ℕ) (v : Pt4D) (t : ℝ) : Finset Cell4D :=
  (cells4D n).filter (Meets4D v t)

/-- Number of open unit 4-cubes of `[0, n]⁴` cut by `v · x = t`. -/
def cutCount4D (n : ℕ) (v : Pt4D) (t : ℝ) : ℕ := (cutSet4D n v t).card

/-- `N⁴(n)`: maximum number of open unit 4-cubes of `[0, n]⁴` cut by one hyperplane in `ℝ⁴`. -/
def maxCutCount4D (n : ℕ) : ℕ :=
  sSup {k | ∃ (v : Pt4D) (t : ℝ), IsNormal4D v ∧ cutCount4D n v t = k}

/-- **4D Open-Interval Criterion (`meets4D_iff_nonneg`):** For `v ≥ 0` in `ℝ⁴` with `∑ᵢ vᵢ > 0`,
`hyperplane4D v t` meets `OpenCube4D z` iff `∑ᵢ vᵢ zᵢ < t < ∑ᵢ vᵢ zᵢ + ∑ᵢ vᵢ`. -/
theorem meets4D_iff_nonneg {v : Pt4D} {t : ℝ}
    (hv : ∀ i : Fin 4, 0 ≤ v i) (hW : 0 < ∑ i : Fin 4, v i) (z : Cell4D) :
    Meets4D v t z ↔
      (∑ i : Fin 4, v i * (z i : ℝ)) < t ∧
      t < (∑ i : Fin 4, v i * (z i : ℝ)) + ∑ i : Fin 4, v i := by
  have h0 := hv 0; have h1 := hv 1; have h2 := hv 2; have h3 := hv 3
  rw [sum_fin4] at hW
  rw [sum_fin4 (fun i => v i * (z i : ℝ)), sum_fin4 v]
  constructor
  · rintro ⟨p, hp, hq⟩
    simp only [hyperplane4D, OpenCube4D, Set.mem_ofPred_eq, sum_fin4] at hp hq
    have b0 := hq 0; have b1 := hq 1; have b2 := hq 2; have b3 := hq 3
    by_cases hv0 : v 0 = 0
    · by_cases hv1 : v 1 = 0
      · by_cases hv2 : v 2 = 0
        · have hv3 : 0 < v 3 := by linarith
          rw [hv0, hv1, hv2] at hp ⊢; constructor <;> nlinarith
        · have hv2' : 0 < v 2 := lt_of_le_of_ne h2 (Ne.symm hv2)
          rw [hv0, hv1] at hp ⊢; constructor <;> nlinarith
      · have hv1' : 0 < v 1 := lt_of_le_of_ne h1 (Ne.symm hv1)
        rw [hv0] at hp ⊢; constructor <;> nlinarith
    · have hv0' : 0 < v 0 := lt_of_le_of_ne h0 (Ne.symm hv0)
      constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    set S := v 0 + v 1 + v 2 + v 3
    set D := v 0 * (z 0 : ℝ) + v 1 * (z 1 : ℝ) + v 2 * (z 2 : ℝ) + v 3 * (z 3 : ℝ)
    let q : ℝ := (t - D) / S
    have hq0 : 0 < q := div_pos (by linarith) hW
    have hq1 : q < 1 := (div_lt_one hW).2 (by linarith)
    have hqS : q * S = t - D := div_mul_cancel₀ _ (ne_of_gt hW)
    refine ⟨fun i => (z i : ℝ) + q, Set.mem_inter ?_ ?_⟩
    · simp only [hyperplane4D, Set.mem_ofPred_eq, sum_fin4]
      dsimp [S, D] at hqS
      linarith
    · simp only [OpenCube4D, Set.mem_ofPred_eq]
      intro i; exact ⟨by linarith, by linarith⟩

/-- Pure `ℕ` window count in `{0, …, n - 1}⁴` for integer normal `(a, b, c, d)` and shift `m : ℤ`. -/
def win4DCount (n a b c d : ℕ) (m : ℤ) : ℕ :=
  ((range n ×ˢ range n ×ˢ range n ×ˢ range n).filter fun q =>
    m ≤ ((a * q.1 + b * q.2.1 + c * q.2.2.1 + d * q.2.2.2 : ℕ) : ℤ) ∧
    ((a * q.1 + b * q.2.1 + c * q.2.2.1 + d * q.2.2.2 : ℕ) : ℤ) <
      m + ((a + b + c + d : ℕ) : ℤ)).card

private lemma cutCount4D_eq_win4D_half (n a b c d : ℕ) (hS : 0 < a + b + c + d) (m : ℤ) :
    cutCount4D n (vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
      ((m : ℝ) + ((a + b + c + d : ℕ) : ℝ) - 1 / 2) = win4DCount n a b c d m := by
  classical
  have hv : ∀ i : Fin 4, 0 ≤ vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) i := by
    intro i; fin_cases i <;> exact Nat.cast_nonneg _
  have hW : 0 < ∑ i : Fin 4, vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) i := by
    rw [sum_fin4]; dsimp [vec4]; exact_mod_cast hS
  unfold cutCount4D cutSet4D cells4D win4DCount
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  ext q
  rw [Finset.mem_filter, Finset.mem_filter]
  refine and_congr_right fun _ => ?_
  rw [Function.comp_apply, tupleToCell4D_apply, meets4D_iff_nonneg hv hW]
  rw [sum_fin4 (fun i => vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) i * _),
    sum_fin4 (vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))]
  dsimp [vec4]
  set V : ℤ := ((a * q.1 + b * q.2.1 + c * q.2.2.1 + d * q.2.2.2 : ℕ) : ℤ)
  have hVr : (V : ℝ) = (a : ℝ) * (q.1 : ℝ) + (b : ℝ) * (q.2.1 : ℝ) +
      (c : ℝ) * (q.2.2.1 : ℝ) + (d : ℝ) * (q.2.2.2 : ℝ) := by dsimp [V]; push_cast; ring
  rw [← hVr]
  constructor
  · rintro ⟨h1, h2⟩
    have hm_le : m ≤ V := by
      by_contra hc; push Not at hc
      have : (V : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hc
      push_cast at h2; linarith
    have hV_lt : V < m + ((a + b + c + d : ℕ) : ℤ) := by
      by_contra hc; push Not at hc
      have : (m : ℝ) + ((a + b + c + d : ℕ) : ℝ) ≤ (V : ℝ) := by exact_mod_cast hc
      linarith
    exact ⟨hm_le, hV_lt⟩
  · rintro ⟨h1, h2⟩
    have h1r : (m : ℝ) ≤ (V : ℝ) := by exact_mod_cast h1
    have h2r : (V : ℝ) + 1 ≤ (m : ℝ) + ((a + b + c + d : ℕ) : ℝ) := by
      exact_mod_cast (show V + 1 ≤ m + ((a + b + c + d : ℕ) : ℤ) by omega)
    push_cast at h2r ⊢
    constructor <;> linarith

private lemma cutCount4D_le_win4D_ceil (n a b c d : ℕ) (hS : 0 < a + b + c + d) (t : ℝ) :
    cutCount4D n (vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)) t ≤
      win4DCount n a b c d (⌈t⌉ - ((a + b + c + d : ℕ) : ℤ)) := by
  classical
  have hv : ∀ i : Fin 4, 0 ≤ vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) i := by
    intro i; fin_cases i <;> exact Nat.cast_nonneg _
  have hW : 0 < ∑ i : Fin 4, vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) i := by
    rw [sum_fin4]; dsimp [vec4]; exact_mod_cast hS
  unfold cutCount4D cutSet4D cells4D win4DCount
  rw [Finset.filter_map, Finset.card_map]
  apply Finset.card_le_card
  intro q hq
  rw [Finset.mem_filter] at hq ⊢
  refine ⟨hq.1, ?_⟩
  have hm := hq.2
  rw [Function.comp_apply, tupleToCell4D_apply, meets4D_iff_nonneg hv hW,
    sum_fin4 (fun i => vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) i * _),
    sum_fin4 (vec4 (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))] at hm
  dsimp [vec4] at hm
  set V : ℤ := ((a * q.1 + b * q.2.1 + c * q.2.2.1 + d * q.2.2.2 : ℕ) : ℤ)
  have hVr : (V : ℝ) = (a : ℝ) * (q.1 : ℝ) + (b : ℝ) * (q.2.1 : ℝ) +
      (c : ℝ) * (q.2.2.1 : ℝ) + (d : ℝ) * (q.2.2.2 : ℝ) := by dsimp [V]; push_cast; ring
  rw [← hVr] at hm
  have hlt : V < ⌈t⌉ := by
    by_contra hge; push Not at hge
    have : (⌈t⌉ : ℝ) ≤ (V : ℝ) := by exact_mod_cast hge
    linarith [Int.le_ceil t, hm.1]
  have hge : ⌈t⌉ ≤ V + ((a + b + c + d : ℕ) : ℤ) := by
    apply Int.ceil_le.2
    rw [Int.cast_add]; push_cast; exact hm.2.le
  exact ⟨by omega, by omega⟩

/-- **4D `n = 3` Main Diagonal (`(1, 1, 1, 1)`):**
`x₁ + x₂ + x₃ + x₄ = 13/2` cuts `61` open 4-cubes of `[0, 3]⁴`, and EVERY parallel shift
`t ∈ ℝ` cuts at most `61` open 4-cubes (while the unperturbed central hyperplane `t = 6`
cuts only `51`!). -/
theorem cutCount4D_diag_three_max :
    cutCount4D 3 (vec4 1 1 1 1) (13 / 2) = 61 ∧
    cutCount4D 3 (vec4 1 1 1 1) 6 = 51 ∧
    (∀ t : ℝ, cutCount4D 3 (vec4 1 1 1 1) t ≤ 61) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := cutCount4D_eq_win4D_half 3 1 1 1 1 (by omega) 3
    norm_num at h
    rw [h]; decide
  · classical
    have hv : ∀ i : Fin 4, 0 ≤ vec4 (1 : ℝ) 1 1 1 i := by
      intro i; fin_cases i <;> dsimp [vec4] <;> norm_num
    have hW : 0 < ∑ i : Fin 4, vec4 (1 : ℝ) 1 1 1 i := by rw [sum_fin4]; dsimp [vec4]; norm_num
    unfold cutCount4D cutSet4D cells4D
    rw [Finset.filter_map, Finset.card_map]
    have hset : (range 3 ×ˢ range 3 ×ˢ range 3 ×ˢ range 3).filter
        (Meets4D (vec4 1 1 1 1) 6 ∘ tupleToCell4D) =
        (range 3 ×ˢ range 3 ×ˢ range 3 ×ˢ range 3).filter
          (fun q => 3 ≤ q.1 + q.2.1 + q.2.2.1 + q.2.2.2 ∧ q.1 + q.2.1 + q.2.2.1 + q.2.2.2 ≤ 5) := by
      ext q
      rw [Finset.mem_filter, Finset.mem_filter]
      refine and_congr_right fun _ => ?_
      rw [Function.comp_apply, tupleToCell4D_apply, meets4D_iff_nonneg hv hW,
        sum_fin4 (fun i => vec4 (1 : ℝ) 1 1 1 i * _), sum_fin4 (vec4 (1 : ℝ) 1 1 1)]
      dsimp [vec4]
      set s : ℕ := q.1 + q.2.1 + q.2.2.1 + q.2.2.2
      have hsr : (1 : ℝ) * (q.1 : ℝ) + 1 * (q.2.1 : ℝ) + 1 * (q.2.2.1 : ℝ) + 1 * (q.2.2.2 : ℝ) =
          (s : ℝ) := by dsimp [s]; push_cast; ring
      rw [hsr]
      constructor
      · rintro ⟨h1, h2⟩
        have hle5 : s ≤ 5 := by
          by_contra hc; have : (6 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (show 6 ≤ s by omega)
          linarith
        have hge3 : 3 ≤ s := by
          by_contra hc; have : (s : ℝ) ≤ 2 := by exact_mod_cast (show s ≤ 2 by omega)
          linarith
        exact ⟨hge3, hle5⟩
      · rintro ⟨h1, h2⟩
        have h1r : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1
        have h2r : (s : ℝ) ≤ 5 := by exact_mod_cast h2
        constructor <;> linarith
    rw [hset]; decide
  · intro t
    have hle := cutCount4D_le_win4D_ceil 3 1 1 1 1 (by omega) t
    norm_num at hle
    obtain ⟨m, hm⟩ : ∃ m : ℤ, m = ⌈t⌉ - 4 := ⟨_, rfl⟩
    rw [← hm] at hle
    by_cases hm_lo : m ≤ 0
    · have hsub : win4DCount 3 1 1 1 1 m ≤ win4DCount 3 1 1 1 1 0 := by
        unfold win4DCount; apply Finset.card_le_card
        intro q hq; rw [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, by omega, by omega⟩
      have h0 : win4DCount 3 1 1 1 1 0 ≤ 61 := by decide
      omega
    · by_cases hm_hi : 6 ≤ m
      · have hsub : win4DCount 3 1 1 1 1 m ≤ win4DCount 3 1 1 1 1 6 := by
          unfold win4DCount; apply Finset.card_le_card
          intro q hq; rw [Finset.mem_filter] at hq ⊢
          have hqc := hq.1; simp only [Finset.mem_product, Finset.mem_range] at hqc
          exact ⟨hq.1, by omega, by omega⟩
        have h6 : win4DCount 3 1 1 1 1 6 ≤ 61 := by decide
        omega
      · have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl
        · exact le_trans hle (by decide)
        · exact le_trans hle (by decide)
        · exact le_trans hle (by decide)
        · exact le_trans hle (by decide)
        · exact le_trans hle (by decide)

/-- **4D `n = 3` Bárány–Frankl Analogue (`(2, 2, 2, 3)`):**
`2x₁ + 2x₂ + 2x₃ + 3x₄ = 25/2` (and symmetrically `29/2`) cuts `62 = F₄(3)` open 4-cubes of
`[0, 3]⁴`, and EVERY parallel shift `t ∈ ℝ` cuts at most `62` open 4-cubes. -/
theorem cutCount4D_bf_three_max :
    cutCount4D 3 (vec4 2 2 2 3) (25 / 2) = 62 ∧
    cutCount4D 3 (vec4 2 2 2 3) (29 / 2) = 62 ∧
    (∀ t : ℝ, cutCount4D 3 (vec4 2 2 2 3) t ≤ 62) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := cutCount4D_eq_win4D_half 3 2 2 2 3 (by omega) 4
    norm_num at h
    rw [h]; decide
  · have h := cutCount4D_eq_win4D_half 3 2 2 2 3 (by omega) 6
    norm_num at h
    rw [h]; decide
  · intro t
    have hle := cutCount4D_le_win4D_ceil 3 2 2 2 3 (by omega) t
    norm_num at hle
    obtain ⟨m, hm⟩ : ∃ m : ℤ, m = ⌈t⌉ - 9 := ⟨_, rfl⟩
    rw [← hm] at hle
    by_cases hm_lo : m ≤ 0
    · have hsub : win4DCount 3 2 2 2 3 m ≤ win4DCount 3 2 2 2 3 0 := by
        unfold win4DCount; apply Finset.card_le_card
        intro q hq; rw [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, by omega, by omega⟩
      have h0 : win4DCount 3 2 2 2 3 0 ≤ 62 := by decide
      omega
    · by_cases hm_hi : 19 ≤ m
      · have hsub : win4DCount 3 2 2 2 3 m ≤ win4DCount 3 2 2 2 3 19 := by
          unfold win4DCount; apply Finset.card_le_card
          intro q hq; rw [Finset.mem_filter] at hq ⊢
          have hqc := hq.1; simp only [Finset.mem_product, Finset.mem_range] at hqc
          exact ⟨hq.1, by omega, by omega⟩
        have h19 : win4DCount 3 2 2 2 3 19 ≤ 62 := by decide
        omega
      · interval_cases m <;> exact le_trans hle (by decide)

/-- **The 4D `n = 3` Surprise (`63 > 62 > 61`, `ZO02`):**
In `[0, 3]⁴`, the downward-tilted hyperplane `x₁ + 2x₂ + 2x₃ + 2x₄ = 21/2` cuts **63** open
unit 4-cubes, strictly beating EVERY shift of the main diagonal `(1, 1, 1, 1)` (`≤ 61`) and
EVERY shift of the Bárány–Frankl 4D analogue `(2, 2, 2, 3)` (`≤ 62`), hence `63 ≤ maxCutCount4D 3`. -/
theorem cutCount4D_tilted_surprise_three :
    cutCount4D 3 (vec4 1 2 2 2) (21 / 2) = 63 ∧ 63 ≤ maxCutCount4D 3 := by
  have h63 : cutCount4D 3 (vec4 1 2 2 2) (21 / 2) = 63 := by
    have h := cutCount4D_eq_win4D_half 3 1 2 2 2 (by omega) 4
    norm_num at h
    rw [h]; decide
  refine ⟨h63, ?_⟩
  have hbdd : BddAbove {k | ∃ (v : Pt4D) (t : ℝ), IsNormal4D v ∧ cutCount4D 3 v t = k} := by
    refine ⟨3 ^ 4, ?_⟩
    rintro k ⟨v, t, _, rfl⟩
    unfold cutCount4D cutSet4D
    rw [← card_cells4D 3]
    classical exact Finset.card_filter_le _ _
  have hnorm : IsNormal4D (vec4 1 2 2 2) := by
    intro h0
    have : vec4 (1 : ℝ) 2 2 2 0 = 0 := congrFun h0 0
    norm_num [vec4] at this
  exact le_csSup hbdd ⟨vec4 1 2 2 2, 21 / 2, hnorm, h63⟩

end

/-! ### Section 6: Pure-kernel 2D Farkas-BSP certificate verifier and unconditional `n = 5..16` -/

/-- A signed integer affine form `((ap, an), (bp, bn), (cp, cn))` in `ℕ⁶` representing
`(ap - an) u + (bp - bn) w + (cp - cn)`. -/
abbrev PNForm := (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

/-- Exact negation of a `PNForm` by swapping `(pos, neg)` in each component. -/
def negPNForm (f : PNForm) : PNForm :=
  ((f.1.2, f.1.1), (f.2.1.2, f.2.1.1), (f.2.2.2, f.2.2.1))

/-- Context item `(form, isStrict)` (`true` for `0 < form(u, w)`, `false` for `0 ≤ form(u, w)`). -/
abbrev CtxItem := PNForm × Bool

/-- Safe out-of-bounds fallback `0 ≤ 0 · u + 0 · w + 0`, universally true on `ℝ²`. -/
def dummyCtxItem : CtxItem := (((0, 0), (0, 0), (0, 0)), false)

/-- Lookup index `idx` from the head of `ctx`, returning `dummyCtxItem` if out of range. -/
def getCtx : List CtxItem → ℕ → CtxItem
  | [], _ => dummyCtxItem
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getCtx xs k

/-- Pure-`ℕ` tent helper `⌊(k + 1)² / 4⌋` for `k ≥ 1`, `0` for `k = 0`. -/
def t2NatP1 (k : ℕ) : ℕ :=
  if k == 0 then 0 else ((k + 1) * (k + 1)) / 4

/-- Pure-`ℕ` pairing gain `T2(S + 1) - T2(S + 1 - 2 L')` for `1 ≤ L' ≤ S / 2 + 1`. -/
def gNat (S L' : ℕ) : ℕ :=
  if L' == 0 then 0 else ((S + 2) * (S + 2)) / 4 - t2NatP1 (S + 1 - 2 * L')

/-- Unpack an 8-tuple `(M, i1, w1, i2, w2, i3, w3, wc)` from a packed `ℕ` word. -/
def unpackFk (fk : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let i1 := fk &&& 0xFF
  let r1 := fk >>> 8
  let i2 := r1 &&& 0xFF
  let r2 := r1 >>> 8
  let i3 := r2 &&& 0xFF
  let r3 := r2 >>> 8
  let m  := r3 &&& 0xFFFFFFFF
  let r4 := r3 >>> 32
  let w1 := r4 &&& 0xFFFFFFFF
  let r5 := r4 >>> 32
  let w2 := r5 &&& 0xFFFFFFFF
  let r6 := r5 >>> 32
  let w3 := r6 &&& 0xFFFFFFFF
  let wc := r6 >>> 32
  (m, i1, w1, i2, w2, i3, w3, wc)

/-- Pure-`ℕ` Farkas positivity checker on three resolved `CtxItem`s. -/
def checkFarkasItems (c1 c2 c3 : CtxItem) (target : PNForm)
    (m w1 w2 w3 wc : ℕ) : Bool :=
  (1 ≤ m) &&
  (w1 * c1.1.1.1 + w2 * c2.1.1.1 + w3 * c3.1.1.1 + m * target.1.2 ==
    w1 * c1.1.1.2 + w2 * c2.1.1.2 + w3 * c3.1.1.2 + m * target.1.1) &&
  (w1 * c1.1.2.1.1 + w2 * c2.1.2.1.1 + w3 * c3.1.2.1.1 + m * target.2.1.2 ==
    w1 * c1.1.2.1.2 + w2 * c2.1.2.1.2 + w3 * c3.1.2.1.2 + m * target.2.1.1) &&
  (w1 * c1.1.2.2.1 + w2 * c2.1.2.2.1 + w3 * c3.1.2.2.1 + wc + m * target.2.2.2 ==
    w1 * c1.1.2.2.2 + w2 * c2.1.2.2.2 + w3 * c3.1.2.2.2 + m * target.2.2.1) &&
  ((1 ≤ wc) || ((1 ≤ w1) && c1.2) || ((1 ≤ w2) && c2.2) || ((1 ≤ w3) && c3.2))

/-- Pure-`ℕ` Farkas positivity checker: unpacks `fk` and calls `checkFarkasItems`. -/
def checkFarkas (ctx : List CtxItem) (target : PNForm) (fk : ℕ) : Bool :=
  let (m, i1, w1, i2, w2, i3, w3, wc) := unpackFk fk
  checkFarkasItems (getCtx ctx i1) (getCtx ctx i2) (getCtx ctx i3) target m w1 w2 w3 wc

/-- Subtraction-free `PNForm` representation of `hpForm k n S L'`. -/
def hpFormPN (k : Fin 3) (n S L' : ℕ) : PNForm :=
  let h := n - 1
  let lm := L' - 1
  match k with
  | ⟨0, _⟩ => ((4 * h, S), (2 * h + S, 3 * lm), (h, 3 + S))
  | ⟨1, _⟩ => ((2 * S, 2 * h + 3 * lm), (2 * h + S, 3 * lm), (h, 3 + S))
  | ⟨2, _⟩ => ((2 * S, 2 * h + 3 * lm), (S, 4 * h), (h, 3 + S))

/-- Subtraction-free `PNForm` representations of `KForm1 c` and `KForm2 c`. -/
def kFormPN1 (c : ℕ) : PNForm := ((0, 3 * c + 8), (3 * c + 5, 0), (1, 0))
def kFormPN2 (c : ℕ) : PNForm := ((0, 3 * c + 5), (0, 6 * c + 13), (1, 0))

/-- Verify one pair `(S, L', fk)` at a `leaf_P` node and return `(ok, gain)`. -/
def checkPairCert (k : Fin 3) (n : ℕ) (ctx : List CtxItem) (S L' fk : ℕ) : Bool × ℕ :=
  if L' == 0 then (true, 0)
  else if L' ≤ S / 2 + 1 && checkFarkas ctx (hpFormPN k n S L') fk then
    (true, gNat S L')
  else (false, 0)

/-- Unpack a `PNForm` from the payload of a `split` word. -/
def unpackSplit (pay : ℕ) : PNForm :=
  let ap := pay &&& 0xFFFF
  let r1 := pay >>> 16
  let an := r1 &&& 0xFFFF
  let r2 := r1 >>> 16
  let bp := r2 &&& 0xFFFF
  let r3 := r2 >>> 16
  let bn := r3 &&& 0xFFFF
  let r4 := r3 >>> 16
  let cp := r4 &&& 0xFFFF
  let cn := (r4 >>> 16) &&& 0xFFFF
  ((ap, an), (bp, bn), (cp, cn))

/-- Unpack `(S0, L0, S1, L1, S2, L2)` from the payload of a `leaf_P` word. -/
def unpackLeafP (pay : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let s0 := pay &&& 0xFFF
  let r1 := pay >>> 12
  let l0 := r1 &&& 0xFFF
  let r2 := r1 >>> 12
  let s1 := r2 &&& 0xFFF
  let r3 := r2 >>> 12
  let l1 := r3 &&& 0xFFF
  let r4 := r3 >>> 12
  let s2 := r4 &&& 0xFFF
  let l2 := (r4 >>> 12) &&& 0xFFF
  (s0, l0, s1, l1, s2, l2)

/-- Recursive pure-`ℕ` 2D Farkas-BSP tree checker bounded by tree depth `fuel`. -/
def checkBsp : ℕ → ℕ → List CtxItem → List ℕ → Bool × List ℕ
  | 0, _, _, words => (false, words)
  | _ + 1, _, _, [] => (false, [])
  | fuel + 1, n, ctx, w :: rest =>
    if (w &&& 3) == 0 then
      let f := unpackSplit (w >>> 2)
      let (ok1, r1) := checkBsp fuel n ((f, true) :: ctx) rest
      if !ok1 then (false, r1)
      else checkBsp fuel n ((negPNForm f, false) :: ctx) r1
    else if (w &&& 3) == 1 then
      let fPos : PNForm := ((1, 0), (0, 1), (0, 0))
      let fNeg : PNForm := ((0, 1), (1, 0), (0, 0))
      let (ok1, r1) := checkBsp fuel n ((fPos, true) :: ctx) rest
      if !ok1 then (false, r1)
      else checkBsp fuel n ((fNeg, true) :: ctx) r1
    else if (w &&& 3) == 2 then
      match rest with
      | fk0 :: fk1 :: fk2 :: r1 =>
        let (s0, l0, s1, l1, s2, l2) := unpackLeafP (w >>> 2)
        let p0 := checkPairCert 0 n ctx s0 l0 fk0
        let p1 := checkPairCert 1 n ctx s1 l1 fk1
        let p2 := checkPairCert 2 n ctx s2 l2 fk2
        (p0.1 && p1.1 && p2.1 && decide (D n ≤ p0.2 + p1.2 + p2.2), r1)
      | _ => (false, rest)
    else
      match rest with
      | fk1 :: fk2 :: r1 =>
        if 6 ≤ n && n % 2 == 0 then
          let c := (n - 4) / 2
          (checkFarkas ctx (kFormPN1 c) fk1 && checkFarkas ctx (kFormPN2 c) fk2, r1)
        else (false, r1)
      | _ => (false, rest)

/-- Initial context `[-rq · u - 2 rq · w + rp ≥ 0, w > 0, u > 0]` for cone `Z(rp / rq)`. -/
def initCtx (rp rq : ℕ) : List CtxItem :=
  [(((0, rq), (0, 2 * rq), (rp, 0)), false),
   (((0, 0), (1, 0), (0, 0)), true),
   (((1, 0), (0, 0), (0, 0)), true)]

/-- Complete pure-`ℕ` certificate checker for box size `n ≥ 5`. -/
def checkCertN (n rp rq fuel : ℕ) (words : List ℕ) : Bool :=
  (5 ≤ n) && (1 ≤ rq) && (2 * rp ≤ rq) &&
  (if n < 16 then rq ≤ 2 * rp else 8 * rq * rq ≤ 3 * (n + 6) * rp * rp) &&
  (checkBsp fuel n (initCtx rp rq) words).1

noncomputable section

/-- Real affine form corresponding to a `PNForm`. -/
def toAffForm (f : PNForm) : AffForm :=
  ((f.1.1 : ℝ) - (f.1.2 : ℝ), (f.2.1.1 : ℝ) - (f.2.1.2 : ℝ), (f.2.2.1 : ℝ) - (f.2.2.2 : ℝ))

/-- Semantic validity of a single `CtxItem` at `p = (u, w) ∈ ℝ²`. -/
def CtxItemHolds (p : ℝ × ℝ) (it : CtxItem) : Prop :=
  if it.2 then 0 < evalForm (toAffForm it.1) p else 0 ≤ evalForm (toAffForm it.1) p

/-- Semantic validity of all inequalities in `ctx` at `p = (u, w) ∈ ℝ²`. -/
def CtxHolds (p : ℝ × ℝ) (ctx : List CtxItem) : Prop :=
  ∀ it ∈ ctx, CtxItemHolds p it

private lemma evalForm_negPNForm (f : PNForm) (p : ℝ × ℝ) :
    evalForm (toAffForm (negPNForm f)) p = -evalForm (toAffForm f) p := by
  unfold evalForm toAffForm negPNForm; ring

private lemma getCtx_holds {p : ℝ × ℝ} {ctx : List CtxItem} (hctx : CtxHolds p ctx) :
    ∀ idx : ℕ, CtxItemHolds p (getCtx ctx idx) := by
  induction ctx with
  | nil =>
    intro _
    unfold getCtx dummyCtxItem CtxItemHolds evalForm toAffForm
    simp
  | cons x xs ih =>
    intro idx
    cases idx with
    | zero =>
      exact hctx x List.mem_cons_self
    | succ k =>
      exact ih (fun y hy => hctx y (List.mem_cons_of_mem x hy)) k

private lemma ctxItemHolds_nonneg {p : ℝ × ℝ} {it : CtxItem} (h : CtxItemHolds p it) :
    0 ≤ evalForm (toAffForm it.1) p := by
  unfold CtxItemHolds at h
  split_ifs at h
  · exact h.le
  · exact h

private lemma nat_lin_eq {w1 a1p a1n w2 a2p a2n w3 a3p a3n m atp atn : ℕ}
    (h : w1 * a1p + w2 * a2p + w3 * a3p + m * atn =
      w1 * a1n + w2 * a2n + w3 * a3n + m * atp) :
    (w1 : ℝ) * ((a1p : ℝ) - (a1n : ℝ)) + (w2 : ℝ) * ((a2p : ℝ) - (a2n : ℝ)) +
      (w3 : ℝ) * ((a3p : ℝ) - (a3n : ℝ)) = (m : ℝ) * ((atp : ℝ) - (atn : ℝ)) := by
  have hr : ((w1 * a1p + w2 * a2p + w3 * a3p + m * atn : ℕ) : ℝ) =
      ((w1 * a1n + w2 * a2n + w3 * a3n + m * atp : ℕ) : ℝ) := congrArg Nat.cast h
  push_cast at hr; linarith

private lemma nat_lin_eq_c {w1 d1p d1n w2 d2p d2n w3 d3p d3n wc m dtp dtn : ℕ}
    (h : w1 * d1p + w2 * d2p + w3 * d3p + wc + m * dtn =
      w1 * d1n + w2 * d2n + w3 * d3n + m * dtp) :
    (w1 : ℝ) * ((d1p : ℝ) - (d1n : ℝ)) + (w2 : ℝ) * ((d2p : ℝ) - (d2n : ℝ)) +
      (w3 : ℝ) * ((d3p : ℝ) - (d3n : ℝ)) + (wc : ℝ) = (m : ℝ) * ((dtp : ℝ) - (dtn : ℝ)) := by
  have hr : ((w1 * d1p + w2 * d2p + w3 * d3p + wc + m * dtn : ℕ) : ℝ) =
      ((w1 * d1n + w2 * d2n + w3 * d3n + m * dtp : ℕ) : ℝ) := congrArg Nat.cast h
  push_cast at hr; linarith

private lemma real_farkas_comb {u w m w1 w2 w3 wc a1 b1 d1 a2 b2 d2 a3 b3 d3 atv btv dtv : ℝ}
    (eqA : w1 * a1 + w2 * a2 + w3 * a3 = m * atv)
    (eqB : w1 * b1 + w2 * b2 + w3 * b3 = m * btv)
    (eqC : w1 * d1 + w2 * d2 + w3 * d3 + wc = m * dtv) :
    m * (atv * u + btv * w + dtv) =
      w1 * (a1 * u + b1 * w + d1) + w2 * (a2 * u + b2 * w + d2) +
      w3 * (a3 * u + b3 * w + d3) + wc := by
  have eA := congrArg (· * u) eqA
  have eB := congrArg (· * w) eqB
  simp only [add_mul, mul_add, mul_assoc] at eA eB ⊢
  linarith only [eA, eB, eqC]

private lemma checkFarkasItems_sound {p : ℝ × ℝ} {c1 c2 c3 : CtxItem}
    (h1 : CtxItemHolds p c1) (h2 : CtxItemHolds p c2) (h3 : CtxItemHolds p c3)
    (target : PNForm) (m w1 w2 w3 wc : ℕ)
    (hok : checkFarkasItems c1 c2 c3 target m w1 w2 w3 wc = true) :
    0 < evalForm (toAffForm target) p := by
  unfold checkFarkasItems at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨hm, heqA⟩, heqB⟩, heqC⟩, hstrict⟩
  have hcomb := real_farkas_comb (u := p.1) (w := p.2)
    (nat_lin_eq heqA) (nat_lin_eq heqB) (nat_lin_eq_c heqC)
  change (m : ℝ) * evalForm (toAffForm target) p =
    (w1 : ℝ) * evalForm (toAffForm c1.1) p + (w2 : ℝ) * evalForm (toAffForm c2.1) p +
    (w3 : ℝ) * evalForm (toAffForm c3.1) p + (wc : ℝ) at hcomb
  clear heqA heqB heqC
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have ht1 : 0 ≤ (w1 : ℝ) * evalForm (toAffForm c1.1) p :=
    mul_nonneg (Nat.cast_nonneg _) (ctxItemHolds_nonneg h1)
  have ht2 : 0 ≤ (w2 : ℝ) * evalForm (toAffForm c2.1) p :=
    mul_nonneg (Nat.cast_nonneg _) (ctxItemHolds_nonneg h2)
  have ht3 : 0 ≤ (w3 : ℝ) * evalForm (toAffForm c3.1) p :=
    mul_nonneg (Nat.cast_nonneg _) (ctxItemHolds_nonneg h3)
  have hwc_nn : (0 : ℝ) ≤ (wc : ℝ) := Nat.cast_nonneg _
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hstrict
  have hrhs_pos : 0 < (m : ℝ) * evalForm (toAffForm target) p := by
    rcases hstrict with ((hwc1 | ⟨hw1, hs1⟩) | ⟨hw2, hs2⟩) | ⟨hw3, hs3⟩
    · have : (1 : ℝ) ≤ (wc : ℝ) := by exact_mod_cast hwc1
      linarith only [hcomb, ht1, ht2, ht3, this]
    · have hw1r : (1 : ℝ) ≤ (w1 : ℝ) := by exact_mod_cast hw1
      have hc1_pos : 0 < evalForm (toAffForm c1.1) p := by
        unfold CtxItemHolds at h1; rw [ite_eq_left_iff.2 (fun h => absurd hs1 h)] at h1; exact h1
      have hp1 : 0 < (w1 : ℝ) * evalForm (toAffForm c1.1) p := mul_pos (by linarith only [hw1r]) hc1_pos
      linarith only [hcomb, hp1, ht2, ht3, hwc_nn]
    · have hw2r : (1 : ℝ) ≤ (w2 : ℝ) := by exact_mod_cast hw2
      have hc2_pos : 0 < evalForm (toAffForm c2.1) p := by
        unfold CtxItemHolds at h2; rw [ite_eq_left_iff.2 (fun h => absurd hs2 h)] at h2; exact h2
      have hp2 : 0 < (w2 : ℝ) * evalForm (toAffForm c2.1) p := mul_pos (by linarith only [hw2r]) hc2_pos
      linarith only [hcomb, ht1, hp2, ht3, hwc_nn]
    · have hw3r : (1 : ℝ) ≤ (w3 : ℝ) := by exact_mod_cast hw3
      have hc3_pos : 0 < evalForm (toAffForm c3.1) p := by
        unfold CtxItemHolds at h3; rw [ite_eq_left_iff.2 (fun h => absurd hs3 h)] at h3; exact h3
      have hp3 : 0 < (w3 : ℝ) * evalForm (toAffForm c3.1) p := mul_pos (by linarith only [hw3r]) hc3_pos
      linarith only [hcomb, ht1, ht2, hp3, hwc_nn]
  exact (mul_pos_iff_of_pos_left hm_pos).1 hrhs_pos

private lemma checkFarkas_sound {p : ℝ × ℝ} {ctx : List CtxItem}
    (hctx : CtxHolds p ctx) (target : PNForm) (fk : ℕ)
    (hok : checkFarkas ctx target fk = true) :
    0 < evalForm (toAffForm target) p := by
  unfold checkFarkas at hok
  rcases h : unpackFk fk with ⟨m, i1, w1, i2, w2, i3, w3, wc⟩
  rw [h] at hok
  exact checkFarkasItems_sound (getCtx_holds hctx i1) (getCtx_holds hctx i2)
    (getCtx_holds hctx i3) target m w1 w2 w3 wc hok

private lemma toAffForm_hpFormPN (k : Fin 3) (n S L' : ℕ) :
    toAffForm (hpFormPN k n S L') = hpForm k n S L' := by
  fin_cases k <;> simp only [hpFormPN, hpForm, toAffForm, Prod.mk.injEq] <;>
    push_cast <;> refine ⟨by ring, by ring, by ring⟩

private lemma toAffForm_kFormPN1 (c : ℕ) : toAffForm (kFormPN1 c) = KForm1 c := by
  simp only [kFormPN1, KForm1, toAffForm, Prod.mk.injEq]; push_cast; refine ⟨by ring, by ring, by ring⟩

private lemma toAffForm_kFormPN2 (c : ℕ) : toAffForm (kFormPN2 c) = KForm2 c := by
  simp only [kFormPN2, KForm2, toAffForm, Prod.mk.injEq]; push_cast; refine ⟨by ring, by ring, by ring⟩

private lemma gNat_le_Gval {p q g : ℝ} {S L' : ℕ} (hL1 : 1 ≤ L') (hL_le : L' ≤ Lval p q g S) :
    gNat S L' ≤ Gval p q g S := by
  have h1 : T2 ((S : ℤ) + 1) = ((S + 2) * (S + 2)) / 4 := by
    have heq : (S : ℤ) + 1 = ((S + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [heq, T2_nat]
    have hsq : (S + 1 + 1) ^ 2 = (S + 2) * (S + 2) := by ring
    rw [hsq]
  have h2 : T2 ((S : ℤ) + 1 - 2 * (L' : ℤ)) = t2NatP1 (S + 1 - 2 * L') := by
    unfold T2 t2NatP1
    by_cases hle : S + 1 ≤ 2 * L'
    · have hsub0 : S + 1 - 2 * L' = 0 := by omega
      have hint0 : (S : ℤ) + 1 - 2 * (L' : ℤ) ≤ 0 := by omega
      rw [hsub0, ite_eq_left hint0]; rfl
    · push Not at hle
      have hne0 : (S + 1 - 2 * L' == 0) = false := beq_false_of_ne (by omega)
      have hint_pos : ¬((S : ℤ) + 1 - 2 * (L' : ℤ) ≤ 0) := by omega
      rw [hne0, ite_eq_right hint_pos]
      have hto : ((S : ℤ) + 1 - 2 * (L' : ℤ) + 1).toNat = S + 1 - 2 * L' + 1 := by omega
      rw [hto]
      have hsq : (S + 1 - 2 * L' + 1) ^ 2 = (S + 1 - 2 * L' + 1) * (S + 1 - 2 * L' + 1) := by ring
      rw [hsq]; rfl
  have hmono : T2 ((S : ℤ) + 1 - 2 * (Lval p q g S : ℤ)) ≤ T2 ((S : ℤ) + 1 - 2 * (L' : ℤ)) := by
    unfold T2
    split_ifs with ha hb
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · omega
    · apply Nat.div_le_div_right; apply Nat.pow_le_pow_left; omega
  unfold gNat Gval
  have hLne0 : (L' == 0) = false := beq_false_of_ne (by omega)
  rw [hLne0, h1, ← h2]
  exact Nat.sub_le_sub_left hmono _

private def bPairTarget (k : Fin 3) (n : ℕ) (u w : ℝ) : ℕ :=
  if k.val = 0 then B1 n u w else if k.val = 1 then B2 n u w else B3 n u w

private lemma checkPairCert_sound (k : Fin 3) {n : ℕ} (hn : 1 ≤ n) {u w : ℝ}
    (hu : 0 < u) (hw : 0 < w) (hx1 : 0 < x1 u w) {ctx : List CtxItem}
    (hctx : CtxHolds (u, w) ctx) (S L' fk : ℕ)
    (hok : (checkPairCert k n ctx S L' fk).1 = true) :
    (checkPairCert k n ctx S L' fk).2 ≤ bPairTarget k n u w := by
  unfold checkPairCert at hok ⊢
  cases hL0 : (L' == 0)
  · rw [hL0] at hok
    have hL1 : 1 ≤ L' := by
      have : L' ≠ 0 := beq_eq_false_iff_ne.1 hL0
      omega
    cases hcond : (decide (L' ≤ S / 2 + 1) && checkFarkas ctx (hpFormPN k n S L') fk)
    · rw [hcond] at hok; simp at hok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have hcap : L' ≤ cap S := hcond.1
      have hpos := checkFarkas_sound hctx (hpFormPN k n S L') fk hcond.2
      rw [toAffForm_hpFormPN] at hpos
      have hLle := (hpForm_iff_le_Lval hn k S L' hL1 hcap hu hw).1 hpos
      fin_cases k <;> simp only [bPairTarget] <;> dsimp only at hLle ⊢
      · exact le_trans (gNat_le_Gval hL1 hLle) (G1_le_B1 hn hx1 hu.le hw.le S)
      · exact le_trans (gNat_le_Gval hL1 hLle) (G2_le_B2 hn hx1 hu.le hw.le S)
      · exact le_trans (gNat_le_Gval hL1 hLle) (G3_le_B3 hn hx1 hu.le hw.le S)
  · exact Nat.zero_le _

private lemma checkBsp_sound (fuel : ℕ) :
    ∀ {n : ℕ} (_hn : 5 ≤ n) {u w : ℝ} (t : ℝ) (_hu : 0 < u) (_hw : 0 < w) (_hne : u ≠ w)
      (_hx1 : 0 < x1 u w) (ctx : List CtxItem) (_hctx : CtxHolds (u, w) ctx) (words : List ℕ),
      (checkBsp fuel n ctx words).1 = true →
      D n ≤ missedCount n u w t := by
  induction fuel with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ hok
    simp [checkBsp] at hok
  | succ fuel ih =>
    intro n hn u w t hu hw hne hx1 ctx hctx words hok
    cases words with
    | nil => simp [checkBsp] at hok
    | cons wrd rest =>
      unfold checkBsp at hok
      cases htag0 : (wrd &&& 3 == 0)
      · rw [ite_eq_right (by simp [htag0])] at hok
        cases htag1 : (wrd &&& 3 == 1)
        · rw [ite_eq_right (by simp [htag1])] at hok
          cases htag2 : (wrd &&& 3 == 2)
          · rw [ite_eq_right (by simp [htag2])] at hok
            rcases rest with _ | ⟨fk1, _ | ⟨fk2, r1⟩⟩ <;> try simp at hok
            by_cases hev_chk : 6 ≤ n ∧ n % 2 = 0
            · rw [ite_eq_left hev_chk] at hok
              dsimp only at hok
              simp only [Bool.and_eq_true] at hok
              let c := (n - 4) / 2
              have hc1 : 1 ≤ c := by dsimp [c]; omega
              have hn_eq : 2 * c + 4 = n := by dsimp [c]; omega
              have hk1 := checkFarkas_sound hctx (kFormPN1 c) fk1 hok.1
              have hk2 := checkFarkas_sound hctx (kFormPN2 c) fk2 hok.2
              rw [toAffForm_kFormPN1] at hk1
              rw [toAffForm_kFormPN2] at hk2
              have hinK : inK c u w := (inK_iff_KForm c (u, w)).2 ⟨hk1, hk2⟩
              have hp_ne : (u, w) ≠ (0, 0) := fun h => by simp only [Prod.mk.injEq] at h; linarith
              have hC := lemma_C_coupling c hc1 u w t hu.le hw.le hp_ne hinK
              rwa [hn_eq] at hC
            · rw [ite_eq_right hev_chk] at hok; simp at hok
          · rw [ite_eq_left htag2] at hok
            rcases rest with _ | ⟨fk0, _ | ⟨fk1, _ | ⟨fk2, r1⟩⟩⟩
            · simp at hok
            · simp at hok
            · simp at hok
            · rcases hul : unpackLeafP (wrd >>> 2) with ⟨s0, l0, s1, l1, s2, l2⟩
              rw [hul] at hok
              dsimp only at hok
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
              rcases hok with ⟨⟨⟨hok0, hok1⟩, hok2⟩, hDle⟩
              have hb0 := checkPairCert_sound 0 (by omega) hu hw hx1 hctx s0 l0 fk0 hok0
              have hb1 := checkPairCert_sound 1 (by omega) hu hw hx1 hctx s1 l1 fk1 hok1
              have hb2 := checkPairCert_sound 2 (by omega) hu hw hx1 hctx s2 l2 fk2 hok2
              dsimp [bPairTarget] at hb0 hb1 hb2
              have hsumB := lemma_P_sum_B (n := n) (by omega) hx1 hu.le hw.le t
              omega
        · rw [ite_eq_left htag1] at hok
          dsimp only at hok
          rcases hres1 : checkBsp fuel n ((((1, 0), (0, 1), (0, 0)), true) :: ctx) rest with ⟨ok1, r1⟩
          rw [hres1] at hok
          dsimp only at hok
          cases hok1 : ok1
          · rw [hok1] at hok; simp at hok
          · rw [hok1, Bool.not_true, ite_eq_right Bool.false_ne_true] at hok
            have hok1' : (checkBsp fuel n ((((1, 0), (0, 1), (0, 0)), true) :: ctx) rest).1 = true := by
              rw [hres1, hok1]
            rcases lt_trichotomy w u with hwu | heq | huw
            · apply ih hn t hu hw hne hx1 ((((1, 0), (0, 1), (0, 0)), true) :: ctx) _ rest hok1'
              intro it hit
              rcases List.mem_cons.1 hit with rfl | hmem
              · simp only [CtxItemHolds, evalForm, toAffForm, ↓reduceIte]; push_cast; linarith
              · exact hctx it hmem
            · exact absurd heq.symm hne
            · apply ih hn t hu hw hne hx1 ((((0, 1), (1, 0), (0, 0)), true) :: ctx) _ r1 hok
              intro it hit
              rcases List.mem_cons.1 hit with rfl | hmem
              · simp only [CtxItemHolds, evalForm, toAffForm, ↓reduceIte]; push_cast; linarith
              · exact hctx it hmem
      · rw [ite_eq_left htag0] at hok
        dsimp only at hok
        set f := unpackSplit (wrd >>> 2)
        rcases hres1 : checkBsp fuel n ((f, true) :: ctx) rest with ⟨ok1, r1⟩
        rw [hres1] at hok
        dsimp only at hok
        cases hok1 : ok1
        · rw [hok1] at hok; simp at hok
        · rw [hok1, Bool.not_true, ite_eq_right Bool.false_ne_true] at hok
          have hok1' : (checkBsp fuel n ((f, true) :: ctx) rest).1 = true := by
            rw [hres1, hok1]
          rcases lt_or_ge 0 (evalForm (toAffForm f) (u, w)) with hpos | hnonpos
          · apply ih hn t hu hw hne hx1 ((f, true) :: ctx) _ rest hok1'
            intro it hit
            rcases List.mem_cons.1 hit with rfl | hmem
            · exact hpos
            · exact hctx it hmem
          · apply ih hn t hu hw hne hx1 ((negPNForm f, false) :: ctx) _ r1 hok
            intro it hit
            rcases List.mem_cons.1 hit with rfl | hmem
            · simp only [CtxItemHolds, Bool.false_eq_true, ↓reduceIte]
              rw [evalForm_negPNForm]; linarith
            · exact hctx it hmem

private lemma two_mul_sq_le_F {n : ℕ} (hn : 3 ≤ n) : 2 * n ^ 2 ≤ F n := by
  unfold F
  refine (Nat.le_div_iff_mul_le (by omega)).2 ?_
  have : 8 * n ^ 2 + 17 ≤ 9 * n ^ 2 + 4 * n := by nlinarith
  omega

private lemma perturb_step_le (n : ℕ) (a b c t : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      cutCount n a b c t ≤ cutCount n a (b + δ) (c + 3 * δ) t := by
  by_cases hne : (cutSet n a b c t).Nonempty
  · let dmin : ℝ := (cutSet n a b c t).inf' hne (fun z => t - dot a b c z)
    have hdmin : 0 < dmin := by
      rw [Finset.lt_inf'_iff]
      intro z hz
      have hm := (meets_iff_nonneg ha.le (by linarith) (by linarith) (by linarith) z).1
        (mem_cutSet.1 hz).2
      linarith [hm.1]
    let ε : ℝ := dmin / (4 * (n : ℝ) + 1)
    have hε : 0 < ε := div_pos hdmin (by positivity)
    refine ⟨ε, hε, fun δ hδ0 hδle => ?_⟩
    unfold cutCount
    apply Finset.card_le_card
    intro z hz
    have hz' := mem_cutSet.1 hz
    have hzc := mem_cells.1 hz'.1
    have hm := (meets_iff_nonneg ha.le (by linarith) (by linarith) (by linarith) z).1 hz'.2
    refine mem_cutSet.2 ⟨hz'.1, ?_⟩
    rw [meets_iff_nonneg ha.le (by linarith) (by linarith) (by linarith)]
    have hdz : dmin ≤ t - dot a b c z := Finset.inf'_le (fun z => t - dot a b c z) hz
    have hy : (z.2.1 : ℝ) < (n : ℝ) := by exact_mod_cast hzc.2.1
    have hw : (z.2.2 : ℝ) < (n : ℝ) := by exact_mod_cast hzc.2.2
    have hdot : dot a (b + δ) (c + 3 * δ) z =
        dot a b c z + δ * ((z.2.1 : ℝ) + 3 * (z.2.2 : ℝ)) := by
      unfold dot; ring
    have hsmall : δ * ((z.2.1 : ℝ) + 3 * (z.2.2 : ℝ)) < dmin := by
      have hbd0 : 0 ≤ (z.2.1 : ℝ) + 3 * (z.2.2 : ℝ) := by positivity
      have hbd : (z.2.1 : ℝ) + 3 * (z.2.2 : ℝ) < 4 * (n : ℝ) + 1 := by linarith
      calc δ * ((z.2.1 : ℝ) + 3 * (z.2.2 : ℝ))
          ≤ ε * ((z.2.1 : ℝ) + 3 * (z.2.2 : ℝ)) := mul_le_mul_of_nonneg_right hδle hbd0
        _ < ε * (4 * (n : ℝ) + 1) := mul_lt_mul_of_pos_left hbd hε
        _ = dmin := div_mul_cancel₀ dmin (by positivity)
    have hnn : 0 ≤ δ * ((z.2.1 : ℝ) + 3 * (z.2.2 : ℝ)) :=
      mul_nonneg hδ0.le (by positivity)
    constructor <;> linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨1, zero_lt_one, fun _ _ _ => ?_⟩
    unfold cutCount
    rw [hne, Finset.card_empty]
    exact Nat.zero_le _

/-- Open-condition perturbation separating both `0 < a < b' < c'` and `b' - a ≠ c' - b'`
(`u ≠ w`) without decreasing `cutCount`. -/
theorem perturb_strict_ordered_ne (n : ℕ) (a b c t : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ b' c' : ℝ, a < b' ∧ b' < c' ∧ b' - a ≠ c' - b' ∧
      cutCount n a b c t ≤ cutCount n a b' c' t := by
  obtain ⟨ε, hε, hstep⟩ := perturb_step_le n a b c t ha hab hbc
  by_cases hne : (b + ε) - a ≠ (c + 3 * ε) - (b + ε)
  · exact ⟨b + ε, c + 3 * ε, by linarith, by linarith, hne, hstep ε hε (le_refl _)⟩
  · push Not at hne
    refine ⟨b + ε / 2, c + 3 * (ε / 2), by linarith, by linarith, ?_,
      hstep (ε / 2) (by linarith) (by linarith)⟩
    intro heq
    linarith

/-- **Generalized Reduction R (`reduction_R_general`):** Unconditional over `ℝ` for every `n ≥ 3`
(using the column-bound cone `u + 2w ≤ 1/2` for `3 ≤ n ≤ 15` and `u + 2w ≤ 3 rad n` for `n ≥ 16`,
together with `u ≠ w` from openness of `Meets`). -/
theorem reduction_R_general (n : ℕ) (hn : 3 ≤ n) (R1 : ℝ)
    (hR1 : (n < 16 → 1 / 2 ≤ R1) ∧ (16 ≤ n → 3 * rad n ≤ R1))
    (hstar : ∀ u w t : ℝ, 0 < u → 0 < w → u ≠ w → u + 2 * w ≤ R1 →
      D n ≤ missedCount n u w t) :
    ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n := by
  intro a b c t hv
  by_contra hgt
  push Not at hgt
  have h2sq : 2 * n ^ 2 ≤ F n := two_mul_sq_le_F hn
  obtain ⟨h, rfl⟩ : ∃ h : ℕ, n = h + 1 := ⟨n - 1, by omega⟩
  obtain ⟨a1, b1, c1, t1, ha1, hab1, hbc1, hsum1, heq1⟩ := wlog_ordered_nonneg (h + 1) a b c t hv
  rw [heq1] at hgt
  have hc1_pos : 0 < c1 := by linarith
  have hcol1 : c1 < a1 + b1 := by
    by_contra hcon; push Not at hcon
    have := column_bound (h + 1) a1 b1 c1 t1 ha1 (by linarith) hc1_pos hcon
    omega
  have ha1_pos : 0 < a1 := by linarith
  obtain ⟨b', c', hab', hbc', hne', hpert⟩ :=
    perturb_strict_ordered_ne (h + 1) a1 b1 c1 t1 ha1_pos hab1 hbc1
  have hgt2 : F (h + 1) < cutCount (h + 1) a1 b' c' t1 := lt_of_lt_of_le hgt hpert
  let W : ℝ := a1 + b' + c'
  have hW : 0 < W := by dsimp [W]; linarith
  let p1 : ℝ := a1 / W
  let p2 : ℝ := b' / W
  let p3 : ℝ := c' / W
  let t2 : ℝ := t1 / W
  have hscale : cutCount (h + 1) p1 p2 p3 t2 = cutCount (h + 1) a1 b' c' t1 := by
    have hinv : W⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hW)
    have hsc := cutCount_scale (n := h + 1) (a := a1) (b := b') (c := c')
      (t := t1) (lam := W⁻¹) hinv
    simpa [p1, p2, p3, t2, div_eq_inv_mul] using hsc
  rw [← hscale] at hgt2
  have hp1 : 0 < p1 := div_pos ha1_pos hW
  have hp12 : p1 < p2 := div_lt_div_of_pos_right hab' hW
  have hp23 : p2 < p3 := div_lt_div_of_pos_right hbc' hW
  have hp_sum : p1 + p2 + p3 = 1 := by
    dsimp [p1, p2, p3]; rw [← add_div, ← add_div]; exact div_self (ne_of_gt hW)
  have hp_col : p3 < p1 + p2 := by
    by_contra hcon; push Not at hcon
    have := column_bound (h + 1) p1 p2 p3 t2 hp1.le (by linarith) (by linarith) hcon
    omega
  have hcol2 : 2 * p3 < p1 + p2 + p3 := by linarith
  obtain ⟨t3, ht3_lo, ht3_hi, hcen⟩ :=
    exists_central h p1 p2 p3 t2 hp1 (by linarith) (by linarith) hcol2
  have hgt3 : F (h + 1) < cutCount (h + 1) p1 p2 p3 t3 := lt_of_lt_of_le hgt2 hcen
  let u : ℝ := p2 - p1
  let w : ℝ := p3 - p2
  have hu_pos : 0 < u := by dsimp [u]; linarith
  have hw_pos : 0 < w := by dsimp [w]; linarith
  have hu_ne_w : u ≠ w := by
    intro heq
    have hmul : (p2 - p1) * W = (p3 - p2) * W := by dsimp [u, w] at heq; rw [heq]
    have hl : (p2 - p1) * W = b' - a1 := by
      dsimp [p1, p2]; rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hW), div_mul_cancel₀ _ (ne_of_gt hW)]
    have hr : (p3 - p2) * W = c' - b' := by
      dsimp [p2, p3]; rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hW), div_mul_cancel₀ _ (ne_of_gt hW)]
    exact hne' (by linarith)
  have hx1 : x1 u w = p1 := by unfold x1; dsimp [u, w]; linarith
  have hx2 : x2 u w = p2 := by unfold x2; dsimp [u, w]; linarith
  have hx3 : x3 u w = p3 := by unfold x3; dsimp [u, w]; linarith
  have hcone : u + 2 * w ≤ R1 := by
    by_cases h16 : h + 1 < 16
    · have hp3_half : p3 < 1 / 2 := by linarith [hp_sum, hcol2]
      have huw_half : u + 2 * w ≤ 1 / 2 := by dsimp [u, w]; linarith [hp_sum, hp3_half]
      exact le_trans huw_half (hR1.1 h16)
    · push Not at h16
      have hu2 := u2_sorted_cone h (by omega) p1 p2 p3 t3 hp1.le (by linarith) (by linarith)
        (by linarith) hp23.le hgt3.le
      have h3 : p3 / (p1 + p2 + p3) - 1 / 3 ≤ rad (h + 1) := hu2.2
      rw [hp_sum, div_one] at h3
      have huw_rad : u + 2 * w ≤ 3 * rad (h + 1) := by dsimp [u, w]; linarith
      exact le_trans huw_rad (hR1.2 h16)
  have hmiss : D (h + 1) ≤ missedCount (h + 1) u w t3 := hstar u w t3 hu_pos hw_pos hu_ne_w hcone
  have hT := lemmaT_le h p1 p2 p3 t3 hp1.le (by linarith) (by linarith) (by linarith)
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have hp2_pos : 0 < p2 := by linarith
  have hp3_pos : 0 < p3 := by linarith
  have ht3_hi' : t3 ≤ (h : ℝ) + 1 - (h : ℝ) * p3 := by rw [hp_sum, mul_one] at ht3_hi; exact ht3_hi
  have hp1_le_p2 : (h : ℝ) * p1 ≤ (h : ℝ) * p2 := mul_le_mul_of_nonneg_left hp12.le hh0
  have hp2_le_p3 : (h : ℝ) * p2 ≤ (h : ℝ) * p3 := mul_le_mul_of_nonneg_left hp23.le hh0
  have hp1_le_p3 : (h : ℝ) * p1 ≤ (h : ℝ) * p3 := le_trans hp1_le_p2 hp2_le_p3
  have hsum_h : (h : ℝ) * p1 + (h : ℝ) * p2 + (h : ℝ) * p3 = (h : ℝ) := by
    calc (h : ℝ) * p1 + (h : ℝ) * p2 + (h : ℝ) * p3 = (h : ℝ) * (p1 + p2 + p3) := by ring
      _ = (h : ℝ) := by rw [hp_sum, mul_one]
  have eqA1 : tri p2 p3 ((p2 + p3) * (h : ℝ) - t3) h =
      triNat (x2 u w) (x3 u w) (alpha1 (h + 1) u w t3) := by
    rw [hx2, hx3]
    have ha_eq : alpha1 (h + 1) u w t3 = (p2 + p3) * (h : ℝ) - t3 := by
      unfold alpha1 s1; rw [hx1]; simp only [Nat.add_sub_cancel]
      have : 1 - p1 = p2 + p3 := by linarith
      rw [this]
    rw [ha_eq]; exact tri_eq_triNat hp2_pos hp3_pos (by linarith) (by linarith)
  have eqB1 : tri p2 p3 (t3 - (h : ℝ) * p1 - (p2 + p3 + p1)) h =
      triNat (x2 u w) (x3 u w) (beta1 (h + 1) u w t3) := by
    rw [hx2, hx3]
    have hb_eq : beta1 (h + 1) u w t3 = t3 - (h : ℝ) * p1 - (p2 + p3 + p1) := by
      unfold beta1; rw [hx1]; simp only [Nat.add_sub_cancel]; linarith
    rw [hb_eq]; exact tri_eq_triNat hp2_pos hp3_pos (by linarith) (by linarith)
  have eqA2 : tri p1 p3 ((p1 + p3) * (h : ℝ) - t3) h =
      triNat (x1 u w) (x3 u w) (alpha2 (h + 1) u w t3) := by
    rw [hx1, hx3]
    have ha_eq : alpha2 (h + 1) u w t3 = (p1 + p3) * (h : ℝ) - t3 := by
      unfold alpha2 s2; rw [hx2]; simp only [Nat.add_sub_cancel]
      have : 1 - p2 = p1 + p3 := by linarith
      rw [this]
    rw [ha_eq]; exact tri_eq_triNat hp1 hp3_pos (by linarith) (by linarith)
  have eqB2 : tri p1 p3 (t3 - (h : ℝ) * p2 - (p1 + p3 + p2)) h =
      triNat (x1 u w) (x3 u w) (beta2 (h + 1) u w t3) := by
    rw [hx1, hx3]
    have hb_eq : beta2 (h + 1) u w t3 = t3 - (h : ℝ) * p2 - (p1 + p3 + p2) := by
      unfold beta2; rw [hx2]; simp only [Nat.add_sub_cancel]; linarith
    rw [hb_eq]; exact tri_eq_triNat hp1 hp3_pos (by linarith) (by linarith)
  have eqA3 : tri p1 p2 ((p1 + p2) * (h : ℝ) - t3) h =
      triNat (x1 u w) (x2 u w) (alpha3 (h + 1) u w t3) := by
    rw [hx1, hx2]
    have ha_eq : alpha3 (h + 1) u w t3 = (p1 + p2) * (h : ℝ) - t3 := by
      unfold alpha3 s3; rw [hx3]; simp only [Nat.add_sub_cancel]
      have : 1 - p3 = p1 + p2 := by linarith
      rw [this]
    rw [ha_eq]; exact tri_eq_triNat hp1 hp2_pos (by linarith) (by linarith)
  have eqB3 : tri p1 p2 (t3 - (h : ℝ) * p3 - (p1 + p2 + p3)) h =
      triNat (x1 u w) (x2 u w) (beta3 (h + 1) u w t3) := by
    rw [hx1, hx2]
    have hb_eq : beta3 (h + 1) u w t3 = t3 - (h : ℝ) * p3 - (p1 + p2 + p3) := by
      unfold beta3; rw [hx3]; simp only [Nat.add_sub_cancel]; linarith
    rw [hb_eq]; exact tri_eq_triNat hp1 hp2_pos (by linarith) (by linarith)
  rw [eqA1, eqB1, eqA2, eqB2, eqA3, eqB3] at hT
  have hcube : (h + 1) ^ 3 - h ^ 3 = 3 * (h + 1) ^ 2 - 3 * (h + 1) + 1 := by
    have h1 : h ^ 3 ≤ (h + 1) ^ 3 := by nlinarith
    have h2 : 3 * (h + 1) ≤ 3 * (h + 1) ^ 2 := by nlinarith
    zify [h1, h2]; ring
  have hF_le := F_le_diag (h + 1) (by omega)
  unfold missedCount Delta at hmiss
  unfold D at hmiss
  omega

/-- **Soundness of `checkCertN` (`checkCertN_sound`):** A passing pure-`ℕ` Farkas-BSP certificate
for `n ≥ 5` unconditionally proves `cutCount n a b c t ≤ F n` for EVERY nonzero real plane. -/
theorem checkCertN_sound (n rp rq fuel : ℕ) (words : List ℕ)
    (hok : checkCertN n rp rq fuel words = true) :
    ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n := by
  unfold checkCertN at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨hn5, hrq1⟩, hrp_half⟩, hrad_chk⟩, hbsp⟩
  have hrq_pos : (0 : ℝ) < (rq : ℝ) := by exact_mod_cast (show 0 < rq by omega)
  have hR1_le_half : (rp : ℝ) / (rq : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hrq_pos (by norm_num)]
    have : ((2 * rp : ℕ) : ℝ) ≤ (rq : ℝ) := by exact_mod_cast hrp_half
    push_cast at this; linarith
  apply reduction_R_general n (by omega) ((rp : ℝ) / (rq : ℝ))
  · refine ⟨fun h16 => ?_, fun h16 => ?_⟩
    · rw [ite_eq_left h16, decide_eq_true_eq] at hrad_chk
      rw [div_le_div_iff₀ (by norm_num) hrq_pos]
      have : (rq : ℝ) ≤ ((2 * rp : ℕ) : ℝ) := by exact_mod_cast hrad_chk
      push_cast at this; linarith
    · have hnot16 : ¬(n < 16) := by omega
      rw [ite_eq_right hnot16, decide_eq_true_eq] at hrad_chk
      have hsq : (3 * rad n) ^ 2 ≤ ((rp : ℝ) / (rq : ℝ)) ^ 2 := by
        have hrad2 : (3 * rad n) ^ 2 = 8 / (3 * ((n : ℝ) + 6)) := by
          calc (3 * rad n) ^ 2 = 9 * (rad n) ^ 2 := by ring
            _ = 9 * (8 / (27 * ((n : ℝ) + 6))) := by rw [rad_sq]
            _ = 8 / (3 * ((n : ℝ) + 6)) := by field_simp; ring
        rw [hrad2, div_pow, div_le_div_iff₀ (by positivity) (sq_pos_of_pos hrq_pos)]
        have hr : ((8 * rq * rq : ℕ) : ℝ) ≤ ((3 * (n + 6) * rp * rp : ℕ) : ℝ) := by
          exact_mod_cast hrad_chk
        push_cast at hr; nlinarith
      have hnn1 : 0 ≤ 3 * rad n := mul_nonneg (by norm_num) (rad_pos n).le
      have hnn2 : 0 ≤ (rp : ℝ) / (rq : ℝ) := div_nonneg (Nat.cast_nonneg _) hrq_pos.le
      nlinarith
  · intro u w t hu hw hne hcone
    have hx1 : 0 < x1 u w := by
      have hhalf : u + 2 * w ≤ 1 / 2 := le_trans hcone hR1_le_half
      unfold x1; linarith
    have hctx0 : CtxHolds (u, w) (initCtx rp rq) := by
      intro it hit
      simp only [initCtx, List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl | rfl
      · simp only [CtxItemHolds, evalForm, toAffForm, Bool.false_eq_true, ↓reduceIte]
        have hm := (le_div_iff₀ hrq_pos).1 hcone
        push_cast; linarith
      · simp only [CtxItemHolds, evalForm, toAffForm, ↓reduceIte]; push_cast; linarith
      · simp only [CtxItemHolds, evalForm, toAffForm, ↓reduceIte]; push_cast; linarith
    exact checkBsp_sound fuel hn5 t hu hw hne hx1 (initCtx rp rq) hctx0 words hbsp

end

/-! ### Pure-kernel Farkas-BSP certificate tables for `5 ≤ n ≤ 32` -/

private def bspWords_5 : List ℕ := [0x800000000002000000034, 0x800e, 0x100000001000200, 0x1000000, 0x1000000, 0x400000000001c00000038, 0x800a, 0x100000001000300, 0x1000000, 0x1000000, 0xc00080000, 0x4004004006, 0x30000001500000001000005, 0x30000000000000001000005, 0x1000000, 0x400000000002800000038, 0x400000400a, 0x100000001000200, 0x300000000000000200000001c00000007000200, 0x1000000, 0x4000004000004006, 0x3f0000000f00000002000501, 0x300000000000000040000006000000007000005, 0x300000000000000480000001c0000001f000100]
private def bspMeta_5 : ℕ × ℕ × ℕ := (1, 2, 5)

private def bspWords_6 : List ℕ := [0x1, 0x400000020002c0000, 0x4004c000000200000, 0x3, 0x10000000000000001000104, 0x10000000000000001000001, 0x400000000001000000020, 0x400400c012, 0x200000001000200, 0xf00000000000000280000001300000024000200, 0x1000000, 0x40028000000140000, 0x400000400400800e, 0x10000000900000001000204, 0x1e0000000000000050000000130000005b000302, 0x20000000000000001000001, 0x800000000002c00000040, 0x4004008012, 0x10000000000000001000005, 0x300000000000000090000000800000004000201, 0x1000000, 0x400800800e, 0x400000000000000090000002800000005000105, 0x600000000000000280000005600000023000001, 0x1000000, 0x4004c000000200000, 0x400400400400800e, 0x600000000000000f6000000110000000b000401, 0x10000001e00000001000004, 0x10000000000000001000004, 0x400000000000c00000014, 0xc016, 0x300000001000500, 0x1000000, 0x1000000, 0x400000000001000000020, 0x400000c012, 0x200000001000600, 0x20000001000000001000106, 0x1000000, 0x400000400400800e, 0x480000000000000052000000510000005b000203, 0xf000000030000000100000002060002, 0x3000000000000000a0000001900000009000300, 0x4004c000000200000, 0x3, 0x800000000000000010000005b00000009000001, 0x10000000000000001000001, 0x800000000002c00000040, 0x8008008012, 0x100000001000200, 0x90000000000000001000200, 0x1000000, 0x400000000002800000044, 0x800800800e, 0x100000001000300, 0x90000000000000001000300, 0x1000000, 0x400000800800800a, 0x900000000000000090000010e00000013000206, 0x9000000010000000100000002030002, 0x180000000200000001000600]
private def bspMeta_6 : ℕ × ℕ × ℕ := (1, 2, 7)

private def bspWords_7 : List ℕ := [0x400000000000c00000018, 0x1001a, 0x300000001000200, 0x1000000, 0x1000000, 0x800000000002c0000004c, 0x400400c016, 0x100000001000300, 0x100000000000000050000003600000003000103, 0x1000000, 0x400000000002800000050, 0x10000c0000, 0x800c00c012, 0x10000000000000001000106, 0x300000001000200, 0x1000000, 0x40058000000200000, 0x400800400800c012, 0x100000001000602, 0x300000000000000080000016200000013000306, 0x10000000000000001000003, 0x1400080000, 0x400000800800c012, 0x60000000000000037000000b400000031000102, 0x11000000000000000b0000006e00000027000400, 0x570000000000000144000000780000006d000204, 0x400400400800c012, 0x3000000000000000a0000001e00000007000100, 0x1200000000000000300000003b00000037000401, 0xe000000000000006d0000002000000027000004, 0x400580000002c0000, 0x800800800800800e, 0xc0000001500000001000506, 0x9000000000000000b0000014a00000014000105, 0x10000000000000001000001, 0x8005c000000280000, 0x400000000003400000050, 0x4004008008008012, 0x10000000000000001000008, 0x9000000000000000b0000000a0000000a000302, 0x10000000000000001000103, 0x400400800c00800e, 0x60000000000000006000000a50000000b000208, 0x9000000000000006e0000007700000063000002, 0x3000000000000014a000000170000000d000800, 0x4000008010008012, 0x3000000000000000d0000014a00000017000007, 0x300000000000000610000006e00000078000200, 0x300000000000000b40000000c00000005000702]
private def bspMeta_7 : ℕ × ℕ × ℕ := (1, 2, 7)

private def bspWords_8 : List ℕ := [0x40000002c00380000, 0x400640000002c0000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x40000000000140000001c, 0x800c00c01e, 0x300000001000200, 0x1700000000000000330000001900000031000200, 0x1000000, 0x400000000001c0000002c, 0x4000000000040001c0000, 0x801400c01a, 0x20000000000000001000107, 0x100000001000200, 0x1000000, 0x400000800c00c01a, 0x200000001000401, 0x15000000000000004d0000001900000049000401, 0x200000000000000060000001400000007000002, 0x40000000000340000005c, 0x400040000, 0x400000c01000c016, 0x10000000000000001000108, 0xc00000001000200, 0x1e0000000400000001000802, 0x80068000000340000, 0x800800800c00c016, 0x1000000010000000c00000002020501, 0x27000000000000008f000000190000009d000605, 0x10000000000000001000003, 0x400400801000c016, 0xb000000000000000c0000008f0000000d000001, 0x9000000000000008f0000004c00000041000300, 0x500000000000000470000000d00000006000103, 0x40000000000400000005c, 0x8008008010008016, 0x10000000000000001000008, 0xc00000000000000410000004d00000048000104, 0x210000000200000001000801, 0x800800c01000c012, 0xc000000000000000c000001d400000019000408, 0xc00000000000000900000009c00000085000004, 0x300000000000000c30000000d00000008000800, 0x400640000002c0000, 0x800c00800c00c016, 0x900000000000001b3000000170000000e000301, 0x10000002700000001000003, 0x10000000000000001000003, 0x800000000001400000028, 0x14022, 0x200000001000400, 0x1000000, 0x1000000, 0x40000000000100000001c, 0x400801001e, 0x300000001000500, 0x10000001500000001000105, 0x1000000, 0x800000000002c00000058, 0x400400800801001a, 0x100000001000600, 0x1000000000000000d0000008f00000007000106, 0x1e000000000000008d000001fe00000085000401, 0x800800800c00c016, 0x840000000000000091000000900000009d000304, 0x27000000030000000200000004060003, 0x45000000000000008f000000a900000084000400]
private def bspMeta_8 : ℕ × ℕ × ℕ := (1, 2, 8)

private def bspWords_9 : List ℕ := [0x1400000000004400000058, 0x1002a, 0x100000001000200, 0x1000000, 0x1000000, 0x400000000001000000020, 0x1400100000, 0xc014014022, 0x30000000000000001000103, 0x300000001000200, 0x1000000, 0x400000044002c0000, 0x8010014022, 0x30000000000000001000201, 0x100000001000300, 0x1000000, 0x100000000000400000005c, 0x4000004008010026, 0x100000001000600, 0x300000000000000060000012c0000000b000406, 0x270000000000000090000000d0000000bb000104, 0x4008008008014022, 0x300000001000603, 0x9000000000000000f0000024900000017000006, 0x1500000000000000a6000000b2000000bd000100, 0x800000000003800000064, 0x400000000004000280000, 0xc01801001e, 0x10000000000000001000106, 0x100000001000200, 0x1000000, 0x800040000, 0x400000801401001e, 0x10000000000000001000201, 0x900000001000300, 0x300000000000000080000001800000007000103, 0x80074000000340000, 0x800c00800c01001e, 0x100000001000703, 0x3000000000000000d000000b400000008000407, 0x10000000000000001000004, 0x40000003800380000, 0x400800c01001001e, 0x1200000000000000400000021f00000037000102, 0x100000001000500, 0x300000000000000600000001b0000000a000205, 0x800800800c01001e, 0x9900000000000000b6000000b5000000c4000100, 0x3000000000000000d0000000400000004000501, 0x9000000000000001e000000690000001c000005, 0x80074000000340000, 0x400000000003400000068, 0x800c00801001001a, 0x100000001000600, 0x3000000000000000b0000024300000019000206, 0x10000000000000001000102, 0x1400100000, 0x800c00c01400c016, 0x30000002700000001000008, 0x30000000000000001000008, 0x10000000000000001000201, 0x400000000004000000068, 0x801000c01000c01a, 0x100000001000200, 0x600000000000000620000005b0000000d000200, 0xf0000000000000249000000a7000000b6000102, 0xc01000c01000c016, 0xc30000001b00000004000801, 0x60000000000000007000001260000000d000008, 0x600000000000000fc0000005b00000061000100, 0x400000000004000280000, 0x400000c01800c01a, 0x30000000000000010000002220000001d000107, 0x100000001000200, 0x300000000000001200000001000000007000702, 0x400000000004c001c0000, 0x400800c01401001a, 0x300000000000000b6000000c3000000a6000201, 0x630000000000000029000000b5000000bf000300, 0x90000000000000061000000520000005a000103, 0x800800801401001a, 0x3000000000000000d0000000d0000000a000200, 0x3600000000000000a5000000c0000000b5000302, 0x3f00000000000000b4000000a5000000bf000003]
private def bspMeta_9 : ℕ × ℕ × ℕ := (1, 2, 8)

private def bspWords_10 : List ℕ := [0x40000003800440000, 0x4007c000000380000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x400000000001400000024, 0xc014014026, 0x300000001000200, 0x5100000000000000df0000005d000000d3000200, 0x1000000, 0x400000000001c00000038, 0x400000000004000340000, 0x1001c014022, 0x20000000000000001000107, 0x100000001000200, 0x1000000, 0x400040000, 0x4004010018014022, 0x20000000000000001000201, 0xf00000001000300, 0x6300000000000000eb000002c7000000d1000103, 0x800800c014014022, 0x200000001000502, 0x1800000000000000700000001f00000069000502, 0x500000000000000dd000000330000000e000003, 0x80080000000340000, 0x400000000004000000074, 0xc00080000, 0x801000c01801001e, 0x10000000000000001000102, 0x600000001000300, 0x10000000000000001000203, 0x800000000004400000070, 0x801000c014010022, 0x100000001000700, 0x3300000000000000ee0000001f000000e3000700, 0x900000000000001650000006700000038000104, 0xc01000c01401001e, 0xf0000000000000077000002a300000068000601, 0x3000000000000000e00000001f000000f1000706, 0x60000000000000138000000380000003b000100, 0x400000000004c00000074, 0xc01000c01800c01e, 0x10000000000000001000009, 0x1e00000000000000d0000000ee000000e1000105, 0x2a0000000200000001000901, 0xc01001001801001a, 0xf000000000000000f000002d00000001f000509, 0xf00000000000000e1000000f0000000d3000005, 0x600000000000002700000002000000013000900, 0x400000000004000340000, 0x400401001c01001e, 0x10000002a00000001000008, 0x100000001000200, 0x360000000500000001000802, 0x4002c000000140000, 0x800c00c01801001e, 0x249000000290000001e00000034090201, 0x1200000000000000ce0000007000000077000302, 0x30000000000000001000003, 0x800800c01c00c022, 0x3600000000000002c4000000d0000000df000001, 0xc00000000000000cd0000015000000077000300, 0x90000000000000011000000220000000f000103, 0x4007c000000380000, 0xc01400c01401001e, 0xc00000000000002a60000001d00000011000301, 0x10000003000000001000003, 0x10000000000000001000003, 0x1400000000003800000064, 0x1802e, 0x100000001000400, 0x1000000, 0x1000000, 0x400000000001400000024, 0x800000000002000000034, 0x800c01402a, 0x200000001000600, 0x30000008400000005000206, 0x1000000, 0x4008008010014026, 0x300000001000601, 0x10000001b00000001000006, 0x900000000000000370000008100000035000400, 0x400000000001c00000038, 0x40000004400380000, 0x800c00c014014022, 0x200000001000001, 0x10000000000000001000001, 0x5400000000000000de00000303000000d3000502, 0x40040000000200000, 0xc01000c010014022, 0x300000000200000001000801, 0x20000000000000010000000e000000009000308, 0x20000000000000001000003, 0x800c008014014022, 0xc000000000000001c0000000e0000000f000001, 0x30000000000000150000000eb00000068000300, 0xae00000000000000de000002cd000000df000103, 0xc01000c01401001e, 0xd200000000000000e2000000e1000000f1000304, 0x18000000030000000100000002060003, 0x4200000000000000700000010000000069000400]
private def bspMeta_10 : ℕ × ℕ × ℕ := (1, 2, 9)

private def bspWords_11 : List ℕ := [0x800000000001800000024, 0x18036, 0x300000001000200, 0x1000000, 0x1000000, 0x1000000000004000000074, 0x400000000005800280000, 0xc02001802e, 0x10000000000000001000103, 0x100000001000200, 0x1000000, 0x1400000000004400000070, 0x800c018032, 0x100000001000500, 0x200000000000000110000011a00000009000305, 0x1000000, 0x40000005000380000, 0x400000c01801802e, 0x10000000000000001000302, 0x100000001000100, 0x5700000000000000820000008c00000083000201, 0x800800801001802e, 0x100000001000603, 0x9000000000000000f0000034b0000001c000106, 0x3000000000000000d000000100000000e000001, 0x400000000001c00000028, 0x400000000004c00340000, 0x1002001002a, 0x30000000000000001000106, 0x100000001000200, 0x1000000, 0x40000004400440000, 0x400000000001400000028, 0x400401001801802a, 0x30000000000000001000002, 0x100000001000401, 0x6900000000000001190000011b000000fd000204, 0x800801001801002a, 0x30000000000000001000302, 0x10000000000000001000103, 0x900000000000000130000003900000011000200, 0x400000000001400000028, 0x800c00801401802a, 0x300000001000700, 0x6000000000000000d0000034e0000001d000407, 0x1500000000000000590000006600000055000104, 0xc01000c01401002a, 0x300000001000003, 0x40000000000000097000000870000000a000003, 0x27000000000000005a0000013200000055000100, 0x1800140000, 0x40030000000180000, 0x400000000004000000080, 0xc01001001c014022, 0x100000001000200, 0x30000000000000001000200, 0x30000000000000001000102, 0x8008c000000400000, 0xc01401001c01001e, 0x30000003000000001000309, 0x30000000000000001000309, 0x10000000000000001000001, 0xc010010020010022, 0x300000000000000130000033000000023000009, 0x300000000000000fd0000011000000120000100, 0x300000000000000d80000000900000004000901, 0x80000000000440000007c, 0x400401001c014026, 0x10000000000000001000008, 0x30000000000000001000201, 0x300000000000001080000002700000007000803, 0x400000000004000400000, 0x8008014020014022, 0x100000000000000040000004800000003000209, 0x10000000000000001000002, 0x900000000000003570000002600000011000901, 0x800c00c020014022, 0x200000000000000080000000300000003000200, 0xd000000000000002a0000008e0000002d000102, 0x51000000000000008f0000009000000080000001, 0x80000000000500000007c, 0x40000004400440000, 0x8010010018010026, 0x10000000000000001000102, 0x100000001000300, 0x300000000000000330000003600000013000203, 0x40000005000380000, 0x801400c018010026, 0x100000001000802, 0x10000000000000001000008, 0x1500000000000001030000033000000121000104, 0xc01400c014014026, 0x3000000000000035a0000001f0000000e000800, 0x200000000000000080000009700000005000408, 0xc00000000000000770000019500000095000004, 0x400000000004000000080, 0xc01400c018014022, 0x100000001000700, 0x3000000000000000e000003840000001f000107, 0x1e00000000000002fd0000010f0000011e000201, 0x400000000004c00000080, 0xc018010018010022, 0x100000001000100, 0xf00000000000001210000011000000020000100, 0x900000000000001b00000007f00000088000301, 0x1001801001801001e, 0x1200000002100000005000803, 0xf00000000000000110000036300000020000008, 0xf00000000000002fd000001100000011f000300]
private def bspMeta_11 : ℕ × ℕ × ℕ := (1, 2, 8)

private def bspWords_12 : List ℕ := [0x40000004400500000, 0x40094000000440000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x800000000002c00000040, 0xc020014032, 0x200000001000200, 0x3000000000000002b0000001700000029000200, 0x1000000, 0x800000000004400000088, 0x400000000004c00400000, 0x400001402401802a, 0x10000000000000001000107, 0x100000001000200, 0x2a0000000400000001000702, 0x400040000, 0x40028000000140000, 0xc01001402001802a, 0x10000000000000001000302, 0x120000000000000001000103, 0x400000001000200, 0x40000000000180000002c, 0x800801402001802e, 0x30000000000000001000003, 0x1200000001000502, 0x63000000000000009300000165000000a0000305, 0x800c01402001802a, 0x300000000000000120000000500000005000103, 0x1200000000000000870000009900000028000001, 0xab0000000000000151000003f900000131000300, 0x40034000000180000, 0xc01401001c01802a, 0x100000001000603, 0x3900000000000001430000002500000132000603, 0x30000000000000001000006, 0x40000000000180000002c, 0x800c01001c01802e, 0x30000000000000001000002, 0x8400000000000001550000006f0000016a000701, 0x500000000000000950000001400000009000205, 0xc01000c02001802a, 0xd00000000000000330000015400000013000102, 0x24000000000000012c000001500000006b000001, 0x800000000000001400000003c00000011000200, 0x800980000004c0000, 0x400000000004c0000008c, 0x1001801001c014026, 0x10000000000000001000001, 0x3900000000000001430000002500000157000504, 0x10000000000000001000102, 0x40000000000580000008c, 0x10018010020010026, 0x10000000000000001000009, 0x9000000000000004c0000005500000051000105, 0x330000000200000001000901, 0x10018014020014022, 0x1200000000000000120000040200000025000509, 0x1200000000000001440000015600000133000005, 0x300000000000001c8000000130000000b000900, 0x400000000004c00400000, 0x800c014024014026, 0x10000003300000001000008, 0x100000001000200, 0x3000000000000042f0000002900000011000802, 0x400040000, 0x40034000000180000, 0xc014014020014026, 0x330000000300000002000000040a0302, 0x1200000001000401, 0x30000000000000001000004, 0xc01001002401002a, 0x2100000000000001fb00000098000000a1000002, 0x1b000000000000012d000003c900000154000400, 0x6000000000000000a0000000a00000009000204, 0x400000000002800000044, 0xc01400c02001402a, 0x20000000000000001000001, 0x4800000000000001300000015400000143000403, 0xd00000000000001540000001300000011000104, 0xc014010020014026, 0x1100000000000000120000014300000013000301, 0xf0000000000000143000000a900000098000003, 0x800000000000000a10000001300000009000100, 0x40094000000440000, 0x1001c01001c014026, 0x300000000000000c30000000700000004000301, 0x10000003900000001000003, 0x10000000000000001000003, 0x800000000001400000028, 0x1000000000001c00000038, 0x24042, 0x200000001000500, 0x1000000, 0x1000000, 0x401002003a, 0x300000001000501, 0x10000002100000001000005, 0x1000000, 0x400000000001000000020, 0x140000000000440000007c, 0x801401c036, 0x100000001000600, 0x30000003f00000002000206, 0x1000000, 0x40000005c00380000, 0x800800c01c01c032, 0x40000000000000001000205, 0x100000001000100, 0x36000000000000013b0000018f00000121000501, 0x800c00c01401c032, 0x400000001000702, 0x30000000000000012000003bd0000001f000107, 0xd8000000000000013c000001510000013d000001, 0x40000000000180000002c, 0x40034000000180000, 0xc01400c01801802e, 0x300000001000701, 0x20000001e00000001000207, 0x30000000000000001000002, 0x801001001801802e, 0x9c0000000000000399000001410000016a000005, 0x1b0000000000000169000000e400000050000200, 0x3000000000000001c0000007900000018000502, 0x800000000004400000088, 0x800980000004c0000, 0x1001801001801802a, 0x100000001000801, 0x30000000000000013000001430000000b000208, 0x10000000000000001000002, 0xc01400c01c01802a, 0xd500000000000001320000014300000169000006, 0x900000000000003c90000015100000130000200, 0x9c00000000000001410000043e00000133000602, 0x1001801001c014026, 0x13200000000000001450000014400000157000405, 0x39000000030000000200000004070004, 0xd500000000000001430000016900000132000500]
private def bspMeta_12 : ℕ × ℕ × ℕ := (1, 2, 9)

private def bspWords_13 : List ℕ := [0x1c00000000005800000080, 0xc00000000001800000028, 0x2404a, 0x300000001000300, 0x1000000, 0x1000000, 0x401001c042, 0x100000001000301, 0x10000000000000008000000bc00000005000003, 0x1000000, 0x1400000000005c00000088, 0x8000000000068002c0000, 0x1002c01803a, 0x10000000000000001000105, 0x100000001000200, 0x1000000, 0x40000006800380000, 0xc02001803a, 0x10000000000000001000201, 0x100000001000300, 0x1000000, 0x800000000001c0000002c, 0x800800801401c03e, 0x300000001000600, 0x90000000000000011000004b600000020000406, 0x2a00000000000000a1000000cf000000be000104, 0x801000c01401803a, 0x100000001000603, 0x40000000000000014000001890000000b000006, 0x1100000000000000750000017200000080000100, 0x400000000001800000030, 0x400000000005800400000, 0x1402801c032, 0x30000000000000001000106, 0x100000001000200, 0x1000000, 0x40000005000500000, 0x100000000000580000008c, 0x8008014020018036, 0x10000000000000001000002, 0x100000001000401, 0x3f00000000000000730000008a0000007c000204, 0x800c01402001c032, 0x30000000000000001000302, 0x10000000000000001000103, 0x12900000000000001730000018a00000176000200, 0x400380000001c0000, 0x1001801001801c032, 0x300000001000703, 0x30000003f00000001000007, 0x30000000000000001000007, 0x1000000000004c0000008c, 0xc01000c01801c036, 0x10000000000000001000002, 0x600000000000000090000026700000011000508, 0x300000000000000210000002c00000026000205, 0xc01400c02001c032, 0x2100000000000000b40000003f00000046000102, 0x100000000000000120000003800000011000001, 0x900000000000000190000001c00000018000200, 0x400380000001c0000, 0x2000140000, 0x400000000004c00000098, 0x1001801002401802a, 0x100000001000100, 0x30000000000000001000100, 0x30000000000000001000201, 0x400a0000000440000, 0x10020010024014026, 0x15000001a100000008000209, 0x30000000000000001000209, 0x10000000000000001000001, 0x800a40000004c0000, 0x1001c014024014026, 0x150000000000000015000004b30000002800010a, 0x1500000000000001670000017c0000018f000201, 0x10000000000000001000002, 0x1001801402801402a, 0x30000000000000016000004740000002900000a, 0x300000000000001660000017c0000018f000200, 0xf00000000000004ad0000002a00000013000a02, 0x800000000005000000094, 0x40000005000500000, 0x1001801402001802e, 0x10000000000000001000102, 0x100000001000400, 0x3000000030000000300000002030204, 0x40000005c00440000, 0x1001801002001802e, 0x100000001000902, 0x10000000000000001000009, 0xb00000000000000150000004600000014000105, 0xc01c01001c01802e, 0x300000000000004a70000002500000011000900, 0x500000000000000130000017a0000000c000509, 0x1d0000000000000084000001630000007e000005, 0x400000000004c00000098, 0x1001c01002001802a, 0x100000001000800, 0x30000000000000011000004a700000025000108, 0x1a000000000000017b0000007700000084000201, 0x14020014020014026, 0x1a10000002700000005000802, 0x9000000000000000a0000023a00000013000008, 0xd000000000000017c0000007800000085000200, 0x400000000004c004c0000, 0x1400b0000000580000, 0xc01001802801802a, 0x500000000000000130000018f0000000e000208, 0x100000001000301, 0x10000000000000001000003, 0x400401802801802e, 0x30000000000000005000001290000000b000008, 0xa00000000000000d10000003900000042000300, 0x100000000000001b00000002f00000006000803, 0x400000000006400340000, 0x800000000005000000094, 0xc01001002801802e, 0x10000000000000001000002, 0x100000001000401, 0xa0000000000000042000000d100000039000204, 0xc01401002801802a, 0x500000000000000130000000700000007000302, 0x1f00000000000000770000018b0000007e000003, 0xf9000000000000018d0000018f00000169000200, 0x1c00180000, 0xc01401402401802e, 0x1f000000000000018b0000007e00000077000301, 0x300000001000400, 0x130000000000000084000001610000007e000104, 0x400000000001c00000030, 0xc014014020018032, 0x30000000000000001000001, 0xb00000000000000460000003c00000015000504, 0x2900000000000000c6000000c70000003c000105, 0xc01401002401802e, 0x71000000000000017b0000017a00000085000401, 0xf000000000000017a0000018900000077000004, 0x3500000000000000bc000000c70000003f000100]
private def bspMeta_13 : ℕ × ℕ × ℕ := (1, 2, 9)

private def bspWords_14 : List ℕ := [0x400000050005c0000, 0x400ac000000500000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x1000000000004c00000098, 0x400000000002400100000, 0x1403402003a, 0x10000000000000001000106, 0x300000001000400, 0x1000000, 0x1c0000000000640000008c, 0x1002c01c046, 0x100000001000400, 0x2400000000000001b300000080000001a9000400, 0x1000000, 0x400000000006400400000, 0x1402c02003a, 0x10000000000000001000302, 0x100000001000100, 0x1000000, 0x1400000000005000000094, 0x400401002802003e, 0x100000001000600, 0x6600000000000001b10000006b00000190000600, 0x7e000000000000018b000001d8000001a9000102, 0x800c01402402003a, 0x100000001000604, 0x9900000000000001a20000002b0000018f000604, 0xbd00000000000001c3000001c50000019f000100, 0x1000b80000005c0000, 0x400000000002800000050, 0x400000000001c00000034, 0x1001801402401c036, 0x300000001000500, 0x6f00000000000001b700000081000001a5000500, 0x10000000000000001000203, 0x400040000, 0x1001801802801c032, 0x20000000000000001000203, 0x1500000001000100, 0x10000000000000001000301, 0x4003c0000001c0000, 0x1001c01402401c032, 0x200000001000703, 0x2100000000000000dc0000002b000000d2000703, 0x30000000000000001000002, 0x1001801002801c032, 0x8000000000000001e000000e60000000b000001, 0x1500000000000000cf000000e400000049000200, 0xb00000000000001b50000004500000014000102, 0x4000000000058000000a4, 0x400040000, 0x400000000006400400000, 0x1001801402c01802e, 0x1000000000000000100020a, 0x100000001000300, 0x10000000000000001000403, 0x1001c01802801802e, 0x10000000000000001000200, 0x1500000001000301, 0x3000000000000002e000000530000002c000003, 0x400580000002c0000, 0x1402001402401802e, 0x1000000010000001500000002020601, 0x4200000000000001b80000002b000001cf000706, 0x20000000000000001000003, 0x800000000005c000000a0, 0x1001c010028018032, 0x10000000000000001000002, 0x1500000000000000d1000000e60000006e000401, 0x400000000000000730000000b00000005000204, 0xc02001402801802e, 0xa0000000000000015000000dc0000000b000102, 0x1200000000000000dc000001ca000000d1000001, 0x200000000000001d00000001400000015000200, 0x4000000000070000000a4, 0x4000000000064000000a4, 0x1402001402801402e, 0x1000000000000000100000a, 0x2a00000000000001a2000001cc000001b9000206, 0x3c0000000200000001000a02, 0x1402001802801802a, 0x300000000000000030000002d0000000400010a, 0x1500000000000001b9000001ce000001a5000006, 0x600000000000004e60000002c00000019000a00, 0x1402001802801802a, 0x1500000000000000150000056a0000002b000509, 0x2a00000000000001b9000001e300000191000005, 0x300000000000001290000000b00000007000900, 0x800000000005c00440000, 0x1000000000006400000098, 0x1803001803a, 0x10000000000000001000008, 0x100000001000301, 0x1000000, 0x8008018030018032, 0x10000003900000001000108, 0x10000000000000001000108, 0x330000000200000001000800, 0x4000000000058004c0000, 0x400000000001c00000034, 0x800c01802c01c036, 0x30000000000000001000002, 0x100000001000401, 0x1b00000000000001db000001c60000018f000204, 0xc01001802c018032, 0x39000000030000000200000004090302, 0x10000000000000001000103, 0x6000000000000000c000000240000000b000200, 0x400000000001c00000034, 0x400040000, 0xc01001802801c036, 0x30000000000000001000102, 0x1500000001000500, 0x60000000000000098000000a000000085000205, 0xc01401402401c036, 0xb0000000000000014000001b500000017000400, 0xb100000000000001e3000001a2000001b5000504, 0x300000000000001c80000001700000013000005, 0xc014018028014036, 0x3900000000000001c900000187000001cc000301, 0xe700000000000005a9000001a4000001b5000003, 0x10500000000000001c900000561000001a3000100, 0x400ac000000500000, 0x1402401402401802e, 0x12000000000000052e0000002900000017000301, 0x10000004200000001000003, 0x10000000000000001000003, 0x1c00000000004c0000008c, 0xc0000000000180000002c, 0x2804e, 0x300000001000500, 0x1000000, 0x1000000, 0x8010024046, 0x100000001000501, 0x30000000000000015000001a70000000b000005, 0x1000000, 0x1000000000004c00000098, 0x1400bc000000580000, 0x800000064004c0000, 0xc01401002002003a, 0x100000001000002, 0x10000000000000001000002, 0x10000000000000001000100, 0x400000000000c00000018, 0xc01400c018024042, 0x600000001000800, 0x40000010200000007000408, 0x10000000000000001000204, 0x1400000000005000000094, 0xc01400c01c02003e, 0x100000001000900, 0x30000002400000001000109, 0x80000000000000048000001e100000045000201, 0x1001801001c02003a, 0x450000000200000001000902, 0x600000000000000150000051c00000025000009, 0x33000000000000008a000000a100000091000200, 0x400000000000c00000018, 0x400000c01c024042, 0x60000000000000001000005, 0xc00000000000001e0000001ad00000199000301, 0xe400000000000001ba0000023c0000017b000503, 0x1400000000005000000094, 0x800801002002003e, 0x10000000000000001000006, 0x800000000000001e10000004500000048000102, 0x1d000000000000004b000002260000003f000601, 0x801401402401803e, 0x5400000000000001be00000185000001fb000206, 0x6c00000000000001e2000001a1000001b1000002, 0x1200000000000001c5000001e700000190000600, 0x400000000001c00000034, 0x40000006800440000, 0x1001801002401c036, 0x30000000000000001000105, 0x100000001000200, 0x900000000000001b5000001fa0000018f000502, 0xc01c01002001c036, 0x300000001000701, 0x10000004500000002000207, 0x7b00000000000001c80000019b000001b5000002, 0x400000000002800000050, 0x400580000002c0000, 0x1402001402001c032, 0x200000001000801, 0x40000000000000016000001b80000000d000208, 0x20000000000000001000002, 0x1001c01002401c032, 0x4e00000000000000d20000006e00000079000006, 0x60000000000000294000001c9000000d1000200, 0xf600000000000001b6000005af000001a5000602, 0x1402001402401802e, 0x1a400000000000001ba000001b9000001cf000405, 0x21000000030000000100000002070004, 0x4e000000000000006e000000f200000069000500]
private def bspMeta_14 : ℕ × ℕ × ℕ := (1, 2, 10)

private def bspWords_15 : List ℕ := [0x2000000000005c00000094, 0x2800000000004c0000008c, 0x2c056, 0x100000001000300, 0x1000000, 0x1000000, 0x801402404e, 0x100000001000301, 0x3000000cf00000005000003, 0x1000000, 0x800000000002400000034, 0x800000000007400380000, 0x1403401c046, 0x30000000000000001000105, 0x100000001000200, 0x1000000, 0x40000007400440000, 0x1002801c046, 0x30000000000000001000201, 0x100000001000300, 0x1000000, 0x1c00000000006400000098, 0x800c00c01802004a, 0x100000001000600, 0x900000000000000160000060600000025000406, 0xf00000000000000e70000010f000000f4000104, 0x800000000001c00000034, 0x801400c01c024046, 0x300000001000700, 0x6000000000000000a0000032100000013000107, 0x5100000000000001d7000001ec000001fd000201, 0xc01400c02001c046, 0x300000001000004, 0x30000000000000114000001020000000d000004, 0x15900000000000001ef0000061b000001f0000200, 0x10000000000070000000a4, 0x4000000000064004c0000, 0x1803001803e, 0x10000000000000001000106, 0x100000001000200, 0x1000000, 0x40000006800500000, 0x1400c8000000580000, 0xc01801402801803e, 0x10000000000000001000302, 0x10000000000000001000103, 0x100000001000200, 0x400000000001000000020, 0x800c014028024042, 0x50000000000000001000003, 0x100000001000502, 0xf000000000000001d000000660000001f000305, 0x10000000000058000000a4, 0x801001802802003e, 0x10000000000000001000004, 0x3000000000000008a000000170000001a000102, 0xf000000000000006c000002090000005c000401, 0xc01401403001803e, 0x750000000000000207000001de000001f4000204, 0x2d00000000000000ec000000fa00000105000002, 0x11100000000000002090000020b000001e1000400, 0x40040000000180000, 0x800000070004c0000, 0xc02001002401803e, 0x100000001000804, 0x10000000000000001000008, 0x30000000000000001000100, 0xc02000c02002003e, 0x6000000000000061e0000002900000013000800, 0x30000000000000012000002280000000d000508, 0x30000000000000001000105, 0x400000000001000000020, 0xc014010020024042, 0x50000000000000001000002, 0x300000000000000f90000010e0000004d000501, 0x10b00000000000001bf0000066c00000206000205, 0x1001801002402003e, 0x3f00000000000002f100000106000000ee000102, 0x900000000000000760000004b0000001a000001, 0xf00000000000000320000011300000030000200, 0x400400000001c0000, 0x800000000005c000000ac, 0x40000005c005c0000, 0x1002001802801c036, 0x10000000000000001000102, 0x100000001000200, 0x30000000000000001000200, 0x400000000001c00000038, 0x1002001002402003a, 0x300000001000800, 0x600000000000000130000069000000029000408, 0x30000000000000001000304, 0x40000006800500000, 0x1402001402801c036, 0x100000001000903, 0x10000000000000001000009, 0x6300000000000000a800000228000000a1000201, 0x1002401402401c036, 0x3000000000000062a0000002b00000014000900, 0x3000000000000000b000000fc00000007000109, 0x2100000000000000af000001de000000a8000001, 0x4000000000058000000b0, 0x20001c0000, 0x1002001802c01c032, 0x10000000000000001000109, 0x300000001000200, 0x30000000000000001000302, 0x400b8000000440000, 0x1002801402801c032, 0x100000001000902, 0x300000000000000140000062a0000002b000309, 0x10000000000000001000003, 0x800040000, 0x8000000000068000000ac, 0x10024018028018036, 0x10000000000000001000003, 0x3f0000000000000017000005ee0000006d000501, 0x300000000000000630000001e1000001f9000305, 0x1402401802801c032, 0x1800000000000000fd00000339000000e5000203, 0x4200000000000000170000063300000070000001, 0x2a00000000000005a9000001f90000020e000300, 0x1402401802801c032, 0x3000000000000000b000000a500000008000100, 0x300000000000000150000001600000017000401, 0x2400000000000005eb0000005b0000006d000004, 0x400b80000005c0000, 0x1802801802801802e, 0x180000002d00000001000809, 0x150000000000000017000005ee0000002c000108, 0x10000000000000001000001, 0x800bc000000580000, 0x4000000000070000000b0, 0x1402401402c014032, 0x1000000000000000100000b, 0x2d00000000000001e300000210000001fa000302, 0x10000000000000001000103, 0x1402401802c01802e, 0xc000000000000000c000002f70000001700020b, 0x1500000000000000fd00000112000000e6000002, 0x900000000000005ac0000002f0000001c000b00, 0x14020018030018032, 0x30000000000000019000005ee0000002f00000a, 0x300000000000001e1000001fa00000210000200, 0x90000000000000318000000180000000b000a02, 0x400000000005800580000, 0x40028000000140000, 0x1001801c03001c032, 0x3000000000000000b0000011300000008000208, 0x10000000000000001000102, 0x500000001000800, 0x400000000002000000038, 0x800c01c03001c03a, 0x30000000000000001000009, 0x100000001000402, 0xc00000000000005c1000000350000001c000904, 0xc01001403401c036, 0x300000000000000170000013b0000000a000109, 0x21000000000000011d0000020600000064000001, 0x100000000000000820000000d00000002000900, 0x400000000001c00000038, 0x1000c40000005c0000, 0x1001c01402802003a, 0x30000000000000001000100, 0x2700000000000000fb0000032d000000e6000403, 0x10000000000000001000004, 0xc01401402c02003a, 0x30000000000000001000102, 0x9000000000000001f500000219000001c7000400, 0x21000000000000002b000000320000002e000204, 0x800000000005c000000ac, 0x400000000007000400000, 0x1001801403001c036, 0x10000000000000001000103, 0x10000000000000001000004, 0x2d00000000000000af000002260000009a000302, 0x1001c01402c01c036, 0x8d00000000000006240000020f000001c4000400, 0x1b00000000000001dd000001f8000000af000204, 0x300000000000000190000004400000018000002, 0x1001c018030014036, 0x570000000000000630000001e5000001fa000302, 0x1b00000000000001df000005e80000020f000003, 0xb1000000000000010700000108000000f2000200]
private def bspMeta_15 : ℕ × ℕ × ℕ := (1, 2, 11)

private def bspWords_16 : List ℕ := [0x40000005c00680000, 0x400c40000005c0000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x400000000001c0000002c, 0x800000000007400440000, 0x400401803801c042, 0x40000000000000001000106, 0x100000001000400, 0xb0200000000000017700000003b00000fa0000604, 0x40000000000140000001c, 0x400801403001c04a, 0x600000001000400, 0x1600000000000000640000007a00000061000400, 0x16600000000000000c80000001d00000834000105, 0x400000000007c00400000, 0xc01001403401c042, 0x40000000000000001000302, 0x100000001000100, 0x100000000000000070000003100000008000201, 0x14000000000074000000ac, 0xc01401403001c046, 0x100000001000600, 0x6000000000000025c0000007a00000245000600, 0x2e00000000000000550000023200000063000102, 0x1001801802c01c042, 0x400000001000604, 0x2d00000000000000950000003100000091000604, 0xf600000000000002010000023700000257000100, 0x80068000000340000, 0x800000000005c000000b8, 0x40000000000240000003c, 0x1402001802c01c03e, 0x300000001000500, 0x2b00000000000000c700000031000000c1000500, 0x20000000000000001000203, 0x400040000, 0x1402001c03002003a, 0x10000000000000001000203, 0x1800000001000100, 0x20000000000000001000301, 0x800c80000004c0000, 0x1002801802c02003a, 0x100000001000703, 0x4b000000000000023f0000003100000228000703, 0x10000000000000001000007, 0x40044000000200000, 0x1402401802c02003a, 0x1000000010000001b00000002040102, 0x2b0000000000000224000000c7000000c1000301, 0x30000000000000001000003, 0x1402001803002003a, 0x1300000000000000450000025600000019000002, 0x700000000000000bf000000c60000003d000300, 0x3000000000000005b0000000d00000004000203, 0x4000000000064000000bc, 0x400040000, 0x4000000000070004c0000, 0x1402001803401c036, 0x1000000000000000100020a, 0x100000001000300, 0x20000000000000001000403, 0x1402401c03001c036, 0x10000000000000001000200, 0x1800000001000301, 0x210000000000000256000002230000023f000003, 0x800c8000000640000, 0x1802801802c01c036, 0x1000000010000001800000002020601, 0x4b000000000000023f0000003100000259000706, 0x10000000000000001000003, 0x40000000000340000005c, 0x1402401403001c03a, 0x20000000000000001000002, 0x600000000000000226000002560000023f000401, 0x1300000000000002560000001900000017000204, 0x1002801803001c036, 0x1700000000000000180000023f00000019000102, 0x15000000000000023f0000012a00000113000001, 0x1000000000000012d000000170000000c000200, 0x4000000000070000000bc, 0x18028018030018036, 0x10000000000000001000009, 0x1800000000000001130000012b00000120000105, 0x450000000200000001000901, 0x1802801c03001c032, 0x1800000000000000180000070800000031000509, 0x1800000000000002400000025800000229000005, 0x30000000000000339000000190000000e000900, 0x800000000007400440000, 0x40000000000240000003c, 0xc01001803801c03e, 0x30000000000000001000008, 0x100000001000301, 0x3c0000000800000001000803, 0x1001801803801c03a, 0x10000002100000001000208, 0x10000000000000001000102, 0x3f0000000600000001000800, 0x4000000000070004c0000, 0x1001801803402003a, 0x6000000000000023f0000012b00000111000201, 0x100000001000300, 0x2700000000000000870000023700000092000103, 0x1001c01403001c03e, 0x33000000000000024f000001110000011e000200, 0x12000000000000011e0000009800000041000302, 0x1e00000000000000880000023900000093000003, 0x400c40000005c0000, 0x1802c01802c01c036, 0x1500000000000006c30000002f0000001a000301, 0x10000004b00000001000003, 0x10000000000000001000003, 0x800000000001c00000038, 0x40000008c00380000, 0x1c000000000058000000a4, 0x400800c02c02804e, 0x10000000000000001000004, 0x100000001000501, 0x1b5a00000000000007d00000015f000061a8000405, 0x800c01002802804a, 0x30000000000000001000204, 0x3c000000000000004d0000023300000245000001, 0xdb0000000000000245000002bd000001f9000400, 0x800000000001400000028, 0x40000002000140000, 0x400c00c02002c052, 0x400000001000001, 0x40000000000000001000001, 0x1e200000000000003e80000005b00001b58000206, 0x2800000000004c00000098, 0x400c00401403005a, 0x100000001000800, 0x2000000000000000100001d4c00000064000708, 0x3ee00000000000007d00000003500000fa0000107, 0x801000801c02c052, 0x540000000800000001000801, 0x10000005700000002000008, 0xf0000000000000227000000a000000085000100, 0x1c000000000058000000a4, 0x801400c02002804e, 0x100000001000700, 0x20000002a00000001000107, 0xf000000000000001d000000690000001c000201, 0x1001801002002804a, 0x300000001000703, 0x300000000000000170000069f00000029000007, 0x39000000000000021c0000023700000245000200, 0x800000000002c00000058, 0x1000d00000005c0000, 0x400000038002c0000, 0x10020014028024042, 0x200000001000002, 0x20000000000000001000002, 0x10000000000000001000100, 0x1400000000005c000000ac, 0x10020010024024046, 0x100000001000800, 0x30000005100000002000408, 0x10000000000000001000204, 0x14020014024024042, 0x4e0000000400000001000801, 0x90000000000000018000006b10000002b000008, 0x2a00000000000000b6000000680000005f000100, 0x40000007400500000, 0x1400000000005c000000ac, 0xc01401402c024046, 0x10000000000000001000006, 0x100000001000401, 0x50000000000000031000000a90000002a000604, 0xc01c01402c024042, 0x600000000000000100000001200000013000206, 0x1000000010000000100000002010002, 0x60000000000000024f0000027400000211000600, 0x10018014024020046, 0x39000000000000024d0000022200000239000100, 0x700000000000000590000001a0000001b000301, 0x2700000000000000bd0000026d000000b6000003, 0x40000000000200000003c, 0x40044000000200000, 0x1402401402802003e, 0x300000001000701, 0x10000002700000001000207, 0x30000000000000001000002, 0x400000068005c0000, 0x1402001802c02003e, 0x162000000000000067b0000023d00000272000106, 0x100000001000300, 0x15000000000000008f0000014500000084000603, 0x400000000001c0000002c, 0x1402001802801c042, 0x40000000000000001000001, 0x930000000000000271000003390000011e000402, 0x8a000000000000011e0000027000000113000104, 0x1002401402c02003e, 0x1f200000000000006ba0000023d00000257000201, 0x12000000000000023c000001cb00000083000002, 0xc000000000000008a0000023d00000095000100, 0x800000000005c000000b8, 0x800c8000000640000, 0x1802801802802003a, 0x100000001000801, 0x100000000000000050000007300000003000208, 0x10000000000000001000002, 0x1402401402c02003a, 0x1ad00000000000002280000023f00000271000006, 0x30000000000000159000000770000006e000200, 0x162000000000000023d0000075600000229000602, 0x1802801802c01c036, 0x22800000000000002410000024000000259000405, 0x4b000000030000000200000004070004, 0x1ad000000000000023f0000027100000228000500]
private def bspMeta_16 : ℕ × ℕ × ℕ := (698, 2000, 10)

private def bspWords_17 : List ℕ := [0x80000000000200000003c, 0x800000088004c0000, 0x400000074005c0000, 0x800801803002804e, 0x30000000000000001000203, 0x100000001000300, 0x33b000000000000001f00000000000007d0000300, 0x20000000000074000000ac, 0x800801002c024056, 0x10000000000000001000001, 0x100000001000402, 0x33b000000000000001f00000000000007d0000402, 0x801401002c02804e, 0x30000000000000001000301, 0x10000000000000001000203, 0x4e000000000000012e0000015b0000013f000100, 0xc00000000002000000038, 0x401000401802c05a, 0x300000001000400, 0x11000000000000000100001e7800000064000304, 0x29f00000000000007d0000000a300002ee0000103, 0x1400e0000000640000, 0x1002001002002804e, 0x300000001000503, 0x10000005700000001000005, 0x10000000000000001000005, 0x2000000000005c000000ac, 0xc01400c02002c056, 0x10000000000000001000003, 0x2000000000000000b0000014600000007000206, 0x9000000000000025a0000081900000274000302, 0x10018010024028052, 0x2d0000000000000291000002650000027e000103, 0x3300000000000002b80000027b00000263000001, 0x1b00000000000000cb000000e8000000d3000300, 0x10000000000064000000bc, 0x800000000008000440000, 0x800801803c024046, 0x10000000000000001000105, 0x100000001000200, 0x33b000000000000001f00000000000007d0000302, 0x2c00180000, 0x8004c000000240000, 0x1001c014034024046, 0x10000000000000001000302, 0x300000001000001, 0x30000000000000001000001, 0x1400000000005c000000b8, 0xc01001403402804a, 0x10000000000000001000003, 0x3000000030000000300000002020501, 0x6000000000000000f0000002d0000000e000305, 0xc01401c034024046, 0x4e00000000000007890000029c00000263000103, 0x5d00000000000002bb000007020000029b000001, 0x8d00000000000000e6000000d3000000cf000300, 0x1000dc000000680000, 0x80000007000640000, 0x1402401802c024046, 0x10000000000000001000402, 0x100000001000100, 0x10000000000000001000100, 0x1400000000005c000000b8, 0x1402401002802804a, 0x100000001000800, 0x10000000000000007000000dd00000005000608, 0x10000000000000001000206, 0x14024018028024046, 0x100000001000805, 0x3000000000000001b000007470000002e000008, 0x10b0000000000000284000002bd0000026d000100, 0x1400000000005c000000b8, 0xc01c01002c02804a, 0x10000000000000001000002, 0x1800000000000007890000029600000269000501, 0x1600000000000000dd000000ca00000047000205, 0x1002001802c024046, 0xcc000000000000029b0000078f00000268000102, 0x10b00000000000002bd0000026d00000284000001, 0xa500000000000007d10000026300000284000200, 0x1000dc000000680000, 0x8000000000068000000c4, 0x2c00180000, 0x400000000002400000040, 0x14024014034020042, 0x30000000000000001000003, 0x300000001000401, 0x10000000000000001000304, 0x2400200000, 0x1402401c03402003e, 0x10000000000000001000304, 0x30000000000000001000003, 0x10000000000000001000401, 0x1002801403402003e, 0x10000000000000001000300, 0x30000000000000001000203, 0x100000000000000190000001700000008000001, 0x800d4000000580000, 0x40000008000500000, 0x1402c01403002003e, 0x100000001000803, 0x10000000000000001000008, 0x10000000000000001000100, 0x400000000002000000040, 0x1402c01402c024042, 0x300000001000900, 0x60000000000000016000007d70000002f000609, 0x10000000000000001000206, 0x1802c01802c02003e, 0x900000000000008280000003100000014000901, 0x700000000000000190000028800000010000009, 0xb00000000000000360000009b00000038000100, 0x400000000002000000040, 0x400000074005c0000, 0x14024018030024042, 0x30000000000000001000103, 0x100000001000600, 0xcc000000000000078f000002680000029b000306, 0x40048000000240000, 0x1802801402c024042, 0x6f0000000000000288000002a00000026b000301, 0xa800000000000002680000029d00000287000703, 0x30000000000000001000007, 0x10028014030024042, 0x1500000000000000480000001800000019000001, 0xb00000000000000d80000029c000000cf000700, 0x8d000000000000029f0000026900000286000107, 0x1802801803002003e, 0x36000000000000008b0000019500000070000102, 0x25000000000000026b000000d8000000e0000001, 0x3300000000000002880000026d000000e0000200, 0x4000000000064000000c8, 0x2400200000, 0x400000000007000580000, 0x1402401c03802003a, 0x10000000000000001000209, 0x100000001000300, 0x10000000000000001000403, 0x1402801c03402003a, 0x10000000000000001000200, 0x300000001000301, 0xf00000000000001510000013600000144000003, 0x400d0000000500000, 0x1403001803002003a, 0x100000001000802, 0x30000000000000017000007e300000031000308, 0x10000000000000001000003, 0x8000000000074000000c4, 0x1402c01c03001c03e, 0x10000000000000001000002, 0x30000000000000018000000190000001a000401, 0x3600000000000007e90000026e00000289000204, 0x1802c01c03002003a, 0x1b00000000000001450000041a0000012a000102, 0x15000000000000009c000000a9000000a4000001, 0x30000000000000075000000289000002a1000200, 0x400d0000000680000, 0x1c03001c03001c036, 0x1b0000003300000001000708, 0xc000000000000000d000003cf00000019000107, 0x10000000000000001000001, 0x800d4000000640000, 0x400000000007c000000c8, 0x1802c01803401803a, 0x1000000000000000100000a, 0x330000000000000270000002a30000028a000302, 0x10000000000000001000103, 0x1802c01c03401c036, 0x1b000000000000001b0000079e0000003400020a, 0x1800000000000001450000015d0000012b000002, 0x90000000000000753000000350000001f000a00, 0x1802801c03801c03a, 0x3000000000000001c0000079e00000035000009, 0x3000000000000026e0000028a000002a3000200, 0x1500000000000007e90000003600000019000902, 0x800000000007400500000, 0x8004c000000240000, 0x1001c01c03c01c03e, 0x6000000000000001d0000079500000037000207, 0x10000000000000001000102, 0x300000001000700, 0x1c00e8000000740000, 0x1001801c03c01c042, 0x3000000000000001e0000028200000013000108, 0x100000001000402, 0x10000000000000001000004, 0x800c02003c020042, 0xf000000000000001b000007d10000003a000008, 0x4b00000000000002b8000002570000029b000400, 0x6000000000000085e0000003d00000019000804, 0x400000000007000580000, 0x400000000002000000040, 0x1001801c038024042, 0x30000000000000001000002, 0x100000001000401, 0xf000000000000001d0000001d0000001b000204, 0x1001c01c03802003e, 0x60000000000000287000002a10000026a000302, 0x10000000000000001000103, 0x8f00000000000000e800000281000000d0000200, 0x2400200000, 0x1400e0000000700000, 0x1402001c03401c042, 0x39000000000000014e0000013600000143000402, 0x300000001000501, 0x10000000000000001000005, 0x1001c01c03401c046, 0x9000000000000006f0000006200000070000002, 0x2d0000000000000064000000590000005c000500, 0xc0000000000000014e0000014f00000137000205, 0x14020014034024042, 0xed0000000000000138000003f000000151000300, 0xcc00000000000002680000029b00000285000403, 0x2d00000000000001140000006400000059000004]
private def bspMeta_17 : ℕ × ℕ × ℕ := (683, 2000, 10)

private def bspWords_18 : List ℕ := [0x40000006800740000, 0x400dc000000680000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x800000000003800000064, 0x8000000000074005c0000, 0x800c02004002404a, 0x20000000000000001000106, 0x100000001000400, 0x7400000000000004b00000000d00000320000604, 0x400000000001400000020, 0x800c018038024052, 0x600000001000400, 0x2a00000000000001710000019b00000161000400, 0x194400000000000003e80000018f000061a8000105, 0x80050000000240000, 0x1002001c03402404a, 0x200000001000503, 0x900000000000000210000000500000020000503, 0x30000000000000001000001, 0x400000000007000640000, 0xc01402003c02404a, 0x20000000000000001000403, 0x100000001000200, 0x6000000000000001620000090f0000015b000302, 0x14000000000068000000c4, 0x1001801803802804e, 0x10000000000000001000001, 0x1500000000000002cd0000017100000073000302, 0x210000000000000155000009720000015d000103, 0x1001c01803c02804a, 0x10b00000000000007e900000307000002f0000201, 0x4800000000000001570000043800000175000002, 0x4e00000000000002e90000030b000002a2000100, 0x1000e8000000740000, 0x400000000003400000068, 0x400000000002400000044, 0x1802801c034024046, 0x300000001000500, 0x8d00000000000002d7000000a5000002bf000500, 0x10000000000000001000203, 0x400040000, 0x18028020038024042, 0x20000000000000001000203, 0x1b00000001000100, 0x10000000000000001000301, 0x4004c000000240000, 0x1802c01c034024042, 0x200000001000703, 0x2a000000000000016c000000370000015f000703, 0x30000000000000001000002, 0x18028018038024042, 0xb0000000000000027000001790000000e000001, 0x1b000000000000015c0000017700000079000200, 0x1100000000000002d5000000570000001a000102, 0x4000000000070000000d4, 0x400040000, 0x400000000007c00580000, 0x1802801c03c02003e, 0x1000000000000000100020a, 0x100000001000300, 0x10000000000000001000403, 0x1802c02003802003e, 0x10000000000000001000200, 0x1b00000001000301, 0x120000000000000179000002b90000016c000003, 0x40070000000380000, 0x1c03001c03402003e, 0x1000000010000001b00000002020601, 0x5400000000000002d800000037000002f5000706, 0x20000000000000001000003, 0x8000000000074000000d0, 0x1802c018038020042, 0x10000000000000001000002, 0x1b000000000000015e00000179000000b6000401, 0xb00000000000001790000001c0000000d000204, 0x1403001c03802003e, 0xd000000000000001b0000016c0000000e000102, 0xc00000000000000b600000178000000af000001, 0x200000000000002f60000001a0000001b000200, 0x400000000007c000000d4, 0x1c03001c03801c03e, 0x10000000000000001000009, 0x3600000000000002bc000002f2000002d9000105, 0x4e0000000200000001000901, 0x1c03002003802003a, 0x1b000000000000001b000008dc00000037000509, 0x1b00000000000002d9000002f4000002bf000005, 0x60000000000000834000000380000001f000900, 0x400000000004000280000, 0x40028000000140000, 0x1402001c040020042, 0x10000004b00000002000208, 0x200000001000001, 0x60000000000000001000001, 0xc01401c040020046, 0x30000002400000001000008, 0x1000000010000000300000001010300, 0xa50000000900000002000803, 0x400000000007c00580000, 0x400000000002400000044, 0x1002001c03c024046, 0x30000000000000001000002, 0x100000001000401, 0x900000000000000bb000000ac0000005a000204, 0x1402401c03c024042, 0x300000000000000b600000179000000ae000302, 0x1000000030000000100000002010003, 0x1500000000000002ef0000040e0000016a000200, 0x400040000, 0x10024020038020046, 0x7500000000000002eb000002b8000002d5000301, 0x1b00000001000400, 0x300000000000000177000002b300000169000104, 0x14024018038024046, 0x11000000000000001a000002d50000001d000300, 0x2a00000000000002d5000001750000015c000403, 0x700000000000001690000001d0000000d000004, 0x400dc000000680000, 0x1c03401c03402003e, 0x18000000000000088e000000350000001d000301, 0x10000005400000001000003, 0x10000000000000001000003, 0x1c000000000070000000bc, 0x40000002c00200000, 0x2000000000005c000000b8, 0x800c01402c03005a, 0x10000000000000001000004, 0x300000001000501, 0x497400000000000007d0000003810000dac0000405, 0x801001402c028056, 0x10000000000000001000204, 0x30000000000000001000102, 0x300000000000000fd00000122000000cf000400, 0xc0000000000200000003c, 0x140000008800640000, 0x800c01002403005e, 0x300000001000001, 0x10000000000000001000001, 0x205c00000000000007d00000011f00004650000206, 0x2c00000000005c000000ac, 0x8010008010034066, 0x100000001000800, 0x274000000000000001d0002d690000007d0000708, 0x82c00000000000007d0000001af00006d60000107, 0x801800c01c03005e, 0x1aa0000000900000005000801, 0xf000000000000001a000008370000002b000008, 0x7500000000000002b900000320000002a7000100, 0x100000000000340000005c, 0x1001801002402c05a, 0x200000001000700, 0x50000008e00000003000107, 0x300000000000002aa00000345000000e5000201, 0x10020010028028056, 0x100000001000703, 0x10000003000000001000007, 0x300000000000000310000002500000011000200, 0x10000000000064000000c8, 0x1000e80000005c0000, 0x80000007c00640000, 0x1002801803002804a, 0x100000001000002, 0x10000000000000001000002, 0x10000000000000001000100, 0x400000000001000000020, 0x1002801402802c052, 0x600000001000800, 0x6000000000000001a000008b80000002f000408, 0x10000000000000001000204, 0x14000000000068000000c4, 0x1002801402c02804e, 0x100000001000900, 0x30000002d00000001000109, 0x10000000000000001000301, 0x1802801802c02804a, 0x570000000200000001000902, 0xc000000000000001b0000087c00000031000009, 0x7b00000000000000e800000105000000f1000200, 0x400000000001000000020, 0x1001801402c02c052, 0x60000000000000001000005, 0x1b00000000000002cd000002e5000002b6000301, 0xf0000000000000155000001b200000153000503, 0x14000000000068000000c4, 0x400000080005c0000, 0x1001c01803402804e, 0x10000000000000001000107, 0x10000000000000001000003, 0x27000000000000007c000003490000006c000702, 0x1402001403002804e, 0x5d00000000000001690000017600000159000300, 0x1500000000000001570000003c0000003e000203, 0x9000000000000001e000000c30000001d000002, 0x1402401803402804a, 0x5700000000000000870000009b00000098000206, 0x5d00000000000001590000016900000176000002, 0x2400000000000002d10000032d000002a4000600, 0x400000000002400000044, 0x4004c000000240000, 0x1802c018030024046, 0x300000001000701, 0x10000005700000002000207, 0x30000000000000001000002, 0x40000007400680000, 0x1802801c034024046, 0x1e0000000000000083d000002d600000311000106, 0x100000001000300, 0xb100000000000002d50000032c000002a3000603, 0x1000000000007c000000c8, 0x1802801403402004a, 0x10000000000000001000001, 0x27000000000000008b000001c200000091000402, 0x18900000000000002d50000030f000002bc000104, 0x1402c018034024046, 0x2820000000000000885000002d6000002f3000201, 0x5400000000000002d5000009090000029f000002, 0x1b000000000000015f0000016b00000178000100, 0x400000000003400000068, 0x40070000000380000, 0x1c03001c030024042, 0x200000001000801, 0x6000000000000001c000002d800000011000208, 0x20000000000000001000002, 0x1802c018034024042, 0x8d000000000000015f000000b6000000c4000006, 0x90000000000000444000002ef0000015e000200, 0x1e000000000000002d600000933000002bf000602, 0x1403401c03402003e, 0x2be00000000000002da000002d9000002f5000405, 0x2a000000030000000100000002070004, 0xc0000000000000082000000eb00000075000500]
private def bspMeta_18 : ℕ × ℕ × ℕ := (668, 2000, 10)

private def bspWords_19 : List ℕ := [0x1c00000000007c000000c8, 0x40000003000200000, 0x20000000000068000000c4, 0x801001403003005e, 0x10000000000000001000003, 0x300000001000301, 0x109500000000000007d0000001a500005dc0000003, 0x30001c0000, 0x801001803c02805a, 0x10000000000000001000304, 0x30000000000000001000003, 0x5cd0000000000000fa00000032d0000b3b0000304, 0x1001801403002805a, 0x10000000000000001000300, 0x30000000000000001000203, 0x3000000000000006c0000002700000023000001, 0x28000000000070000000bc, 0x8010008018030066, 0x100000001000400, 0x13b000000000000001b0002d690000007d0000304, 0x1b5d0000000000000bb8000000e5000036b0000103, 0x20000000000068000000c4, 0xc01c01002403005e, 0x100000001000500, 0xc000000000000001b000009900000002f000105, 0xf00000000000008df0000035800000314000201, 0x1402401002c02805a, 0x100000001000503, 0xc00000000000000170000099c00000031000005, 0xab0000000000000903000003600000031c000200, 0x1400000000008c000000d0, 0x400000000007c00640000, 0x400000000002c001c0000, 0x800c020048020052, 0x10000000000000001000206, 0x300000001000300, 0xaf500000000000017700000004500000fa0000604, 0xc010020040020052, 0x10000000000000001000200, 0x100000001000301, 0x8d000000000000092a00000352000002ff000003, 0x40000008c005c0000, 0x800000000002c00000044, 0xc018018038024056, 0x30000000000000001000002, 0x100000001000401, 0x21000000000000009e000000ac0000009b000204, 0x2c00200000, 0x1001c01c03c020052, 0x10000000000000001000403, 0x30000000000000001000004, 0xf0000000000000017e0000050d00000191000301, 0x10024018038020052, 0x10000000000000001000400, 0x10000000000000001000204, 0x3000000000000003060000032100000113000001, 0x800000000002c00000044, 0x80000009400580000, 0x10024014034024056, 0x30000000000000001000102, 0x100000001000500, 0x6f00000000000003030000031e00000335000205, 0x1402801402c024056, 0x300000001000701, 0x9000000000000000d000004fe00000019000507, 0x1b00000000000000ba000000c8000000d3000005, 0x14000000000068000000d0, 0x1402801403002c052, 0x100000001000700, 0x300000000000000180000036c00000011000107, 0x570000000000000175000004b3000001a8000201, 0x1402c01c030020052, 0x100000001000004, 0x30000000000000091000000820000001a000004, 0xc900000000000003400000030300000326000200, 0x1000f4000000740000, 0x400000000002800000048, 0x40000008000680000, 0x1802c01c03802404a, 0x30000000000000001000102, 0x100000001000200, 0x10000000000000001000200, 0x10000000000070000000d4, 0x1802c01c03002804e, 0x100000001000700, 0x3000000000000000f000005190000001a000407, 0x10000000000000001000304, 0x800ec000000640000, 0x1803401803402404a, 0x300000001000803, 0x60000000000000019000009c600000035000108, 0x10000000000000001000001, 0x40050000000280000, 0x1c03001803402804a, 0x7b000000000000032a000003450000030a000103, 0xba00000000000003070000034200000329000201, 0x30000000000000001000002, 0x1403001803802804a, 0x1800000000000000510000001b0000001c000003, 0xd000000000000010e0000034100000104000200, 0x2700000000000000d1000000c2000000ca000302, 0x8000000000080000000dc, 0x2800240000, 0x1802c02003c020046, 0x10000000000000001000108, 0x300000001000200, 0x10000000000000001000302, 0x800ec000000700000, 0x1c03401c034020046, 0x100000001000802, 0x4000000000000000e000001a300000009000308, 0x10000000000000001000003, 0x40050000000280000, 0x1c03001c038020046, 0x3600000000000003460000092d0000032b000102, 0xc00000000000004bf000001a200000187000401, 0x30000000000000001000004, 0x1403001c03c01c04a, 0x3000000000000006c0000005a00000023000002, 0xc0000000000000195000001a100000082000400, 0x1000000000000001c0000001a00000009000204, 0x800ec000000700000, 0x4000000000070000000e0, 0x1c03401c038024042, 0x100000001000800, 0x3000000000000001a00000a2000000037000208, 0x10000000000000001000102, 0x2800240000, 0x1c03402003c02003e, 0x3000000540000000100000a, 0x3000000000000000100000a, 0x10000000000000001000201, 0x400000000007c000000e0, 0x1c038020038020042, 0x100000001000200, 0x1b00000000000003490000032c00000038000200, 0xf00000000000004ec0000018700000196000102, 0x2003802003802003e, 0x1180000001300000003000a01, 0x1b000000000000001d000009db0000003800000a, 0x1b000000000000092d0000032c00000347000100, 0x400000000007c00640000, 0x1802c020040020042, 0x3000000000000001f000009840000003b000109, 0x100000001000200, 0x6000000000000097b0000003d00000020000902, 0x1c03002003c024042, 0x3000000000000032c000003480000030d000100, 0x36000000000000032b000003460000030f000201, 0x15000000000000009c000000a2000000a7000002, 0x800000000008c00500000, 0x80054000000280000, 0x1402401c044020046, 0x600000000000000200000097b0000003d000207, 0x10000000000000001000102, 0x300000001000700, 0x1c0100000000800000, 0x1402001c04402004a, 0x1000000000000000b0000010c00000007000108, 0x100000001000402, 0x10000000000000001000004, 0x400000000002800200000, 0xc01402404802404a, 0x9000000000000000f000004e000000020000109, 0x300000001000500, 0xf000000000000093c0000004300000023000905, 0x1001802004402804a, 0x3300000000000000bd00000288000000d0000100, 0x81000000000000034000000337000002e0000501, 0x27900000000000008e50000035a00000320000005, 0x1000000000007c000000d4, 0x2800240000, 0x1402002003c02404e, 0x10000000000000001000102, 0x300000001000400, 0x33000000000000005c0000006400000069000204, 0x1002801803802404e, 0x10000000000000001000100, 0xbd00000000000003260000036b000002cf000403, 0x87000000000000092d0000032800000343000004, 0x400000000002400000048, 0x1402401c03c02804a, 0x30000000000000001000002, 0x6000000000000003270000033f0000030a000103, 0x180000000000000049000000460000004b000201, 0x1802801c040024046, 0xae000000000000034300000346000002e9000302, 0x1900000000000003080000010e00000117000003, 0x110000000000000117000003070000010e000200]
private def bspMeta_19 : ℕ × ℕ × ℕ := (655, 2000, 10)

private def bspWords_20 : List ℕ := [0x40000007400800000, 0x400f4000000740000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x400000000001c00000038, 0x400000000004000340000, 0xc01002404802c052, 0x40000000000000001000106, 0x200000001000400, 0xde000000000000000900000000000001f4000400, 0x800000000002400000048, 0xc01001c04003005a, 0x300000001000400, 0x800000000000000900000004c00000087000400, 0xde000000000000000900000000000001f4000504, 0x1c010c000000800000, 0x400000000009400580000, 0x1402401c04402c052, 0x40000000000000001000403, 0x100000001000100, 0x10000000000000001000100, 0x14000000000074000000dc, 0x1402402003c02c056, 0x100000001000700, 0x11700000000000003630000003d00000349000700, 0x10000000000000001000203, 0x1402802003c02c052, 0x400000001000705, 0x3600000000000000d90000003d000000d2000705, 0x9c0000000000000398000003560000037b000100, 0x400000000001800000024, 0x1001802004002405a, 0x60000000000000001000003, 0x2b00000000000003bb0000011700000132000201, 0xb000000000000003f000000620000001b000302, 0x1001c02004402c052, 0x9000000000000001a4000003b8000001cd000103, 0x600000000000003990000009800000089000001, 0x32000000000000008d000001db0000004a000300, 0x40040000000200000, 0x8000000000074000000e8, 0x40000000000280000004c, 0x1c03002003c02804e, 0x300000001000500, 0x9c0000000000000382000000b700000367000500, 0x40000000000000001000203, 0x400040000, 0x1c03002404002804a, 0x10000000000000001000203, 0x1e00000001000100, 0x40000000000000001000301, 0x40054000000280000, 0x1c03402003c02804a, 0x100000001000703, 0x5d00000000000003830000003d00000366000703, 0x30000000000000001000002, 0x1c03001c04002804a, 0x190000000000000057000003a00000001f000001, 0x3c00000000000003600000039c0000012b000200, 0x140000000000000380000000600000001d000102, 0x400000000007c000000ec, 0x400040000, 0x400000000008800640000, 0x1c030020044024046, 0x1000000000000000100020a, 0x100000001000300, 0x40000000000000001000403, 0x1c034024040024046, 0x10000000000000001000200, 0x1e00000001000301, 0x2700000000000003a00000036100000383000003, 0x800f80000007c0000, 0x2003802003c024046, 0x1000000010000001e00000002020601, 0x5d00000000000003830000003d000003a3000706, 0x10000000000000001000003, 0x400000000004000000074, 0x1c03401c04002404a, 0x20000000000000001000002, 0x780000000000000364000003a000000383000401, 0x1900000000000003a00000001f0000001d000204, 0x1803802004001c04a, 0x20000000000000020000003260000001f000102, 0x1b0000000000000383000001cf000001b2000001, 0x100000000000001d20000001d0000000f000200, 0x4000000000088000000ec, 0x20038020040020046, 0x10000000000000001000009, 0xf00000000000000d9000000e8000000e1000105, 0x570000000200000001000901, 0x20038024040024042, 0x1e000000000000001e00000ae60000003d000509, 0x1e0000000000000384000003a200000367000005, 0x300000000000005160000001f00000011000900, 0x400000000004000340000, 0x1c010c000000800000, 0x1402402404802404a, 0x20000005400000001000108, 0x200000001000301, 0x10000000000000001000003, 0x10000000000094004c0000, 0x10018020050020052, 0x10000004b00000001000009, 0x100000001000400, 0x690000000a00000001000904, 0x1001c02404802804e, 0x9000000000000001e00000b2b00000043000109, 0x2400000000000001cd0000006900000077000401, 0x8100000000000000f50000034c000000d9000004, 0x400000000007c00700000, 0x40000000000280000004c, 0x1402402404402804e, 0x30000000000000001000002, 0x100000001000401, 0x2400000000000000ee000001cd00000069000204, 0x1401040000007c0000, 0x1802c02404402404a, 0x150000000300000001000000010a0403, 0x10000000000000001000204, 0x100000001000300, 0x1802802004802004e, 0x6000000000000001cc0000035f000001bf000003, 0x90000000000000204000000b3000000b9000100, 0x150000000000000042000000630000001f000301, 0x400000000009400580000, 0x40000000000280000004c, 0x1802801c04402804e, 0x30000000000000001000002, 0x100000001000501, 0x18000000000000004d0000013f00000046000205, 0x1802c01c04402004e, 0x15000000000000039d000000d0000000e8000402, 0x3300000000000002880000039b000000e0000004, 0x27f000000000000039d00000add00000365000200, 0x400040000, 0x1802c02404002804e, 0x33000000000000039b000000e0000000d8000401, 0x1e00000001000500, 0x1e00000000000000e70000035b000000e0000105, 0x2c00240000, 0x1802c02004002804e, 0x5000000000000001d000000e000000008000501, 0x300000001000600, 0x300000000000000e70000002000000007000106, 0x1403002003c020052, 0x1500000000000003b500000258000000e8000500, 0x2100000000000000f0000000d900000038000605, 0x600000000000002ca0000035e000000d9000006, 0x400f4000000740000, 0x2003c02003c024046, 0x1b0000000000000a8f0000003b00000020000301, 0x10000005d00000001000003, 0x10000000000000001000003, 0x1c000000000070000000d4, 0x400000050002c0000, 0xc00000000003000000044, 0x8014014038028066, 0x30000000000000001000004, 0x200000001000501, 0x24be0000000000001770000004210000f230000405, 0xc01801403803005e, 0x10000000000000001000204, 0x20000000000000001000102, 0x48000000000000032600000c600000036d000400, 0x800000000001400000028, 0x40000002000140000, 0x801401002c03806a, 0x500000001000001, 0x50000000000000001000001, 0x376a0000000000001770000001d300006d60000206, 0x400000000000800000010, 0x801800801c03c072, 0xc00000001000800, 0x29a000000000000001b0002ee00000007d0000708, 0x6be0000000000000fa00000006100001770000107, 0xc01c00c02803806a, 0x690000000a00000001000801, 0x60000003600000001000008, 0x30000000000000048000000c30000000e000100, 0x40034000000140000, 0x1002c01002c03005e, 0x100000001000703, 0x50000006900000001000007, 0x50000000000000001000007, 0xc00000000002400000044, 0xc01c01002c034066, 0x30000000000000001000003, 0x690000000f0000000a00000004080201, 0x2700000000000000b4000001c500000055000302, 0x1000000000003400000068, 0x1402001802c034062, 0x20000000000000001000004, 0x12000000000000023d00000359000000b0000102, 0x4e000000000000035200000594000001b7000401, 0x1002801403403005e, 0x1800000000000000980000003d0000001b000204, 0x3000000000000000d0000002200000007000002, 0x5d00000000000001c7000001a6000000dd000400, 0x400000000001c00000038, 0x80080000000340000, 0x80000009400640000, 0x1403001803802c052, 0x400000001000702, 0x10000000000000001000007, 0x20000000000000001000100, 0x800000000002400000048, 0x1403001803003005a, 0x300000001000800, 0x9000000000000001d00000a6b00000035000408, 0x20000000000000001000204, 0x14000000000074000000dc, 0x1403001803402c056, 0x100000001000900, 0x30000006300000002000109, 0x5c00000000000001320000035600000129000201, 0x1c03401c03402c052, 0xc0000000000000ad40000003800000019000902, 0x30000000000000006000002190000000b000009, 0x300000000000000ad000000b3000000b8000200, 0x800000000002400000048, 0x400000098005c0000, 0x1002001803c03005a, 0x30000000000000001000106, 0x100000001000400, 0xe10000000000000390000004010000032b000604, 0x1002801403403005a, 0x30000000000000001000100, 0xb700000000000001a900000391000001bc000402, 0x9300000000000001c9000001a8000001bb000004, 0x14000000000074000000dc, 0x40000008c00680000, 0x1002801c03c02c056, 0x10000000000000001000107, 0x10000000000000001000003, 0x1000000000000003f000000c100000036000702, 0x1802801803802c056, 0x66000000000000037d000001cd000001ad000300, 0x2e00000000000001ab0000012900000099000203, 0x2500000000000000630000013f00000060000002, 0x1802c01c03c02c052, 0x1200000000000000348000001dc000001d3000206, 0x6600000000000001ad0000037d000001cd000002, 0x84000000000000037c000003e100000349000600, 0x40000000000280000004c, 0x40054000000280000, 0x1c03401c03802804e, 0x300000001000701, 0x20000003000000001000207, 0x30000000000000001000002, 0x40000008000740000, 0x1c03002003c02804e, 0x3000000000000000c9000000450000004a000106, 0x100000001000300, 0x240000000000000070000001f000000069000603, 0x1403401803c02804e, 0x3240000000000000a8600000381000003a1000100, 0x36000000000000035f000002b5000000e0000301, 0x1800000000000000ee00000361000000d9000003, 0x8000000000074000000e8, 0x800f80000007c0000, 0x2003802003802804a, 0x100000001000801, 0x7000000000000001f0000038300000013000208, 0x10000000000000001000002, 0x1c03401c03c02804a, 0x2cd000000000000036600000383000003c1000006, 0x150000000000000a890000039d00000364000200, 0x300000000000000045000000de00000043000602, 0x1803c02003c024046, 0x366000000000000038500000384000003a3000405, 0x5d000000030000000200000004070004, 0x1b000000000000013f0000012300000122000500]
private def bspMeta_20 : ℕ × ℕ × ℕ := (642, 2000, 10)

private def bspWords_21 : List ℕ := [0x400000000001000000020, 0x40000003400240000, 0x400000000001000000018, 0xc01401803802c06a, 0x90000000000000001000003, 0x300000001000301, 0xa320000000000000bb80000009900001f40000003, 0x3400200000, 0xc01401c044034062, 0x70000000000000001000304, 0x30000000000000001000003, 0x11800000000000000fa00000013000003e8000304, 0x1c0118000000800000, 0x14028018038034062, 0x70000000000000001000400, 0x30000000000000001000304, 0x100000001000400, 0x40000009800680000, 0xc02001c040034062, 0x70000000000000001000502, 0x10000000000000001000001, 0xc000000000000009c000001e300000037000203, 0x14020018038034062, 0x9300000000000000ee000000fc000000fd000100, 0x420000000000000621000000ab00000092000301, 0x900000000000000480000032a00000053000003, 0x28000000000070000000d4, 0x10000000b0005c0000, 0xc01401003403806e, 0x10000000000000001000102, 0x100000001000400, 0x74d60000000000001770000004770000f230000204, 0x1000000000002400000044, 0xc01800802403c076, 0x300000001000600, 0xa000000000000000100001e0000000050000506, 0x8a200000000000007d00000021500007530000105, 0xc02001002803806e, 0x100000001000602, 0x3000000000000001d000003be00000011000006, 0x1fb00000000000003ba00000ba0000003bb000100, 0x100000009800740000, 0x8005c0000002c0000, 0x1802c018034034062, 0x700000001000604, 0x10000000000000001000106, 0x30000000000000001000001, 0x10024018034034066, 0x3100000000000001e8000001d9000000af000003, 0x10000000000000001000100, 0x30000000000000b4f00000412000003ad000302, 0x400000000000c00000018, 0x1002801402c03806a, 0x900000001000600, 0x12000000000000001e00000b5b00000035000206, 0x300000000000000a1000000ae0000009d000102, 0x1402c014030034062, 0x150000000000000b7c000000380000001d000601, 0x1000000000000000e000000a200000003000006, 0x500000000000000240000015d00000023000100, 0x1400000000008c000000e8, 0x400000000008800700000, 0x400000000003000200000, 0xc01402405002805a, 0x10000000000000001000206, 0x300000001000300, 0x1e00000000000000f000000003000000a0000604, 0x800000000002c0000004c, 0xc01402404802c05e, 0x30000000000000001000001, 0x100000001000402, 0x600000000000000390000008100000010000104, 0x1001c02404802805a, 0x10000000000000001000301, 0x10000000000000001000203, 0x4b00000000000001f5000001f60000009e000100, 0x8005c0000002c0000, 0x800000088007c0000, 0x1802c02003c02805a, 0x10000000000000001000301, 0x100000001000100, 0x30000000000000001000100, 0x80000000000280000004c, 0x1802c01c03403005e, 0x300000001000700, 0x40000003300000001000507, 0x30000000000000001000205, 0x10010c000000800000, 0x1c03401803802805a, 0x100000001000805, 0x3000000000000001b000003f300000013000108, 0x10000000000000001000001, 0x1c03001803c03005a, 0x20d00000000000003bd000003da0000041f000002, 0x240000000000000b8b000003f2000003b9000100, 0x2700000000000000ee00000330000000ef000201, 0x40000000000a000580000, 0x1c0118000000740000, 0x1002801c04802805a, 0x10000000000000001000403, 0x10000000000000001000102, 0x100000001000300, 0x1001c01c04803005a, 0x20100000000000003a000000431000003d6000003, 0x100000001000501, 0x1b000000000000004a0000021b00000040000305, 0x3400200000, 0x1002401c04403005a, 0xab0000000000000b8e000003f7000003b2000201, 0x300000001000500, 0x3000000000000004a000001d300000044000105, 0x1002801c03c02c05e, 0x10000000000000014f0000013c0000006d000200, 0x2d000000000000041b000001980000008c000502, 0xf00000000000001bc000003a900000088000005, 0x10010c000000680000, 0x400000000002c00000050, 0x40000008c00740000, 0x10000000000088000000ec, 0x14034020040028056, 0x10000000000000001000003, 0x100000001000401, 0x10000000000000001000304, 0x10010c000000800000, 0x1c034020040028052, 0x30000000000000001000300, 0x10000000000000001000203, 0x100000001000300, 0x14034020044028052, 0x30000000000000001000304, 0x6c00000000000003db000003f6000003bb000100, 0x10000000000000001000401, 0x10000000000088000000ec, 0x40058000000280000, 0x1c038020038028056, 0x100000001000801, 0x9000000000000002100000bfd0000003a000508, 0x30000000000000001000005, 0x1803401c03c028056, 0x390000000000000beb000003be000003dc000002, 0x1800000000000001ed0000061b000001cf000500, 0x300000000000000210000002200000023000205, 0x1c03801c03c028052, 0x300000001000702, 0x6000000000000001c00000c3f0000003b000007, 0x3900000000000003be000003dc000003f9000100, 0x800000000008c000000f4, 0x2c00280000, 0x400000000008800700000, 0x1403402404802404e, 0x10000000000000001000209, 0x100000001000300, 0x10000000000000001000403, 0x1803402404402404e, 0x10000000000000001000200, 0x300000001000301, 0x4500000000000003fd00000b2e000003dc000003, 0x801040000007c0000, 0x2003c02003c02404e, 0x100000001000802, 0x9000000000000001f000003fd00000014000308, 0x10000000000000001000003, 0x400580000002c0000, 0x2003802004002404e, 0x3c00000000000003fd00000b40000003df000102, 0x1b0000000000000b9a000003fb000003bf000401, 0x30000000000000001000004, 0x18038020044020052, 0x1b000000000000041a0000037b00000155000002, 0x1b00000000000003de000003f90000013f000400, 0x1000000000000001f0000001d0000000a000204, 0x801040000007c0000, 0x400000000007c000000f8, 0x2003c02004002804a, 0x100000001000800, 0x3000000000000001d00000c4e0000003d000208, 0x10000000000000001000102, 0x2c00280000, 0x2003c024044024046, 0x30000005d0000000100000a, 0x3000000000000000100000a, 0x10000000000000001000201, 0x4000000000088000000f8, 0x2004002404002404a, 0x100000001000200, 0xf0000000000000200000001f00000001f000200, 0x210000000000000bfd000003bf000003e0000102, 0x24040024040024046, 0x3ff0000003f0000000a000a01, 0xf0000000000000010000006000000001f00000a, 0xf00000000000005a0000001f0000001ff000100, 0x400000000008800700000, 0x1c03402404802404a, 0x3000000000000002200000ba000000041000109, 0x100000001000200, 0x60000000000000b970000004300000023000902, 0x2003802404402804a, 0x300000000000003e0000003ff000003be000100, 0x3c00000000000003df000003fd000003c0000201, 0x7500000000000003bd000003de000003fa000002, 0x800000000008c00680000, 0x40028000000140000, 0x1802802404c02404e, 0x6000000000000002300000c6900000043000207, 0x10000000000000001000102, 0x700000001000700, 0x20011c000000880000, 0x1402402404c02c052, 0x30000002d00000001000108, 0x100000001000402, 0x10000000000000001000004, 0x10018020050024056, 0xc000000000000002500000b7300000047000008, 0x17100000000000003ab000003e7000003d0000400, 0xf0000000000000bb50000004a00000023000804, 0x10000000000088000000ec, 0x400000000009400640000, 0x10028020048028056, 0x10000000000000001000102, 0x100000001000400, 0x3000000000000001d0000001b0000001c000204, 0x1802c020040028056, 0x10000000000000001000100, 0x12900000000000003b7000003f7000003e0000403, 0xb700000000000003b5000003d6000003ef000004, 0x400000000002800000050, 0x400000000008800700000, 0x1402c02404802c052, 0x30000000000000001000103, 0x10000000000000001000001, 0x4800000000000003f9000003b4000003d7000302, 0x1403002404402c052, 0x45000000180000001b0000002e010400, 0x8400000000000003bc000003dd000003ff000204, 0x3000000000000001e0000001c0000001d000002, 0x140110000000880000, 0x1c03002004802804e, 0x1200000000000003dd0000043d00000374000403, 0x1b00000000000001250000006e00000078000104, 0x100000001000300, 0x1802c02004c024052, 0x6300000000000001fa000001dc000001ed000003, 0x900000000000001dc000000a5000000aa000100, 0xed000000000000015e000003d700000140000301]
private def bspMeta_21 : ℕ × ℕ × ℕ := (630, 2000, 10)

private def bspWords_22 : List ℕ := [0x400000080008c0000, 0x4010c000000800000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x40030000000140000, 0x400000000003000000054, 0x40000000000a000640000, 0x4000000000088007c0000, 0x1403002804c028056, 0x30000000000000001000203, 0x100000001000300, 0x60000000000000001000300, 0x80000000000440000007c, 0x1403002004c02c05a, 0x20000000000000001000001, 0x100000001000402, 0x60000000000000001000402, 0x1c03002004c028056, 0x30000000000000001000301, 0x10000000000000001000203, 0x13e000000000000021c000004800000020f000100, 0x1000000000007c000000f8, 0x1400000000008c000000f4, 0x1403001c04802c05e, 0x100000001000600, 0xc000000000000017a0000004e00000161000600, 0x60000000000000001000406, 0x1c03002404403005a, 0x100000001000601, 0xed000000000000041e00000043000003ff000601, 0xba00000000000004140000043800000451000200, 0x1001180000008c0000, 0x20038024044028056, 0x300000001000603, 0x3a0000000000000175000000430000016c000603, 0x10000000000000001000001, 0x400040000, 0x1c03402804802c056, 0x2d00000000000000df000000d9000000d2000103, 0x2100000001000200, 0x81000000000000045c000004150000043d000302, 0x10000000000094000000f8, 0x1c03401c04802805a, 0x10000000000000001000001, 0x108000000000000041a0000045c0000043d000302, 0xf000000000000045c000000230000001f000103, 0x1c03402004802c056, 0x1700000000000000200000043d00000023000201, 0xd8000000000000043d00000473000003f7000002, 0x1900000000000004180000002300000021000100, 0x4005c0000002c0000, 0x400000000004c00000080, 0x3400240000, 0x2003c020048024052, 0x20000000000000001000102, 0x300000001000300, 0x30000000000000001000203, 0x40088000000440000, 0x24040024044024052, 0x200000001000702, 0x3600000000000002400000004300000233000702, 0x20000000000000001000007, 0x2003c02404402c052, 0x420000000000000460000006600000020f000001, 0x5400000000000002310000004300000242000700, 0x1f000000000000015f0000015e0000007f000104, 0x400000000008800000104, 0x400040000, 0x2003c02804802804e, 0x1000000000000000100010a, 0x2100000001000200, 0x30000000000000001000302, 0x80000000000a400000100, 0x20040024044020052, 0x100000001000800, 0x6f00000000000004a00000004300000489000800, 0x100000000000002110000002100000011000103, 0x2404002404402804e, 0x1000000010000002100000002020701, 0x6600000000000004400000004300000463000807, 0x200000000000003da0000002200000023000100, 0x400000000009400000104, 0x2404002404802404e, 0x1000000000000000100000a, 0x42000000000000041e0000046000000441000106, 0x600000000200000001000a01, 0x2404002804802804a, 0x21000000000000002100000d260000004300060a, 0x2100000000000004410000046200000421000006, 0x60000000000000c5a0000004400000025000a00, 0x1001180000008c0000, 0x400000000004000000080, 0x2003802404802c052, 0x20000000000000001000001, 0xa000000000000016a0000017400000075000302, 0x10000000000000001000103, 0x2003802404c02804e, 0xb00000000000000220000046100000017000209, 0x15000000000000041b0000066000000230000002, 0x10000000000000001000100, 0x400000000004c00340000, 0x1c030024050028052, 0x10000005d00000002000109, 0x200000001000300, 0x5a0000000600000001000903, 0x1c03402404c02c052, 0x60000000000000220000004600000020d000100, 0x7000000000000009b0000003500000032000301, 0x2900000000000001690000020b000000b9000003, 0x800000000002c00000050, 0x400000000009400700000, 0xc01402404c030062, 0x30000000000000001000105, 0x100000001000500, 0x5b410000000000000bb80000024500007148000105, 0xc0064000000300000, 0x1402401c048030062, 0x30000000000000001000201, 0x6600000000000000f90000015f00000122000503, 0x30000000000000001000005, 0xc01801c04c034066, 0x2a0000000000000beb0000044f00000478000001, 0x4e000000000000042a00000321000004eb000500, 0xe3100000000000003e80000012500003c8c000106, 0x400000000003000240000, 0x1400000000008c000000f4, 0xc01402805402c05e, 0x10000000000000001000008, 0x30000000000000001000100, 0xc1b00000000000017700000004f00000fa0000806, 0x80000000000440000007c, 0x1001c02805402c05a, 0x20000000000000001000009, 0x30000000000000001000200, 0x1e60000000b00000005000901, 0x14024028054028056, 0x30000005a00000001000209, 0x30000000000000001000209, 0x300000000000006b10000004b00000011000900, 0x1400000000008c000000f4, 0x400000000004c00340000, 0x1402002405002c05e, 0x10000000000000001000102, 0x200000001000300, 0x8000000000000044e0000047400000153000203, 0x400000000009400700000, 0x1402402404c02c05e, 0x100000001000502, 0x10000000000000001000005, 0x11d00000000000004500000067b0000020b000104, 0x1802802004802c05e, 0x4b0000000000000ca50000022d00000209000500, 0x27000000000000020700000435000000b9000405, 0x1ad000000000000043100000d7100000418000004, 0x80000000000440000007c, 0x1402402404c02c05a, 0x200000001000400, 0x4b000000000000020900000ca50000022d000104, 0xbf0000000000000451000001710000015d000201, 0x18028024050028056, 0xa8000000210000000c00000007090402, 0x2a00000000000001f6000006540000011f000004, 0x15000000000000006f0000004a00000023000200, 0x4010c000000800000, 0x2404402404402804e, 0x6000000000000028e0000000d00000007000301, 0x10000006600000001000003, 0x10000000000000001000003, 0x1c00000000007c000000ec, 0x40000003800240000, 0xc0000000000280000004c, 0xc01801803c03806e, 0x30000000000000001000004, 0x300000001000501, 0x252300000000000007d000000287000084d0000405, 0x1c0124000000800000, 0x1402c01803c034066, 0x10000000000000001000300, 0x30000000000000001000203, 0x100000001000300, 0x1c00100000, 0xc01c01c048034066, 0x10000000000000001000406, 0x60000000000000001000001, 0x138000000000000046300000ec7000003be000602, 0x20000000000074000000e8, 0x1402001c03c03806a, 0x100000001000200, 0xae0000000000000d6e000004110000042b000302, 0x1400000000000004280000023a000000ad000103, 0x10028020040034066, 0x3100000000000000b300000451000000ac000201, 0x75000000000000047d000003f70000044e000002, 0x80000000000000179000000390000003a000100, 0x1400000000003800000070, 0x1000000000002400000048, 0x802000c02004007a, 0x300000001000700, 0xc0000000000000002000034bc0000007d000607, 0x810000000000000e100000006d00001900000206, 0xc01c01003003c072, 0x200000001000701, 0x30000007500000002000007, 0x430000000000000438000004910000014d000200, 0x14011c000000700000, 0x14034014034034066, 0x100000001000703, 0x10000007200000001000007, 0x10000000000000001000007, 0x1402801403403806a, 0x1a7000000000000043100000cea00000407000002, 0x39000000030000000100000002070100, 0xf000000000000031e0000023b00000103000201, 0x1000000000007c000000f8, 0x100118000000740000, 0x40000005000380000, 0x1803801c04003005a, 0x100000001000702, 0x20000000000000001000007, 0x10000000000000001000100, 0x400000000001400000028, 0x1803801c038034062, 0x600000001000800, 0xc000000000000002000000ca20000003b000408, 0x10000000000000001000204, 0x14000000000080000000f4, 0x1803801c03c03005e, 0x100000001000900, 0x30000003600000001000109, 0x500000000000000250000006800000012000201, 0x2003c02003c03005a, 0x300000000000003450000001f00000007000902, 0x12000000000000002100000cb40000003d000009, 0x9000000000000041b0000021e0000022c000200, 0x400000000001400000028, 0x4000000a400680000, 0x1802801c044034062, 0x60000000000000001000106, 0x100000001000400, 0xc30000000000000431000004ea000003df000604, 0x40000005000380000, 0x1403001c040034062, 0x60000000000000001000201, 0x200000001000500, 0x13e00000000000004520000040a00000433000105, 0x1403401803c034062, 0xf00000000000000360000006f00000034000300, 0x18f000000000000040c0000045100000435000503, 0xab0000000000000453000002060000021a000005, 0x14000000000080000000f4, 0x40000009800740000, 0x1403002004403005e, 0x10000000000000001000107, 0x10000000000000001000003, 0x40000000000000026000000e800000021000702, 0x1403401c04003005e, 0x6f000000000000021d0000022d0000020a000300, 0xa00000000000000d00000002400000025000203, 0x1800000000000000be00000411000000af000002, 0x1c03402004403005a, 0x2df00000000000003ff0000047b00000466000206, 0x6f000000000000020a0000021d0000022d000002, 0xf60000000000000439000004a700000400000600, 0x400000000002c00000054, 0x4005c0000002c0000, 0x2003c02004002c056, 0x300000001000701, 0x10000006900000002000207, 0x30000000000000001000002, 0x40000008c00800000, 0x2003802404402c056, 0x3120000000000000c630000043e00000485000106, 0x100000001000300, 0x1a1000000000000043d000004a6000003ff000603, 0x1803c01c04402c056, 0x3d80000000000000cbd0000043e00000461000100, 0xed000000000000041900000d140000043d000301, 0x69000000000000047b0000041b0000041e000003, 0x400000000004000000080, 0x40088000000440000, 0x2404002404002c052, 0x200000001000801, 0x800000000000000220000044000000015000208, 0x20000000000000001000002, 0x2003c02004402c052, 0xde00000000000002100000011000000121000006, 0xc00000000000006600000045d0000020f000200, 0x312000000000000043e00000d8f00000421000602, 0x1c04402404402804e, 0x42000000000000004420000044100000463000405, 0x33000000030000000100000002070004, 0xf00000000000000c000000161000000b0000500]
private def bspMeta_22 : ℕ × ℕ × ℕ := (619, 2000, 10)

private def bspWords_23 : List ℕ := [0x20000000000098000000f4, 0x40000003c00240000, 0xc00000000002800000050, 0xc01c01804003c072, 0x30000000000000001000003, 0x300000001000301, 0x84000000000000012c00000015000003e8000003, 0x40000009800800000, 0x1001802404803006e, 0x10000000000000001000304, 0x10000000000000001000003, 0x430000000000000002900000000000007d0000401, 0x1c0130000000800000, 0x1403001804003006e, 0x10000000000000001000400, 0x30000000000000001000304, 0x100000001000400, 0x1402402004003006e, 0x10000000000000001000401, 0x110000000000000272000000b9000000c8000200, 0x700000000000000640000014b0000005a000102, 0x2c000000000074000000e8, 0x10000000c8005c0000, 0xc02001003c04007a, 0x10000000000000001000102, 0x100000001000400, 0x4800000000000003200000002900000898000204, 0x34000000000070000000e0, 0xc02000c024044082, 0x100000001000600, 0x220000000000000002000036330000007d000506, 0x3a000000000000001900000003b00000c80000105, 0xc02c01402c04007a, 0x100000001000602, 0x30000000000000011000006900000001c000006, 0x1500000000000000a800000097000000a4000100, 0x800640000002c0000, 0x1803401803403006e, 0x100000001000503, 0x30000007500000001000005, 0x30000000000000001000005, 0x2800000000007c000000ec, 0x1002801403403c076, 0x10000000000000001000003, 0x9000000000000000f000006cc0000001d000206, 0xc100000000000004a50000018f00000179000302, 0x1802c018038038072, 0x7000000000000018f0000017b00000082000103, 0x1f00000000000000d000000247000000bd000001, 0x13000000000000011b0000006800000061000300, 0x1400000000008000000100, 0x40000000000ac00640000, 0x400000000003800200000, 0x10018024058034062, 0x10000000000000001000204, 0x300000001000300, 0x430000000000000002900000000000007d0000403, 0xc0068000000340000, 0x18028020050034062, 0x10000000000000001000301, 0x10000000000000001000203, 0x300000001000100, 0x1c000000000088000000f8, 0xc02002005003406a, 0x10000000000000001000002, 0x100000001000503, 0x250000000000000256000000ba000000c1000205, 0x1402002405002c066, 0x25000000000000018e0000017900000082000102, 0x500000000000000100000002c0000000f000001, 0x9000000000000003c0000001400000013000200, 0x4000000b000680000, 0x80064000000280000, 0x1403401c048034062, 0x10000000000000001000302, 0x10000000000000001000103, 0x300000001000200, 0x1c00000000007c000000f8, 0x1402801c04803806a, 0x10000000000000001000003, 0x100000001000502, 0x105000000000000046a0000048e000004a7000305, 0x800000000002c00000054, 0x1402c020048034066, 0x30000000000000001000004, 0xb1000000000000046f00000d71000004d8000102, 0x2100000000000004d8000004690000047b000401, 0x1803002404c028066, 0x210000000000000eaf000004830000041f000204, 0x1200000000000004740000047d0000019f000002, 0xe100000000000004bb00000d4d0000049a000400, 0x100124000000740000, 0x400000034002c0000, 0x1803c020040034062, 0x100000001000704, 0x30000000000000001000007, 0x10000000000000001000100, 0x1c00000000007c000000f8, 0x1803c01803c03806a, 0x100000001000800, 0xc000000000000001d00000eca0000003d000608, 0x10000000000000001000206, 0x800000000002c00000054, 0x1803c02003c034066, 0x300000001000900, 0x3000000000000002300000d710000003e000109, 0x10000000000000001000301, 0x2003c01c040034062, 0x900000000000004a0000000400000000b000902, 0x1000000000000000a0000019400000007000009, 0x68000000000000023e00000275000000c5000200, 0x1c00000000007c000000f8, 0x1803001c03c03806a, 0x10000000000000001000002, 0x180000000000000497000004d70000045d000501, 0x9300000000000002270000024a00000264000205, 0x800000000002c00000054, 0x1803401c040034066, 0x30000000000000001000003, 0x18300000000000004700000049a000004b9000102, 0x15300000000000004b90000046e0000049a000301, 0x20038020044034062, 0x19b00000000000002600000027000000211000203, 0x1320000000000000d5f0000049d000004be000002, 0x5d000000000000047b00000de0000004ba000300, 0x800000000009800740000, 0x140000000000a400000100, 0x100000000000a000640000, 0x1001802805c028062, 0x10000000000000001000107, 0x100000001000300, 0x430000000000000002900000000000007d0000503, 0x14024028054028062, 0x10000000000000001000100, 0x100000001000302, 0x330000000000000100000000e9000000e0000003, 0x1c0130000000980000, 0x400000000002c00000058, 0x1c03002805403005a, 0x30000000000000001000008, 0x10000000000000001000300, 0x100000001000801, 0x80064000000300000, 0x1c034028054028056, 0x10000006000000001000409, 0x10000000000000001000409, 0x300000001000900, 0x1c03002405802805a, 0x300000000000000270000049e00000019000009, 0x9000000000000022800000252000000d1000100, 0x100000000000004e60000004c0000000b000901, 0x400000000003000280000, 0x1402402c05803005a, 0x3000000000000002100000eb20000004c000108, 0x30000000000000001000001, 0xf0000000000000daa0000004f00000029000802, 0x1802802805403005a, 0xde00000000000002310000075900000260000100, 0xa500000000000004c0000004b70000044e000201, 0x3c90000000000000d41000004e00000049a000002, 0x400000000002c00000058, 0x3400280000, 0x80064000000300000, 0x1000000000008800000104, 0x1c03402404c03005e, 0x10000000000000001000001, 0x300000001000502, 0x30000000000000001000105, 0x4000000000094007c0000, 0x1c03402805003005a, 0x30000000000000001000405, 0x10000000000000001000004, 0x30000000000000001000201, 0x100124000000800000, 0x1c03c02404c03005a, 0x30000000000000001000500, 0x30000000000000001000405, 0x100000001000500, 0x140128000000940000, 0x2003802404c03005a, 0x30000000000000001000602, 0x9c000000000000047a000004a1000004c3000301, 0x10000000000000001000003, 0x1c03402005002805e, 0x1b00000000000001950000017200000197000002, 0x12f000000000000047b000004bf000004a0000300, 0x33900000000000004c1000004c300000481000203, 0x140000000000a400000100, 0x1802c020050028062, 0x10000000000000001000004, 0xb7000000000000047500000de0000004c0000501, 0x18f00000000000004e0000004bd00000460000405, 0x1c03002805002805e, 0xf60000000000000e2e000004790000049d000104, 0x4b00000000000004c300000e3700000454000001, 0xa5000000000000044e000004c0000004b7000400, 0x400600000002c0000, 0x4000000b000680000, 0x2004001c04803005a, 0x30000000000000001000302, 0x100000001000100, 0x30000000000000001000100, 0x1000000000008800000104, 0x2004002404003005e, 0x100000001000900, 0x300000000000000090000036000000010000609, 0x30000000000000001000206, 0x2404002004403005a, 0x300000001000904, 0x6000000000000001f00000e4600000041000009, 0x3000000000000000c0000000c0000000d000100, 0x40000009800800000, 0x1000000000008800000104, 0x1803802404803005e, 0x10000000000000001000003, 0x100000001000601, 0x500000000000001a00000007f00000080000306, 0x1c03c02404803005a, 0x2700000000000004a4000004c50000017f000203, 0x1000000010000000300000002010002, 0x3400000000000004c30000017e0000018b000300, 0x4000000b000680000, 0x1803c01c04802c05e, 0x3f0000000000000e4600000481000004a2000201, 0x100000001000600, 0x1500000000000000d0000000bf000000c0000106, 0x2003c01c04403005e, 0xf90000000000000750000002510000022a000200, 0x123000000000000047900000e40000004a0000602, 0x9f00000000000002500000023d00000260000006, 0x40060000000300000, 0x3400280000, 0x400000000008800000110, 0x2404002404c02c052, 0x100000001000100, 0x30000000000000001000100, 0x30000000000000001000201, 0x40118000000800000, 0x2404802404c02804e, 0x24000004e90000000d00020a, 0x3000000000000000100020a, 0x10000000000000001000001, 0x8011c000000880000, 0x2404402804c02804e, 0x1200000000000000120000072f0000002300010b, 0x1200000000000002410000025300000264000201, 0x10000000000000001000002, 0x24040028050028052, 0x3000000000000002500000df20000004700000b, 0x30000000000000481000004a6000004c8000200, 0xf000000000000072c0000002400000011000b02, 0x800000000008c0000010c, 0x40000008c008c0000, 0x2404002804802c056, 0x10000000000000001000102, 0x100000001000400, 0x3000000030000000300000002030204, 0x4000000a400740000, 0x1c04402004802c056, 0x100000001000a02, 0x1000000000000000100000a, 0x300000000000000260000006900000023000105, 0x2404402404402c056, 0x90000000000000eb2000000430000001d000a00, 0x50000000000000011000002520000000b00050a, 0x3b000000000000018c0000047f00000197000005, 0x400000000008800000110, 0x2404402404802c052, 0x100000001000900, 0x3000000000000002000000e5200000043000109, 0x2e00000000000004a50000018000000197000201, 0x2804802804802804e, 0x4e9000000450000000a000902, 0x21000000000000002300000df200000044000009, 0x1700000000000004a60000018100000198000200, 0x400000000008800880000, 0x1001240000008c0000, 0x2003c02c05002c052, 0x50000000000000011000002640000000c000209, 0x10000000000000001000102, 0x100000001000400, 0x140128000000940000, 0x2003802c05002c056, 0x600000000000004a3000004c60000047d000105, 0x100000001000402, 0x10000000000000001000004, 0x1c03402405402805a, 0xdb00000000000004bd0000047b000004a0000005, 0x13000000000000047b0000018c00000197000400, 0x12500000000000001a20000049d00000181000504, 0x40000000000ac00640000, 0x1001240000008c0000, 0x2003c020050024056, 0x300000000000000660000001f00000022000302, 0x100000001000401, 0x10000000000000001000004, 0x2003802405002405a, 0x300000000000000220000001f00000022000002, 0x1d000000000000047c0000018c00000197000400, 0xcd0000000000000197000004ea00000176000204, 0x30002c0000, 0x2003c02804c02c056, 0x1c0000000000000139000000630000005d000301, 0x300000001000400, 0x3000000000000000b0000001e0000000b000104, 0x1c04002004c02405a, 0x500000000000000d1000000b400000044000300, 0x1700000000000001800000019700000084000403, 0x300000000000004e60000048000000181000004]
private def bspMeta_23 : ℕ × ℕ × ℕ := (608, 2000, 11)

private def bspWords_24 : List ℕ := [0x40000008c00980000, 0x401240000008c0000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x1c013c000000980000, 0x40000000000300000005c, 0x400000000009400880000, 0x1c03402c05403005e, 0x30000000000000001000107, 0x100000001000200, 0x10000000000000001000200, 0x140134000000880000, 0x400040000, 0x1c03c02c05003005e, 0x30000000000000001000302, 0x2400000001000100, 0x10000000000000001000100, 0x1000000000009400000110, 0x1c03c02804c030062, 0x100000001000700, 0x105000000000000050d00000049000004ee000700, 0x10000000000000001000207, 0x800980000004c0000, 0x2404002804c03005e, 0x300000001000805, 0xba000000000000050e000000db000004ed000805, 0x20000000000000001000001, 0x2003c02405003005e, 0xd00000000000000230000028600000013000002, 0x3c00000000000002860000052a00000273000100, 0x1700000000000005090000002600000023000201, 0x1400000000008c0000010c, 0x1c034020050034066, 0x10000000000000001000002, 0x4800000000000004b3000000ff0000055c000601, 0x10000000000000001000406, 0x140000000000b00000010c, 0x1c034024050028066, 0x10000000000000001000003, 0x1e00000000000000b2000000b8000000bd000102, 0x1a4000000000000052900000554000004c7000301, 0x1c038028050028062, 0x600000000000000270000002500000026000203, 0x14a00000000000005090000054b000004c5000002, 0x6000000000000004be000005300000052d000300, 0x40064000000300000, 0x400000000004c0000008c, 0x2404402804c02c05a, 0x200000001000500, 0x3900000000000002990000004900000289000500, 0x30000000000000001000102, 0x40000000000940000011c, 0x400040000, 0x2404402c05002c056, 0x1000000000000000100010a, 0x2400000001000200, 0x30000000000000001000302, 0x80128000000940000, 0x2804802804c02c056, 0x1000000010000002400000002020701, 0x6f000000000000050f0000004900000535000807, 0x10000000000000001000003, 0x2004802805002405a, 0x20000000000000026000004a000000025000001, 0x21000000000000050f0000029800000275000300, 0x1000000000000029b0000002300000012000103, 0x40000000000a00000011c, 0x28048028050028056, 0x1000000000000000100000a, 0x2400000000000002750000029900000288000106, 0x690000000200000001000a01, 0x2804802c05002c052, 0x24000000000000002400000f9c0000004900060a, 0x24000000000000051000000534000004ed000006, 0x3000000000000075f0000002500000014000a00, 0x140134000000940000, 0x400000000009400880000, 0x800000000008c00000118, 0x2003c02c05403005a, 0x1000000000000000100000a, 0x100000001000401, 0x10000000000000001000204, 0x800980000004c0000, 0x2404002c05402c056, 0xc0000000000000025000005330000001900040b, 0x10000000000000001000204, 0x200000001000b00, 0x2003c02805802c05a, 0x1000000330000000100000b, 0x600000000000002730000050f00000299000100, 0x300000000000002490000000b00000005000b01, 0x800980000004c0000, 0x40000000000ac00700000, 0x2404002405402805a, 0x4500000000000007c80000027500000287000402, 0x100000001000500, 0x20000000000000001000105, 0x2404002405003005a, 0x600000000000000690000002300000020000400, 0x4800000000000004e60000052e000001af000504, 0xf6000000000000050c00000eb20000052d000005, 0x2003c02405402805e, 0x33000000000000052f0000026000000299000001, 0x7b00000000000007590000052d00000286000400, 0x3d5000000000000052f00000f93000004eb000104, 0x80068000000340000, 0x2003802805803005a, 0x30000000000000005000002490000000b000109, 0x330000000000000ea60000050b0000052f000301, 0x30000000000000001000003, 0x1c03402805c02c05e, 0x30000006300000002000009, 0x3000000000000027000000285000000dd000300, 0x500000000000005510000004f0000000c000903, 0x1c0000000000ac00000104, 0x400000000005800340000, 0x1001c02405802c06e, 0x10000000000000001000105, 0x200000001000500, 0x235e00000000000003e80000027300007148000105, 0x1000000000004c00000080, 0xc020024050034072, 0x200000001000500, 0x2d000000000000013f0000005b00000133000500, 0x7200000000000007d00000009d00001f40000106, 0x1002802005002c06e, 0x10000000000000001000201, 0x1f80000000000000501000000ff000005a4000503, 0x45000000000000028d000002640000013d000100, 0x100000000000ac00640000, 0x1400000000008c0000010c, 0x1001c028060034066, 0x10000000000000001000008, 0x10000000000000001000100, 0xea00000000000004b00000001100000320000806, 0x14020028060028062, 0x10000005d00000001000108, 0x10000000000000001000108, 0x2520000000c00000005000800, 0x800000000008c008c0000, 0x140000000000a40000010c, 0x1402403005802c066, 0x100000001000100, 0x10000000000000001000100, 0x5700000000000000f5000000fd00000102000203, 0x1802c03005803005e, 0xf000000000000002400000ff30000004f000409, 0x10000000000000001000104, 0xde000000000000027e000002690000028b000200, 0x400000000001c0000002c, 0x400000000005800340000, 0x1802802405802c06a, 0x60000000000000001000102, 0x200000001000400, 0xb100000000000004a50000059b000004ec000204, 0x1802c02405002c06a, 0x600000001000501, 0x7e000000000000052a0000053c0000048f000405, 0x18000000000000005c0000003100000033000004, 0x1400000000008c0000010c, 0x1802c028054034066, 0x100000001000500, 0x300000000000001b90000004900000043000105, 0x270000000000000067000002bc00000069000201, 0x14030024058034062, 0x1e00000000000000ee0000011000000111000502, 0x9600000000000004da0000050600000529000005, 0x9000000000000008b0000008500000077000200, 0x401240000008c0000, 0x2804c02804c02c056, 0x210000000000000f330000004700000026000301, 0x10000006f00000001000003, 0x10000000000000001000003, 0x400000000001000000020, 0x40000003c00280000, 0x140000000000500000007c, 0xc02001c04403407a, 0x20000000000000001000004, 0x300000001000501, 0x85e00000000000007d00000017300004844000405, 0x1000a0000000440000, 0x1403001c04403c072, 0x80000000000000001000300, 0x30000000000000001000203, 0x200000001000300, 0x14000c0000, 0x1402002005003c072, 0x80000000000000001000406, 0x90000000000000001000001, 0x4200000000000000c400000206000000cd000602, 0x1002801c04803c072, 0x1800000000000001a0000007e0000000cd000100, 0x27000000000000013d0000014b00000096000201, 0x2d0000000000000732000001a5000000d7000002, 0x2c000000000080000000f4, 0x80000003c002c0000, 0xc02001803804007e, 0x100000001000701, 0x30000000000000001000007, 0x79200000000000004b00000004500000dac000206, 0x38000000000074000000e8, 0x1002000c02c04808a, 0x100000001000800, 0x60000000000000003000056b8000000c8000708, 0x25920000000000002ee0000005e500012110000107, 0x1002401003404007e, 0x100000000000004f30000003d0000000b000801, 0x10000008100000002000008, 0x90000000000000e9d000005bc000004a5000100, 0x800680000002c0000, 0x1803801803803c072, 0x800000001000703, 0x3000000000000002100000ed90000003d000107, 0x30000000000000001000001, 0x2800000000007c000000f8, 0x1402c01803804007a, 0x10000000000000001000003, 0x7b000000000000054900000ed9000004d2000201, 0x360000000000000ecd00000546000004d3000302, 0x1803001c03c038076, 0x1b0000000000000519000004da000001a9000103, 0xe1000000000000054d00000e88000004f7000001, 0xb70000000000000ee50000054b000004d8000300, 0x800980000004c0000, 0x40000000000300000005c, 0x80000009400940000, 0x40064000000300000, 0x2404402804803005e, 0x300000001000802, 0x10000000000000001000108, 0x30000000000000001000001, 0x800000000004400000088, 0x24040028048034062, 0x20000000000000001000007, 0x10000000000000001000201, 0x20000000000000001000402, 0x400640000002c0000, 0x2004402004c03005e, 0x3c60000000000000ec70000050d0000055a000208, 0x8100000000000004e5000007c500000286000102, 0x300000001000800, 0x2404002404c03005e, 0x17100000000000004ed000001bb000001bd000008, 0x2100000000000001a100000286000000dd000100, 0x8d0000000000000143000002bf00000132000801, 0x1400000000008c0000010c, 0x24040024040034066, 0x100000001000800, 0x20000007200000001000308, 0x20000000000000001000308, 0x800000000004400000088, 0x40064000000300000, 0x24044024044034062, 0x200000001000a01, 0x15000000000000002400000f210000004300020a, 0x30000000000000001000002, 0x24040020048034062, 0x3720000000000000ebe0000050c00000559000003, 0x15000000000000050b00000f7e000004e7000200, 0xff0000000000000273000002bf00000275000302, 0x1c04802404803005e, 0x1b0000000000000f2d0000004500000025000902, 0x10000003900000001000009, 0x600000000000000280000004a00000025000200, 0x800000000008c00000118, 0x80128000000940000, 0x2804802804803005a, 0x100000001000801, 0x900000000000000250000050f00000017000208, 0x10000000000000001000002, 0x1c04802404c03005a, 0x43500000000000004ec0000050f00000559000006, 0x1b0000000000000f2d0000052f000004ea000200, 0x60000000000000055600000ed0000004ed000602, 0x2004c02804c02c056, 0x4ec00000000000005110000051000000535000405, 0x6f000000030000000200000004070004, 0x2100000000000001c7000001a5000001a4000500, 0x1c0000000000a000000104, 0x40034000000180000, 0x1c03801c04003006e, 0x100000001000701, 0x40000003c00000001000307, 0x60000000000000001000003, 0x4000000a400800000, 0x1402c02404c03006e, 0x10000000000000001000206, 0x100000001000400, 0x3000000000000001c000000f100000018000604, 0x40000005000440000, 0x1803002404803006e, 0x10000000000000001000301, 0x200000001000500, 0x1500000000000000a40000054f00000098000105, 0x1803402004403806e, 0x8400000000000007560000028100000155000200, 0x1b00000000000002a9000001d400000050000502, 0xf00000000000000a4000002a90000004c000005, 0x800000000002c00000058, 0x140134000000940000, 0x2003c02004003806a, 0x30000000000000001000100, 0x300000000000000070000032d0000000d000208, 0x10000000000000001000002, 0x4000000b000740000, 0x1803402004c03806a, 0x30000000000000001000207, 0x100000001000300, 0xed00000000000004dd00000581000004f1000703, 0x1c03801c04803806a, 0x3000000010000000100000002020100, 0xc600000000000005060000055a00000497000301, 0x8a000000000000025d000002810000029e000003, 0x1400000000008c0000010c, 0x4000000b000740000, 0x1803802004c034066, 0x10000000000000001000107, 0x10000000000000001000004, 0x5100000000000001c30000055d0000018c000702, 0x1c03c01c048034066, 0x2700000000000005290000027300000286000400, 0x60000000000000286000001b8000000d1000204, 0x900000000000000280000007100000027000002, 0x2003c02004c034062, 0x11a00000000000004c800000286000002bf000306, 0x2700000000000002860000052900000273000003, 0x3600000000000000b8000000c9000000af000600]
private def bspMeta_24 : ℕ × ℕ × ℕ := (598, 2000, 10)

private def bspWords_25 : List ℕ := [0x2000000000008c0000010c, 0x40000004000280000, 0x2800000000009400000104, 0x1402001c04803c07e, 0x10000000000000001000003, 0x300000001000301, 0x20000000000000000b00000000000001f4000301, 0x4000240000, 0x1402002005403c076, 0x10000000000000001000304, 0x30000000000000001000003, 0x20000000000000000b00000000000001f4000401, 0x20014c000000a00000, 0x1c03401c04803c076, 0x10000000000000001000400, 0x30000000000000001000304, 0x100000001000400, 0x8000000ac00880000, 0x1802802404c03c076, 0x1000000010000000300000002050102, 0x10000000000000001000001, 0x1e30000000000000f9f000005b60000055d000203, 0x1403001c04803807a, 0x2d00000000000002b60000028d000002f5000100, 0x2100000000000000620000005e00000057000301, 0xe70000000000000560000005bc00000547000003, 0x2c00000000008000000100, 0x3400000000007c000000f8, 0x1002400c03004808a, 0x100000001000500, 0x24000000000000000300005910000000c8000405, 0xc400000000000003e80000005300000fa0000204, 0x20014c000000880000, 0x14034014038044082, 0x100000001000602, 0x90000000000000010000007fe0000001f000106, 0x10000000000000001000001, 0x10024018038044082, 0x10000000000000001000203, 0x2bb00000000000005dd0000053500000554000100, 0x810000000000000573000001f2000001b2000301, 0x8006c000000300000, 0x1c03c01c03c03c076, 0x100000001000503, 0x30000007e00000001000005, 0x30000000000000001000005, 0x2800000000008800000104, 0x1803001803c04007e, 0x10000000000000001000003, 0x1500000000000000210000102000000040000206, 0x500000000000000ac0000003d00000038000302, 0x1c03401804403c07a, 0x400000000000000ec000000e10000004d000103, 0xa00000000000001cd00000584000001c1000001, 0x19000000000000010d000000620000005c000300, 0x800000000003c0000005c, 0x80000000000bc00680000, 0x100000000000b800640000, 0x1402002806402c06e, 0x30000000000000001000206, 0x100000001000400, 0x20000000000000000b00000000000001f4000400, 0x1c00000000009400000110, 0x1402002405c038072, 0x10000000000000001000001, 0x100000001000402, 0x20000000000000000b00000000000001f4000504, 0xc0070000000300000, 0x1403002405c02c06e, 0x30000000000000001000400, 0x10000000000000001000304, 0x300000001000400, 0x400000000003c00240000, 0x1402402806002c06e, 0x30000000000000001000503, 0x30000000000000001000001, 0x32d00000000000005ae0000055900000547000302, 0x1802802405c03406e, 0x1100000000000000e7000000f400000048000100, 0xff00000000000002860000081f000002da000201, 0x1500000000000000810000002b00000029000002, 0x8006c000000300000, 0x8000000b8007c0000, 0x80000000000300000005c, 0x1c03c02004c03806e, 0x30000000000000001000002, 0x100000001000201, 0x30000000000000001000201, 0x4000000b000800000, 0x1c03c02405002c06e, 0x30000000000000001000503, 0x10000000000000001000005, 0x30000000000000001000301, 0x1c04002004c02c06e, 0x30000000000000001000500, 0x10000000000000001000205, 0x4b0000000000000166000003f60000015d000001, 0x1c00000000009400000110, 0x1c03c01c044038072, 0x100000001000700, 0xc0000000000000020000010ad00000043000507, 0x3000000010000000100000002020105, 0x80000000000300000005c, 0x2004002404403806e, 0x300000001000800, 0x300000000000000130000083100000022000108, 0x51000000000000054d0000057200000591000201, 0x2404402004802c06e, 0x300000001000005, 0x300000000000001fe000001dd00000017000005, 0x3000000000000005510000106500000596000200, 0x38002c0000, 0x20014c000000a00000, 0x1c03402805402c06e, 0x30000000000000001000403, 0x30000000000000001000102, 0x100000001000300, 0x1802802805403806e, 0xd200000000000005710000059500000542000003, 0x300000001000501, 0x15000000000000002b0000002b00000029000305, 0x1c00000000008800000110, 0x4000000b000800000, 0x1803002405003c072, 0x10000000000000001000102, 0x100000001000600, 0x1000000000000001d0000000a00000009000206, 0x1c03402404803c072, 0x10000000000000001000100, 0xa900000000000001ec0000054e000001cf000603, 0x1cb000000000000056b000005c00000054c000006, 0x40000009800980000, 0x1c03402c05003006e, 0x1600000000000001dc000001c50000009b000302, 0x10000000000000001000003, 0x630000000000000594000001eb000001ba000201, 0x1803802005003806e, 0xad0000000000000532000001dd000001ee000300, 0x7900000000000001c100000572000001dc000103, 0x4200000000000002db000002e500000286000001, 0x40040000000200000, 0x400000000003000000060, 0x4000000a4008c0000, 0x38002c0000, 0x24040028054034062, 0x30000000000000001000203, 0x300000001000300, 0x50000000000000001000300, 0x100000000000940000011c, 0x24040028050034066, 0x10000000000000001000001, 0x100000001000402, 0x50000000000000001000402, 0x20044028050034062, 0x30000000000000001000301, 0x10000000000000001000203, 0x38000000000000059e000001c5000001d3000100, 0x8000000a000940000, 0x400680000002c0000, 0x2004802804c034062, 0x300000001000803, 0x10000000000000001000108, 0x30000000000000001000001, 0x400000000001c00000038, 0x2404002804c03806a, 0x500000001000200, 0x10000000000000001000200, 0x50000000000000001000506, 0x1c04402804c034066, 0xc9000000000000106e0000059f00000551000103, 0x10000000000000001000201, 0x90000000000000062000001c50000005b000300, 0x400000000001c00000038, 0x1c04402004803806a, 0x500000001000800, 0x30000000000000021000005fa00000017000508, 0xa800000000000005390000106b000005c3000105, 0x100000000000940000011c, 0x40068000000340000, 0x28048028048034066, 0x100000001000a01, 0x30000000000000027000003330000000e00020a, 0x30000000000000001000002, 0x1c04802004c034066, 0x151000000000000057b000001c7000001ee000003, 0x100000000000001d40000011f0000005b000200, 0xf0000000000000062000001c60000005b000302, 0x2004c02404c034062, 0x2100000000000010740000004800000025000902, 0x60000000000000022000010d700000047000009, 0xea00000000000005a0000005530000057b000200, 0x800000000009800000124, 0x40000000000b800700000, 0x400000000009400940000, 0x2404003005803005e, 0x10000000000000001000209, 0x100000001000300, 0x50000000000000001000403, 0x10013c000000980000, 0x2404402405803005e, 0x10000000000000001000301, 0x100000001000402, 0x10000000000000001000004, 0x24040028058028062, 0x300000000000000250000002200000025000001, 0x1f0000000000000551000001d4000001e0000400, 0x410000000000000078000001720000006f000104, 0x40000009800980000, 0x40068000000340000, 0x2804802c05003005e, 0x10000000000000001000302, 0x100000001000401, 0x30000000000000001000004, 0x3400300000, 0x2404402c05403005e, 0x3d00000000000002e1000000ea000000dd000103, 0x300000001000500, 0x100000000000000040000000b00000004000305, 0x20048024054028062, 0x2100000000000005c400000507000001e1000100, 0x1900000000000001c7000001e00000009c000501, 0x100000000000001ec000001c700000098000005, 0x4000000b000800000, 0x2004c02405003005e, 0x100000001000903, 0x10000000000000001000009, 0x300000000000000290000007200000026000104, 0x2804c02804c03005e, 0x9000000000000114c0000004900000020000900, 0xb00000000000000250000057c00000018000409, 0x1000000000000000750000015500000078000004, 0x80134000000940000, 0x400000000009400000128, 0x2804c02805003005a, 0x100000001000800, 0x30000000000000023000010e300000049000208, 0x10000000000000001000102, 0x3400300000, 0x2804c02c05402c056, 0x30000006f0000000100000a, 0x3000000000000000100000a, 0x10000000000000001000201, 0x40000000000a000000128, 0x2805002c05002c05a, 0x100000001000200, 0x1200000000000002d2000002bf00000025000200, 0x2700000000000010e9000005570000057e000102, 0x2c05002c05002c056, 0x1e10000001900000004000a01, 0x120000000000000013000008760000002500000a, 0x120000000000000804000002bf000002d1000100, 0x40068000000340000, 0x40000000000ac007c0000, 0x2804802805802c05a, 0x300000000000000280000107a0000004d00020a, 0x100000001000300, 0x30000000000000001000103, 0x2804802805403005a, 0x300000000000000250000002500000022000200, 0x1e00000000000001110000012000000119000302, 0xb7000000000000057c000005550000059f000003, 0x10013c000000980000, 0x2404402805803005a, 0xb0000000000000025000005a30000001a00010a, 0x3d00000000000001c70000059f000001d4000301, 0x10000000000000001000003, 0x2404002c05c02c05e, 0x60000000000000029000010710000004f00000a, 0x600000000000005520000057b000005a1000300, 0xf00000000000008700000002800000013000a03, 0x8000000000098008c0000, 0x20014c000000a00000, 0x100000000000b80000011c, 0x1c03403005c028066, 0x10000000000000001000008, 0x10000000000000001000200, 0x100000001000801, 0x8006c000000340000, 0x2003c03005c03005e, 0x30000000000000013000001b000000008000409, 0x10000000000000001000304, 0x300000001000900, 0x1c03403005c02c062, 0x1000000000000000e000001d200000009000009, 0xde000000000000059f000010d400000527000100, 0x240000000000000fd5000000530000002e000901, 0xc0070000000380000, 0x1c03003005c02c066, 0xc000000000000002b0000104d00000053000108, 0x100000001000402, 0x30000000000000001000004, 0x1402402c060030066, 0x2000000000000000a0000016500000007000008, 0x2d00000000000002ca000002c4000000d9000400, 0x200000000000001c90000001d00000005000804, 0x140000000000b000000118, 0x40000000000ac007c0000, 0x1c03002805802c06a, 0x10000000000000001000102, 0x100000001000400, 0x3930000000000000516000011b800000577000204, 0x38002c0000, 0x2003802805402c06a, 0x10000000000000001000201, 0x300000001000500, 0x12900000000000004f7000010d1000005ae000105, 0x2003c02405002c06a, 0x1000000000000003d000000200000000c000400, 0x300000000000000d8000001750000003e000504, 0x3000000000000004fe0000059d000001e7000005, 0x100000000000a00000011c, 0x8006c000000340000, 0x2003c028054030066, 0x10000000000000001000100, 0x30000000000000024000000b700000020000204, 0x300000001000100, 0x1c03402c058030066, 0x10000000000000001000103, 0x2a00000000000002cf0000086400000293000200, 0x2d00000000000000360000003b00000038000302, 0x80000000000b000740000, 0x2003802805c028062, 0xf00000000000001df0000005800000060000403, 0x10000000000000001000004, 0x1b300000000000002b9000002e2000002ab000301, 0x2003c028058034062, 0x3000000000000015f0000004800000044000400, 0x2700000000000001180000059700000110000104, 0x16200000000000005750000054b00000594000001]
private def bspMeta_25 : ℕ × ℕ × ℕ := (588, 2000, 10)

private def bspWords_26 : List ℕ := [0x40000009800a40000, 0x4013c000000980000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x1c0154000000a40000, 0x400000000003400000064, 0x40000000000a000940000, 0x2003c03005c034066, 0x30000000000000001000107, 0x100000001000200, 0x10000000000000001000200, 0x14014c000000940000, 0x400040000, 0x20044030058034066, 0x30000000000000001000302, 0x2700000001000100, 0x10000000000000001000100, 0x800000000005000000094, 0x2004402c05403406a, 0x200000001000700, 0x8d00000000000002f70000004f000002e6000700, 0x10000000000000001000207, 0x100148000000a40000, 0x2804802c054034066, 0x300000001000805, 0xc900000000000005ef000000ed000005cb000805, 0x10000000000000001000001, 0x24044028058034066, 0x1d0000000000000026000005ed00000029000002, 0x4200000000000005ed00000307000002e2000100, 0xd00000000000002f50000002900000013000201, 0x1400000000009800000124, 0x2003c02c05403806e, 0x10000000000000001000002, 0x1b900000000000006150000004f00000643000601, 0x10000000000000001000406, 0x140000000000bc00000124, 0x2003c02805802c06e, 0x10000000000000001000003, 0xe100000000000005bc000005e90000060f000102, 0x23a000000000000060d0000063b000005a2000301, 0x2004002c05802c06a, 0x6000000000000002a0000002800000029000203, 0xb400000000000002f500000319000002d0000002, 0x6900000000000005990000061400000611000300, 0x4006c000000340000, 0x80000000000a400000130, 0x2804c02c054030062, 0x100000001000500, 0x7b00000000000006160000004f000005f3000500, 0x30000000000000001000102, 0x40000000000a000000134, 0x400040000, 0x2804c03005803005e, 0x1000000000000000100010a, 0x2700000001000200, 0x30000000000000001000302, 0x400a0000000500000, 0x2c05002c05403005e, 0x1000000010000002700000002020701, 0x7800000000000005f00000004f00000619000807, 0x20000000000000001000003, 0x2405002c058028062, 0x10000000000000029000002bc00000014000001, 0x900000000000000be00000185000000b9000300, 0x2000000000000061a0000002600000027000103, 0x40000000000ac00000134, 0x2c05002c05802c05e, 0x1000000000000000100000a, 0x4e00000000000005c800000616000005f1000106, 0x720000000200000001000a01, 0x2c05003005803005a, 0x270000000000000027000012480000004f00060a, 0x2700000000000005f100000618000005cb000006, 0x60000000000001158000000500000002b000a00, 0x14014c000000a00000, 0x40000000000a000940000, 0x400000000004c00000098, 0x2404403005c034062, 0x2000000000000000100000a, 0x100000001000401, 0x10000000000000001000204, 0x100148000000a40000, 0x2804803005c03005e, 0xd0000000000000028000006170000001b00040b, 0x10000000000000001000204, 0x100000001000b00, 0x2404402c060030062, 0x10000006f0000000200000b, 0x600000000000005c4000002f80000030b000100, 0xc000000000000095a0000005300000013000b01, 0x100148000000a40000, 0x40000000000b8007c0000, 0x2804802805c02c062, 0x96000000000000123c000005c8000005ef000402, 0x100000001000500, 0x10000000000000001000105, 0x28048028058034062, 0x600000000000000720000002600000023000400, 0x2700000000000002e200000309000000fd000504, 0x10b00000000000005ed0000114c00000611000005, 0x2404402805c02c066, 0x6f00000000000006130000059b00000616000001, 0x10b000000000000114c00000611000005ed000400, 0x49b00000000000006130000123f000005c9000104, 0x400380000001c0000, 0x2404002c060034062, 0x180000000000000026000012b400000053000109, 0x360000000000001140000005ec00000613000301, 0x60000000000000001000003, 0x2003c02c064030066, 0x30000003600000001000009, 0x300000000000002df000005eb00000103000300, 0x60000000000000638000000550000000d000903, 0x1c0000000000ac0000011c, 0x280160000000a40000, 0x18030024058034076, 0x10000000000000001000100, 0x1aa00000000000005e20000011400000691000402, 0x10000000000000001000004, 0x400000000005800400000, 0x1402002c060034076, 0x10000000000000001000206, 0x200000001000600, 0x2ab000000000000001700000000000003e8000600, 0xc0000000000340000005c, 0x1002402805803c07e, 0x30000000000000001000001, 0x183000000000000062f000000c5000006ba000602, 0x47f00000000000003e80000008300001770000107, 0x1002802805803c076, 0xd500000000000002ce0000062900000302000201, 0x83000000000000062f000001e8000001f1000002, 0x250000000000000209000002fe000000ee000100, 0x800000000005c00380000, 0x800000000003c00000060, 0x1402002c068030072, 0x30000000000000001000008, 0x20000000000000001000100, 0x2ab000000000000001700000000000003e8000602, 0x1802802c06802c06a, 0x20000006600000001000108, 0x20000000000000001000108, 0x630000000600000001000800, 0x400000000004000240000, 0x140000000000a400000124, 0x1402c02806403406e, 0x100000001000100, 0x30000000000000001000100, 0x4b00000000000005fd000002d2000002e9000203, 0x800000000005000000094, 0x1c03402806403406a, 0x200000001000500, 0x30000000000000001000205, 0x210000000000000607000002d8000002ef000301, 0x2003802c064034066, 0x120000000000000027000012a80000005500050a, 0x60000000000000125000000970000009b000005, 0x60000000000000306000002db00000179000300, 0x400000000001c00000030, 0x40000000000ac00880000, 0x1c03002c05c034072, 0x60000000000000001000102, 0x100000001000400, 0x1920000000000001104000005d8000005f3000204, 0x1c034024058034072, 0x600000001000501, 0xd200000000000002f10000030f000002c8000405, 0x3cc00000000000005b100000634000005e1000004, 0x400000000005800400000, 0x1c03402c06003806a, 0xa200000000000005ed000012a50000058d000502, 0x20000000000000001000005, 0x600000000000000320000006100000011000201, 0x1803802805c03006e, 0x990000000000000302000005bb000002f2000500, 0x8100000000000011a900000301000002dd000105, 0x2d00000000000003050000088e00000178000001, 0x4013c000000980000, 0x2c05402c05403005e, 0x2400000000000011d60000004d00000029000301, 0x10000007800000001000003, 0x10000000000000001000003, 0x2000000000008c00000118, 0x800000058004c0000, 0x2800000000009400000110, 0x10024024048040082, 0x10000000000000001000004, 0x200000001000501, 0x62870000000000001770000006e300013880000405, 0x200158000000940000, 0x1803802404804007a, 0x10000000000000001000300, 0x20000000000000001000203, 0x100000001000300, 0x4000000b0008c0000, 0x1402802805404007a, 0x10000000000000001000406, 0x10000000000000001000001, 0x13200000000000005f2000006e200000557000602, 0xc0000000000300000005c, 0x1802c02404c04007e, 0x300000001000200, 0x1410000000000000633000005b8000005d5000302, 0x20400000000000005cf0000068500000595000103, 0x1803402805004007a, 0x2af000000000000059b000006270000060a000201, 0xd500000000000012a500000599000005fe000002, 0x8a00000000000005fd0000129900000598000100, 0x800000000001c0000002c, 0x14000000d0007c0000, 0x1002801804403c08a, 0x60000000000000001000102, 0x100000001000600, 0x2f00000000000003e80000006b00001388000206, 0x1c00000000004000000080, 0x1002801002c04c092, 0x200000001000800, 0x24100000000000000250003d860000007d0000708, 0x2b370000000000000fa00000032300009470000107, 0x1402c01403c03c08a, 0x600000001000802, 0x10000004500000001000008, 0x13500000000000002e00000064d000002d0000100, 0x2800000000009400000110, 0x1c01540000008c0000, 0x1803c018040040082, 0x100000001000801, 0x30000004800000001000208, 0x10000000000000001000002, 0x14030018044044082, 0x2400000000000000ee000001fe00000109000003, 0x1500000000000005cd00000107000000e6000200, 0x2e00000000000000ea000003440000007d000302, 0x14014c000000880000, 0x1c04401c04404007a, 0x100000001000804, 0x10000008400000001000008, 0x10000000000000001000008, 0xc0000000000300000005c, 0x1803c01c04404007e, 0x30000000000000001000004, 0x16ad000000830000005a000000ac090201, 0xab00000000000005d70000031b000002dd000402, 0x1c04001c04804007a, 0x6f0000000000000093000001340000009b000104, 0x25e0000000000001104000005fe000005dd000001, 0x7800000000000002ee000004aa0000016f000400, 0x1400000000009800000124, 0x14014c000000940000, 0x8000000c4007c0000, 0x2004402005003806e, 0x10000000000000001000205, 0x100000001000100, 0x10000000000000001000100, 0x400000000001800000030, 0x2004402004803c072, 0x600000001000800, 0x10000008100000002000408, 0x10000000000000001000204, 0x2804802404c03806e, 0x100000001000803, 0x30000003f00000001000008, 0x700000000000000f6000005ed00000102000100, 0x1c0000000000940000011c, 0x8000000ac00940000, 0x1c03402805003c076, 0x10000000000000001000106, 0x100000001000400, 0x390000000000000604000006b900000555000604, 0x1c03c02804803c076, 0x10000000000000001000100, 0xf00000000000001480000011f0000012d000402, 0x17d0000000000000604000006390000059b000004, 0x4000000b0008c0000, 0x400000000001800000030, 0x1803c02805403c072, 0x60000000000000001000007, 0x10000000000000001000100, 0x24000000000000013c0000014100000119000702, 0x2004002805403806e, 0x2f400000000000005a40000060f00000643000307, 0x10000000000000001000103, 0xa00000000000000810000033500000075000700, 0x40000005000500000, 0x2003c02c050034072, 0x8a000000000000060a000005c2000005e7000301, 0x20000000000000001000003, 0xde00000000000001f600000213000001eb000102, 0x2004002005003c072, 0x5700000000000000b400000183000000c8000300, 0xf600000000000002db00000303000002f2000203, 0x5700000000000005e300000334000002d0000002, 0x400000000003400000064, 0x4006c000000340000, 0x40000005000500000, 0x2804c02c050034066, 0x300000001000802, 0x20000000000000001000008, 0x30000000000000001000100, 0x1000000000009400000128, 0x2804c02804c03806a, 0x100000001000900, 0x180000000000000027000011c400000049000409, 0x30000000000000001000204, 0x20050028050034066, 0x300000000000001c80000000f00000004000901, 0x10000007b00000002000009, 0x3000000000000002b0000001400000014000100, 0x1000000000009400000128, 0x100148000000a40000, 0x2804802405003806a, 0x10000000000000001000107, 0x1800000000000005ec0000122a000005c5000402, 0x10000000000000001000004, 0x2404402405403806a, 0x2d900000000000005a3000005ed00000668000007, 0x5700000000000005ed0000060d000005c4000400, 0x21000000000000005e900000669000005a4000704, 0x4006c000000300000, 0x2404c024054034066, 0x48c0000000000001161000005ee00000641000207, 0x11700000000000005c300001236000005ed000102, 0x300000001000700, 0x28048028054034066, 0x1b700000000000005cb0000020700000209000007, 0x4700000000000001eb000005ed00000206000100, 0x2d900000000000005ed00000668000005a3000701, 0x400000000004c00000098, 0x4000000b0008c0000, 0x20050028054034062, 0x200000001000801, 0x10000000000000001000008, 0x69000000000000063d0000116a000005cb000602, 0x2c05002c050034062, 0x600000000000012420000004c00000023000800, 0x200000000000000080000013000000005000208, 0x600000000000001280000039000000137000002, 0x2405402c05403005e, 0x5ca00000000000005f2000005f100000619000405, 0x3c000000030000000100000002070004, 0x12000000000000010a000001ef000000f7000500]
private def bspMeta_26 : ℕ × ℕ × ℕ := (579, 2000, 10)

private def bspWords_27 : List ℕ := [0xc00000000004000000060, 0x400000044002c0000, 0x280000000000940000011c, 0x10028020050044086, 0x10000000000000001000003, 0x300000001000301, 0x27ba0000000000001f40000006b700011170000003, 0x4400280000, 0x1402402405c034082, 0x30000000000000001000304, 0x30000000000000001000003, 0x109000000000000002ee000000c100001f40000304, 0x200164000000a00000, 0x1c03c020050034082, 0x30000000000000001000400, 0x30000000000000001000304, 0x100000001000400, 0x4000000c800800000, 0x14034024058034082, 0x30000000000000001000502, 0x10000000000000001000001, 0xd200000000000013bf0000061400000629000203, 0x1c03402405003c082, 0x1b00000000000000ce000000c5000000ca000100, 0x18f00000000000006ac0000062c0000064d000301, 0x750000000000000219000002380000020e000003, 0x100000000000300000005c, 0x80000004400300000, 0x1002c01c04404808e, 0x30000000000000001000102, 0x300000001000400, 0x33e000000000000138800000119000032c8000204, 0x3800000000008c0000010c, 0x1002c01003404c096, 0x100000001000600, 0xa00000000000000070000c4e000000190000506, 0x75120000000000007530000006f300014050000105, 0x1403401803c04808e, 0x300000001000602, 0x120000000000000025000012ab00000043000006, 0x318000000000000129f000006ca00000617000100, 0x280000000000940000011c, 0x10000000d400800000, 0x1803401c04c044086, 0x10000000000000001000103, 0x100000001000200, 0x270000000000000641000006a20000020b000302, 0x1c038018044044086, 0x100000001000601, 0x600000000000000210000066600000017000206, 0x10b000000000000061e000013f200000643000002, 0x400000000001000000020, 0x2003c01c048044082, 0x900000001000600, 0xf00000000000000220000135600000047000106, 0x5a00000000000003140000011d0000010d000301, 0x1c044024048034082, 0x300000001000004, 0x6d0000002100000002000004, 0x1500000000000000b80000020b0000003c000300, 0x800000000003c00000064, 0x80000000000bc00800000, 0x100000000000b8007c0000, 0x1402403006c034076, 0x30000000000000001000206, 0x100000001000300, 0x17200000000000004b00000001300000320000604, 0x2c0170000000b80000, 0x1c03002c064034076, 0x30000000000000001000301, 0x10000000000000001000203, 0x100000001000100, 0x1402402c06403c076, 0x1530000000000000611000006a600000678000001, 0x100000001000402, 0x4110000000000000608000013c500000640000104, 0x4000000bc008c0000, 0x200164000000ac0000, 0x2003c028058034076, 0x30000000000000001000302, 0x10000000000000001000103, 0x100000001000200, 0x200000000000b000000124, 0x1803002805803807e, 0x10000000000000001000003, 0x100000001000502, 0x150000000000000130000003e100000148000305, 0x1c0000000000a000000128, 0x1403402405c03c07a, 0x10000000000000001000004, 0x1e0000000000000065500000691000005ff000102, 0x12000000000000006790000061e0000064d000401, 0x1c03403005c034076, 0x15600000000000006770000062c00000657000204, 0x8700000000000006df0000061400000656000002, 0x1ce000000000000033d0000033e00000319000400, 0x140158000000940000, 0x1c00000000009400000128, 0x2004802404804007a, 0x100000001000700, 0x5000000da00000003000507, 0x10000000000000001000105, 0x8000000c400880000, 0x20048024054034076, 0x30000000000000001000503, 0x100000001000100, 0x10000000000000001000201, 0x100154000000980000, 0x2404c02804c034076, 0x300000001000906, 0x90000000000000029000012a50000004a000209, 0x10000000000000001000002, 0x2004802005003c076, 0x1aa00000000000006830000065f00000630000001, 0x1dd000000000000062d000006810000065c000200, 0x1a100000000000006810000062b0000065c000102, 0x200000000000b000000124, 0x40000003c00340000, 0x1c03c02805003807e, 0x10000000000000001000103, 0x300000001000600, 0xf00000000000005d80000138300000698000306, 0x2004002004c03807e, 0x10000000000000001000100, 0x1b00000000000004bf000001b800000170000602, 0x9b00000000000005b0000006df00000238000006, 0x1c00000000009400000128, 0x1c04002405004007a, 0x10000000000000001000003, 0x45000000000000032c0000035000000307000102, 0xcf00000000000006300000065600000679000301, 0x1c04402405403c076, 0x141000000000000065e000006850000062f000203, 0x1a1000000000000062b0000065c00000681000002, 0xc300000000000006a60000062b00000637000300, 0x140158000000ac0000, 0x400000000003400000068, 0x4000000bc008c0000, 0x100000000000ac00000134, 0x2804802805803406e, 0x10000000000000001000003, 0x100000001000301, 0x10000000000000001000301, 0x3800340000, 0x2804803005c03806a, 0x30000000000000001000304, 0x30000000000000001000003, 0x10000000000000001000401, 0x40070000000340000, 0x2805002805803806a, 0x30000000000000001000400, 0x10000000000000001000304, 0x300000001000400, 0x40002c0000, 0x2004c02805c03806a, 0x30000000000000001000502, 0x30000000000000001000001, 0xa800000000000013b00000063b00000665000203, 0x2804c02c05803806a, 0x1000000000000000d0000000d00000004000100, 0x4b00000000000006640000139e0000063d000301, 0x1c800000000000012ae00000637000006a9000003, 0x8000000ac00a00000, 0x40070000000300000, 0x2405002c05403806a, 0x300000001000803, 0x10000000000000001000108, 0x30000000000000001000001, 0x1400000000009800000130, 0x2804802c05403c072, 0x100000001000200, 0x10000000000000001000200, 0x10000000000000001000506, 0x2404c02c05403806e, 0x207000000000000139b0000068c00000608000103, 0x10000000000000001000201, 0x11100000000000006880000063300000662000300, 0x1400000000009800000130, 0x2004c02405003c072, 0x100000001000800, 0x30000000000000024000006cc00000019000508, 0x120000000000000140000003d50000014f000105, 0x100000000000a000000134, 0x8000000b800940000, 0x2005002805403806e, 0x100000001000a01, 0x1000000000000000100000a, 0x51000000000000023a0000021300000214000302, 0x2405002c05003806e, 0x6000000000000139e0000004d00000025000a00, 0x900000000000000150000095a0000002600020a, 0x9900000000000003440000031a00000331000002, 0x2405402805403806a, 0x1200000000000009990000002700000014000902, 0x600000000000000250000139e0000004d000009, 0xfc000000000000068d0000063a00000665000200, 0x80000000000a40000013c, 0x40000000000c4007c0000, 0x40000000000a000a00000, 0x28048034060034066, 0x10000000000000001000209, 0x100000001000300, 0x10000000000000001000403, 0x100154000000a40000, 0x2804c028060034066, 0x10000000000000001000301, 0x100000001000402, 0x10000000000000001000004, 0x2804802c06002c06a, 0x300000000000000280000002500000028000001, 0x210000000000000638000002220000022f000400, 0x141000000000000022f000006b800000208000104, 0x4000000a400a40000, 0x40070000000380000, 0x2c050030058034066, 0x10000000000000001000302, 0x100000001000401, 0x30000000000000001000004, 0x3800340000, 0x2804c03005c034066, 0x4200000000000003590000011100000103000103, 0x300000001000500, 0x3000000000000000d000000240000000d000305, 0x2405002805c02c06a, 0x900000000000001ad0000017a0000008c000100, 0x1b00000000000002140000022f000000b6000501, 0x300000000000006b40000063c00000215000005, 0x4000000bc008c0000, 0x24054028058034066, 0x100000001000903, 0x10000000000000001000009, 0x3000000000000002c0000007b00000029000104, 0x2c05402c054034066, 0x9000000000000141c0000004f00000023000900, 0x60000000000000014000003330000000d000409, 0x4500000000000002220000063b0000022f000004, 0x8014c000000a00000, 0x40000000000a000000140, 0x2c05402c058034062, 0x100000001000800, 0x30000000000000026000013aa0000004f000208, 0x10000000000000001000102, 0x3800340000, 0x2c05403005c03005e, 0x3000000780000000100000a, 0x3000000000000000100000a, 0x10000000000000001000201, 0x40000000000ac00000140, 0x2c058030058030062, 0x100000001000200, 0x2700000000000006910000066800000050000200, 0x1500000000000009d80000031f00000334000102, 0x3005803005803005e, 0x690000000510000000d000a01, 0x270000000000000029000013b30000005000000a, 0x2700000000000012bd000006680000068f000100, 0x40070000000380000, 0x40000000000b800880000, 0x2c05002c060030062, 0x3000000000000002b000013380000005300020a, 0x100000001000300, 0x30000000000000001000103, 0x2c05002c05c034062, 0x300000000000000280000002800000025000200, 0xa2000000000000063c0000068d00000667000302, 0x6300000000000003330000031e00000346000003, 0x100154000000a40000, 0x2804c02c060034062, 0x3000000000000000a000001a40000000700010a, 0x21000000000000010a0000034600000111000301, 0x10000000000000001000003, 0x28048030064030066, 0x6000000000000002c0000132f0000005500000a, 0x60000000000000639000006650000068e000300, 0x2100000000000013a70000005600000029000a03, 0x200164000000ac0000, 0x80000000000bc00800000, 0x100000000000a000000134, 0x2003c02c06403806e, 0x10000000000000001000002, 0x100000001000401, 0x10000000000000001000204, 0x100000000000c400000134, 0x2003c02c06402c06e, 0x10000000000000001000009, 0x10000000000000001000200, 0x10000000000000001000301, 0x80074000000380000, 0x2404402c064034066, 0x210000000000000029000013a70000005600050a, 0x10000000000000001000305, 0x300000001000a00, 0x2003c03406403006a, 0x3000000000000002d000006600000001d00000a, 0xf0000000000000068c0000139b0000060b000100, 0x24000000000000128a0000005900000031000a01, 0x140000000000b000000130, 0x3800340000, 0x2003c03005c034072, 0x10000000000000001000102, 0x300000001000500, 0x156000000000000062c0000130500000677000205, 0x40002c0000, 0x2404002805c034072, 0x10000000000000001000201, 0x300000001000600, 0x3b0000000000000134000001600000006d000106, 0x24044024058038072, 0xa50000000000000683000012a500000662000500, 0x15f0000000000001326000006c2000005e1000605, 0x8400000000000006090000065d00000235000006, 0x40000000000ac00940000, 0x2404003006003806a, 0x3f00000000000006660000068d00000637000402, 0x10000000000000001000004, 0x4e000000000000018c000001970000019f000201, 0x40000000000c4007c0000, 0x1c04402806003006e, 0x21000000000000022d000002040000022f000501, 0x10000000000000001000005, 0xab000000000000068c0000063500000660000102, 0x2404402805c03806e, 0x16500000000000006870000066200000637000500, 0xa500000000000003310000035200000306000205, 0x297000000000000063400000631000006a0000002, 0x100000000000b8007c0000, 0x1802803006c03006e, 0xc000000000000002e0000130b00000059000107, 0x100000001000300, 0x7000000000000066d0000005e0000000f000703, 0x140000000000a400000130, 0x1803402c064038072, 0x10000000000000001000001, 0x1560000000000001305000006770000062c000402, 0x60000000000000067c000012630000064f000104, 0x1c03402c06803406e, 0xc0000000000000659000006840000062b000201, 0x75000000000000062a0000065a00000683000002, 0x3e700000000000006a80000064f00000635000100]
private def bspMeta_27 : ℕ × ℕ × ℕ := (570, 2000, 10)

private def bspWords_28 : List ℕ := [0x4000000a400b00000, 0x40154000000a40000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x1c016c000000b00000, 0x40000000000380000006c, 0x40000000000ac00a00000, 0x2404403406403806e, 0x30000000000000001000107, 0x100000001000200, 0x10000000000000001000200, 0x140164000000a00000, 0x400040000, 0x2404c03406003806e, 0x30000000000000001000302, 0x2a00000001000100, 0x10000000000000001000100, 0x400000000002800000050, 0x2404c03005c03c072, 0x400000001000700, 0xf00000000000000560000001100000054000700, 0x10000000000000001000207, 0x400580000002c0000, 0x2c05003005c03806e, 0x300000001000805, 0xd800000000000006e2000000ff000006bb000805, 0x40000000000000001000001, 0x800000000005c000000a0, 0x2804c028060034072, 0x20000000000000001000003, 0x1500000000000001ad000001c20000006e000201, 0x300000000000000e10000001600000005000302, 0x2005002c06003806e, 0x80000000000000029000001b80000000b000103, 0x2400000000000001b800000394000000d1000001, 0x200000000000003890000002900000015000300, 0x140000000000a40000013c, 0x2404403005c03c076, 0x10000000000000001000002, 0x1da000000000000070b000000550000073c000601, 0x10000000000000001000406, 0x40000000000c400880000, 0x2404402c064030072, 0x6000000000000002d0000002b0000002c000203, 0x10000000000000001000002, 0x2e20000000000000703000007340000068f000301, 0x2404802c06003c072, 0x9c0000000000000370000003980000033f000200, 0xf000000000000006ac000006dc00000705000102, 0xcc0000000000000704000006aa000006db000001, 0x40074000000380000, 0x4000000000058000000a4, 0x2c05403005c03406a, 0x200000001000500, 0x4200000000000003860000005500000373000500, 0x30000000000000001000102, 0x40000000000ac0000014c, 0x400040000, 0x2c054034060034066, 0x1000000000000000100010a, 0x2a00000001000200, 0x30000000000000001000302, 0x80158000000ac0000, 0x3005803005c034066, 0x1000000010000002a00000002020701, 0x8100000000000006e3000000550000070f000807, 0x10000000000000001000003, 0x2805803006002c06a, 0x2000000000000002c000006620000002b000001, 0x2700000000000006e3000003850000035c000300, 0x100000000000003880000002900000015000103, 0x40000000000b80000014c, 0x30058030060030066, 0x1000000000000000100000a, 0x1500000000000001ae000001c3000001b9000106, 0x7b0000000200000001000a01, 0x30058034060034062, 0x2a000000000000002a0000152a0000005500060a, 0x2a00000000000006e40000070e000006bb000006, 0x30000000000000a140000002b00000017000a00, 0x140164000000ac0000, 0x40000000000ac00a00000, 0x80000000000a400000148, 0x2804c03406403806a, 0x1000000000000000100000a, 0x100000001000401, 0x10000000000000001000204, 0x400580000002c0000, 0x2c050034064034066, 0xe000000000000002b0000070d0000001d00040b, 0x10000000000000001000204, 0x400000001000b00, 0x2804c03006803406a, 0x20000003c0000000100000b, 0x300000000000001ad000006e3000001c3000100, 0x1b000000000000159f0000005900000029000b01, 0x400580000002c0000, 0x40000000000d0007c0000, 0x2c05002806403006a, 0x510000000000000a8f0000035c00000371000402, 0x100000001000500, 0x40000000000000001000105, 0x2c05002c06003806a, 0x1dd000000000000159f0000070c0000065b000400, 0x5400000000000006b4000007080000024b000504, 0x1200000000000000370000009cc00000397000005, 0x2804c02c06403006e, 0x1e0000000000000709000001a2000001c3000001, 0x48000000000000050700000707000001b8000400, 0x573000000000000070900001521000006b9000104, 0x800780000003c0000, 0x2804803006803806a, 0x1b00000000000000290000159f00000059000109, 0x390000000000001410000006df00000709000301, 0x30000000000000001000003, 0x2404403006c03406e, 0x30000007500000002000009, 0x1000000000000011d0000012500000064000300, 0x100000000000001070000000d00000002000903, 0x1c0000000000ac00000134, 0x400000000004800240000, 0x1802802806c03c07e, 0x10000000000000001000105, 0x300000001000500, 0x1ce000000000000003100000000000007d0000500, 0xc00000000003c00000064, 0x1802802c06003c086, 0x300000001000500, 0xa800000000000006cc0000027c00000695000500, 0x1ce000000000000003100000000000007d0000605, 0xc007c000000340000, 0x1803c02806003c07e, 0x100000001000603, 0x300000000000000120000000300000011000603, 0x30000000000000001000006, 0x1c03002c06003c07e, 0x10000000000000001000302, 0xa800000000000006cc0000027c00000769000600, 0x34000000000000023000000240000000c3000201, 0x400000000001c00000034, 0x400000000004400280000, 0x1802802c06c03c07a, 0x60000000000000001000106, 0x300000001000200, 0x1ce000000000000003100000000000007d0000602, 0x200170000000ac0000, 0x2004002806003c07a, 0x60000000000000001000200, 0x1e000000000000009f0000001b000000b0000604, 0x10000000000000001000003, 0x1c03802806403c07a, 0x60000000000000001000201, 0x26700000000000006a0000006f3000006d1000300, 0xe400000000000014e200000698000006cb000103, 0x800000000005c00440000, 0x400000000002000000034, 0x1802803407003407a, 0x60000000000000001000009, 0x20000000000000001000100, 0x1ce000000000000003100000000000007d0000702, 0x1c030034070034072, 0x20000007200000001000109, 0x20000000000000001000109, 0x6c0000000c00000001000900, 0x4000000000040002c0000, 0x140000000000c80000013c, 0x1c03403006c030076, 0x100000001000100, 0x30000000000000001000100, 0x90000000000000053000000f300000026000203, 0x2003c03006c03806e, 0x30000000000000006000003150000000d00050a, 0x30000000000000001000105, 0xf300000000000006a30000036800000379000200, 0x80000000000bc008c0000, 0x1000b80000005c0000, 0x24040030068038072, 0x3f00000000000006d90000150c000006a9000602, 0x10000000000000001000106, 0x20000000000000001000001, 0x20038030068034076, 0xc900000000000006f5000009f90000036a000002, 0x10000000000000001000100, 0x9000000000000002f0000005e0000000f000204, 0x40000000000ac00a00000, 0x2003c034064034076, 0x14d00000000000006fa000006ab000006d7000601, 0x10000000000000001000006, 0x11100000000000001bf00000a7d000001ac000104, 0x2404002806403c076, 0x2e2000000000000068f0000070300000734000600, 0x10b00000000000013f50000037d0000036b000406, 0xb4000000000000036a0000161a00000347000004, 0x40154000000a40000, 0x3005c03005c034066, 0x2700000000000014af000000530000002c000301, 0x10000008100000001000003, 0x10000000000000001000003, 0xc00000000003800000064, 0x400000048002c0000, 0x2c0000000000b000000124, 0x1802802005404008e, 0x10000000000000001000004, 0x300000001000501, 0x1ce000000000000003100000000000007d0000501, 0xc007c000000380000, 0x1c03c020054040086, 0x30000000000000001000300, 0x30000000000000001000203, 0x300000001000300, 0x4000000bc00980000, 0x1802c02c05c040086, 0x30000000000000001000406, 0x10000000000000001000001, 0x13b0000000000000687000008110000066b000602, 0x14034020058044086, 0x5c00000000000006850000025100000264000100, 0x8200000000000002410000070100000225000201, 0x66000000000000023f0000026200000237000002, 0x340000000000b80000011c, 0x40000002400180000, 0x1402c01c048040096, 0x10000000000000001000102, 0x600000001000600, 0x33ba00000000000046500000074300013880000206, 0x140000000000300000005c, 0x1402c01003805009e, 0x300000001000800, 0x4200000000000000070000c99000000190000708, 0x95a0000000000000bb8000000a300001b58000107, 0x14034014044040096, 0x100000001000802, 0x10000000000000020000006cd00000017000008, 0x400000000000000370000001e00000009000100, 0x2c0000000000b000000124, 0x40034000000140000, 0x1804401c04404008e, 0x100000001000801, 0x300000000000000260000158700000047000208, 0x70000000000000001000002, 0x1403801c04804008e, 0x10000000000000001000103, 0x60000000000000052000002620000004d000200, 0xd8000000000000099f0000035b0000037c000302, 0x80078000000340000, 0x20048020048040086, 0x300000001000804, 0x900000000000000270000153f00000049000108, 0x30000000000000001000001, 0x2800000000009400000128, 0x1c04001c04c04808a, 0x10000000000000001000004, 0x1b00000000000006c70000158700000652000201, 0x9000000000000009ae0000036200000383000402, 0x1c04402404c044086, 0x4b000000000000025100000245000000bc000104, 0x219000000000000072d000013f2000006cb000001, 0x28b00000000000014d000000695000006cb000400, 0x800b00000004c0000, 0x400000000002800000050, 0x40000005c00500000, 0x2405002c05803c072, 0x400000001000001, 0x20000000000000001000001, 0x20000000000000001000200, 0x800000000003400000068, 0x2405002405004007a, 0x300000001000800, 0x20000008a00000001000308, 0x20000000000000001000308, 0x140000000000a40000013c, 0x2405002805403c076, 0x100000001000900, 0x30000008700000002000109, 0x20000000000000001000401, 0x2405402c05403c072, 0x840000000400000001000902, 0x1b000000000000002a0000149d0000004f000009, 0x9c0000000000000707000003580000036f000200, 0x40000000000380000006c, 0x400ac000000440000, 0x2405802c05803806e, 0x300000001000801, 0x20000004200000001000208, 0x20000000000000001000002, 0x40074000000380000, 0x2c05403005803806e, 0x3900000000000006bb0000039b0000035f000107, 0x300000000000000560000002b00000017000301, 0x30000000000000001000003, 0x40074000000340000, 0x2805402805c03806e, 0x5640000000000001431000006e10000073a000108, 0xf00000000000001570000010e00000058000401, 0x30000000000000001000004, 0x2c05002c05c03806e, 0x20300000000000006bb000002590000025b000008, 0x13000000000000023b000001b800000096000400, 0x39000000000000006e000001d900000069000804, 0x80000000000a400000148, 0x4000000bc00980000, 0x2405802c05c03806a, 0x100000001000901, 0x10000000000000001000009, 0x7200000000000007360000143a000006bb000702, 0x3005803005803806a, 0x30000000000000a920000002900000013000900, 0xb000000000000002b000006e30000001b000209, 0x2100000000000006b8000014a900000709000002, 0x2805c03005c034066, 0x6ba00000000000006e5000006e40000070f000506, 0x81000000030000000200000004080005, 0x2700000000000002670000023f0000023e000600, 0x1c0000000000a000000134, 0x80078000000340000, 0x40000004400300000, 0x2004802405404007e, 0x10000000000000001000201, 0x300000001000400, 0x30000000000000001000104, 0x1000000000004c00000098, 0x2004802404c044082, 0x200000001000900, 0x100000000000000080000016500000005000509, 0x2100000000000006a8000006cf00000251000105, 0x2004c02405004007e, 0xf900000000000006fd00000a4400000353000401, 0x45000000030000000200000002090004, 0x1050000000000000a77000006a10000036a000100, 0x4000000c8008c0000, 0x1c03802805c04007e, 0x10000000000000001000206, 0x100000001000400, 0x6c0000000000000242000007bc00000223000604, 0x1000000000004c00000098, 0x2003c024054044082, 0x20000000000000001000001, 0x2100000000000006cf000006f300000238000502, 0x3800000000000000710000016f00000074000105, 0x1c04402405804007e, 0x27000000000000020d000000b3000000aa000201, 0xf600000000000006a000000a3e0000037d000002, 0x270000000000000130000002350000011d000100, 0x800000000003400000068, 0x8000000ac00ac0000, 0x1c04403005804007a, 0x30000000000000001000106, 0x10000000000000001000001, 0x14400000000000007250000073e00000667000602, 0x8000000c400940000, 0x2404802805804007a, 0x30000000000000001000201, 0x10000000000000001000004, 0x13e00000000000006d6000007640000068d000103, 0x2004c02405404007a, 0xba00000000000006db0000038100000355000400, 0xf90000000000000353000006fd0000036c000304, 0x1a700000000000006ff000006a6000006d7000003, 0x140000000000a40000013c, 0x4000000bc00980000, 0x2404802c05c03c076, 0x10000000000000001000107, 0x10000000000000001000004, 0x2b000000000000012b000003b300000111000702, 0x2004c02805803c076, 0x8a00000000000006dd0000038300000357000400, 0x3e0000000000000355000002490000012b000204, 0x390000000000000263000006ab0000023c000002, 0x2804c02c05c03c072, 0x840000000000000150000000b8000000b5000306, 0x8a0000000000000357000006dd00000383000003, 0x2b800000000000006dc0000076500000691000600]
private def bspMeta_28 : ℕ × ℕ × ℕ := (562, 2000, 11)

private def bspWords_29 : List ℕ := [0xc00000000003400000068, 0x40000004c002c0000, 0x2c0000000000a400000130, 0x1802c020058048092, 0x10000000000000001000003, 0x300000001000301, 0x2ce600000000000007d00000076100012110000003, 0x4000000c800980000, 0x1802c02c06004808a, 0x30000000000000001000304, 0x10000000000000001000003, 0xa8a00000000000007d00000029700006590000304, 0x20017c000000a00000, 0x1c04402005804808a, 0x30000000000000001000400, 0x30000000000000001000304, 0x100000001000400, 0x8000000c400a00000, 0x1803802c05c04808a, 0x30000000000000001000502, 0x10000000000000001000001, 0x30000000000000767000007a6000006fa000203, 0x1803c02805404808a, 0xa2000000000000012b0000014500000140000100, 0x93000000000000028f000002610000026c000301, 0x510000000000000769000007ab000006fc000003, 0x3400000000009400000128, 0x80000004c00300000, 0x1403001c04c05009a, 0x10000000000000001000102, 0x300000001000400, 0x44300000000000005dc0000007900001405000204, 0x1400000000003000000060, 0x1003801003c0540a2, 0x300000001000600, 0x7a00000000000000070000ce4000000190000506, 0x40a000000000000bb800000075700014ff0000105, 0x1803801804405009a, 0x100000001000602, 0x700000000000000250000072c00000018000006, 0x133000000000000072c000007c900000258000100, 0x2c00000000009800000130, 0x14000000dc00940000, 0x1c03802005004c092, 0x10000000000000001000103, 0x100000001000200, 0x7500000000000015ae000007a000000715000302, 0x1c04001c04804c092, 0x100000001000601, 0xc000000000000001300000ad700000025000206, 0xa5000000000000073a000007a200000715000002, 0x8007c000000340000, 0x2004c01c05004808a, 0x300000001000604, 0x3000000000000001100000b2200000026000106, 0x30000000000000001000001, 0x280000000000a000000134, 0x1c04402404c04808e, 0x10000000000000001000004, 0x1f500000000000007ad0000156000000746000201, 0x27000000000000012c0000005f00000062000402, 0x2404802805004808a, 0x3000000000000000d0000000d00000004000104, 0x26d00000000000007b2000015750000074b000001, 0x900000000000001f2000000aa000000ad000400, 0x80000000000380000006c, 0xc0080000000400000, 0x8000000b800ac0000, 0x1c0000000000a000000140, 0x2404003005c044082, 0x10000000000000001000002, 0x100000001000401, 0x30000000000000001000204, 0x4000340000, 0x2404003006404007e, 0x30000000000000001000403, 0x30000000000000001000004, 0x30000000000000001000301, 0x8007c000000380000, 0x2404c03005c04007e, 0x30000000000000001000500, 0x10000000000000001000305, 0x300000001000500, 0x2404402806004007e, 0x30000000000000001000501, 0x8900000000000002610000075800000280000200, 0x430000000000000280000000db000000c8000102, 0x140170000000a00000, 0x40000004400340000, 0x2405002805804007e, 0x300000001000704, 0x30000000000000001000007, 0x10000000000000001000100, 0x200000000000a40000013c, 0x24050028050044086, 0x100000001000800, 0x1000000000000002b000007290000001a000608, 0x10000000000000001000206, 0x1c0000000000a000000140, 0x24050024054044082, 0x100000001000900, 0xc0000000000000026000016710000004f000109, 0x1000000030000000100000002030201, 0x2405402c05404007e, 0x30000000000000783000000510000000d000902, 0x3000000000000000b0000056400000014000009, 0x1dd00000000000016800000072500000758000200, 0x200000000000a40000013c, 0x8000000dc00880000, 0x1c04402405c044086, 0x10000000000000001000103, 0x100000001000600, 0xb00000000000000820000018b00000075000306, 0x2004802c050044086, 0x10000000000000001000100, 0x1300000000000003f40000012b00000138000602, 0xbf000000000000027d0000071900000270000006, 0x1c0000000000a000000140, 0x24048024058044082, 0x10000000000000001000003, 0x12f0000000000000390000003bd000003aa000102, 0xa50000000000000752000007e600000707000301, 0x2804c02805c04007e, 0x17100000000000001cd000001e1000001e3000203, 0x6f00000000000001c9000001d6000001e0000002, 0x18f0000000000000758000007e700000708000300, 0x4000000000044002c0000, 0x1802c03007004007e, 0x30000000000000001000204, 0x300000001000300, 0x5060000000000001770000007f900013880000204, 0x80000000000d400800000, 0x200000000000c80000013c, 0x1403002c06c038086, 0x10000000000000001000002, 0x100000001000501, 0xb00000000000002a400000268000000c3000205, 0x2003802c06c04007e, 0x30000000000000001000402, 0x10000000000000001000103, 0x5100000000000006e40000027d00000277000200, 0xc00000000004400000068, 0x1c03402806003808a, 0x30000000000000001000001, 0x49000000000000029000000263000000d0000503, 0x520000000000000145000003b80000012b000105, 0x200000000000b00000013c, 0x20038028064040086, 0x10000000000000001000002, 0x1b00000000000001800000018900000070000104, 0x20100000000000006b30000166500000782000201, 0x1c03c03006403c082, 0x800000000000000770000002600000027000402, 0x2100000000000000a8000001cb00000098000004, 0x15000000000000007750000071400000749000200, 0x80000000000b000a40000, 0x140000000000b000000148, 0x100000000000ac00a00000, 0x1802c03c07403c07a, 0x10000000000000001000107, 0x100000001000300, 0x2e00000000000017700000006500000fa0000705, 0x1c03403806c03c07a, 0x10000000000000001000100, 0x100000001000302, 0x25800000000000007d100001788000006b9000003, 0x20017c000000b80000, 0x100000000000b80000014c, 0x2404403806c038076, 0x100000001000300, 0x10000000000000001000300, 0x10000000000000001000102, 0x400000000003800000070, 0x2404403806c03c072, 0x30000000000000001000009, 0x10000000000000001000400, 0x100000001000902, 0x2804803806c03806e, 0x10000007e00000001000409, 0x10000000000000001000409, 0x200000000000003db0000002f00000007000900, 0xc0080000000380000, 0x1c040030070034076, 0xc0000000000000031000015ff0000005f000108, 0x7b00000000000007230000075600000782000201, 0x300000001000800, 0x1c03403007403c076, 0x1000000000000002b0000080600000020000008, 0x3f00000000000001ae0000057f000001f6000200, 0x300000000000002220000000900000004000802, 0x10016c000000b00000, 0x400000000003800000070, 0x8000000b800ac0000, 0x400780000003c0000, 0x3005803005c03c072, 0x300000001000802, 0x10000000000000001000108, 0x30000000000000001000001, 0x100000000000ac0000014c, 0x2c05403005c03c076, 0x10000000000000001000004, 0x10000000000000001000201, 0x10000000000000001000402, 0x2c05402c06003c072, 0x30000000000000001000304, 0x1700000000000002760000078800000267000001, 0x10000000000000001000400, 0x140000000000a400000148, 0x2c05402805804007a, 0x100000001000800, 0x1000000000000000d0000028100000009000508, 0x10000000000000001000305, 0x100000000000ac0000014c, 0x400780000003c0000, 0x3005803005803c076, 0x100000001000a01, 0x15000000000000002d0000159f0000005200020a, 0x30000000000000001000002, 0x2405802805c03c076, 0x1df00000000000007610000026700000294000003, 0x700000000000002760000078700000267000200, 0x5700000000000002900000026600000267000302, 0x2805c02c05c03c072, 0x270000000000001626000000540000002b000902, 0x600000000000000280000169b00000053000009, 0x10e000000000000078c0000073300000761000200, 0x80000000000b000000154, 0x3c00380000, 0x2c05403406403806e, 0x10000000000000001000103, 0x300000001000200, 0x10000000000000001000302, 0x80164000000ac0000, 0x3005c03005c03806e, 0x100000001000902, 0xd000000000000002b000007620000001c000309, 0x10000000000000001000003, 0x48002c0000, 0x2805802806403806e, 0x1000000010000000300000002030102, 0x300000001000400, 0x300000000000007b60000073500000268000204, 0x4000000b000b00000, 0x3005803406003806e, 0x20a00000000000007de00001629000006d9000201, 0x100000001000500, 0x5700000000000003b10000038400000149000105, 0x2805c02c06003806e, 0x70b00000000000007640000076300000790000200, 0x25000000000000039a000001420000013b000502, 0x3000000000000002f000000840000002c000005, 0x40000000000ac00000158, 0x3c00380000, 0x40000000000b800a00000, 0x2c05403406803806a, 0x1000000000000000100020b, 0x100000001000300, 0x10000000000000001000503, 0x2c05803406403806a, 0x10000000000000001000200, 0x300000001000301, 0x1800000000000003c70000039a000003b1000003, 0x4000000b000b00000, 0x401600000008c0000, 0x2806003406003806a, 0x100000001000b03, 0x1000000000000000100010b, 0x10000000000000001000004, 0x80000000000bc00000154, 0x2c05c03406003406e, 0x10000000000000001000003, 0x600000000000000290000002b0000002d000501, 0x5a00000000000016ad0000073600000763000305, 0x3005c03406003806a, 0x870000000000000764000017af000006dd000103, 0x111000000000000070c0000079000000799000001, 0x5400000000000015a8000007630000078d000300, 0x2c06003006003806a, 0x150000000000000b160000002b00000016000a00, 0x30000000000000029000016a70000005500030a, 0x3000000000000002c0000002a0000002b000003, 0x40160000000b00000, 0x34060034060034066, 0x2d000000570000000100090a, 0x15000000000000001600000b160000002b000109, 0x10000000000000001000001, 0x80164000000ac0000, 0x40000000000d000000158, 0x3005c03006402c06a, 0x1000000000000000100000c, 0x5700000000000007380000078f00000764000302, 0x10000000000000001000103, 0x3005c034064034066, 0x2d000000000000002d0000162c0000005800020c, 0x3f00000000000003b2000003f100000370000002, 0xf000000000000152a0000005900000034000c00, 0x3005803406803406a, 0x3000000000000002e0000162c0000005900000b, 0x30000000000000736000007640000078f000200, 0x2700000000000016ad0000005a0000002b000b02, 0x40000000000b800a00000, 0x8007c0000003c0000, 0x400000000003c00000070, 0x2804c034068038072, 0x30000000000000001000004, 0x10000000000000001000200, 0x300000001000401, 0x140170000000b80000, 0x2c05003406803406e, 0x6000000000000002f000016230000005b00040a, 0x1000000030000000100000002030104, 0x100000001000500, 0x2804c03006c030072, 0x5700000000000002830000025600000284000005, 0x14d0000000000001590000007850000075e000100, 0x5970000000000000789000016a100000737000501, 0x140000000000a400000148, 0x2004003406804007a, 0x10000000000000001000004, 0x100000001000502, 0x3300000000000003d500000b8e00000371000405, 0x140000000000c800000148, 0x2404403406803407a, 0x10000000000000001000005, 0x10000000000000001000302, 0x12f00000000000007b0000007b5000006e3000501, 0x100000000000ac0000014c, 0x1c04803406803c076, 0x10000000000000001000006, 0x3300000000000003c500000b4600000380000103, 0x3c00000000000003c800000399000003af000601, 0x2804803006c030076, 0x1020000000000001698000007010000078b000306, 0x72000000000000072b0000161700000788000003, 0x3750000000000000787000007b60000070d000600, 0x140000000000b000000148, 0x4400300000, 0x2404402c06403c07a, 0x10000000000000001000102, 0x300000001000500, 0x2700000000000000710000015c0000006a000205, 0x4000000c800980000, 0x2404c02c06003c07a, 0x10000000000000001000201, 0x100000001000600, 0x22000000000000028100000262000000d1000106, 0x2405002805c03c07a, 0x3600000000000003c200000399000003af000400, 0x3c00000000000016170000078200000731000604, 0xab00000000000003c200000abc000003ad000006, 0x140170000000b80000, 0x100000000000ac0000014c, 0x2c05002c06003c076, 0x100000001000400, 0x3600000000000003af000003c200000399000204, 0x10000000000000001000102, 0x40000000000d000880000, 0x2c05002c068034072, 0x3300000000000001e2000001cd000001d8000504, 0x10000000000000001000005, 0x100000001000402, 0x2c05002c06403c072, 0x3000000000000000e0000000e0000000d000500, 0x15c0000000000000730000007870000075f000105, 0xc000000000000003af00000398000003c3000001, 0x40000000000d000880000, 0x2804802c068034076, 0x1200000000000001410000012b00000142000103, 0x10000000000000001000001, 0x24300000000000003ac000003db0000039a000302, 0x2804c02c06403c076, 0xc000000000000003c3000003af00000398000100, 0x5a00000000000003af000003c100000398000201, 0xea00000000000003ad00000395000003c0000002]
private def bspMeta_29 : ℕ × ℕ × ℕ := (554, 2000, 12)

private def bspWords_30 : List ℕ := [0x4000000b000bc0000, 0x4016c000000b00000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x140000000000b000000154, 0x400000000004400300000, 0x1c0000000000c40000014c, 0x1802c03407403c086, 0x10000000000000001000005, 0x300000001000501, 0x19ba00000000000000fa0000010300002616000005, 0x140000000000d400800000, 0x1802c03407c04007e, 0x10000000000000001000308, 0x10000000000000001000003, 0x21600000000000004b00000001500000320000806, 0x1c03803407404007e, 0x10000000000000001000300, 0x30000000000000001000203, 0x7e00000000000007f600000790000007c5000001, 0x200000000000bc00000148, 0x400000000005000240000, 0x1403002807404008a, 0x10000000000000001000102, 0x300000001000600, 0x61a0000000000000960000000cb00002008000206, 0x280000000000c400000140, 0x18030030068040092, 0x100000001000600, 0x11100000000000007cd000000e300000795000600, 0x5ba0000000000000bb8000001df00004a38000107, 0x1803802c06804008a, 0x100000001000602, 0x1f800000000000007f80000013e00000793000602, 0x16500000000000017430000071a000007f9000100, 0x1000c40000005c0000, 0x40000000000dc00880000, 0x2404802c06c04007e, 0x10000000000000001000401, 0x100000001000100, 0x20000000000000001000100, 0x400000000001c00000038, 0x24048034064044082, 0x600000001000700, 0xc000000000000002e0000000d0000002d000700, 0x20000000000000001000207, 0x2804c03406404007e, 0x100000001000705, 0x19e00000000000007b90000005b00000790000705, 0x300000000000000157000007a900000150000100, 0x1c0000000000c40000014c, 0x4002c000000140000, 0x2004402c06803c086, 0x10000000000000001000100, 0x10e00000000000003ea0000013e00000451000702, 0x90000000000000001000003, 0x2003802c06c03c086, 0x10000000000000001000104, 0xf90000000000000289000017dc0000029b000300, 0x321000000000000174f0000082b000007a6000403, 0x80000000000bc00a40000, 0x1c04003807004007e, 0x10000000000000001000504, 0x10000000000000001000002, 0xd200000000000018000000079c000007cf000401, 0x400000000001c00000038, 0x2404003006c044082, 0x600000001000300, 0xab00000000000003eb000007fb000003d4000203, 0x4b00000000000000c3000000d7000000c5000102, 0x2404403806c034082, 0x3c0000000000000403000001df00000203000301, 0x600000000000000d30000003f00000023000003, 0x60000000000000046000001a50000003f000100, 0x14017c000000b80000, 0x400000000003c00000074, 0x800000000005c000000ac, 0x2c05403406403c07a, 0x200000001000500, 0xa200000000000003f30000005b000003df000500, 0x10000000000000001000203, 0x400040000, 0x2c05403806803c076, 0x30000000000000001000203, 0x2d00000001000100, 0x10000000000000001000301, 0x100178000000bc0000, 0x3005803406403c076, 0x300000001000703, 0x210000000000000121000000270000011b000703, 0x10000000000000001000002, 0x2c05403006803c076, 0x23000000000000002c000007e50000002f000001, 0x4e00000000000007e500000406000003db000200, 0x1000000000000003f10000002f00000016000102, 0x4000000000058000000b0, 0x40000000000c400a00000, 0x2c05403406c03c072, 0x20000000000000001000109, 0x100000001000200, 0x10000000000000001000302, 0x20001c0000, 0x2c05803406803c072, 0x20000000000000001000201, 0x600000001000300, 0x6600000000000008120000171c000007e5000103, 0x2c05c03406403c072, 0x200000001000702, 0x4500000000000003f40000005b000003de000702, 0x180000000000000813000003db00000151000003, 0x400b80000005c0000, 0x40000000000b800000164, 0x3406003406403806e, 0x10000000000000001000001, 0x8a00000000000007e80000005b00000817000706, 0x20000000000000001000102, 0x40000000000c400000164, 0x3406003406803406e, 0x1000000000000000100000b, 0x5a00000000000007ba00000814000007e9000107, 0x840000000200000001000b01, 0x3406003806803806a, 0x2d000000000000002d000018420000005b00070b, 0x2d00000000000007e900000816000007bd000007, 0x6000000000000172e0000005c00000031000b00, 0x4007c0000003c0000, 0x40000000000d000940000, 0x3005c03006c03806e, 0x1000000420000000100020b, 0x100000001000300, 0x30000000000000001000103, 0x400040000, 0x3005c03806803806e, 0x42000000000000041f000001fa000001e3000301, 0x2d00000001000400, 0x300000000000000160000002900000016000104, 0x28060030068030072, 0x1000000000000002f000003af00000017000300, 0x2d00000000000003dd0000040a000001fa000403, 0x100000000000004360000002b00000016000004, 0x100178000000bc0000, 0x3005803406c03806e, 0xf000000000000002e000008150000001f00010b, 0x1b00000000000007b700000bdc0000040a000301, 0x10000000000000001000003, 0x2c054034070038072, 0x1000000810000000200000b, 0x300000000000003db000001fa00000205000300, 0xf0000000000000c600000005f00000016000b03, 0x4000000000048002c0000, 0x100000000000ac00000158, 0xc0084000000400000, 0x2404403007404007a, 0x10000000000000001000100, 0x300000001000402, 0x30000000000000001000004, 0x40028000000140000, 0x2404003c07404007a, 0x1000000000000000100020a, 0xba000000000000083a0000162900000835000501, 0xa0000000000000001000005, 0x2003803807803807e, 0x50000003c0000000100000a, 0x4200000000000000cd0000078b000000d2000500, 0x90000000000000c8d0000003300000016000a05, 0x8000000000068000000ac, 0x200188000000c40000, 0x2804803007403407a, 0x2000000000000000100010a, 0x30000000000000001000301, 0x100000001000a00, 0x2404003c07403807a, 0x10000007b0000000200000a, 0x900000000000000310000002c00000031000200, 0x1e0000000000001932000000640000002b000a02, 0x400000000003c00000074, 0x2804803007403c076, 0x3000000000000000100000a, 0x30000000000000001000300, 0x600000000000005be000000310000000d000a01, 0x2804c030074030076, 0x3000000780000000100030a, 0x3000000000000000100030a, 0x8000000000000083c000000610000000f000a00, 0x4000000000064004c0000, 0x8000000000068000000ac, 0x2804803407003407a, 0x20000000000000001000002, 0x200000001000401, 0x450000000000000c0f000003d4000003ef000204, 0x400000000003c00000074, 0x2804c03407003c076, 0x30000000000000001000003, 0x20000000000000001000204, 0x2850000000000000b850000077900000424000301, 0x2c05003407003c072, 0x1e000000000000002c000018c00000005f00040a, 0xc000000000000049e000001940000019d000004, 0x2e00000000000002b000000280000000e5000300, 0x40000000000b800ac0000, 0x40040000000200000, 0x2c05003806c03c076, 0x600000000000000ca0000019d000000c5000402, 0x10000000000000001000104, 0x600000001000200, 0x2804803806c03807a, 0x1b000000000000040300000148000000a8000002, 0x100000001000501, 0x210000000000000062000000310000002f000205, 0x40000000000d000940000, 0x2804c03006c03407a, 0x2a00000000000002b000000282000002b1000401, 0x100000001000500, 0x39c000000000000080b0000083f0000078e000105, 0x2805002c06804007a, 0xa500000000000007e500000810000007b1000400, 0x1c200000000000007b00000080a000007e1000504, 0x360000000000000203000001eb000001f8000005, 0x4016c000000b00000, 0x3406403406403806e, 0x2a00000000000017be000000590000002f000301, 0x10000008a00000001000003, 0x10000000000000001000003, 0xc0000000000380000006c, 0x40000004c00300000, 0x2c0000000000a40000013c, 0x1803002405c04c096, 0x10000000000000001000004, 0x300000001000501, 0x9c200000000000003e80000024b000059d8000405, 0xc0084000000380000, 0x1c04402405c04808e, 0x30000000000000001000300, 0x30000000000000001000203, 0x300000001000300, 0x4000000c800a40000, 0x1803403006404808e, 0x30000000000000001000406, 0x10000000000000001000001, 0x960000000000000816000008ff00000709000602, 0x400000000001000000020, 0x1c03802c05c04c092, 0xa00000001000200, 0xfc000000000000083400001677000007f1000302, 0x1a400000000000007ee0000089200000755000103, 0x2003c02806404808e, 0x39c000000000000168c0000082500000805000201, 0x2100000000000007930000024c000000d0000002, 0x4b00000000000000cc00000895000000bc000100, 0x340000000000a000000134, 0x40000002800180000, 0x1403401c05005009e, 0x10000000000000001000102, 0x600000001000600, 0x8260000000000000ea600000103000029fe000206, 0x1400000000003400000064, 0x1403801403c0540a6, 0x300000001000800, 0x4000000000000000100001b8a00000032000708, 0x420000000000001194000000810000157c000107, 0x1c04001c04805009e, 0x100000001000802, 0x80000018a00000005000008, 0x100000000000000f10000008200000029000100, 0x2c0000000000a40000013c, 0x200188000000ac0000, 0x2004802004c04c096, 0x100000001000801, 0x60000000000000029000017400000004d000208, 0x10000000000000001000002, 0x1c03c02005004c096, 0x1000000010000000300000002010003, 0x14d000000000000082b000007bf00000796000200, 0xc000000000000017310000082600000797000302, 0x400400000001c0000, 0x2405002405004808e, 0x300000001000804, 0xc000000000000002a000017640000004f000108, 0x60000000000000001000001, 0x400000000001000000020, 0x1c04802005404c092, 0xa0000000000000001000004, 0x600000000000003e6000017d3000003d1000201, 0x2ee00000000000017d600000790000007c9000402, 0x2004c02805404808e, 0x7800000000000007fb000003ea00000145000104, 0x900000000000001070000009300000019000001, 0x45000000000000026400000797000000c8000400, 0x100178000000a40000, 0x100000000000ac00000158, 0x8000000c400ac0000, 0x2805803006004007a, 0x100000001000001, 0x10000000000000001000001, 0x10000000000000001000200, 0x400000000001c00000038, 0x28058028058044082, 0x600000001000800, 0x10000009300000001000308, 0x10000000000000001000308, 0x140000000000b000000154, 0x2805802c05c04007e, 0x100000001000900, 0x30000004800000001000109, 0x10000000000000001000401, 0x2805c03005c04007a, 0x8d0000000200000001000902, 0x60000000000000009000004bc00000011000009, 0x14d000000000000080f000007b2000007e3000200, 0x400000000003c00000074, 0x80170000000940000, 0x2806003006003c076, 0x300000001000801, 0x10000008d00000002000208, 0x10000000000000001000002, 0x4007c0000003c0000, 0x3005c03406003c076, 0x7b00000000000007bd00000841000007c0000107, 0x6000000000000002e0000002e00000031000301, 0x30000000000000001000003, 0x4007c000000380000, 0x2c05c02c06403c076, 0x64e0000000000001737000007e600000845000108, 0x14100000000000007b500001830000007e5000401, 0x30000000000000001000004, 0x3005803006403c076, 0x25500000000000007bd000002b1000002b3000008, 0x510000000000000291000007e5000002b0000400, 0x45900000000000007e5000008720000078f000804, 0x4000000000058000000b0, 0x4000000c800a40000, 0x2806003006403c072, 0x200000001000901, 0x10000000000000001000009, 0x7b000000000000084100001740000007bd000702, 0x3406003406003c072, 0x6000000000000183c0000005800000029000900, 0xc000000000000002e000007e80000001d000209, 0x2400000000000007ba000017b800000811000002, 0x2c06403406403806e, 0x7bc00000000000007ea000007e900000817000506, 0x45000000030000000100000002080005, 0x150000000000000160000002950000014a000600, 0x1c0000000000ac0000014c, 0x400400000001c0000, 0x40000004800340000, 0x2405002805c044086, 0x10000000000000001000201, 0x300000001000100, 0x60000000000000001000100, 0x200000000000a400000148, 0x2405002805404808a, 0x100000001000900, 0x6000000000000002b000007d60000001b000509, 0x6000000030000000300000002020105, 0x24054028058044086, 0x213000000000000080500001797000007a8000401, 0x93000000030000000200000004090004, 0x22b0000000000001806000007a3000007d9000100, 0x4000000d400980000, 0x2004002c064044086, 0x10000000000000001000206, 0x100000001000400, 0x6300000000000003fd00000d380000039b000604, 0x40000006800500000, 0x1c04802c060044086, 0xcf000000000000179100000403000003d3000201, 0x200000001000500, 0x1020000000000000826000016d4000007ab000105, 0x2804803005804008a, 0x270000000000000c00000003d7000001f6000200, 0x140000000000000439000007870000014e000502, 0x3900000000000003d400000651000001eb000005, 0x400000000001c00000038, 0x4000000e0008c0000, 0x2404c028064044082, 0x60000000000000001000106, 0x10000000000000001000001, 0x8700000000000008050000087500000763000602, 0x40000006800500000, 0x2c05002c060044082, 0x60000000000000001000201, 0x20000000000000001000004, 0xa200000000000007b0000007e000000803000103, 0x2405402805c044082, 0x6300000000000001f800000405000001eb000400, 0x21300000000000007a800000805000007dd000304, 0xe10000000000000807000003d4000003ee000003, 0x140000000000b000000154, 0x4000000c800a40000, 0x2c05003006404007e, 0x10000000000000001000107, 0x10000000000000001000004, 0x60000000000000070000002e000000069000702, 0x2405402c06004007e, 0x9300000000000003f100000407000003d8000400, 0x4200000000000007ac0000015000000157000204, 0x1e000000000000015e000007ad00000149000002, 0x2c05403006404007a, 0x60f000000000000078f0000083b0000081a000306, 0x9300000000000003d8000003f100000407000003, 0x37200000000000007e10000087300000790000600]
private def bspMeta_30 : ℕ × ℕ × ℕ := (546, 2000, 11)

private def bspWords_31 : List ℕ := [0xc00000000003800000070, 0x40000005000300000, 0x2c0000000000a400000148, 0x1803402406005009a, 0x10000000000000001000003, 0x300000001000301, 0xa200000000000004b0000001c300004010000003, 0x4c00300000, 0x1403402c06c04c092, 0x30000000000000001000304, 0x30000000000000001000003, 0xd000000000000027100000031000006d6000304, 0xc0088000000400000, 0x2404802406004c092, 0x30000000000000001000400, 0x30000000000000001000304, 0x300000001000400, 0x4000000e000980000, 0x2003c02c06804c092, 0x30000000000000001000502, 0x10000000000000001000001, 0x510000000000001977000008b500000802000203, 0x280000000000ac0000014c, 0x2004002806004c096, 0x100000001000200, 0x25500000000000008be0000188100000854000402, 0xab000000000000087d000008b800000802000104, 0x1c04802c06404c092, 0x15c00000000000006270000022200000223000201, 0x2d300000000000008c00000188d00000856000002, 0x3300000000000001720000015a0000015d000100, 0x340000000000a000000140, 0x80000005000340000, 0x140380200540540a2, 0x10000000000000001000102, 0x300000001000400, 0xada00000000000011940000010d00002af8000204, 0x1400000000003400000068, 0x1403c0140400580aa, 0x300000001000600, 0xc000000000000000100001c2000000032000506, 0x15600000000000020d0000001b9000047e0000105, 0x1c04401c04c0540a2, 0x100000001000602, 0x400000000000000140000041d0000000d000006, 0x7000000000000083a000008ab000002b1000100, 0x2c0000000000a400000148, 0x200194000000b80000, 0x2404c02005005009a, 0x100000001000601, 0x1b0000000000000029000018d800000050000206, 0x10000000000000001000002, 0x100000000000380000006c, 0x2004002005405009e, 0x30000000000000001000004, 0x19b00000000000008b90000084800000820000301, 0x4500000000000006360000022d00000208000403, 0x1c04802005c05009a, 0x1000000010000000300000002020104, 0x6000000000000018f30000087400000823000001, 0x2f00000000000001690000015800000076000400, 0x80084000000380000, 0x2405402005804c092, 0x300000001000604, 0x300000000000000250000197700000052000106, 0x30000000000000001000001, 0x280000000000ac0000014c, 0x1c05002805404c096, 0x10000000000000001000004, 0x2af00000000000008c10000188100000854000201, 0x30000000000000cf9000003d40000042a000402, 0x2805003005804c092, 0x9000000000000002a0000002a0000000d000104, 0x300000000000008ff0000181e00000859000001, 0x6f00000000000018870000085c00000880000400, 0x800000000003c00000074, 0x80000000000d400980000, 0x100000000000d000940000, 0x1c03003807c044086, 0x30000000000000001000206, 0x100000001000400, 0x1da000000000000001b00000000000003e8000400, 0x200000000000bc00000154, 0x1c03003407404408e, 0x10000000000000001000001, 0x100000001000402, 0x1da000000000000001b00000000000003e8000504, 0x20038034074044086, 0x30000000000000001000301, 0x10000000000000001000203, 0xbd000000000000087d000008b200000805000100, 0x1c0190000000bc0000, 0x8000000e800940000, 0x1c0000000000b800000158, 0x2805002806404408a, 0x10000000000000001000002, 0x100000001000201, 0x10000000000000001000201, 0x4000000d400a40000, 0x28050030068044086, 0x30000000000000001000503, 0x10000000000000001000005, 0x10000000000000001000301, 0x24054028064044086, 0x30000000000000001000500, 0x10000000000000001000205, 0x1a100000000000008920000082f00000864000001, 0x140188000000c40000, 0x40000004800380000, 0x3005802c060044086, 0x300000001000805, 0x30000000000000001000008, 0x10000000000000001000100, 0x1c0000000000ac00000158, 0x3005803005804808a, 0x100000001000900, 0x10000009300000001000209, 0x10000000000000001000209, 0x2805c03005c044086, 0x30000000000000894000000570000000e000901, 0xf000000000000002f000018b100000056000009, 0x1fb00000000000019b30000083000000866000100, 0x200000000000b000000154, 0x2805002c05804808e, 0x10000000000000001000002, 0x100000000000000170000041a0000000e000608, 0x1000000010000000300000002030206, 0x2c05402c05c04808a, 0x5700000000000008910000083b0000086c000102, 0x21f00000000000008ff000008630000080a000001, 0x7e0000000000000835000008650000088a000200, 0x40000000000e800880000, 0xc0088000000400000, 0x2404802c070044086, 0x30000000000000001000403, 0x10000000000000001000102, 0x300000001000300, 0x200000000000b000000154, 0x1c03c02c07004808e, 0x10000000000000001000004, 0x100000001000602, 0x3000000000000007e0000016b00000070000406, 0x2404002c07003c08a, 0xdb0000000000000cc3000004160000042e000104, 0xd2000000000000041200000c8d00000445000001, 0x1890000000000000888000008bc0000080b000400, 0x200000000000b000000154, 0x4000000d400a40000, 0x2004403006804808e, 0x10000000000000001000102, 0x100000001000600, 0xf00000000000001730000040e0000015e000206, 0x2804803006004808e, 0x10000000000000001000100, 0x2f00000000000008fb000002ae000002ca000603, 0x300000000000002ca000008f7000002ae000006, 0x1c0000000000ac00000158, 0x2404803406404808a, 0x10000000000000001000002, 0x14100000000000008fd0000080f00000860000103, 0xd20000000000000445000004120000042f000201, 0x2804c02c06c044086, 0x381000000000000089000000893000007fa000302, 0x18f000000000000082d0000086600000891000003, 0x16b00000000000008910000082c00000866000200, 0x80084000000400000, 0x400000000003c00000078, 0x4000000bc00bc0000, 0x100000000000b800000164, 0x140000000000bc00000160, 0x2c054038068040082, 0x10000000000000001000004, 0x100000001000502, 0x30000000000000001000405, 0x40003c0000, 0x2c05403806c04007e, 0x10000000000000001000205, 0x30000000000000001000002, 0x30000000000000001000501, 0x2405803806804007e, 0x10000000000000001000200, 0x10000000000000001000302, 0xf0000000000001a580000083e00000841000001, 0x40000000000dc00940000, 0x2c05403007004007a, 0x30000000000000001000304, 0x10000000000000001000003, 0x30000000000000001000401, 0x100184000000bc0000, 0x3005c03806804007a, 0x30000000000000001000401, 0x10000000000000001000304, 0x10000000000000001000002, 0x3005803006c04007a, 0x3000000000000000f0000000f0000000e000001, 0x174000000000000083b000008980000086d000200, 0x19b000000000000086c0000083b00000897000102, 0x40080000000380000, 0x8000000c400b80000, 0x2c06003406404007a, 0x300000001000803, 0x10000000000000001000008, 0x30000000000000001000100, 0x140000000000b000000160, 0x2c06002c060044082, 0x100000001000900, 0x3000000000000002a000008940000001d000609, 0x30000000000000001000206, 0x100000000000b800000164, 0x2c06003406004007e, 0x100000001000a00, 0x30000000000000006000003180000000b00010a, 0x30000000000000001000301, 0x2c06403006404007a, 0x150000000000000ca80000002d00000017000a02, 0x6000000000000002b000019ce0000005900000a, 0x120000000000000089d0000083e0000086f000200, 0x140000000000b000000160, 0x100184000000b00000, 0x2c05c02c060044082, 0x10000000000000001000100, 0x4b000000000000041a0000044a00000167000602, 0x10000000000000001000006, 0x4000000d400a40000, 0x2c054030068044082, 0x10000000000000001000204, 0x100000001000700, 0x2e5000000000000086700001afd00000814000407, 0x2805802c064044082, 0x135000000000000086c0000089800000837000100, 0x1e6000000000000189c0000089300000869000701, 0x16b00000000000008950000189900000868000007, 0x100184000000bc0000, 0x3005c03006403807e, 0x6300000000000019e30000084800000872000203, 0x57000000000000020e0000065100000226000102, 0x100000001000300, 0x3005802c06804007e, 0x21300000000000002c1000002cf000002f0000003, 0xd5000000000000041d0000044c00000436000100, 0x3d5000000000000086c000008ff00000814000301, 0x40000000000c400ac0000, 0x80000000000bc0000016c, 0x80000000000c800a40000, 0x2c05403807403c076, 0x10000000000000001000109, 0x100000001000300, 0x30000000000000001000403, 0x100184000000a40000, 0x2805c03807003c076, 0x10000000000000001000201, 0x10000000000000001000302, 0x100000001000100, 0x140188000000c40000, 0x3005803807003c076, 0x12000000000000086f000008fc000007d9000102, 0x100000001000504, 0x10000000000000001000005, 0x2c05403407403807a, 0x12f00000000000008950000083b0000086c000002, 0x17000000000000083b000002d0000002df000500, 0x24100000000000002ee00000869000002c1000205, 0x40080000000380000, 0x2c060038070038072, 0x10000008700000001000209, 0x10000000000000001000209, 0x300000001000900, 0x100184000000bc0000, 0x3005c03807003c072, 0x700000000000000170000047e0000001000010a, 0x33000000000000040700000ca800000467000201, 0x100000001000a00, 0x30058038074038076, 0x600000000000000320000194d0000006100000a, 0x6000000000000083d0000086f0000089e000200, 0x2700000000000019d7000000620000002f000a02, 0x8017c000000b80000, 0x4800340000, 0x40000000000b800000170, 0x3406403006c03c072, 0x100000001000100, 0x30000000000000001000100, 0x10000000000000001000201, 0x40003c0000, 0x3406403806c03806e, 0x30000008a0000000100000b, 0x3000000000000000100000b, 0x300000000000008a00000084100000872000401, 0x3406803006c03806e, 0x4500000047d0000001f000200, 0x30000000000000001000200, 0x180000000000000cf00000042100000439000001, 0x80000000000bc0000016c, 0x3406403406403c076, 0x100000001000900, 0x70000000000000017000004380000000f000409, 0x10000000000000001000204, 0x40000000000b800000170, 0x3406403406803c072, 0x100000001000a00, 0x3000000000000002c000019da0000005b00010a, 0x17400000000000019530000080f000008c9000201, 0x3806803806803806e, 0x8fa0000005d0000000d000a02, 0x2d000000000000002f000019560000005c00000a, 0x5d0000000000000cab0000040a00000467000200, 0x40080000000400000, 0x40003c0000, 0x3406003806c03c072, 0x30000000000000872000008a000000841000203, 0x300000001000100, 0x30000000000000001000100, 0x4c00300000, 0x3406002c06c038076, 0x5a000000000000089e000018c900000871000301, 0x300000001000500, 0x30000000000000001000205, 0x4000000bc00bc0000, 0x3406003806803c076, 0x22e00000000000008f500001953000007de000401, 0x100000001000600, 0x1f0000000000000168000001580000007d000106, 0x2c06403006803c076, 0x813000000000000087200000871000008a1000400, 0x4f000000000000083f000002df000002d0000604, 0x300000000000000320000008d0000002f000006, 0x100184000000bc0000, 0x40003c0000, 0x3005c03806c038076, 0x3b000000000000089b000002c0000002d0000204, 0x300000001000500, 0x10000000000000001000105, 0x2c06003006c03407a, 0x150000000000000465000003f000000170000200, 0x1f00000000000002c0000002df000000f0000502, 0x100000000000002ee000002c0000000eb000005, 0x3005803407003807a, 0xdb00000000000008990000083f0000086e000003, 0x25000000000000083c000002d0000002df000400, 0x270000000000000031000000930000002f000304, 0xc0088000000440000, 0x80000000000bc00b00000, 0x140000000000d400000160, 0x2804803c074038082, 0x10000000000000001000002, 0x100000001000401, 0x30000000000000001000204, 0x100000000000c400000164, 0x2804803c07403c07e, 0x10000000000000001000009, 0x10000000000000001000200, 0x30000000000000001000301, 0x1c0190000000c80000, 0x2c05003c07403807a, 0x10000000000000011000002ce0000000b00050a, 0x10000000000000001000305, 0x100000001000a00, 0x2804803407804007a, 0x30000000000000009000005460000001400000a, 0x3000000000000000d2000000db000000d7000100, 0x2100000000000019b30000006600000031000a01, 0x140000000000b000000160, 0x40000000000c400ac0000, 0x28048038070044082, 0x10000000000000001000102, 0x100000001000500, 0x300000000000000810000019500000077000205, 0x40000000000dc00940000, 0x2804c030070044082, 0x10000000000000001000201, 0x100000001000600, 0x1a7000000000000044900000d2c00000409000106, 0x2805002c06c044082, 0x15000000000000024c000000c8000000bf000500, 0x3e00000000000002bc000002db000000ef000605, 0x3900000000000001b7000004e9000001ae000006, 0x140000000000e000000160, 0x140000000000c800000160, 0x2804c03007003c082, 0x10000000000000001000003, 0x1500000000000000bf0000024c000000c8000205, 0x1cb00000000000008c4000008c9000007e8000302, 0x2804c034070034082, 0x10000000000000001000103, 0x24000000000000010d0000033600000107000005, 0x54f0000000000000862000008c900000840000300, 0x2c05003807003407e, 0x11400000000000019cb000008090000089c000402, 0x1a1000000000000089b00001a40000007d8000004, 0x300000000000000280000002d0000002c000200, 0x140000000000e000800000, 0x10008c000000440000, 0x2003c034080034082, 0x10000007800000001000108, 0x100000001000401, 0x30000000000000001000004, 0x1c030038080038086, 0x600000000000000360000084f00000023000008, 0x620000000000000427000004070000017c000400, 0x300000000000003060000002400000005000804, 0x100000000000d000940000, 0x2003c03807c04007e, 0x100000000000000170000046200000011000208, 0x100000001000400, 0xb1000000000000011d0000030900000107000104, 0x800000000004400000074, 0x2404003c07403c086, 0x30000000000000001000001, 0x10000000000000087000000770000002b000503, 0x28500000000000008bc000019980000080f000105, 0x20044034078038082, 0xb30000000000000883000002b9000002ca000301, 0x9f000000000000085e00000882000002b9000003, 0x6c000000000000088c0000186f00000859000100]
private def bspMeta_31 : ℕ × ℕ × ℕ := (538, 2000, 11)

private def bspWords_32 : List ℕ := [0x4000000bc00c80000, 0x40184000000bc0000, 0x3, 0x10000000000000001000103, 0x10000000000000001000001, 0x140000000000bc0000016c, 0x400000000004800340000, 0x1c0000000000d000000164, 0x1c03403807c04008e, 0x10000000000000001000005, 0x300000001000501, 0x57a100000000000007d00000093500014820000005, 0x140000000000d400980000, 0x1c03403c084044086, 0x10000000000000001000308, 0x10000000000000001000003, 0x42300000000000017700000006f00000fa0000806, 0x2c01ac000000d00000, 0x2404403807c044086, 0x10000000000000001000401, 0x30000000000000001000304, 0x10000000000000001000002, 0x2003c03408003808a, 0x15300000000000004840000045700000471000001, 0x31800000000000008aa00000906000008e1000200, 0x4b9000000000000090b0000090d000008b7000102, 0x200000000000bc00000160, 0x400000000005400280000, 0x1c03402c07c048092, 0x10000000000000001000102, 0x300000001000600, 0x18b700000000000004b0000001e3000044c0000206, 0x280000000000c400000158, 0x1c03403407004809a, 0x100000001000600, 0x5d000000000000045d000000790000043a000600, 0x1fad00000000000005dc0000023100005014000107, 0x2003c030070048092, 0x100000001000602, 0x1ad00000000000008eb0000015300000872000602, 0x4110000000000001a790000089b000008f8000100, 0x1000d00000005c0000, 0x40000000000e800940000, 0x24050030074044086, 0x10000000000000001000401, 0x100000001000100, 0x20000000000000001000100, 0x800000000003c00000078, 0x2405003806c04808a, 0x300000001000700, 0xb300000000000002df00000061000002d0000700, 0x20000000000000001000207, 0x2c05403806c044086, 0x100000001000705, 0x1b900000000000008cd00000061000008a1000705, 0x65000000000000030c000008bd000002fd000100, 0x1c0000000000d000000164, 0x80000000000ec008c0000, 0x2404003007804008e, 0x10000000000000001000104, 0x100000001000300, 0x16e0000000000001b360000094800000893000403, 0x2404803007004008e, 0x10000000000000001000100, 0x5100000000000001730000007100000199000702, 0x17a0000000000000916000008ac000008e7000003, 0x400000000006400580000, 0x2004803c078044086, 0x10000000000000001000504, 0x20000000000000001000002, 0x6f0000000000000da70000045800000473000401, 0x800000000003c00000078, 0x2804803407404808a, 0x300000001000300, 0x15f000000000000045b0000091500000478000203, 0x1d700000000000008b2000004c300000463000102, 0x2804c03407803808a, 0x6f0000000000000490000004630000023d000301, 0xe0000000000000440000002ee00000195000003, 0xb000000000000009f000000ef00000048000100, 0x140194000000c40000, 0x40000000000400000007c, 0x100000000000c400000170, 0x3005c03806c040082, 0x100000001000500, 0x15900000000000008fd00000061000008d2000500, 0x10000000000000001000203, 0x400040000, 0x3005c03c07004007e, 0x30000000000000001000203, 0x3000000001000100, 0x10000000000000001000301, 0x40084000000340000, 0x2806403806c04007e, 0x300000001000703, 0xf600000000000008fe00000123000008d1000703, 0x30000000000000001000002, 0x800c8000000640000, 0x3406003806c04007e, 0x3000000000000008d0000098d0000002e000102, 0x1f2000000000000089900001af70000095f000301, 0x20000000000000001000003, 0x3005c03407004007e, 0x13000000000000002f0000047e00000019000002, 0x54000000000000047e0000092600000465000300, 0x2300000000000008f9000000320000002f000203, 0x80000000000bc00000178, 0x40000000000d000ac0000, 0x3005c03807404007a, 0x10000000000000001000109, 0x100000001000200, 0x10000000000000001000302, 0x44003c0000, 0x3006003807004007a, 0x10000000000000001000201, 0x300000001000300, 0x1b000000000000024b000006960000023f000103, 0x3006403806c04007a, 0x100000001000702, 0x9300000000000008ff00000061000008d0000702, 0x33000000000000092d000008ca000002ff000003, 0x80188000000c40000, 0x40000000000c40000017c, 0x3806803806c03c076, 0x10000000000000001000001, 0x9300000000000008ff0000006100000931000706, 0x10000000000000001000102, 0x40000000000d00000017c, 0x38068038070038076, 0x1000000000000000100000b, 0x3000000000000004670000049700000480000107, 0x8d0000000200000001000b01, 0x3806803c07003c072, 0x30000000000000003000001b900000006100070b, 0x30000000000000090000000930000008d1000007, 0x30000000000000d35000000310000001a000b00, 0x40084000000400000, 0x40000000000dc00a00000, 0x3406403407403c076, 0x10000008d0000000200020b, 0x100000001000300, 0x30000000000000001000103, 0x400040000, 0x3406403c07003c076, 0x11a000000000000095b000008ff0000089d000301, 0x3000000001000400, 0x6000000000000002f0000002c0000002f000104, 0x2c06803407003407a, 0x200000000000000320000086c00000031000300, 0xc000000000000008ce0000092e000008ff000403, 0x2000000000000098c0000002e0000002f000004, 0x800c8000000640000, 0x3406003807403c076, 0x1000000000000000310000092f0000002100010b, 0x3900000000000008cb00001afd0000092e000301, 0x20000000000000001000003, 0x3005c03807803c07a, 0x1000000450000000100000b, 0x60000000000000465000008ff00000497000300, 0x210000000000001c17000000650000002f000b03, 0x1c019c000000b00000, 0x80000000000d400a40000, 0x40000000000400000007c, 0x2405403807804007e, 0x30000000000000001000009, 0x100000001000201, 0x10000000000000001000201, 0x80088000000440000, 0x3005803807804007a, 0x21000000000000002f00001c170000006500040a, 0x3f0000000000001a52000008fb0000092b000104, 0x300000001000a00, 0x2c05403807c03c07e, 0x3000000870000000200000a, 0x300000000000004620000047d00000187000100, 0x900000000000009590000006700000010000a01, 0x40000000000c400b80000, 0x800000000005c000000b8, 0x2405403c074044082, 0x20000000000000001000002, 0x100000001000501, 0x10000000000000001000305, 0x2405803c07404007e, 0x3f00000000000008fb0000092b000008c6000402, 0x10000000000000001000104, 0x600000000000004da0000085800000467000200, 0x40000000000e800940000, 0x80088000000440000, 0x30058030074038082, 0x2d000000000000030e000002dd0000030f000502, 0x100000001000601, 0x30000000000000001000006, 0x2c054030074044082, 0x1b600000000000008a00000030e0000031f000002, 0xad00000000000002ec00000923000002fd000600, 0x46800000000000009250000095c0000089f000206, 0x30058030070044082, 0xc000000000000002e0000002e0000002b000400, 0x780000000000000231000002490000023e000504, 0x20700000000000008f7000008c400000923000005, 0xc008c000000440000, 0x4000000000040003c0000, 0x2804c04007c04007e, 0x1b000000000000003000001d2b00000067000209, 0x300000001000400, 0x30000000000000001000104, 0x400000000004800340000, 0x2804c03807c038082, 0x1b00000000000008f900001b90000008c9000301, 0x300000001000500, 0x1500000000000001bf60000095700000871000105, 0x140000000000d40000016c, 0x2804c03407803c086, 0x10000000000000001000001, 0x22e000000000000084e000008f600000983000604, 0x6840000000000001bf6000008eb000008c9000106, 0x2c05003c078040082, 0xcf00000000000008f500001c9800000853000401, 0x9000000000000008c4000008f60000092b000004, 0x240000000000000204000000b0000000b3000100, 0x2801a8000000d40000, 0x28048034080040082, 0x100000000000000070000015500000005000109, 0x66000000000000044000000d6e000004a9000401, 0x10000000000000001000004, 0x2404004008003c086, 0x10000008100000002000009, 0x300000000000000350000003000000035000400, 0x180000000000001c7a0000006c0000002f000904, 0x40184000000bc0000, 0x3806c03806c03c076, 0x90000000000000567000000130000000a000301, 0x10000009300000001000003, 0x10000000000000001000003, 0xc00000000003c00000074, 0x400000038002c0000, 0x2c0000000000b000000154, 0x4000000ec00980000, 0x1c03402c06c05009e, 0x10000000000000001000105, 0x100000001000600, 0x13bd00000000000000fa0000015100002fda000506, 0x340000000000d00000014c, 0x1803802c0600480a6, 0x10000000000000001000001, 0x400000001000703, 0x40310000000000001f400000093500015f90000107, 0x2003c02c06005009e, 0x10000000000000001000201, 0x40000000000000001000302, 0x17d000000000000083100000977000008f3000100, 0xc008c000000400000, 0x2404c02c06004c096, 0x30000000000000001000300, 0x40000000000000001000203, 0x300000001000300, 0x14000c0000, 0x2003c02c07004c096, 0x30000000000000001000406, 0xc0000000000000001000001, 0x27000000000000090700000a5700000811000602, 0x4000000ec00980000, 0x1c04402c06c04c096, 0x90000000000000072000001d100000025000201, 0x10000000000000001000002, 0x420000000000001b9f000002270000022d000103, 0x1c04802c06404809a, 0x310000000000000484000001730000017b000200, 0xe6000000000000031a000008b7000002f5000302, 0x780000000000000312000002e0000002e7000003, 0x340000000000ac0000014c, 0x80000005400340000, 0x180380200580540a6, 0x10000000000000001000102, 0x300000001000600, 0x41b00000000000003e80000004f00000bb8000206, 0x2000000000005c000000a0, 0x1803c0180400540b2, 0x200000001000800, 0x1500000000000000090000ef1000000190000708, 0x5590000000000001d4c0000025900005bcc000107, 0x1c04401c0500540a6, 0x100000001000802, 0x10000005700000001000008, 0x750000000000000c960000093500000473000100, 0x2c0000000000b000000154, 0x1000d00000005c0000, 0x2405002405405009e, 0x100000001000801, 0x9000000000000002c00001a8500000053000208, 0x20000000000000001000002, 0x1c04802005c05009e, 0x2d00000000000001170000023800000095000003, 0x21000000000000046c000008fd00000455000200, 0x1e00000000000008fe0000025200000221000302, 0x800880000003c0000, 0x2805802805804c096, 0x300000001000804, 0x300000000000000090000055500000011000108, 0x30000000000000001000001, 0x280000000000ac00000158, 0x2405002405c05009a, 0x10000000000000001000004, 0x300000000000001c70000056d000001be000201, 0x5a00000000000004700000012a00000117000402, 0x2c05403005c04c096, 0x1c500000000000006b1000008eb00000248000104, 0x5d000000000000098e000019b3000008e7000001, 0x300000000000000ac0000002f0000002b000400, 0x400640000002c0000, 0x800000000005c000000b8, 0x400000068005c0000, 0x2c060034068044082, 0x200000001000001, 0x20000000000000001000001, 0x40000000000000001000200, 0x800000000003c00000078, 0x2c06002c06004808a, 0x300000001000800, 0x40000009c00000001000308, 0x40000000000000001000308, 0x140000000000bc0000016c, 0x2c060030064044086, 0x100000001000900, 0x30000009900000002000109, 0x40000000000000001000401, 0x2c064034064044082, 0x960000000400000001000902, 0x21000000000000003000001af10000005b000009, 0xb10000000000000929000004630000047d000200, 0x40000000000400000007c, 0x400c4000000500000, 0x2c06803406804007e, 0x300000001000801, 0x10000004b00000001000208, 0x20000000000000001000002, 0x40084000000400000, 0x3406403806804007e, 0x4200000000000008d1000004af0000046a000107, 0x30000000000000031000000310000001a000301, 0x30000000000000001000003, 0x2806403006c04007e, 0x74a0000000000001a73000008fd00000962000007, 0xab00000000000008c900000dbf0000047e000300, 0x900000000000004c3000008d500000450000703, 0x80000000000bc00000178, 0x80188000000c40000, 0x3806803806804007a, 0x100000001000901, 0xd0000000000000031000008ff0000001f000209, 0x10000000000000001000002, 0x2c06803406c04007a, 0x7dd00000000000008d0000008ff00000961000007, 0x270000000000001afd0000092b000008ce000200, 0x84000000000000095e00001a7c000008d1000702, 0x3006c03806c03c076, 0x8d000000000000009010000090000000931000506, 0x93000000030000000200000004080005, 0x2d000000000000031f000002f1000002f0000600, 0x1c0000000000b800000164, 0x40044000000200000, 0x200000000000bc00000160, 0x2c05802c05c048092, 0x100000001000800, 0x7000000000000002e000008ed0000001d000408, 0x60000000000000001000104, 0x2c05802c06004808e, 0x10000000000000001000201, 0x1fad0000009b000001a8000000cc080003, 0x60000000000000001000100, 0x4000000ec00980000, 0x1c019c000000b00000, 0x2405402c06c04808e, 0x10000000000000001000307, 0x10000000000000001000102, 0x100000001000700, 0x800000000002c00000058, 0x2804802c06c04c092, 0x40000000000000001000008, 0x100000001000602, 0x2400000000000008e700001e6f00000841000806, 0x2005003006c04808e, 0x29a00000000000008710000094d00000966000108, 0x1500000000000002e7000000bb000000c6000001, 0xf000000000000025d0000096700000210000800, 0x800000000002c00000058, 0x2405002806404c092, 0x40000000000000001000001, 0xf00000000000004770000091500000175000502, 0x240000000000000091600001a0a000008e9000105, 0x2805403406404808e, 0x13e0000000000001b57000004790000045e000201, 0x1e0000000000000264000003390000008f000002, 0x810000000000000247000008b50000023c000100, 0x800000000003c00000078, 0x4000000ec00980000, 0x2805402c06c04808a, 0x30000000000000001000106, 0x10000000000000001000001, 0x123000000000000091f0000099500000871000602, 0x8000000dc00ac0000, 0x3005803006804808a, 0x30000000000000001000201, 0x10000000000000001000004, 0xb100000000000008c4000008f70000091d000103, 0x2805c02c06404808a, 0x1500000000000001cb0000007500000070000400, 0x8d000000000000022f0000091f0000023d000304, 0x1dd0000000000000921000008bc000008f3000003, 0x140000000000bc0000016c, 0x4000000d400b00000, 0x3005803406c044086, 0x10000000000000001000107, 0x10000000000000001000004, 0x1d00000000000000ff00000341000000f0000702, 0x2805c030068044086, 0x4e00000000000008f90000024a00000231000400, 0x700000000000000700000009900000027000204, 0x150000000000000109000002eb000000fa000002, 0x3005c03406c044082, 0x1c200000000000008a0000002560000024d000306, 0x4e0000000000000231000008f90000024a000003, 0x43e00000000000008f800000993000008a1000600]
private def bspMeta_32 : ℕ × ℕ × ℕ := (531, 2000, 11)

noncomputable section

/-- **Unconditional Real-Plane Upper Bound for `3 ≤ n ≤ 32` (`cutCount_le_F_3_to_32`):**
Proved 100% in Lean 4's pure kernel (`decide` on exact `ℕ` Farkas-BSP certificates for `5 ≤ n ≤ 32`,
together with the algebraic proofs for `n = 3, 4` above; zero `native_decide`, zero external C code). -/
theorem cutCount_le_F_3_to_32 (n : ℕ) (hn3 : 3 ≤ n) (hn32 : n ≤ 32) :
    ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n := by
  interval_cases n
  · exact cutCount_three_le_nineteen
  · exact cutCount_four_le_thirtyfive
  · exact checkCertN_sound 5 1 2 5 bspWords_5 (by decide)
  · exact checkCertN_sound 6 1 2 7 bspWords_6 (by decide)
  · exact checkCertN_sound 7 1 2 7 bspWords_7 (by decide)
  · exact checkCertN_sound 8 1 2 8 bspWords_8 (by decide)
  · exact checkCertN_sound 9 1 2 8 bspWords_9 (by decide)
  · exact checkCertN_sound 10 1 2 9 bspWords_10 (by decide)
  · exact checkCertN_sound 11 1 2 8 bspWords_11 (by decide)
  · exact checkCertN_sound 12 1 2 9 bspWords_12 (by decide)
  · exact checkCertN_sound 13 1 2 9 bspWords_13 (by decide)
  · exact checkCertN_sound 14 1 2 10 bspWords_14 (by decide)
  · exact checkCertN_sound 15 1 2 11 bspWords_15 (by decide)
  · exact checkCertN_sound 16 698 2000 10 bspWords_16 (by decide)
  · exact checkCertN_sound 17 683 2000 10 bspWords_17 (by decide)
  · exact checkCertN_sound 18 668 2000 10 bspWords_18 (by decide)
  · exact checkCertN_sound 19 655 2000 10 bspWords_19 (by decide)
  · exact checkCertN_sound 20 642 2000 10 bspWords_20 (by decide)
  · exact checkCertN_sound 21 630 2000 10 bspWords_21 (by decide)
  · exact checkCertN_sound 22 619 2000 10 bspWords_22 (by decide)
  · exact checkCertN_sound 23 608 2000 11 bspWords_23 (by decide)
  · exact checkCertN_sound 24 598 2000 10 bspWords_24 (by decide)
  · exact checkCertN_sound 25 588 2000 10 bspWords_25 (by decide)
  · exact checkCertN_sound 26 579 2000 10 bspWords_26 (by decide)
  · exact checkCertN_sound 27 570 2000 10 bspWords_27 (by decide)
  · exact checkCertN_sound 28 562 2000 11 bspWords_28 (by decide)
  · exact checkCertN_sound 29 554 2000 12 bspWords_29 (by decide)
  · exact checkCertN_sound 30 546 2000 11 bspWords_30 (by decide)
  · exact checkCertN_sound 31 538 2000 11 bspWords_31 (by decide)
  · exact checkCertN_sound 32 531 2000 11 bspWords_32 (by decide)

/-- **Unconditional Discharge of `h_small_3_15` (`cutCount_le_F_3_to_15`):**
Eliminates the external `exact.c` small-`n` hypothesis of `Main.theoremM_all_n` completely! -/
theorem cutCount_le_F_3_to_15 (n : ℕ) (hn3 : 3 ≤ n) (hn15 : n ≤ 15) :
    ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n :=
  cutCount_le_F_3_to_32 n hn3 (by omega)

/-- **Unconditional Exact `maxCutCount n = F n` for all `3 ≤ n ≤ 32` (`maxCutCount_eq_F_3_to_32`):**
Closes `m(n) = ⌊(9n² + 4n - 17)/4⌋` unconditionally in pure Lean 4 kernel for every `3 ≤ n ≤ 32`. -/
theorem maxCutCount_eq_F_3_to_32 (n : ℕ) (hn3 : 3 ≤ n) (hn32 : n ≤ 32) :
    maxCutCount n = F n :=
  maxCutCount_eq_of_bounds (cutCount_le_F_3_to_32 n hn3 hn32) (barany_frankl_lower_bound n hn3)

/-- **Exact `m(5) = 57` and `m(6) = 82` (Unconditional over `ℝ`).** -/
theorem maxCutCount_five_and_six : maxCutCount 5 = 57 ∧ maxCutCount 6 = 82 := by
  rw [maxCutCount_eq_F_3_to_32 5 (by omega) (by omega),
      maxCutCount_eq_F_3_to_32 6 (by omega) (by omega)]
  decide

/-- **Exact Resolution of Bárány–Frankl's Open `n = 10` Case (`maxCutCount 10 = 230`):**
Bárány and Frankl (2021, p. 119) wrote for `n = 10` (`230` cubes): *"The exact number is unknown."*
We prove unconditionally in pure Lean 4 kernel that `m(10) = 230`. -/
theorem maxCutCount_ten : maxCutCount 10 = 230 := by
  rw [maxCutCount_eq_F_3_to_32 10 (by omega) (by omega)]
  decide

/-- **Theorem U Extended Unconditionally to All `n ≥ 2` (`theoremU_bound_all_ge_2`):**
Every nonzero real plane cuts at most `Ubound n = ⌊(9n² + 6n - 20)/4⌋` open unit cubes for ALL `n ≥ 2`
(removing the `n ≥ 16` threshold of `Phase4.theoremU_bound`). -/
theorem theoremU_bound_all_ge_2 (n : ℕ) (hn : 2 ≤ n) (a b c t : ℝ) (hv : IsNormal a b c) :
    cutCount n a b c t ≤ Ubound n := by
  by_cases hn2 : n = 2
  · subst hn2
    have h7 := cutCount_two_le_seven a b c t hv
    have hU2 : Ubound 2 = 7 := by decide
    omega
  · by_cases hn15 : n ≤ 15
    · have hF := cutCount_le_F_3_to_15 n (by omega) hn15 a b c t hv
      have hFU : F n ≤ Ubound n := by
        have h3 : 3 ≤ n := by omega
        interval_cases n <;> decide
      exact le_trans hF hFU
    · exact theoremU_bound n (by omega) a b c t hv

/-- **Strengthened Headline Theorem M (`theoremM_all_n_from_arr_33_699`):**
With `3 ≤ n ≤ 32` (including all of `h_small_3_15`) and `n ≥ 700` proved unconditionally in Lean's
pure kernel, `maxCutCount n = F n` for ALL `n ≥ 3` requires `ArrVerifyPass` ONLY on `33 ≤ n ≤ 699`. -/
theorem theoremM_all_n_from_arr_33_699
    (h_arr_33_699 : ∀ n : ℕ, 33 ≤ n → n ≤ 699 → ∃ cfg : ArrVerifyCfg, ArrVerifyPass n cfg)
    (n : ℕ) (hn : 3 ≤ n) :
    maxCutCount n = F n ∧ maxCutCount n < F n + 2 := by
  have hub : ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n := by
    by_cases h32 : n ≤ 32
    · exact cutCount_le_F_3_to_32 n hn h32
    · by_cases h699 : n ≤ 699
      · obtain ⟨cfg, hpass⟩ := h_arr_33_699 n (by omega) h699
        exact prop_V_arr_verify_sound n (by omega) cfg hpass
      · exact theorem_A_upper_bound_ge_700 n (by omega)
  have heq : maxCutCount n = F n :=
    maxCutCount_eq_of_bounds hub (barany_frankl_lower_bound n hn)
  exact ⟨heq, by omega⟩

open Classical in
/-- **Unconditional Discrete Arithmetic Plane Bound (`stdArithPlane_card_le_F_uncond`):**
For every `n` with `3 ≤ n ≤ 32` or `700 ≤ n`, every Reveillès–Andres standard arithmetic plane
`(a, b, c) ∈ ℕ³ \ {0}`, `μ ∈ ℤ` contains at most `F(n)` voxels of `{0, …, n - 1}³`. -/
theorem stdArithPlane_card_le_F_uncond (n : ℕ) (hn : (3 ≤ n ∧ n ≤ 32) ∨ 700 ≤ n)
    (a b c : ℕ) (hS : 0 < a + b + c) (μ : ℤ) :
    ((cells n).filter (stdArithPlaneZ a b c μ)).card ≤ F n := by
  have hcut : ((cells n).filter (stdArithPlaneZ a b c μ)).card =
      cutCount n (a : ℝ) (b : ℝ) (c : ℝ) ((μ : ℝ) + ((a + b + c : ℕ) : ℝ) - 1 / 2) := by
    unfold cutCount
    rw [cutSet_eq_stdArithPlaneZ_half n a b c hS μ]
  rw [hcut]
  have hv : IsNormal (a : ℝ) (b : ℝ) (c : ℝ) :=
    isNormal_of_pos_sum (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hS)
  rcases hn with ⟨h3, h32⟩ | h700
  · exact cutCount_le_F_3_to_32 n h3 h32 (a : ℝ) (b : ℝ) (c : ℝ) _ hv
  · exact theorem_A_upper_bound_ge_700 n h700 (a : ℝ) (b : ℝ) (c : ℝ) _ hv

/-- Closed-form maximum `m_diag(n) = ⌊(9n² - 5 - 3[n even])/4⌋` of `(1, 1, 1)` slices (`n ≥ 2`). -/
def mDiagFormula (n : ℕ) : ℕ :=
  if n = 1 then 1 else (9 * n ^ 2 - (if n % 2 = 0 then 8 else 5)) / 4

/-- **Exact Linear Tilt Gain Over the Main Diagonal (`F_eq_mDiag_add_sub_three`):**
For EVERY `n ≥ 3`, Bárány–Frankl's tilted normal `(n - 1, n - 1, n)` exceeds the main-diagonal
formula `mDiagFormula n` by **exact linear margin `n - 3`** (`0` at `n = 3`, `+1` at `n = 4`,
`+7` at `n = 10`), whereas at `n = 2`, `mDiagFormula 2 = 7 = F 2 + 1`. -/
theorem F_eq_mDiag_add_sub_three :
    mDiagFormula 2 = F 2 + 1 ∧
    ∀ n : ℕ, 3 ≤ n → F n = mDiagFormula n + (n - 3) := by
  refine ⟨by decide, fun n hn => ?_⟩
  unfold mDiagFormula
  rw [ite_eq_right (by omega)]
  by_cases hev : n % 2 = 0
  · rw [ite_eq_left hev]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 2 * k := ⟨n / 2, by omega⟩
    have hk2 : 2 ≤ k := by omega
    have hsq : 4 ≤ k ^ 2 := by nlinarith
    rw [F_even k hk2]
    have h9 : (9 * (2 * k) ^ 2 - 8) / 4 = 9 * k ^ 2 - 2 := by
      have h1 : 8 ≤ 9 * (2 * k) ^ 2 := by nlinarith
      have h2 : 2 ≤ 9 * k ^ 2 := by nlinarith
      have heq : 9 * (2 * k) ^ 2 - 8 = 4 * (9 * k ^ 2 - 2) := by zify [h1, h2]; ring
      rw [heq]; omega
    rw [h9]
    omega
  · rw [ite_eq_right hev]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hsq : 1 ≤ k ^ 2 := by nlinarith
    rw [F_odd k hk1]
    have h9 : (9 * (2 * k + 1) ^ 2 - 5) / 4 = 9 * k ^ 2 + 9 * k + 1 := by
      have h1 : 5 ≤ 9 * (2 * k + 1) ^ 2 := by nlinarith
      have heq : 9 * (2 * k + 1) ^ 2 - 5 = 4 * (9 * k ^ 2 + 9 * k + 1) := by zify [h1]; ring
      rw [heq]; omega
    rw [h9]
    omega

end

end CheeseCutM
