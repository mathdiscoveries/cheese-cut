module

public import CheeseCutM.TheoremA

import Mathlib.Tactic

/-!
# Headline Results: Bárány–Frankl (2021) Cheese-Cutting Theorem M

Assembles the full Theorem M package over `ℝ`:
* `theoremM_ge_700` (**100% unconditional over `ℝ`**): for every `n ≥ 700`,
  `(∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n) ∧ (∃ a b c t : ℝ, IsNormal a b c ∧ cutCount n a b c t = F n)`.
* `maxCutCount_eq_F_ge_700` (**100% unconditional over `ℝ`**): for every `n ≥ 700`,
  `maxCutCount n = F n = ⌊(9n² + 4n - 17)/4⌋`.
* `barany_frankl_plus_two_refuted_ge_700` (**100% unconditional over `ℝ`**): refutation of
  Bárány–Frankl's Section 5 "+2" remark (`maxCutCount n < F n + 2`) for all `n ≥ 700`.
* `theoremM_all_n`: for EVERY `n ≥ 3`, `maxCutCount n = F n` and `maxCutCount n < F n + 2`,
  explicitly parameterized by the finite-range certificates `h_small_3_15` (exact enumeration
  for `3 ≤ n ≤ 15`) and `h_arr_16_699` (passing `arr_verify` vertex certificates via
  Proposition V for `16 ≤ n ≤ 699`).
-/

@[expose] public section

namespace CheeseCutM

noncomputable section

/-- Helper: turning an upper bound `∀ plane, cutCount ≤ F n` and lower bound `∃ plane, cutCount = F n`
into `maxCutCount n = F n`. -/
lemma maxCutCount_eq_of_bounds {n M : ℕ}
    (hub : ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ M)
    (hlb : ∃ a b c t : ℝ, IsNormal a b c ∧ cutCount n a b c t = M) :
    maxCutCount n = M := by
  apply le_antisymm
  · obtain ⟨a0, b0, c0, t0, hv0, hcnt0⟩ := hlb
    apply csSup_le
    · exact ⟨M, a0, b0, c0, t0, hv0, hcnt0⟩
    · rintro k ⟨a, b, c, t, hv, rfl⟩
      exact hub a b c t hv
  · obtain ⟨a0, b0, c0, t0, hv0, hcnt0⟩ := hlb
    exact le_csSup (bddAbove_counts n) ⟨a0, b0, c0, t0, hv0, hcnt0⟩

/-- **Headline Theorem M for `n ≥ 700` (`theoremM_ge_700`, 100% UNCONDITIONAL over `ℝ`):**
For every `n ≥ 700`, every nonzero real plane cuts at most `F(n) = ⌊(9n² + 4n - 17)/4⌋`
open unit cubes of the `n × n × n` box, and some real plane cuts exactly `F(n)` cubes. -/
theorem theoremM_ge_700 (n : ℕ) (hn : 700 ≤ n) :
    (∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n) ∧
    (∃ a b c t : ℝ, IsNormal a b c ∧ cutCount n a b c t = F n) :=
  ⟨theorem_A_upper_bound_ge_700 n hn, barany_frankl_lower_bound n (by omega)⟩

/-- **`maxCutCount n = F n` for all `n ≥ 700` (100% UNCONDITIONAL over `ℝ`).** -/
theorem maxCutCount_eq_F_ge_700 (n : ℕ) (hn : 700 ≤ n) :
    maxCutCount n = F n := by
  have ⟨hub, hlb⟩ := theoremM_ge_700 n hn
  exact maxCutCount_eq_of_bounds hub hlb

/-- **Refutation of Bárány–Frankl's Section 5 "+2" remark for all `n ≥ 700` (100% UNCONDITIONAL):**
`m(n) = F(n) < F(n) + 2` for every `n ≥ 700`. -/
theorem barany_frankl_plus_two_refuted_ge_700 (n : ℕ) (hn : 700 ≤ n) :
    maxCutCount n < F n + 2 := by
  rw [maxCutCount_eq_F_ge_700 n hn]
  omega

/-- **Headline Theorem M for all `n ≥ 3` (`theoremM_all_n`):**
Given the finite-range upper bounds for `3 ≤ n ≤ 15` (`h_small_3_15`, exact enumeration)
and passing `arr_verify` vertex-principle certificates for `16 ≤ n ≤ 699` (`h_arr_16_699`,
verified via Proposition V), `maxCutCount n = F n = ⌊(9n² + 4n - 17)/4⌋` and
`maxCutCount n < F n + 2` hold for EVERY `n ≥ 3`. -/
theorem theoremM_all_n
    (h_small_3_15 : ∀ n : ℕ, 3 ≤ n → n ≤ 15 →
      ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n)
    (h_arr_16_699 : ∀ n : ℕ, 16 ≤ n → n ≤ 699 →
      ∃ cfg : ArrVerifyCfg, ArrVerifyPass n cfg)
    (n : ℕ) (hn : 3 ≤ n) :
    maxCutCount n = F n ∧ maxCutCount n < F n + 2 := by
  have hub : ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n := by
    by_cases h15 : n ≤ 15
    · exact h_small_3_15 n hn h15
    · by_cases h699 : n ≤ 699
      · obtain ⟨cfg, hpass⟩ := h_arr_16_699 n (by omega) h699
        exact prop_V_arr_verify_sound n (by omega) cfg hpass
      · exact theorem_A_upper_bound_ge_700 n (by omega)
  have heq : maxCutCount n = F n :=
    maxCutCount_eq_of_bounds hub (barany_frankl_lower_bound n hn)
  exact ⟨heq, by omega⟩

end

end CheeseCutM
