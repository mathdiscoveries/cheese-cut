module

public import CheeseCutM.Phase4

import Mathlib.Tactic

/-!
# Pairing Lemma (Lemma P), Corollary P1, and Coupling Lemma (Lemma C)

100% unconditional proofs over `ℝ`:
* `lemma_P_pairing_bound`: for `0 < p ≤ q`, any `α, β : ℝ`, and any level `S : ℕ`,
  `Δ(p, q; α) + Δ(p, q; β) ≥ G(S) = T2(S + 1) - T2(S + 1 - 2 L(S))`.
* `cor_P1_full`, `cor_P1_full_of_lt`, `cor_P1_full_mono`, `cor_P1_not_full`,
  `cor_P1_quad_bound`: full-level characterization, downward monotonicity of fullness,
  and quadratic deficit bound `G(S) ≥ T2(S + 1) - (z + 2)²/4`.
* `B1`, `B2`, `B3` and `lemma_P_sum_B`: `B₁ + B₂ + B₃ ≤ missedCount n u w t` for all `t : ℝ`.
* `lemma_C_coupling`: for every even `n = 2c + 4 ≥ 6` and every `(u, w) ≠ (0, 0)` with
  `u ≥ 0, w ≥ 0` in `K`, `missedCount n u w t ≥ D(n)` for every `t : ℝ`.
-/

@[expose] public section

namespace CheeseCutM

open Finset

noncomputable section

/-! ### Row decomposition of `triNat` and Lemma P -/

open Classical in
/-- Row `s` of `triNat p q c`: values `b ∈ {0, …, s}` with `p (s - b) + q b < c`. -/
def rowSet (p q c : ℝ) (s : ℕ) : Finset ℕ :=
  (range (s + 1)).filter (fun b => p * ((s - b : ℕ) : ℝ) + q * (b : ℝ) < c)

/-- Number of lattice points on row `a + b = s` of `triNat p q c`. -/
def rowCard (p q c : ℝ) (s : ℕ) : ℕ := (rowSet p q c s).card

lemma rowCard_eq_pos {p q c : ℝ} (hpq : p < q) (s : ℕ) :
    rowCard p q c s = min (s + 1) ⌈(c - p * (s : ℝ)) / (q - p)⌉₊ := by
  have hd : 0 < q - p := by linarith
  have hset : rowSet p q c s = range (min (s + 1) ⌈(c - p * (s : ℝ)) / (q - p)⌉₊) := by
    ext b
    unfold rowSet
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    constructor
    · rintro ⟨hbs, hlt⟩
      refine ⟨hbs, Nat.lt_ceil.2 ?_⟩
      rw [lt_div_iff₀ hd]
      rw [Nat.cast_sub (by omega : b ≤ s)] at hlt
      linarith
    · rintro ⟨hbs, hbl⟩
      refine ⟨hbs, ?_⟩
      have h1 : (b : ℝ) < (c - p * (s : ℝ)) / (q - p) := Nat.lt_ceil.1 hbl
      rw [lt_div_iff₀ hd] at h1
      rw [Nat.cast_sub (by omega : b ≤ s)]
      linarith
  unfold rowCard
  rw [hset, Finset.card_range]

lemma rowCard_eq_zero {p q c : ℝ} (hpq : p = q) (s : ℕ) :
    rowCard p q c s = if p * (s : ℝ) < c then s + 1 else 0 := by
  subst hpq
  unfold rowCard rowSet
  by_cases hlt : p * (s : ℝ) < c
  · rw [ite_eq_left hlt]
    have hset : (range (s + 1)).filter (fun b => p * ((s - b : ℕ) : ℝ) + p * (b : ℝ) < c) =
        range (s + 1) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
      intro hb
      rw [Nat.cast_sub (by omega : b ≤ s)]
      linarith
    rw [hset, Finset.card_range]
  · rw [ite_eq_right hlt]
    have hset : (range (s + 1)).filter (fun b => p * ((s - b : ℕ) : ℝ) + p * (b : ℝ) < c) = ∅ := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
      intro hb
      rw [Nat.cast_sub (by omega : b ≤ s)]
      linarith
    rw [hset, Finset.card_empty]

/-- Summing row counts over rows `0..S` never exceeds `Delta(p, q; c)`. -/
lemma sum_rowCard_le_Delta {p q c : ℝ} (hp : 0 < p) (hq : 0 < q) (S : ℕ) :
    ∑ s ∈ range (S + 1), rowCard p q c s ≤ Delta p q c := by
  unfold Delta rowCard
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun sb : (s : ℕ) × ℕ => (sb.1 - sb.2, sb.2))
  · intro sb hsb
    have h1 := Finset.mem_sigma.1 (Finset.mem_coe.1 hsb)
    have h2 := Finset.mem_filter.1 h1.2
    refine Finset.mem_coe.2 ((mem_triNat_iff hp hq _).2 ?_)
    exact h2.2
  · intro sb hsb sb' hsb' heq
    have h1 := Finset.mem_filter.1 (Finset.mem_sigma.1 (Finset.mem_coe.1 hsb)).2
    have h2 := Finset.mem_filter.1 (Finset.mem_sigma.1 (Finset.mem_coe.1 hsb')).2
    have hb1 : sb.2 ≤ sb.1 := by have := Finset.mem_range.1 h1.1; omega
    have hb2 : sb'.2 ≤ sb'.1 := by have := Finset.mem_range.1 h2.1; omega
    simp only [Prod.mk.injEq] at heq
    have hs : sb.1 = sb'.1 := by omega
    exact Sigma.ext hs (heq_of_eq heq.2)

/-- Maximum height of the tent at level `S`: `cap(S) = ⌊S/2⌋ + 1`. -/
def cap (S : ℕ) : ℕ := S / 2 + 1

/-- Pairing level height `L(S)` from Lemma P. -/
def Lval (p q g : ℝ) (S : ℕ) : ℕ :=
  if p < q then min (cap S) ⌈(g - p * (S : ℝ)) / (q - p)⌉₊
  else if p * (S : ℝ) < g then cap S else 0

/-- Pairing lower bound `G(S) = T2(S + 1) - T2(S + 1 - 2 L(S))`. -/
def Gval (p q g : ℝ) (S : ℕ) : ℕ :=
  T2 ((S : ℤ) + 1) - T2 ((S : ℤ) + 1 - 2 * (Lval p q g S : ℤ))

lemma Lval_le_cap (p q g : ℝ) (S : ℕ) : Lval p q g S ≤ cap S := by
  unfold Lval
  split_ifs
  · exact min_le_left _ _
  · exact le_refl _
  · exact Nat.zero_le _

/-- Truncated tent sum identity: for `L ≤ cap S`,
`∑_{s=0}^S min(L, s + 1, S - s + 1) = T2(S + 1) - T2(S + 1 - 2 L)`. -/
theorem tent_sum (S L : ℕ) (hL : L ≤ cap S) :
    ∑ s ∈ range (S + 1), min L (min (s + 1) (S - s + 1)) =
      T2 ((S : ℤ) + 1) - T2 ((S : ℤ) + 1 - 2 * (L : ℤ)) := by
  induction L with
  | zero =>
    simp
  | succ L ih =>
    have hL' : L ≤ cap S := by omega
    have ih' := ih hL'
    have h2L : 2 * L ≤ S := by unfold cap at hL; omega
    have hstep : ∑ s ∈ range (S + 1), min (L + 1) (min (s + 1) (S - s + 1)) =
        (∑ s ∈ range (S + 1), min L (min (s + 1) (S - s + 1))) +
        ∑ s ∈ range (S + 1), (if L ≤ s ∧ s ≤ S - L then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : s ≤ S := by have := Finset.mem_range.1 hs; omega
      split_ifs with h <;> omega
    have hcount : ∑ s ∈ range (S + 1), (if L ≤ s ∧ s ≤ S - L then 1 else 0) =
        S + 1 - 2 * L := by
      rw [← Finset.card_filter]
      have hfilt : (range (S + 1)).filter (fun s => L ≤ s ∧ s ≤ S - L) =
          Finset.Icc L (S - L) := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        omega
      rw [hfilt, Nat.card_Icc]
      omega
    have hk_pos : 1 ≤ S + 1 - 2 * L := by omega
    have hT := T2_sub_two (S + 1 - 2 * L) hk_pos
    have hT_le : T2 ((S : ℤ) + 1 - 2 * (L : ℤ)) ≤ T2 ((S : ℤ) + 1) := by
      have harg1 : (0 : ℤ) ≤ (S : ℤ) + 1 - 2 * (L : ℤ) := by omega
      have harg2 : (S : ℤ) + 1 - 2 * (L : ℤ) ≤ (S : ℤ) + 1 := by omega
      unfold T2
      split_ifs with ha hb
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · omega
      · apply Nat.div_le_div_right
        apply Nat.pow_le_pow_left
        omega
    have hcast1 : ((S + 1 - 2 * L : ℕ) : ℤ) = (S : ℤ) + 1 - 2 * (L : ℤ) := by omega
    have hcast2 : (S : ℤ) + 1 - 2 * (L : ℤ) - 2 = (S : ℤ) + 1 - 2 * ((L + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [hcast1, hcast2] at hT
    rw [hstep, ih', hcount]
    omega

/-- Pointwise pairing bound for rows `s` and `S - s`. -/
lemma rowCard_pair_ge {p q α β : ℝ} (hpq : p ≤ q) {S s : ℕ} (hs : s ≤ S) :
    min (Lval p q (α + β) S) (min (s + 1) (S - s + 1)) ≤
      rowCard p q α s + rowCard p q β (S - s) := by
  have hmin_cap : min (s + 1) (S - s + 1) ≤ cap S := by unfold cap; omega
  rcases lt_or_eq_of_le hpq with hlt | heq
  · rw [rowCard_eq_pos hlt, rowCard_eq_pos hlt]
    unfold Lval
    rw [ite_eq_left hlt]
    have hd : 0 < q - p := by linarith
    let X : ℝ := (α - p * (s : ℝ)) / (q - p)
    let Y : ℝ := (β - p * ((S - s : ℕ) : ℝ)) / (q - p)
    have hXY : (α + β - p * (S : ℝ)) / (q - p) = X + Y := by
      dsimp [X, Y]
      rw [Nat.cast_sub hs]
      ring
    have hceil_add : ⌈X + Y⌉₊ ≤ ⌈X⌉₊ + ⌈Y⌉₊ := by
      apply Nat.ceil_le.2
      push_cast
      linarith [Nat.le_ceil X, Nat.le_ceil Y]
    change min (min (cap S) ⌈(α + β - p * (S : ℝ)) / (q - p)⌉₊) (min (s + 1) (S - s + 1)) ≤
      min (s + 1) ⌈X⌉₊ + min (S - s + 1) ⌈Y⌉₊
    rw [hXY]
    omega
  · rw [rowCard_eq_zero heq, rowCard_eq_zero heq]
    unfold Lval
    rw [ite_eq_right (not_lt.2 heq.ge)]
    by_cases hg : p * (S : ℝ) < α + β
    · rw [ite_eq_left hg]
      have hcast : p * (s : ℝ) + p * ((S - s : ℕ) : ℝ) = p * (S : ℝ) := by
        rw [Nat.cast_sub hs]; ring
      by_cases h1 : p * (s : ℝ) < α
      · rw [ite_eq_left h1]; omega
      · have h2 : p * ((S - s : ℕ) : ℝ) < β := by linarith
        rw [ite_eq_left h2]; omega
    · rw [ite_eq_right hg]; omega

/-- **Lemma P (`lemma_P_pairing_bound`):** For `0 < p ≤ q`, any `α, β : ℝ`, and any level `S : ℕ`,
`G(S) ≤ Δ(p, q; α) + Δ(p, q; β)`. -/
theorem lemma_P_pairing_bound {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (α β : ℝ) (S : ℕ) :
    Gval p q (α + β) S ≤ Delta p q α + Delta p q β := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have h1 := sum_rowCard_le_Delta hp hq (c := α) S
  have h2 := sum_rowCard_le_Delta hp hq (c := β) S
  have hrev : ∑ s ∈ range (S + 1), rowCard p q β (S - s) =
      ∑ s ∈ range (S + 1), rowCard p q β s := by
    apply Finset.sum_nbij' (fun s => S - s) (fun s => S - s)
    · intro s hs; simp only [Finset.mem_range] at hs ⊢; omega
    · intro s hs; simp only [Finset.mem_range] at hs ⊢; omega
    · intro s hs; simp only [Finset.mem_range] at hs; omega
    · intro s hs; simp only [Finset.mem_range] at hs; omega
    · intro s _; rfl
  have hsum : ∑ s ∈ range (S + 1), min (Lval p q (α + β) S) (min (s + 1) (S - s + 1)) ≤
      ∑ s ∈ range (S + 1), (rowCard p q α s + rowCard p q β (S - s)) := by
    apply Finset.sum_le_sum
    intro s hs
    exact rowCard_pair_ge hpq (by have := Finset.mem_range.1 hs; omega)
  rw [Finset.sum_add_distrib, hrev] at hsum
  rw [tent_sum S (Lval p q (α + β) S) (Lval_le_cap p q (α + β) S)] at hsum
  exact le_trans hsum (Nat.add_le_add h1 h2)

/-! ### Corollary P1: full levels and quadratic deficit bound -/

lemma Gval_of_full {p q g : ℝ} {S : ℕ} (hfull : Lval p q g S = cap S) :
    Gval p q g S = T2 ((S : ℤ) + 1) := by
  unfold Gval
  rw [hfull]
  have hle0 : (S : ℤ) + 1 - 2 * (cap S : ℤ) ≤ 0 := by unfold cap; omega
  have hT0 : T2 ((S : ℤ) + 1 - 2 * (cap S : ℤ)) = 0 := by unfold T2; rw [ite_eq_left hle0]
  rw [hT0, Nat.sub_zero]

/-- **Corollary P1(i) (`cor_P1_full`):** Level `S` is full (`L(S) = cap(S)`) iff
`S - [S odd] · (q - p)/(p + q) < 2g/(p + q)`. -/
theorem cor_P1_full {p q g : ℝ} (hp : 0 < p) (hpq : p ≤ q) (S : ℕ) :
    Lval p q g S = cap S ↔
      (S : ℝ) - (if Odd S then (1 : ℝ) else 0) * ((q - p) / (p + q)) < 2 * g / (p + q) := by
  have hs : 0 < p + q := by linarith
  have hpar : 2 * ((S / 2 : ℕ) : ℝ) = (S : ℝ) - if Odd S then (1 : ℝ) else 0 := by
    by_cases hodd : Odd S
    · rw [ite_eq_left hodd]
      rcases hodd with ⟨k, rfl⟩
      have hdiv : (2 * k + 1) / 2 = k := by omega
      rw [hdiv]; push_cast; ring
    · rw [ite_eq_right hodd]
      have hev : Even S := Nat.not_odd_iff_even.1 hodd
      rcases hev with ⟨k, rfl⟩
      have hdiv : (k + k) / 2 = k := by omega
      rw [hdiv]; push_cast; ring
  rcases lt_or_eq_of_le hpq with hlt | heq
  · have hd : 0 < q - p := by linarith
    unfold Lval
    rw [ite_eq_left hlt]
    have hiff : min (cap S) ⌈(g - p * (S : ℝ)) / (q - p)⌉₊ = cap S ↔
        S / 2 < ⌈(g - p * (S : ℝ)) / (q - p)⌉₊ := by
      unfold cap; omega
    rw [hiff, Nat.lt_ceil, lt_div_iff₀ hd, lt_div_iff₀ hs]
    have key : (p + q) * ((S : ℝ) - (if Odd S then (1 : ℝ) else 0) * ((q - p) / (p + q))) =
        2 * (p * (S : ℝ) + ((S / 2 : ℕ) : ℝ) * (q - p)) := by
      field_simp
      nlinarith [hpar]
    constructor <;> intro h <;> linarith
  · subst heq
    unfold Lval
    rw [ite_eq_right (lt_irrefl p)]
    have hcap_pos : cap S ≠ 0 := by unfold cap; omega
    have hiff : (if p * (S : ℝ) < g then cap S else 0) = cap S ↔ p * (S : ℝ) < g := by
      by_cases h : p * (S : ℝ) < g
      · simp [h]
      · simp [h, hcap_pos.symm]
    rw [hiff]
    have hsub : (p - p) / (p + p) = 0 := by ring
    rw [hsub, mul_zero, sub_zero, lt_div_iff₀ hs]
    constructor <;> intro h <;> linarith

lemma cor_P1_full_of_lt {p q g : ℝ} (hp : 0 < p) (hpq : p ≤ q) {S : ℕ}
    (hS : (S : ℝ) < 2 * g / (p + q)) : Lval p q g S = cap S := by
  rw [cor_P1_full hp hpq S]
  have hnn : 0 ≤ (if Odd S then (1 : ℝ) else 0) * ((q - p) / (p + q)) := by
    apply mul_nonneg
    · split_ifs <;> norm_num
    · exact div_nonneg (by linarith) (by linarith)
  linarith

lemma cor_P1_full_mono {p q g : ℝ} (hp : 0 < p) (hpq : p ≤ q) {S' S : ℕ}
    (hSS : S' ≤ S) (hfull : Lval p q g S = cap S) : Lval p q g S' = cap S' := by
  rw [cor_P1_full hp hpq] at hfull ⊢
  have hle1 : (q - p) / (p + q) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have h0 : 0 ≤ (q - p) / (p + q) := div_nonneg (by linarith) (by linarith)
  by_cases heq : S' = S
  · subst heq; exact hfull
  · have hlt : (S' : ℝ) + 1 ≤ (S : ℝ) := by exact_mod_cast (show S' + 1 ≤ S by omega)
    have hodd1 : (if Odd S' then (1 : ℝ) else 0) ≥ 0 := by split_ifs <;> norm_num
    have hodd2 : (if Odd S then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    nlinarith

/-- **Corollary P1(ii) (`cor_P1_not_full`):** If `0 < p < q` and level `S` is not full,
with `f = ⌊((p+q)/(q-p) · (S - 2g/(p+q)) - [S odd]) / 2⌋₊ + 1`, then `f ≥ 1` and
`G(S) ≥ T2(S + 1) - f (f + [S odd])`. -/
theorem cor_P1_not_full {p q g : ℝ} (hp : 0 < p) (hpq : p < q) (S : ℕ)
    (hnf : Lval p q g S < cap S) :
    let z := ((p + q) / (q - p)) * ((S : ℝ) - 2 * g / (p + q))
    let f := ⌊(z - if Odd S then (1 : ℝ) else 0) / 2⌋₊ + 1
    1 ≤ f ∧
      (T2 ((S : ℤ) + 1) : ℤ) - (f : ℤ) * ((f : ℤ) + if Odd S then 1 else 0) ≤
        (Gval p q g S : ℤ) := by
  intro z f
  refine ⟨by omega, ?_⟩
  have hd : 0 < q - p := by linarith
  have hs : 0 < p + q := by linarith
  have hnotfull : ¬(Lval p q g S = cap S) := ne_of_lt hnf
  have hge := not_lt.1 ((cor_P1_full hp hpq.le S).not.1 hnotfull)
  have hpar : 2 * ((S / 2 : ℕ) : ℝ) = (S : ℝ) - if Odd S then (1 : ℝ) else 0 := by
    by_cases hodd : Odd S
    · rw [ite_eq_left hodd]; rcases hodd with ⟨k, rfl⟩
      rw [show (2 * k + 1) / 2 = k by omega]; push_cast; ring
    · rw [ite_eq_right hodd]; rcases Nat.not_odd_iff_even.1 hodd with ⟨k, rfl⟩
      rw [show (k + k) / 2 = k by omega]; push_cast; ring
  let Xi : ℝ := (g - p * (S : ℝ)) / (q - p)
  have hXi_rel : ((S / 2 : ℕ) : ℝ) - Xi = (z - if Odd S then (1 : ℝ) else 0) / 2 := by
    dsimp [Xi, z]
    field_simp
    nlinarith [hpar]
  have hnonneg : 0 ≤ (z - if Odd S then (1 : ℝ) else 0) / 2 := by
    dsimp [z]
    have hmul : (p + q) * ((S : ℝ) - 2 * g / (p + q)) ≥
        (if Odd S then (1 : ℝ) else 0) * (q - p) := by
      have := mul_le_mul_of_nonneg_left hge hs.le
      field_simp at this ⊢
      linarith
    have hdiv : (p + q) / (q - p) * ((S : ℝ) - 2 * g / (p + q)) ≥
        if Odd S then (1 : ℝ) else 0 := by
      have hrw : (p + q) / (q - p) * ((S : ℝ) - 2 * g / (p + q)) =
          (p + q) * ((S : ℝ) - 2 * g / (p + q)) / (q - p) := by ring
      rw [ge_iff_le, hrw, le_div_iff₀ hd]
      exact hmul
    linarith
  have hLval : Lval p q g S = ⌈Xi⌉₊ := by
    unfold Lval at hnf ⊢
    rw [ite_eq_left hpq] at hnf ⊢
    exact min_eq_right (by omega)
  have hfloor_lo : ((f - 1 : ℕ) : ℝ) ≤ ((S / 2 : ℕ) : ℝ) - Xi := by
    rw [hXi_rel]
    have : f - 1 = ⌊(z - if Odd S then (1 : ℝ) else 0) / 2⌋₊ := by omega
    rw [this]
    exact Nat.floor_le hnonneg
  have hfloor_hi : ((S / 2 : ℕ) : ℝ) - Xi < (f : ℝ) := by
    rw [hXi_rel]
    dsimp [f]
    push_cast
    exact Nat.lt_floor_add_one _
  by_cases hXi_pos : 0 < Xi
  · have hceil_pos : 1 ≤ ⌈Xi⌉₊ := Nat.ceil_pos.2 hXi_pos
    have hceil_lt : (⌈Xi⌉₊ : ℝ) < Xi + 1 := Nat.ceil_lt_add_one hXi_pos.le
    have hceil_ge : Xi ≤ (⌈Xi⌉₊ : ℝ) := Nat.le_ceil Xi
    have hf_eq : ⌈Xi⌉₊ + f = cap S := by
      have hfl : (f : ℝ) - 1 ≤ ((S / 2 : ℕ) : ℝ) - Xi := by
        have : ((f - 1 : ℕ) : ℝ) = (f : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ f)]; simp
        linarith
      have h1 : ((⌈Xi⌉₊ + f : ℕ) : ℝ) < ((S / 2 : ℕ) : ℝ) + 2 := by push_cast; linarith
      have h2 : ((S / 2 : ℕ) : ℝ) < ((⌈Xi⌉₊ + f : ℕ) : ℝ) := by push_cast; linarith
      have h1' : ⌈Xi⌉₊ + f < S / 2 + 2 := by exact_mod_cast h1
      have h2' : S / 2 < ⌈Xi⌉₊ + f := by exact_mod_cast h2
      unfold cap; omega
    have harg : (S : ℤ) + 1 - 2 * (Lval p q g S : ℤ) =
        2 * (f : ℤ) - 1 + if Odd S then 1 else 0 := by
      rw [hLval]
      have hS_par : (S : ℤ) = 2 * (S / 2 : ℤ) + if Odd S then 1 else 0 := by
        by_cases hodd : Odd S
        · rw [ite_eq_left hodd]; rcases hodd with ⟨k, rfl⟩; omega
        · rw [ite_eq_right hodd]; rcases Nat.not_odd_iff_even.1 hodd with ⟨k, rfl⟩; omega
      unfold cap at hf_eq
      omega
    have hT2_rem : (T2 ((S : ℤ) + 1 - 2 * (Lval p q g S : ℤ)) : ℤ) =
        (f : ℤ) * ((f : ℤ) + if Odd S then 1 else 0) := by
      rw [harg]
      have h4 := four_mul_T2 (2 * (f : ℤ) - 1 + if Odd S then 1 else 0) (by split_ifs <;> omega)
      by_cases hodd : Odd S
      · rw [ite_eq_left hodd] at h4 ⊢
        have hev : Even (2 * (f : ℤ) - 1 + 1) := ⟨(f : ℤ), by ring⟩
        rw [ite_eq_left hev] at h4
        linarith
      · rw [ite_eq_right hodd] at h4 ⊢
        have hne : ¬Even (2 * (f : ℤ) - 1 + 0) := by rintro ⟨r, hr⟩; omega
        rw [ite_eq_right hne] at h4
        linarith
    have hle_T : T2 ((S : ℤ) + 1 - 2 * (Lval p q g S : ℤ)) ≤ T2 ((S : ℤ) + 1) := by
      have : (S : ℤ) + 1 - 2 * (Lval p q g S : ℤ) ≤ (S : ℤ) + 1 := by omega
      unfold T2
      split_ifs with ha hb
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · omega
      · apply Nat.div_le_div_right; apply Nat.pow_le_pow_left; omega
    unfold Gval
    omega
  · push Not at hXi_pos
    have hceil0 : ⌈Xi⌉₊ = 0 := Nat.ceil_eq_zero.2 hXi_pos
    have hcap_le_f : cap S ≤ f := by
      have h1 : ((S / 2 : ℕ) : ℝ) < (f : ℝ) := by linarith
      have h1' : S / 2 < f := by exact_mod_cast h1
      unfold cap; omega
    have hT_eq : (T2 ((S : ℤ) + 1) : ℤ) = (cap S : ℤ) * ((cap S : ℤ) + if Odd S then 1 else 0) := by
      have h4 := four_mul_T2 ((S : ℤ) + 1) (by omega)
      by_cases hodd : Odd S
      · rw [ite_eq_left hodd]
        rcases hodd with ⟨k, rfl⟩
        have hev : Even (((2 * k + 1 : ℕ) : ℤ) + 1) := ⟨(k : ℤ) + 1, by push_cast; ring⟩
        rw [ite_eq_left hev] at h4
        have hc : (cap (2 * k + 1) : ℤ) = (k : ℤ) + 1 := by unfold cap; omega
        rw [hc]; push_cast at h4 ⊢; linarith
      · rw [ite_eq_right hodd]
        rcases Nat.not_odd_iff_even.1 hodd with ⟨k, rfl⟩
        have hne : ¬Even (((k + k : ℕ) : ℤ) + 1) := by rintro ⟨r, hr⟩; push_cast at hr; omega
        rw [ite_eq_right hne] at h4
        have hc : (cap (k + k) : ℤ) = (k : ℤ) + 1 := by unfold cap; omega
        rw [hc]; push_cast at h4 ⊢; linarith
    have hprod : (cap S : ℤ) * ((cap S : ℤ) + if Odd S then 1 else 0) ≤
        (f : ℤ) * ((f : ℤ) + if Odd S then 1 else 0) := by
      have hc' : (cap S : ℤ) ≤ (f : ℤ) := by exact_mod_cast hcap_le_f
      split_ifs <;> nlinarith
    have hG0 : (0 : ℤ) ≤ (Gval p q g S : ℤ) := Nat.cast_nonneg _
    linarith

/-- Uniform quadratic lower bound from Corollary P1 (used in Theorem A Step 0):
for `0 < p < q` and any `S : ℕ` with `2g/(p+q) ≤ S`,
`G(S) ≥ T2(S + 1) - (z + 2)² / 4`, where `z = ((p+q)/(q-p)) (S - 2g/(p+q))`. -/
theorem cor_P1_quad_bound {p q g : ℝ} (hp : 0 < p) (hpq : p < q) (S : ℕ) :
    let z := ((p + q) / (q - p)) * ((S : ℝ) - 2 * g / (p + q))
    (T2 ((S : ℤ) + 1) : ℝ) - (z + 2) ^ 2 / 4 ≤ (Gval p q g S : ℝ) := by
  intro z
  rcases lt_or_eq_of_le (Lval_le_cap p q g S) with hlt | heq
  · have hP1 := cor_P1_not_full hp hpq S hlt
    have h2 : (T2 ((S : ℤ) + 1) : ℝ) -
        ((⌊(z - if Odd S then (1 : ℝ) else 0) / 2⌋₊ + 1 : ℕ) : ℝ) *
        (((⌊(z - if Odd S then (1 : ℝ) else 0) / 2⌋₊ + 1 : ℕ) : ℝ) +
          if Odd S then (1 : ℝ) else 0) ≤ (Gval p q g S : ℝ) := by
      have hcast := hP1.2
      by_cases hodd : Odd S
      · simp only [hodd, ↓reduceIte] at hcast ⊢
        exact_mod_cast hcast
      · simp only [hodd, ↓reduceIte] at hcast ⊢
        exact_mod_cast hcast
    have hd : 0 < q - p := by linarith
    have hs : 0 < p + q := by linarith
    have hge := not_lt.1 ((cor_P1_full hp hpq.le S).not.1 (ne_of_lt hlt))
    have hz_ge : (if Odd S then (1 : ℝ) else 0) ≤ z := by
      dsimp [z]
      have hmul : (p + q) * ((S : ℝ) - 2 * g / (p + q)) ≥
          (if Odd S then (1 : ℝ) else 0) * (q - p) := by
        have := mul_le_mul_of_nonneg_left hge hs.le
        field_simp at this ⊢; linarith
      have : (p + q) / (q - p) * ((S : ℝ) - 2 * g / (p + q)) * (q - p) =
          (p + q) * ((S : ℝ) - 2 * g / (p + q)) := by field_simp
      nlinarith
    have hfl : (⌊(z - if Odd S then (1 : ℝ) else 0) / 2⌋₊ : ℝ) ≤
        (z - if Odd S then (1 : ℝ) else 0) / 2 :=
      Nat.floor_le (by linarith)
    have hf_nn : (0 : ℝ) ≤ ((⌊(z - if Odd S then (1 : ℝ) else 0) / 2⌋₊ + 1 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    by_cases hodd : Odd S
    · rw [ite_eq_left hodd] at h2 hfl hz_ge
      have hfb : ((⌊(z - 1) / 2⌋₊ + 1 : ℕ) : ℝ) ≤ (z + 1) / 2 := by push_cast; linarith
      have hsq : ((⌊(z - 1) / 2⌋₊ + 1 : ℕ) : ℝ) * (((⌊(z - 1) / 2⌋₊ + 1 : ℕ) : ℝ) + 1) ≤
          (z + 2) ^ 2 / 4 := by
        nlinarith
      linarith
    · rw [ite_eq_right hodd] at h2 hfl hz_ge
      have hfb : ((⌊(z - 0) / 2⌋₊ + 1 : ℕ) : ℝ) ≤ (z + 2) / 2 := by push_cast; linarith
      have hsq : ((⌊(z - 0) / 2⌋₊ + 1 : ℕ) : ℝ) * (((⌊(z - 0) / 2⌋₊ + 1 : ℕ) : ℝ) + 0) ≤
          (z + 2) ^ 2 / 4 := by
        nlinarith
      linarith
  · rw [Gval_of_full heq]
    have : 0 ≤ (z + 2) ^ 2 / 4 := by positivity
    linarith

/-! ### Pair quantities `γ_k`, `G_k`, `B_k` and sum bound -/

/-- Combined thresholds `γ_k = α_k + β_k = 2 h s_k - n` (independent of `t`). -/
def gamma1 (n : ℕ) (u w : ℝ) : ℝ := 2 * ((n - 1 : ℕ) : ℝ) * s1 u w - (n : ℝ)
def gamma2 (n : ℕ) (u w : ℝ) : ℝ := 2 * ((n - 1 : ℕ) : ℝ) * s2 u w - (n : ℝ)
def gamma3 (n : ℕ) (u w : ℝ) : ℝ := 2 * ((n - 1 : ℕ) : ℝ) * s3 u w - (n : ℝ)

lemma alpha_add_beta1 (n : ℕ) (hn : 1 ≤ n) (u w t : ℝ) :
    alpha1 n u w t + beta1 n u w t = gamma1 n u w := by
  unfold alpha1 beta1 gamma1 s1
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [hcast]; ring

lemma alpha_add_beta2 (n : ℕ) (hn : 1 ≤ n) (u w t : ℝ) :
    alpha2 n u w t + beta2 n u w t = gamma2 n u w := by
  unfold alpha2 beta2 gamma2 s2
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [hcast]; ring

lemma alpha_add_beta3 (n : ℕ) (hn : 1 ≤ n) (u w t : ℝ) :
    alpha3 n u w t + beta3 n u w t = gamma3 n u w := by
  unfold alpha3 beta3 gamma3 s3
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [hcast]; ring

/-- Level pairing bounds `G_k(S)` for pairs 1, 2, 3. -/
def G1 (n : ℕ) (u w : ℝ) (S : ℕ) : ℕ := Gval (x2 u w) (x3 u w) (gamma1 n u w) S
def G2 (n : ℕ) (u w : ℝ) (S : ℕ) : ℕ := Gval (x1 u w) (x3 u w) (gamma2 n u w) S
def G3 (n : ℕ) (u w : ℝ) (S : ℕ) : ℕ := Gval (x1 u w) (x2 u w) (gamma3 n u w) S

/-- Supremum pairing bounds `B_k(u, w) = sup_S G_k(S)` for pairs 1, 2, 3. -/
def B1 (n : ℕ) (u w : ℝ) : ℕ := sSup {m : ℕ | ∃ S : ℕ, G1 n u w S = m}
def B2 (n : ℕ) (u w : ℝ) : ℕ := sSup {m : ℕ | ∃ S : ℕ, G2 n u w S = m}
def B3 (n : ℕ) (u w : ℝ) : ℕ := sSup {m : ℕ | ∃ S : ℕ, G3 n u w S = m}

lemma x_ordered {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    x1 u w ≤ x2 u w ∧ x2 u w ≤ x3 u w := by
  unfold x1 x2 x3; constructor <;> linarith

lemma G1_le_pair {n : ℕ} (hn : 1 ≤ n) {u w t : ℝ} (hx1 : 0 < x1 u w) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (S : ℕ) :
    G1 n u w S ≤ Delta (x2 u w) (x3 u w) (alpha1 n u w t) +
      Delta (x2 u w) (x3 u w) (beta1 n u w t) := by
  have ⟨h12, h23⟩ := x_ordered hu hw
  unfold G1
  rw [← alpha_add_beta1 n hn u w t]
  exact lemma_P_pairing_bound (lt_of_lt_of_le hx1 h12) h23 _ _ S

lemma G2_le_pair {n : ℕ} (hn : 1 ≤ n) {u w t : ℝ} (hx1 : 0 < x1 u w) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (S : ℕ) :
    G2 n u w S ≤ Delta (x1 u w) (x3 u w) (alpha2 n u w t) +
      Delta (x1 u w) (x3 u w) (beta2 n u w t) := by
  have ⟨h12, h23⟩ := x_ordered hu hw
  unfold G2
  rw [← alpha_add_beta2 n hn u w t]
  exact lemma_P_pairing_bound hx1 (le_trans h12 h23) _ _ S

lemma G3_le_pair {n : ℕ} (hn : 1 ≤ n) {u w t : ℝ} (hx1 : 0 < x1 u w) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (S : ℕ) :
    G3 n u w S ≤ Delta (x1 u w) (x2 u w) (alpha3 n u w t) +
      Delta (x1 u w) (x2 u w) (beta3 n u w t) := by
  have ⟨h12, _⟩ := x_ordered hu hw
  unfold G3
  rw [← alpha_add_beta3 n hn u w t]
  exact lemma_P_pairing_bound hx1 h12 _ _ S

lemma G1_le_B1 {n : ℕ} (hn : 1 ≤ n) {u w : ℝ} (hx1 : 0 < x1 u w) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (S : ℕ) : G1 n u w S ≤ B1 n u w := by
  apply le_csSup
  · refine ⟨Delta (x2 u w) (x3 u w) (alpha1 n u w 0) +
      Delta (x2 u w) (x3 u w) (beta1 n u w 0), ?_⟩
    rintro m ⟨S', rfl⟩
    exact G1_le_pair hn hx1 hu hw S'
  · exact ⟨S, rfl⟩

lemma G2_le_B2 {n : ℕ} (hn : 1 ≤ n) {u w : ℝ} (hx1 : 0 < x1 u w) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (S : ℕ) : G2 n u w S ≤ B2 n u w := by
  apply le_csSup
  · refine ⟨Delta (x1 u w) (x3 u w) (alpha2 n u w 0) +
      Delta (x1 u w) (x3 u w) (beta2 n u w 0), ?_⟩
    rintro m ⟨S', rfl⟩
    exact G2_le_pair hn hx1 hu hw S'
  · exact ⟨S, rfl⟩

lemma G3_le_B3 {n : ℕ} (hn : 1 ≤ n) {u w : ℝ} (hx1 : 0 < x1 u w) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (S : ℕ) : G3 n u w S ≤ B3 n u w := by
  apply le_csSup
  · refine ⟨Delta (x1 u w) (x2 u w) (alpha3 n u w 0) +
      Delta (x1 u w) (x2 u w) (beta3 n u w 0), ?_⟩
    rintro m ⟨S', rfl⟩
    exact G3_le_pair hn hx1 hu hw S'
  · exact ⟨S, rfl⟩

/-- **Lemma P sum bound (`lemma_P_sum_B`):** For any `(u, w)` with `0 < x₁(u, w)` and `u, w ≥ 0`,
and EVERY real shift `t : ℝ`, `B₁(u, w) + B₂(u, w) + B₃(u, w) ≤ missedCount n u w t`. -/
theorem lemma_P_sum_B {n : ℕ} (hn : 1 ≤ n) {u w : ℝ} (hx1 : 0 < x1 u w) (hu : 0 ≤ u)
    (hw : 0 ≤ w) (t : ℝ) :
    B1 n u w + B2 n u w + B3 n u w ≤ missedCount n u w t := by
  have h1 : B1 n u w ≤ Delta (x2 u w) (x3 u w) (alpha1 n u w t) +
      Delta (x2 u w) (x3 u w) (beta1 n u w t) := by
    apply csSup_le
    · exact ⟨G1 n u w 0, 0, rfl⟩
    · rintro m ⟨S, rfl⟩; exact G1_le_pair hn hx1 hu hw S
  have h2 : B2 n u w ≤ Delta (x1 u w) (x3 u w) (alpha2 n u w t) +
      Delta (x1 u w) (x3 u w) (beta2 n u w t) := by
    apply csSup_le
    · exact ⟨G2 n u w 0, 0, rfl⟩
    · rintro m ⟨S, rfl⟩; exact G2_le_pair hn hx1 hu hw S
  have h3 : B3 n u w ≤ Delta (x1 u w) (x2 u w) (alpha3 n u w t) +
      Delta (x1 u w) (x2 u w) (beta3 n u w t) := by
    apply csSup_le
    · exact ⟨G3 n u w 0, 0, rfl⟩
    · rintro m ⟨S, rfl⟩; exact G3_le_pair hn hx1 hu hw S
  unfold missedCount
  omega

/-! ### Lemma C (even-`n` coupling lemma on region `K`) -/

/-- The open coupling region `K` for even `n = 2c + 4 ≥ 6`:
`(3c + 8) u - (3c + 5) w < 1` and `(3c + 5) u + (6c + 13) w < 1`. -/
def inK (c : ℕ) (u w : ℝ) : Prop :=
  (3 * (c : ℝ) + 8) * u - (3 * (c : ℝ) + 5) * w < 1 ∧
    (3 * (c : ℝ) + 5) * u + (6 * (c : ℝ) + 13) * w < 1

/-- Helper: adding a strict bonus `+ k` at a single row index `s0 ≤ S` of the pairing sum. -/
private lemma pair_sum_with_bonus {p q α β : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    {S s0 bonus : ℕ} (hs0 : s0 ≤ S)
    (hbonus : min (Lval p q (α + β) S) (min (s0 + 1) (S - s0 + 1)) + bonus ≤
      rowCard p q α s0 + rowCard p q β (S - s0)) :
    Gval p q (α + β) S + bonus ≤ Delta p q α + Delta p q β := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have h1 := sum_rowCard_le_Delta hp hq (c := α) S
  have h2 := sum_rowCard_le_Delta hp hq (c := β) S
  have hrev : ∑ s ∈ range (S + 1), rowCard p q β (S - s) =
      ∑ s ∈ range (S + 1), rowCard p q β s := by
    apply Finset.sum_nbij' (fun s => S - s) (fun s => S - s)
    · intro s hs; simp only [Finset.mem_range] at hs ⊢; omega
    · intro s hs; simp only [Finset.mem_range] at hs ⊢; omega
    · intro s hs; simp only [Finset.mem_range] at hs; omega
    · intro s hs; simp only [Finset.mem_range] at hs; omega
    · intro _ _; rfl
  have hs0_mem : s0 ∈ range (S + 1) := Finset.mem_range.2 (by omega)
  have hsum : (∑ s ∈ range (S + 1), min (Lval p q (α + β) S) (min (s + 1) (S - s + 1))) + bonus ≤
      ∑ s ∈ range (S + 1), (rowCard p q α s + rowCard p q β (S - s)) := by
    have hsplit1 := Finset.add_sum_erase (range (S + 1))
      (fun s => min (Lval p q (α + β) S) (min (s + 1) (S - s + 1))) hs0_mem
    have hsplit2 := Finset.add_sum_erase (range (S + 1))
      (fun s => rowCard p q α s + rowCard p q β (S - s)) hs0_mem
    have hrest : ∑ s ∈ (range (S + 1)).erase s0,
        min (Lval p q (α + β) S) (min (s + 1) (S - s + 1)) ≤
        ∑ s ∈ (range (S + 1)).erase s0, (rowCard p q α s + rowCard p q β (S - s)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsr : s ∈ range (S + 1) := Finset.mem_of_mem_erase hs
      exact rowCard_pair_ge hpq (by have := Finset.mem_range.1 hsr; omega)
    omega
  rw [Finset.sum_add_distrib, hrev] at hsum
  rw [tent_sum S (Lval p q (α + β) S) (Lval_le_cap p q (α + β) S)] at hsum
  exact le_trans hsum (Nat.add_le_add h1 h2)

/-- **Lemma C (`lemma_C_coupling`):** For every even `n = 2c + 4 ≥ 6` (`c ≥ 1`), every
`(u, w) ≠ (0, 0)` with `u ≥ 0, w ≥ 0` in `K(c)`, and EVERY real shift `t : ℝ`,
`missedCount (2c + 4) u w t ≥ D(2c + 4)`. -/
theorem lemma_C_coupling (c : ℕ) (hc : 1 ≤ c) (u w t : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hne : (u, w) ≠ (0, 0)) (hK : inK c u w) :
    D (2 * c + 4) ≤ missedCount (2 * c + 4) u w t := by
  have hc_r : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have huw_pos : 0 < u + w := by
    by_contra hle
    push Not at hle
    have hu0 : u = 0 := by linarith
    have hw0 : w = 0 := by linarith
    exact hne (Prod.ext hu0 hw0)
  have hx1_pos : 0 < x1 u w := by
    unfold x1
    have h2 : (3 * (c : ℝ) + 5) * u + (6 * (c : ℝ) + 13) * w < 1 := hK.2
    nlinarith
  have ⟨hx12, hx23⟩ := x_ordered hu hw
  have hx2_pos : 0 < x2 u w := lt_of_lt_of_le hx1_pos hx12
  have hx3_pos : 0 < x3 u w := lt_of_lt_of_le hx2_pos hx23
  -- Target D(2c + 4) = (c + 1)^2 + 2 c (c + 1) + 1
  have hD_val : D (2 * c + 4) = (c + 1) ^ 2 + 2 * (c * (c + 1)) + 1 := by
    have hev : Even (2 * c + 4) := ⟨c + 2, by ring⟩
    rw [D_eq_Tstar (2 * c + 4) (by omega), ite_eq_left hev]
    unfold Tstar
    have hT1 : T2 (((2 * c + 4 : ℕ) : ℤ) - 3) = (c + 1) ^ 2 := by
      have heq : ((2 * c + 4 : ℕ) : ℤ) - 3 = ((2 * c + 1 : ℕ) : ℤ) := by push_cast; omega
      rw [heq, T2_nat]
      have : (2 * c + 1 + 1) ^ 2 = 4 * (c + 1) ^ 2 := by ring
      rw [this]; omega
    have hT2 : T2 (((2 * c + 4 : ℕ) : ℤ) - 4) = c * (c + 1) := by
      have heq : ((2 * c + 4 : ℕ) : ℤ) - 4 = ((2 * c : ℕ) : ℤ) := by push_cast; omega
      rw [heq, T2_nat]
      have : (2 * c + 1) ^ 2 = 4 * (c * (c + 1)) + 1 := by ring
      rw [this]; omega
    rw [hT1, hT2]
  have hT2_2c1 : T2 (((2 * c : ℕ) : ℤ) + 1) = (c + 1) ^ 2 := by
    have heq : ((2 * c : ℕ) : ℤ) + 1 = ((2 * c + 1 : ℕ) : ℤ) := by push_cast; omega
    rw [heq, T2_nat]
    have : (2 * c + 1 + 1) ^ 2 = 4 * (c + 1) ^ 2 := by ring
    rw [this]; omega
  have hT2_2c : T2 (((2 * c - 1 : ℕ) : ℤ) + 1) = c * (c + 1) := by
    have heq : ((2 * c - 1 : ℕ) : ℤ) + 1 = ((2 * c : ℕ) : ℤ) := by omega
    rw [heq, T2_nat]
    have : (2 * c + 1) ^ 2 = 4 * (c * (c + 1)) + 1 := by ring
    rw [this]; omega
  -- Explicit formulas for gamma_k in terms of c, u, w
  have hg1 : gamma1 (2 * c + 4) u w =
      (2 * (c : ℝ) + (4 * (c : ℝ) + 6) * (2 * u + w)) / 3 := by
    unfold gamma1 s1 x1
    have : ((2 * c + 4 - 1 : ℕ) : ℝ) = 2 * (c : ℝ) + 3 := by
      rw [show 2 * c + 4 - 1 = 2 * c + 3 by omega]; push_cast; ring
    rw [this]; push_cast; ring
  have hg2 : gamma2 (2 * c + 4) u w =
      (2 * (c : ℝ) + (4 * (c : ℝ) + 6) * (w - u)) / 3 := by
    unfold gamma2 s2 x2
    have : ((2 * c + 4 - 1 : ℕ) : ℝ) = 2 * (c : ℝ) + 3 := by
      rw [show 2 * c + 4 - 1 = 2 * c + 3 by omega]; push_cast; ring
    rw [this]; push_cast; ring
  have hg3 : gamma3 (2 * c + 4) u w =
      (2 * (c : ℝ) - (4 * (c : ℝ) + 6) * (u + 2 * w)) / 3 := by
    unfold gamma3 s3 x3
    have : ((2 * c + 4 - 1 : ℕ) : ℝ) = 2 * (c : ℝ) + 3 := by
      rw [show 2 * c + 4 - 1 = 2 * c + 3 by omega]; push_cast; ring
    rw [this]; push_cast; ring
  -- (a) Pair 3 is full at level 2c - 1
  have hfull3 : Lval (x1 u w) (x2 u w) (gamma3 (2 * c + 4) u w) (2 * c - 1) = cap (2 * c - 1) := by
    rw [cor_P1_full hx1_pos hx12]
    have hodd : Odd (2 * c - 1) := ⟨c - 1, by omega⟩
    rw [ite_eq_left hodd, one_mul]
    have hs3 : x1 u w + x2 u w = (2 - u - 2 * w) / 3 := by unfold x1 x2; ring
    have hd3 : x2 u w - x1 u w = u := by unfold x1 x2; ring
    have hs3_pos : 0 < x1 u w + x2 u w := by linarith
    have hc_sub : ((2 * c - 1 : ℕ) : ℝ) = 2 * (c : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * c)]; push_cast; ring
    rw [lt_div_iff₀ hs3_pos]
    have hmul : (((2 * c - 1 : ℕ) : ℝ) - (x2 u w - x1 u w) / (x1 u w + x2 u w)) *
        (x1 u w + x2 u w) = (2 * (c : ℝ) - 1) * ((2 - u - 2 * w) / 3) - u := by
      rw [hc_sub, sub_mul, div_mul_cancel₀ _ (ne_of_gt hs3_pos), hs3, hd3]
    rw [hmul, hg3]
    linarith [hK.2]
  have hC3 : c * (c + 1) ≤ Delta (x1 u w) (x2 u w) (alpha3 (2 * c + 4) u w t) +
      Delta (x1 u w) (x2 u w) (beta3 (2 * c + 4) u w t) := by
    have hG3 := G3_le_pair (n := 2 * c + 4) (by omega) (t := t) hx1_pos hu hw (2 * c - 1)
    unfold G3 at hG3
    rw [Gval_of_full hfull3, hT2_2c] at hG3
    exact hG3
  -- (b) Pair 2 satisfies Xi_2(2c - 1) > c, hence full at level 2c - 1
  have hXi2 : (c : ℝ) < (gamma2 (2 * c + 4) u w - x1 u w * ((2 * c - 1 : ℕ) : ℝ)) /
      (x3 u w - x1 u w) := by
    have hd2 : x3 u w - x1 u w = u + w := by unfold x1 x3; ring
    have hc_sub : ((2 * c - 1 : ℕ) : ℝ) = 2 * (c : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * c)]; push_cast; ring
    rw [hd2, lt_div_iff₀ huw_pos, hc_sub, hg2]
    unfold x1
    linarith [hK.1]
  have hfull2 : Lval (x1 u w) (x3 u w) (gamma2 (2 * c + 4) u w) (2 * c - 1) = cap (2 * c - 1) := by
    have hlt13 : x1 u w < x3 u w := by unfold x1 x3; linarith
    unfold Lval
    rw [ite_eq_left hlt13]
    have hcap2 : cap (2 * c - 1) = c := by unfold cap; omega
    rw [hcap2]
    have hceil : c < ⌈(gamma2 (2 * c + 4) u w - x1 u w * ((2 * c - 1 : ℕ) : ℝ)) /
        (x3 u w - x1 u w)⌉₊ := Nat.lt_ceil.2 hXi2
    omega
  have hC2 : c * (c + 1) ≤ Delta (x1 u w) (x3 u w) (alpha2 (2 * c + 4) u w t) +
      Delta (x1 u w) (x3 u w) (beta2 (2 * c + 4) u w t) := by
    have hG2 := G2_le_pair (n := 2 * c + 4) (by omega) (t := t) hx1_pos hu hw (2 * c - 1)
    unfold G2 at hG2
    rw [Gval_of_full hfull2, hT2_2c] at hG2
    exact hG2
  -- (c) Pair 1 is full at level 2c
  have hfull1 : Lval (x2 u w) (x3 u w) (gamma1 (2 * c + 4) u w) (2 * c) = cap (2 * c) := by
    apply cor_P1_full_of_lt hx2_pos hx23
    have hs1 : x2 u w + x3 u w = (2 + 2 * u + w) / 3 := by unfold x2 x3; ring
    have hs1_pos : 0 < x2 u w + x3 u w := by linarith
    rw [lt_div_iff₀ hs1_pos, hs1, hg1]
    push_cast
    nlinarith
  have hC1 : (c + 1) ^ 2 ≤ Delta (x2 u w) (x3 u w) (alpha1 (2 * c + 4) u w t) +
      Delta (x2 u w) (x3 u w) (beta1 (2 * c + 4) u w t) := by
    have hG1 := G1_le_pair (n := 2 * c + 4) (by omega) (t := t) hx1_pos hu hw (2 * c)
    unfold G1 at hG1
    rw [Gval_of_full hfull1, hT2_2c1] at hG1
    exact hG1
  -- (d), (e), (f): theta = t - (c + 2), tau_1 = (c + 2) u + w, tau_2 = u - (c + 1) w
  let theta : ℝ := t - ((c : ℝ) + 2)
  let tau1 : ℝ := ((c : ℝ) + 2) * u + w
  let tau2 : ℝ := u - ((c : ℝ) + 1) * w
  have ha1_th : alpha1 (2 * c + 4) u w t = gamma1 (2 * c + 4) u w / 2 - theta := by
    unfold alpha1 gamma1; dsimp [theta]; push_cast; ring
  have hb1_th : beta1 (2 * c + 4) u w t = gamma1 (2 * c + 4) u w / 2 + theta := by
    unfold beta1 gamma1 s1; dsimp [theta]; push_cast; ring
  have ha2_th : alpha2 (2 * c + 4) u w t = gamma2 (2 * c + 4) u w / 2 - theta := by
    unfold alpha2 gamma2; dsimp [theta]; push_cast; ring
  have hb2_th : beta2 (2 * c + 4) u w t = gamma2 (2 * c + 4) u w / 2 + theta := by
    unfold beta2 gamma2 s2; dsimp [theta]; push_cast; ring
  have htau1_eq : gamma1 (2 * c + 4) u w / 2 - (c : ℝ) * x3 u w = tau1 := by
    rw [hg1]; unfold x3; dsimp [tau1]; ring
  have htau2_eq : (c : ℝ) * x1 u w - gamma2 (2 * c + 4) u w / 2 = tau2 := by
    rw [hg2]; unfold x1; dsimp [tau2]; ring
  have htau_diff : tau2 < tau1 := by
    dsimp [tau1, tau2]; nlinarith
  -- Split into |theta| < tau1 vs theta > tau2 vs theta < -tau2
  by_cases hcase1 : |theta| < tau1
  · -- Case (d): both row c of alpha1 and row c of beta1 are complete (2(c+1) points)
    have hth_lo : -tau1 < theta := (abs_lt.1 hcase1).1
    have hth_hi : theta < tau1 := (abs_lt.1 hcase1).2
    have ha1_gt : (c : ℝ) * x3 u w < alpha1 (2 * c + 4) u w t := by linarith
    have hb1_gt : (c : ℝ) * x3 u w < beta1 (2 * c + 4) u w t := by linarith
    have hrow_full : ∀ val : ℝ, (c : ℝ) * x3 u w < val →
        rowCard (x2 u w) (x3 u w) val c = c + 1 := by
      intro val hval
      unfold rowCard rowSet
      have hset : (range (c + 1)).filter
          (fun b => x2 u w * ((c - b : ℕ) : ℝ) + x3 u w * (b : ℝ) < val) = range (c + 1) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
        intro hb
        have hbc : b ≤ c := by omega
        rw [Nat.cast_sub hbc]
        nlinarith [show (0 : ℝ) ≤ (c : ℝ) - (b : ℝ) by exact_mod_cast (show 0 ≤ c - b by omega)]
      rw [hset, Finset.card_range]
    have hbonus : Gval (x2 u w) (x3 u w) (alpha1 (2 * c + 4) u w t + beta1 (2 * c + 4) u w t)
          (2 * c) + 1 ≤
        Delta (x2 u w) (x3 u w) (alpha1 (2 * c + 4) u w t) +
        Delta (x2 u w) (x3 u w) (beta1 (2 * c + 4) u w t) := by
      apply pair_sum_with_bonus hx2_pos hx23 (s0 := c) (by omega)
      have hr1 := hrow_full (alpha1 (2 * c + 4) u w t) ha1_gt
      have hr2 := hrow_full (beta1 (2 * c + 4) u w t) hb1_gt
      have hsub : 2 * c - c = c := by omega
      rw [hsub, hr1, hr2]
      omega
    rw [alpha_add_beta1 (2 * c + 4) (by omega), Gval_of_full hfull1, hT2_2c1] at hbonus
    unfold missedCount
    rw [hD_val]
    omega
  · -- Case (e): either theta > tau2 or theta < -tau2
    push Not at hcase1
    have hlt13 : x1 u w < x3 u w := by unfold x1 x3; linarith
    have hd2 : x3 u w - x1 u w = u + w := by unfold x1 x3; ring
    have hsum_ab2 : alpha2 (2 * c + 4) u w t + beta2 (2 * c + 4) u w t =
        gamma2 (2 * c + 4) u w := alpha_add_beta2 (2 * c + 4) (by omega) u w t
    have hC2_plus : c * (c + 1) + 1 ≤
        Delta (x1 u w) (x3 u w) (alpha2 (2 * c + 4) u w t) +
        Delta (x1 u w) (x3 u w) (beta2 (2 * c + 4) u w t) := by
      rcases le_or_gt 0 theta with hth0 | hth0
      · have hth_gt : tau2 < theta := by
          rw [abs_of_nonneg hth0] at hcase1; linarith
        have hb2_gt : (c : ℝ) * x1 u w < beta2 (2 * c + 4) u w t := by linarith
        have hbonus : Gval (x1 u w) (x3 u w)
              (alpha2 (2 * c + 4) u w t + beta2 (2 * c + 4) u w t) (2 * c - 1) + 1 ≤
            Delta (x1 u w) (x3 u w) (alpha2 (2 * c + 4) u w t) +
            Delta (x1 u w) (x3 u w) (beta2 (2 * c + 4) u w t) := by
          apply pair_sum_with_bonus hx1_pos (le_trans hx12 hx23) (s0 := c - 1) (by omega)
          have hsub : 2 * c - 1 - (c - 1) = c := by omega
          rw [hsub, rowCard_eq_pos hlt13, rowCard_eq_pos hlt13]
          let X : ℝ := (alpha2 (2 * c + 4) u w t - x1 u w * ((c - 1 : ℕ) : ℝ)) / (x3 u w - x1 u w)
          let Y : ℝ := (beta2 (2 * c + 4) u w t - x1 u w * (c : ℝ)) / (x3 u w - x1 u w)
          have hY_pos : 0 < Y := div_pos (by linarith) (by linarith)
          have hY_ceil : 1 ≤ ⌈Y⌉₊ := Nat.ceil_pos.2 hY_pos
          have hXY_eq : X + Y =
              (gamma2 (2 * c + 4) u w - x1 u w * ((2 * c - 1 : ℕ) : ℝ)) / (x3 u w - x1 u w) := by
            dsimp [X, Y]
            rw [← add_div, ← hsum_ab2]
            have hcast : ((c - 1 : ℕ) : ℝ) + (c : ℝ) = ((2 * c - 1 : ℕ) : ℝ) := by
              rw [Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_sub (by omega : 1 ≤ 2 * c)]
              push_cast; ring
            congr 1; rw [← hcast]; ring
          have hXY_ceil : c < ⌈X + Y⌉₊ := by rw [hXY_eq]; exact Nat.lt_ceil.2 hXi2
          have hceil_add : ⌈X + Y⌉₊ ≤ ⌈X⌉₊ + ⌈Y⌉₊ := by
            apply Nat.ceil_le.2; push_cast; linarith [Nat.le_ceil X, Nat.le_ceil Y]
          have hmin_le : min (Lval (x1 u w) (x3 u w)
              (alpha2 (2 * c + 4) u w t + beta2 (2 * c + 4) u w t) (2 * c - 1))
              (min (c - 1 + 1) (c + 1)) ≤ c := by
            exact le_trans (min_le_right _ _) (by omega)
          have hgoal : c + 1 ≤ min (c - 1 + 1) ⌈X⌉₊ + min (c + 1) ⌈Y⌉₊ := by omega
          exact le_trans (Nat.add_le_add_right hmin_le 1) hgoal
        rw [hsum_ab2, Gval_of_full hfull2, hT2_2c] at hbonus
        exact hbonus
      · have hth_lt : theta < -tau2 := by
          rw [abs_of_neg hth0] at hcase1; linarith
        have ha2_gt : (c : ℝ) * x1 u w < alpha2 (2 * c + 4) u w t := by linarith
        have hbonus : Gval (x1 u w) (x3 u w)
              (alpha2 (2 * c + 4) u w t + beta2 (2 * c + 4) u w t) (2 * c - 1) + 1 ≤
            Delta (x1 u w) (x3 u w) (alpha2 (2 * c + 4) u w t) +
            Delta (x1 u w) (x3 u w) (beta2 (2 * c + 4) u w t) := by
          apply pair_sum_with_bonus hx1_pos (le_trans hx12 hx23) (s0 := c) (by omega)
          have hsub : 2 * c - 1 - c = c - 1 := by omega
          rw [hsub, rowCard_eq_pos hlt13, rowCard_eq_pos hlt13]
          let X : ℝ := (alpha2 (2 * c + 4) u w t - x1 u w * (c : ℝ)) / (x3 u w - x1 u w)
          let Y : ℝ := (beta2 (2 * c + 4) u w t - x1 u w * ((c - 1 : ℕ) : ℝ)) / (x3 u w - x1 u w)
          have hX_pos : 0 < X := div_pos (by linarith) (by linarith)
          have hX_ceil : 1 ≤ ⌈X⌉₊ := Nat.ceil_pos.2 hX_pos
          have hXY_eq : X + Y =
              (gamma2 (2 * c + 4) u w - x1 u w * ((2 * c - 1 : ℕ) : ℝ)) / (x3 u w - x1 u w) := by
            dsimp [X, Y]
            rw [← add_div, ← hsum_ab2]
            have hcast : (c : ℝ) + ((c - 1 : ℕ) : ℝ) = ((2 * c - 1 : ℕ) : ℝ) := by
              rw [Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_sub (by omega : 1 ≤ 2 * c)]
              push_cast; ring
            congr 1; rw [← hcast]; ring
          have hXY_ceil : c < ⌈X + Y⌉₊ := by rw [hXY_eq]; exact Nat.lt_ceil.2 hXi2
          have hceil_add : ⌈X + Y⌉₊ ≤ ⌈X⌉₊ + ⌈Y⌉₊ := by
            apply Nat.ceil_le.2; push_cast; linarith [Nat.le_ceil X, Nat.le_ceil Y]
          have hmin_le : min (Lval (x1 u w) (x3 u w)
              (alpha2 (2 * c + 4) u w t + beta2 (2 * c + 4) u w t) (2 * c - 1))
              (min (c + 1) (c - 1 + 1)) ≤ c := by
            exact le_trans (min_le_right _ _) (by omega)
          have hgoal : c + 1 ≤ min (c + 1) ⌈X⌉₊ + min (c - 1 + 1) ⌈Y⌉₊ := by omega
          exact le_trans (Nat.add_le_add_right hmin_le 1) hgoal
        rw [hsum_ab2, Gval_of_full hfull2, hT2_2c] at hbonus
        exact hbonus
    unfold missedCount
    rw [hD_val]
    omega

end

end CheeseCutM
