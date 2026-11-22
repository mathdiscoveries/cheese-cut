module

public import Mathlib.Analysis.Real.Sqrt
public import CheeseCutM.Defs

import Mathlib.Tactic

/-!
# Foundation: Diagonal Lines, Lemma T, Theorem U, Corollary U2, and Reduction R

100% unconditional proofs over `ℝ`:
* Diagonal-line decomposition (`lines_bound`, `cutCount_le_starts`)
* Lattice triangle count `Delta(p, q; c)` and bounded `tri(p, q, c, h)` (`tri_eq_triNat`,
  `tri_lb`, `tri_lb_sym`)
* Lemma T inequality half (`lemmaT_le`)
* Column bound (`column_bound`), central shifting (`exists_central`), Theorem U (`theoremU_bound`)
* Corollary U2 (`u2_sorted_cone`)
* Open-condition strict-ordering perturbation (`perturb_strict_ordered`) and **Reduction R**
  (`reduction_R`): reducing `∀ a b c t, IsNormal a b c → cutCount n a b c t ≤ F n` for any
  `n ≥ 16` unconditionally to the cone missed-diagonal bound `(*)` on
  `{u > 0, w > 0, u + 2w ≤ 3 r(n)}`.
-/

@[expose] public section

namespace CheeseCutM

open Finset

noncomputable section

/-! ### Diagonal-line decomposition (Lemma 1(c) & Lemma T base) -/

/-- Starts of diagonal lines: cells with at least one zero coordinate. -/
def starts (n : ℕ) : Finset Cell :=
  (cells n).filter (fun x => x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0)

/-- Minimum coordinate of a cell. -/
def mn (z : Cell) : ℕ := min z.1 (min z.2.1 z.2.2)

/-- Start of the diagonal line through `z`. -/
def lineStart (z : Cell) : Cell := (z.1 - mn z, z.2.1 - mn z, z.2.2 - mn z)

open Classical in
def missA1 (n : ℕ) (a b c t : ℝ) : Finset Cell :=
  (cells n).filter (fun x => x.1 = 0 ∧ 1 ≤ x.2.1 ∧ 1 ≤ x.2.2 ∧ t ≤ dot a b c x)

open Classical in
def missA2 (n : ℕ) (a b c t : ℝ) : Finset Cell :=
  (cells n).filter (fun x => x.2.1 = 0 ∧ 1 ≤ x.1 ∧ 1 ≤ x.2.2 ∧ t ≤ dot a b c x)

open Classical in
def missA3 (n : ℕ) (a b c t : ℝ) : Finset Cell :=
  (cells n).filter (fun x => x.2.2 = 0 ∧ 1 ≤ x.1 ∧ 1 ≤ x.2.1 ∧ t ≤ dot a b c x)

open Classical in
def missB1 (n : ℕ) (a b c t : ℝ) : Finset Cell :=
  (cells n).filter (fun x => (x.2.1 = 0 ∨ x.2.2 = 0) ∧ x.2.1 < x.1 ∧
    x.2.2 < x.1 ∧ dot a b c x + ((n : ℝ) - (x.1 : ℝ)) * (a + b + c) ≤ t)

open Classical in
def missB2 (n : ℕ) (a b c t : ℝ) : Finset Cell :=
  (cells n).filter (fun x => (x.1 = 0 ∨ x.2.2 = 0) ∧ x.1 < x.2.1 ∧
    x.2.2 < x.2.1 ∧ dot a b c x + ((n : ℝ) - (x.2.1 : ℝ)) * (a + b + c) ≤ t)

open Classical in
def missB3 (n : ℕ) (a b c t : ℝ) : Finset Cell :=
  (cells n).filter (fun x => (x.1 = 0 ∨ x.2.1 = 0) ∧ x.1 < x.2.2 ∧
    x.2.1 < x.2.2 ∧ dot a b c x + ((n : ℝ) - (x.2.2 : ℝ)) * (a + b + c) ≤ t)

lemma card_starts (h : ℕ) : (starts (h + 1)).card + h ^ 3 ≤ (h + 1) ^ 3 := by
  have e : (starts (h + 1)).card + ((cells (h + 1)).filter
      (fun x : Cell => ¬(x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0))).card =
      (cells (h + 1)).card :=
    Finset.card_filter_add_card_filter_not _
  have hi : (cells h).card ≤ ((cells (h + 1)).filter
      (fun x : Cell => ¬(x.1 = 0 ∨ x.2.1 = 0 ∨ x.2.2 = 0))).card := by
    apply Finset.card_le_card_of_injOn
      (fun z : Cell => (z.1 + 1, z.2.1 + 1, z.2.2 + 1))
    · intro z hz
      have hz' := mem_cells.1 (Finset.mem_coe.1 hz)
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_cells.2 ?_, ?_⟩)
      · dsimp only; omega
      · dsimp only; omega
    · intro z _ z' _ hzz
      simp only [Prod.mk.injEq] at hzz
      exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))
  have c1 := card_cells (h + 1)
  have c2 := card_cells h
  omega

private lemma mn_le (z : Cell) : mn z ≤ z.1 ∧ mn z ≤ z.2.1 ∧ mn z ≤ z.2.2 := by
  unfold mn; omega

private lemma dot_sub (a b c : ℝ) (z : Cell) (m : ℕ) (h1 : m ≤ z.1) (h2 : m ≤ z.2.1)
    (h3 : m ≤ z.2.2) :
    dot a b c (z.1 - m, z.2.1 - m, z.2.2 - m) + (m : ℝ) * (a + b + c) =
      dot a b c z := by
  show a * ((z.1 - m : ℕ) : ℝ) + b * ((z.2.1 - m : ℕ) : ℝ) +
      c * ((z.2.2 - m : ℕ) : ℝ) + (m : ℝ) * (a + b + c) =
      a * (z.1 : ℝ) + b * (z.2.1 : ℝ) + c * (z.2.2 : ℝ)
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
  ring

private lemma dot_lineStart (a b c : ℝ) (z : Cell) :
    dot a b c (lineStart z) + (mn z : ℝ) * (a + b + c) = dot a b c z := by
  obtain ⟨h1, h2, h3⟩ := mn_le z
  exact dot_sub a b c z (mn z) h1 h2 h3

private lemma lineStart_bounds {n : ℕ} {z : Cell} (hz : z ∈ cells n) :
    (lineStart z).1 + mn z + 1 ≤ n ∧ (lineStart z).2.1 + mn z + 1 ≤ n ∧
      (lineStart z).2.2 + mn z + 1 ≤ n := by
  rw [mem_cells] at hz
  simp only [lineStart, mn]
  omega

private lemma lineStart_mem_starts {n : ℕ} {z : Cell} (hz : z ∈ cells n) :
    lineStart z ∈ starts n := by
  rw [mem_cells] at hz
  unfold starts
  rw [Finset.mem_filter, mem_cells]
  simp only [lineStart, mn]
  omega

/-- **Diagonal-line decomposition (`lines_bound`):** For `v ≥ 0`, `a + b + c > 0`, and any `t`,
`cutCount + Σ |missA k| + Σ |missB k| ≤ |starts|`. -/
theorem lines_bound {n : ℕ} {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hW : 0 < a + b + c) :
    cutCount n a b c t +
      ((missA1 n a b c t).card + (missA2 n a b c t).card +
        (missA3 n a b c t).card) +
      ((missB1 n a b c t).card + (missB2 n a b c t).card +
        (missB3 n a b c t).card) ≤ (starts n).card := by
  have cut_lt : ∀ z ∈ cutSet n a b c t,
      dot a b c z < t ∧ t < dot a b c z + (a + b + c) := fun z hz =>
    (meets_iff_nonneg ha hb hc hW z).1 (mem_cutSet.1 hz).2
  have keyA : ∀ z ∈ cutSet n a b c t, dot a b c (lineStart z) < t := by
    intro z hz
    obtain ⟨h1, _⟩ := cut_lt z hz
    have d := dot_lineStart a b c z
    have : (0 : ℝ) ≤ (mn z : ℝ) * (a + b + c) :=
      mul_nonneg (Nat.cast_nonneg _) hW.le
    linarith
  have keyB : ∀ z ∈ cutSet n a b c t, ∀ k : ℕ, k + mn z + 1 ≤ n →
      t < dot a b c (lineStart z) + ((n : ℝ) - (k : ℝ)) * (a + b + c) := by
    intro z hz k hk
    obtain ⟨_, h2⟩ := cut_lt z hz
    have d := dot_lineStart a b c z
    have hk' : (k : ℝ) + (mn z : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - k - mn z - 1) hW.le]
  have hinj : Set.InjOn lineStart (cutSet n a b c t : Set Cell) := by
    intro z hz z' hz' heq
    have hz0 := Finset.mem_coe.1 hz
    have hz0' := Finset.mem_coe.1 hz'
    obtain ⟨u1, u2⟩ := cut_lt z hz0
    obtain ⟨u1', u2'⟩ := cut_lt z' hz0'
    have dz := dot_lineStart a b c z
    have dz' := dot_lineStart a b c z'
    rw [heq] at dz
    have hm : mn z = mn z' := by
      rcases lt_trichotomy (mn z) (mn z') with hlt | hm | hgt
      · exfalso
        have hl : (mn z : ℝ) + 1 ≤ (mn z' : ℝ) := by exact_mod_cast hlt
        nlinarith [mul_nonneg (sub_nonneg.2 hl) hW.le]
      · exact hm
      · exfalso
        have hl : (mn z' : ℝ) + 1 ≤ (mn z : ℝ) := by exact_mod_cast hgt
        nlinarith [mul_nonneg (sub_nonneg.2 hl) hW.le]
    obtain ⟨l1, l2, l3⟩ := mn_le z
    obtain ⟨l1', l2', l3'⟩ := mn_le z'
    unfold lineStart at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨e1, e2, e3⟩ := heq
    exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))
  have hI : ((cutSet n a b c t).image lineStart).card = cutCount n a b c t :=
    Finset.card_image_of_injOn hinj
  have hA12 : Disjoint (missA1 n a b c t) (missA2 n a b c t) := by
    refine Finset.disjoint_left.2 (fun x h1 h2 => ?_)
    simp only [missA1, missA2, Finset.mem_filter] at h1 h2; omega
  have hA123 : Disjoint (missA1 n a b c t ∪ missA2 n a b c t) (missA3 n a b c t) := by
    refine Finset.disjoint_left.2 (fun x h1 h2 => ?_)
    simp only [missA1, missA2, missA3, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
  have hB12 : Disjoint (missB1 n a b c t) (missB2 n a b c t) := by
    refine Finset.disjoint_left.2 (fun x h1 h2 => ?_)
    simp only [missB1, missB2, Finset.mem_filter] at h1 h2; omega
  have hB123 : Disjoint (missB1 n a b c t ∪ missB2 n a b c t) (missB3 n a b c t) := by
    refine Finset.disjoint_left.2 (fun x h1 h2 => ?_)
    simp only [missB1, missB2, missB3, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
  have hBelow : ∀ x ∈ cells n, ∀ k : ℕ, k < n →
      dot a b c x + ((n : ℝ) - (k : ℝ)) * (a + b + c) ≤ t → dot a b c x < t := by
    intro x _ k hk hle
    have hk' : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
    nlinarith [mul_pos (by linarith : (0 : ℝ) < (n : ℝ) - k) hW]
  have hAB : Disjoint (missA1 n a b c t ∪ missA2 n a b c t ∪ missA3 n a b c t)
      (missB1 n a b c t ∪ missB2 n a b c t ∪ missB3 n a b c t) := by
    refine Finset.disjoint_left.2 (fun x h1 h2 => ?_)
    have hA : t ≤ dot a b c x := by
      simp only [missA1, missA2, missA3, Finset.mem_union, Finset.mem_filter] at h1
      rcases h1 with (h | h) | h
      · exact h.2.2.2.2
      · exact h.2.2.2.2
      · exact h.2.2.2.2
    have hB : dot a b c x < t := by
      simp only [missB1, missB2, missB3, Finset.mem_union, Finset.mem_filter] at h2
      rcases h2 with (h | h) | h
      · exact hBelow x h.1 _ (mem_cells.1 h.1).1 h.2.2.2.2
      · exact hBelow x h.1 _ (mem_cells.1 h.1).2.1 h.2.2.2.2
      · exact hBelow x h.1 _ (mem_cells.1 h.1).2.2 h.2.2.2.2
    linarith
  have hIS : Disjoint ((cutSet n a b c t).image lineStart)
      ((missA1 n a b c t ∪ missA2 n a b c t ∪ missA3 n a b c t) ∪
        (missB1 n a b c t ∪ missB2 n a b c t ∪ missB3 n a b c t)) := by
    refine Finset.disjoint_left.2 (fun x h1 h2 => ?_)
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 h1
    have hzc := (mem_cutSet.1 hz).1
    have kA := keyA z hz
    obtain ⟨b1, b2, b3⟩ := lineStart_bounds hzc
    simp only [missA1, missA2, missA3, missB1, missB2, missB3, Finset.mem_union,
      Finset.mem_filter] at h2
    rcases h2 with ((h | h) | h) | ((h | h) | h)
    · linarith [h.2.2.2.2]
    · linarith [h.2.2.2.2]
    · linarith [h.2.2.2.2]
    · linarith [h.2.2.2.2, keyB z hz _ b1]
    · linarith [h.2.2.2.2, keyB z hz _ b2]
    · linarith [h.2.2.2.2, keyB z hz _ b3]
  have hsub : (cutSet n a b c t).image lineStart ∪
      ((missA1 n a b c t ∪ missA2 n a b c t ∪ missA3 n a b c t) ∪
        (missB1 n a b c t ∪ missB2 n a b c t ∪ missB3 n a b c t)) ⊆
      starts n := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
      exact lineStart_mem_starts (mem_cutSet.1 hz).1
    · unfold starts
      rw [Finset.mem_filter]
      simp only [missA1, missA2, missA3, missB1, missB2, missB3,
        Finset.mem_union, Finset.mem_filter] at hx
      rcases hx with ((h | h) | h) | ((h | h) | h)
      · exact ⟨h.1, Or.inl h.2.1⟩
      · exact ⟨h.1, Or.inr (Or.inl h.2.1)⟩
      · exact ⟨h.1, Or.inr (Or.inr h.2.1)⟩
      · rcases h.2.1 with h' | h'
        · exact ⟨h.1, Or.inr (Or.inl h')⟩
        · exact ⟨h.1, Or.inr (Or.inr h')⟩
      · rcases h.2.1 with h' | h'
        · exact ⟨h.1, Or.inl h'⟩
        · exact ⟨h.1, Or.inr (Or.inr h')⟩
      · rcases h.2.1 with h' | h'
        · exact ⟨h.1, Or.inl h'⟩
        · exact ⟨h.1, Or.inr (Or.inl h')⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hIS, Finset.card_union_of_disjoint hAB,
    Finset.card_union_of_disjoint hA123, Finset.card_union_of_disjoint hA12,
    Finset.card_union_of_disjoint hB123, Finset.card_union_of_disjoint hB12,
    hI] at hle
  omega

theorem cutCount_le_starts {n : ℕ} {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hW : 0 < a + b + c) : cutCount n a b c t ≤ (starts n).card := by
  have := lines_bound (n := n) (t := t) ha hb hc hW
  omega

/-! ### Lattice points in right triangles (`tri` and `Delta`) -/

open Classical in
/-- Bounded triangle `{(a, b) ∈ {0, …, h - 1}² : p a + q b < c}`. -/
def tri (p q c : ℝ) (h : ℕ) : Finset (ℕ × ℕ) :=
  (range h ×ˢ range h).filter (fun uw => p * (uw.1 : ℝ) + q * (uw.2 : ℝ) < c)

open Classical in
/-- Unbounded `ℕ²` lattice triangle `{(a, b) ∈ ℕ² : p a + q b < c}` (valid for `p, q > 0`). -/
def triNat (p q c : ℝ) : Finset (ℕ × ℕ) :=
  (range ⌈c / p⌉₊ ×ˢ range ⌈c / q⌉₊).filter (fun ab => p * (ab.1 : ℝ) + q * (ab.2 : ℝ) < c)

/-- `Δ(p, q; c) = #{(a, b) ∈ ℕ² : p a + q b < c}` (for `p, q > 0`). -/
def Delta (p q c : ℝ) : ℕ := (triNat p q c).card

lemma mem_triNat_iff {p q c : ℝ} (hp : 0 < p) (hq : 0 < q) (ab : ℕ × ℕ) :
    ab ∈ triNat p q c ↔ p * (ab.1 : ℝ) + q * (ab.2 : ℝ) < c := by
  unfold triNat
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · intro h; exact h.2
  · intro hlt
    refine ⟨⟨?_, ?_⟩, hlt⟩
    · refine Nat.lt_ceil.2 ?_
      rw [lt_div_iff₀ hp]
      have : (0 : ℝ) ≤ q * (ab.2 : ℝ) := mul_nonneg hq.le (Nat.cast_nonneg _)
      linarith
    · refine Nat.lt_ceil.2 ?_
      rw [lt_div_iff₀ hq]
      have : (0 : ℝ) ≤ p * (ab.1 : ℝ) := mul_nonneg hp.le (Nat.cast_nonneg _)
      linarith

lemma tri_eq_triNat {p q c : ℝ} {h : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcp : c ≤ (h : ℝ) * p) (hcq : c ≤ (h : ℝ) * q) :
    tri p q c h = triNat p q c := by
  ext ab
  rw [mem_triNat_iff hp hq]
  unfold tri
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · intro H; exact H.2
  · intro hlt
    refine ⟨⟨?_, ?_⟩, hlt⟩
    · have h1 : p * (ab.1 : ℝ) < (h : ℝ) * p := by
        have : (0 : ℝ) ≤ q * (ab.2 : ℝ) := mul_nonneg hq.le (Nat.cast_nonneg _)
        linarith
      have h2 : (ab.1 : ℝ) < (h : ℝ) := by nlinarith
      exact_mod_cast h2
    · have h1 : q * (ab.2 : ℝ) < (h : ℝ) * q := by
        have : (0 : ℝ) ≤ p * (ab.1 : ℝ) := mul_nonneg hp.le (Nat.cast_nonneg _)
        linarith
      have h2 : (ab.2 : ℝ) < (h : ℝ) := by nlinarith
      exact_mod_cast h2

open Classical in
private def triRow (p r : ℝ) (h : ℕ) : Finset ℕ :=
  (range h).filter (fun u => p * (u : ℝ) < r)

private lemma tri_card_eq (p q c : ℝ) (h : ℕ) :
    (tri p q c h).card = ∑ w ∈ range h, (triRow p (c - q * (w : ℝ)) h).card := by
  unfold tri triRow
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  show (if p * (u : ℝ) + q * (w : ℝ) < c then 1 else 0) =
    (if p * (u : ℝ) < c - q * (w : ℝ) then 1 else 0)
  by_cases huw : p * (u : ℝ) + q * (w : ℝ) < c
  · rw [ite_eq_left huw, ite_eq_left (by linarith)]
  · rw [ite_eq_right huw, ite_eq_right (fun hh => huw (by linarith))]

private lemma row_card (p r : ℝ) (h : ℕ) (hp : 0 < p) (hr : r ≤ (h : ℝ) * p) :
    r / p ≤ ((triRow p r h).card : ℝ) := by
  by_cases hr0 : r ≤ 0
  · have : r / p ≤ 0 := by rw [div_le_iff₀ hp]; linarith
    exact le_trans this (Nat.cast_nonneg _)
  · push Not at hr0
    have hk : ⌈r / p⌉₊ ≤ h := Nat.ceil_le.2 (by rw [div_le_iff₀ hp]; linarith)
    have hsub : range ⌈r / p⌉₊ ⊆ triRow p r h := by
      intro u hu
      rw [Finset.mem_range] at hu
      unfold triRow
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨lt_of_lt_of_le hu hk, ?_⟩
      have h1 : (u : ℝ) < r / p := Nat.lt_ceil.1 hu
      rw [lt_div_iff₀ hp] at h1
      linarith
    calc r / p ≤ (⌈r / p⌉₊ : ℝ) := Nat.le_ceil _
      _ = ((range ⌈r / p⌉₊).card : ℝ) := by rw [Finset.card_range]
      _ ≤ ((triRow p r h).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub

private lemma sum_row (c q : ℝ) :
    ∀ K : ℕ, ∑ w ∈ range K, (c - q * (w : ℝ)) =
      (K : ℝ) * c - q * ((K : ℝ) * ((K : ℝ) - 1) / 2)
  | 0 => by simp
  | K + 1 => by
    rw [Finset.sum_range_succ, sum_row c q K]
    push_cast
    ring

private lemma row_sum_lb (c q K : ℝ) (hq : 0 < q) (h1 : q * (K - 1) < c)
    (h2 : c ≤ q * K) :
    c ^ 2 / (2 * q) + c / 2 ≤ K * c - q * (K * (K - 1) / 2) := by
  have hq' : q ≠ 0 := ne_of_gt hq
  have key : K * c - q * (K * (K - 1) / 2) - (c ^ 2 / (2 * q) + c / 2) =
      (c - q * (K - 1)) * (q * K - c) / (2 * q) := by
    field_simp
    ring
  have hnn : 0 ≤ (c - q * (K - 1)) * (q * K - c) / (2 * q) := by
    apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  linarith

theorem tri_lb (p q c : ℝ) (h : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : 0 < c)
    (hcp : c ≤ (h : ℝ) * p) (hcq : c ≤ (h : ℝ) * q) :
    c ^ 2 / (2 * p * q) + c / (2 * p) ≤ ((tri p q c h).card : ℝ) := by
  have hp' : p ≠ 0 := ne_of_gt hp
  have hq' : q ≠ 0 := ne_of_gt hq
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈c / q⌉₊ := ⟨_, rfl⟩
  have hcq0 : 0 ≤ c / q := (div_pos hc hq).le
  have hK1 : (K : ℝ) < c / q + 1 := by rw [hK]; exact Nat.ceil_lt_add_one hcq0
  have hK2 : c / q ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
  have hKh : K ≤ h := by
    rw [hK]
    exact Nat.ceil_le.2 (by rw [div_le_iff₀ hq]; linarith)
  have hk1 : q * ((K : ℝ) - 1) < c := by
    have : (K : ℝ) - 1 < c / q := by linarith
    rw [lt_div_iff₀ hq] at this; linarith
  have hk2 : c ≤ q * (K : ℝ) := by rw [div_le_iff₀ hq] at hK2; linarith
  rw [tri_card_eq]
  push_cast
  calc c ^ 2 / (2 * p * q) + c / (2 * p)
        = (c ^ 2 / (2 * q) + c / 2) / p := by field_simp
    _ ≤ ((K : ℝ) * c - q * ((K : ℝ) * ((K : ℝ) - 1) / 2)) / p := by
          gcongr; exact row_sum_lb c q K hq hk1 hk2
    _ = ∑ w ∈ range K, (c - q * (w : ℝ)) / p := by rw [← Finset.sum_div, sum_row]
    _ ≤ ∑ w ∈ range K, ((triRow p (c - q * (w : ℝ)) h).card : ℝ) := by
          apply Finset.sum_le_sum
          intro w _
          apply row_card p _ h hp
          have : (0 : ℝ) ≤ q * (w : ℝ) := mul_nonneg hq.le (Nat.cast_nonneg _)
          linarith
    _ ≤ ∑ w ∈ range h, ((triRow p (c - q * (w : ℝ)) h).card : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hKh)
          intro w _ _; exact Nat.cast_nonneg _

private lemma tri_card_swap (p q c : ℝ) (h : ℕ) : (tri q p c h).card = (tri p q c h).card := by
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro uw huw
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    rw [Finset.mem_product] at hm
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hm.1.2, hm.1.1⟩, ?_⟩)
    simp only [Prod.fst_swap, Prod.snd_swap]; linarith [hm.2]
  · intro uw huw
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    rw [Finset.mem_product] at hm
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hm.1.2, hm.1.1⟩, ?_⟩)
    simp only [Prod.fst_swap, Prod.snd_swap]; linarith [hm.2]
  · intro uw _; exact Prod.swap_swap uw
  · intro uw _; exact Prod.swap_swap uw

theorem tri_lb_sym (p q c : ℝ) (h : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : 0 < c)
    (hcp : c ≤ (h : ℝ) * p) (hcq : c ≤ (h : ℝ) * q) :
    2 * c ^ 2 / (p + q) ^ 2 + c / (p + q) ≤ ((tri p q c h).card : ℝ) := by
  have hs : 0 < p + q := by linarith
  have quad : 2 * c ^ 2 / (p + q) ^ 2 ≤ c ^ 2 / (2 * p * q) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (p - q))]
  rcases le_total p q with hpq | hqp
  · have lin : c / (p + q) ≤ c / (2 * p) := by
      rw [div_le_div_iff₀ hs (by positivity)]; nlinarith
    have := tri_lb p q c h hp hq hc hcp hcq
    linarith
  · have lin : c / (p + q) ≤ c / (2 * q) := by
      rw [div_le_div_iff₀ hs (by positivity)]; nlinarith
    have quad' : c ^ 2 / (2 * p * q) = c ^ 2 / (2 * q * p) := by ring
    have := tri_lb q p c h hq hp hc hcq hcp
    rw [tri_card_swap] at this
    linarith

/-! ### Tangent-line inequalities for Theorem U and Corollary U2 -/

private def Acoef (h : ℝ) : ℝ := (h + 1 - 2) * (h + 1 - 4) / 4

private def Bcoef (h : ℝ) : ℝ := -9 * (h + 1) * (h + 1 - 3) / 4

private lemma tangent_pos (h y : ℝ) (hh : 3 ≤ h) (hy : 1 ≤ y) :
    Acoef h + Bcoef h * (2 / 3 - 1 / y) ≤
      (2 * h - (h + 1) * y) ^ 2 + (2 * h - (h + 1) * y) := by
  have hy0 : 0 < y := by linarith
  have hy' : y ≠ 0 := ne_of_gt hy0
  have key : (2 * h - (h + 1) * y) ^ 2 + (2 * h - (h + 1) * y) -
      (Acoef h + Bcoef h * (2 / 3 - 1 / y)) =
      (h + 1) * (2 * y - 3) ^ 2 * ((h + 1) * y - h + 2) / (4 * y) := by
    unfold Acoef Bcoef; field_simp; ring
  have hnn : 0 ≤ (h + 1) * (2 * y - 3) ^ 2 * ((h + 1) * y - h + 2) / (4 * y) := by
    apply div_nonneg (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by nlinarith))
      (by linarith)
  linarith

private lemma tangent_neg (h y : ℝ) (hh : 3 ≤ h) (hy : 2 * h ≤ (h + 1) * y) :
    Acoef h + Bcoef h * (2 / 3 - 1 / y) ≤ 0 := by
  have hy0 : 0 < y := by nlinarith
  have hy' : y ≠ 0 := ne_of_gt hy0
  have hP : 0 < (h + 1) * y := mul_pos (by linarith) hy0
  have key : (Acoef h + Bcoef h * (2 / 3 - 1 / y)) * ((h + 1) * y) =
      -(5 * h ^ 2 - 2 * h - 15) / 4 * ((h + 1) * y - 2 * h) -
        (h - 3) ^ 2 * (h + 2) / 4 := by
    unfold Acoef Bcoef; field_simp; ring
  have h5 : 0 ≤ 5 * h ^ 2 - 2 * h - 15 := by nlinarith
  have hprod : (Acoef h + Bcoef h * (2 / 3 - 1 / y)) * ((h + 1) * y) ≤ 0 := by
    rw [key]
    have t1 : 0 ≤ (5 * h ^ 2 - 2 * h - 15) * ((h + 1) * y - 2 * h) := mul_nonneg h5 (by linarith)
    have t2 : 0 ≤ (h - 3) ^ 2 * (h + 2) := mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  by_contra hcon
  push Not at hcon
  have := mul_pos hcon hP
  linarith

private lemma psi_lb (Ca Cb ua ub : ℝ) (h0a : 0 ≤ Ca) (h0b : 0 ≤ Cb)
    (ha : 0 < ua → 2 * ua ^ 2 + ua ≤ Ca) (hb : 0 < ub → 2 * ub ^ 2 + ub ≤ Cb)
    (hr : 0 < ua + ub) : (ua + ub) ^ 2 + (ua + ub) ≤ Ca + Cb := by
  rcases lt_or_ge 0 ua with hua | hua <;> rcases lt_or_ge 0 ub with hub | hub
  · have e1 := ha hua; have e2 := hb hub
    nlinarith [sq_nonneg (ua - ub)]
  · have e1 := ha hua
    nlinarith [mul_nonneg (neg_nonneg.2 hub) (by linarith : (0 : ℝ) ≤ 2 * ua + ub), sq_nonneg ua]
  · have e2 := hb hub
    nlinarith [mul_nonneg (neg_nonneg.2 hua) (by linarith : (0 : ℝ) ≤ 2 * ub + ua), sq_nonneg ub]
  · linarith

/-! ### Lemma T inequality half (`lemmaT_le`) -/

private lemma card_tri_le_A1 (h : ℕ) (a b c t : ℝ) :
    (tri b c ((b + c) * (h : ℝ) - t) h).card ≤ (missA1 (h + 1) a b c t).card := by
  apply Finset.card_le_card_of_injOn (fun uw : ℕ × ℕ => ((0 : ℕ), h - uw.1, h - uw.2))
  · intro uw huw
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    simp only [Finset.mem_product, Finset.mem_range] at hm
    obtain ⟨⟨hu, hw⟩, hlt⟩ := hm
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_cells.2 ?_, rfl, ?_, ?_, ?_⟩)
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · show t ≤ a * ((0 : ℕ) : ℝ) + b * ((h - uw.1 : ℕ) : ℝ) + c * ((h - uw.2 : ℕ) : ℝ)
      rw [Nat.cast_sub hu.le, Nat.cast_sub hw.le, Nat.cast_zero]; linarith
  · intro uw huw uw' huw' heq
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 huw')
    simp only [Finset.mem_product, Finset.mem_range] at hm hm'
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)

private lemma card_tri_le_A2 (h : ℕ) (a b c t : ℝ) :
    (tri a c ((a + c) * (h : ℝ) - t) h).card ≤ (missA2 (h + 1) a b c t).card := by
  apply Finset.card_le_card_of_injOn (fun uw : ℕ × ℕ => (h - uw.1, (0 : ℕ), h - uw.2))
  · intro uw huw
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    simp only [Finset.mem_product, Finset.mem_range] at hm
    obtain ⟨⟨hu, hw⟩, hlt⟩ := hm
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_cells.2 ?_, rfl, ?_, ?_, ?_⟩)
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · show t ≤ a * ((h - uw.1 : ℕ) : ℝ) + b * ((0 : ℕ) : ℝ) + c * ((h - uw.2 : ℕ) : ℝ)
      rw [Nat.cast_sub hu.le, Nat.cast_sub hw.le, Nat.cast_zero]; linarith
  · intro uw huw uw' huw' heq
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 huw')
    simp only [Finset.mem_product, Finset.mem_range] at hm hm'
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)

private lemma card_tri_le_A3 (h : ℕ) (a b c t : ℝ) :
    (tri a b ((a + b) * (h : ℝ) - t) h).card ≤ (missA3 (h + 1) a b c t).card := by
  apply Finset.card_le_card_of_injOn (fun uw : ℕ × ℕ => (h - uw.1, h - uw.2, (0 : ℕ)))
  · intro uw huw
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    simp only [Finset.mem_product, Finset.mem_range] at hm
    obtain ⟨⟨hu, hw⟩, hlt⟩ := hm
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_cells.2 ?_, rfl, ?_, ?_, ?_⟩)
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
    · show t ≤ a * ((h - uw.1 : ℕ) : ℝ) + b * ((h - uw.2 : ℕ) : ℝ) + c * ((0 : ℕ) : ℝ)
      rw [Nat.cast_sub hu.le, Nat.cast_sub hw.le, Nat.cast_zero]; linarith
  · intro uw huw uw' huw' heq
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 huw')
    simp only [Finset.mem_product, Finset.mem_range] at hm hm'
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)

private def bmap1 (h : ℕ) (uw : ℕ × ℕ) : Cell :=
  if uw.1 ≤ uw.2 then (h - uw.1, 0, uw.2 - uw.1) else (h - uw.2, uw.1 - uw.2, 0)

private def bmap2 (h : ℕ) (uw : ℕ × ℕ) : Cell :=
  if uw.1 ≤ uw.2 then (0, h - uw.1, uw.2 - uw.1) else (uw.1 - uw.2, h - uw.2, 0)

private def bmap3 (h : ℕ) (uw : ℕ × ℕ) : Cell :=
  if uw.1 ≤ uw.2 then (0, uw.2 - uw.1, h - uw.1) else (uw.1 - uw.2, 0, h - uw.2)

private lemma card_tri_le_B1 (h : ℕ) (a b c t : ℝ) :
    (tri b c (t - (h : ℝ) * a - (b + c + a)) h).card ≤
      (missB1 (h + 1) a b c t).card := by
  apply Finset.card_le_card_of_injOn (bmap1 h)
  · intro uw huw
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    simp only [Finset.mem_product, Finset.mem_range] at hm
    obtain ⟨⟨hu, hw⟩, hlt⟩ := hm
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ?_)
    by_cases huw : uw.1 ≤ uw.2
    · rw [bmap1, ite_eq_left huw]
      refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega⟩, Or.inl rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
      show a * ((h - uw.1 : ℕ) : ℝ) + b * ((0 : ℕ) : ℝ) + c * ((uw.2 - uw.1 : ℕ) : ℝ) +
          (((h + 1 : ℕ) : ℝ) - ((h - uw.1 : ℕ) : ℝ)) * (a + b + c) ≤ t
      rw [Nat.cast_sub huw, Nat.cast_sub hu.le]; push_cast; linarith
    · rw [bmap1, ite_eq_right huw]
      have hwu : uw.2 ≤ uw.1 := by omega
      refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega⟩, Or.inr rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
      show a * ((h - uw.2 : ℕ) : ℝ) + b * ((uw.1 - uw.2 : ℕ) : ℝ) + c * ((0 : ℕ) : ℝ) +
          (((h + 1 : ℕ) : ℝ) - ((h - uw.2 : ℕ) : ℝ)) * (a + b + c) ≤ t
      rw [Nat.cast_sub hwu, Nat.cast_sub hw.le]; push_cast; linarith
  · intro uw huw uw' huw' heq
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 huw')
    simp only [Finset.mem_product, Finset.mem_range] at hm hm'
    unfold bmap1 at heq
    split_ifs at heq <;> simp only [Prod.mk.injEq] at heq <;> exact Prod.ext (by omega) (by omega)

private lemma card_tri_le_B2 (h : ℕ) (a b c t : ℝ) :
    (tri a c (t - (h : ℝ) * b - (a + c + b)) h).card ≤
      (missB2 (h + 1) a b c t).card := by
  apply Finset.card_le_card_of_injOn (bmap2 h)
  · intro uw huw
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    simp only [Finset.mem_product, Finset.mem_range] at hm
    obtain ⟨⟨hu, hw⟩, hlt⟩ := hm
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ?_)
    by_cases huw : uw.1 ≤ uw.2
    · rw [bmap2, ite_eq_left huw]
      refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega⟩, Or.inl rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
      show a * ((0 : ℕ) : ℝ) + b * ((h - uw.1 : ℕ) : ℝ) + c * ((uw.2 - uw.1 : ℕ) : ℝ) +
          (((h + 1 : ℕ) : ℝ) - ((h - uw.1 : ℕ) : ℝ)) * (a + b + c) ≤ t
      rw [Nat.cast_sub huw, Nat.cast_sub hu.le]; push_cast; linarith
    · rw [bmap2, ite_eq_right huw]
      have hwu : uw.2 ≤ uw.1 := by omega
      refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega⟩, Or.inr rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
      show a * ((uw.1 - uw.2 : ℕ) : ℝ) + b * ((h - uw.2 : ℕ) : ℝ) + c * ((0 : ℕ) : ℝ) +
          (((h + 1 : ℕ) : ℝ) - ((h - uw.2 : ℕ) : ℝ)) * (a + b + c) ≤ t
      rw [Nat.cast_sub hwu, Nat.cast_sub hw.le]; push_cast; linarith
  · intro uw huw uw' huw' heq
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 huw')
    simp only [Finset.mem_product, Finset.mem_range] at hm hm'
    unfold bmap2 at heq
    split_ifs at heq <;> simp only [Prod.mk.injEq] at heq <;> exact Prod.ext (by omega) (by omega)

private lemma card_tri_le_B3 (h : ℕ) (a b c t : ℝ) :
    (tri a b (t - (h : ℝ) * c - (a + b + c)) h).card ≤
      (missB3 (h + 1) a b c t).card := by
  apply Finset.card_le_card_of_injOn (bmap3 h)
  · intro uw huw
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    simp only [Finset.mem_product, Finset.mem_range] at hm
    obtain ⟨⟨hu, hw⟩, hlt⟩ := hm
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ?_)
    by_cases huw : uw.1 ≤ uw.2
    · rw [bmap3, ite_eq_left huw]
      refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega⟩, Or.inl rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
      show a * ((0 : ℕ) : ℝ) + b * ((uw.2 - uw.1 : ℕ) : ℝ) + c * ((h - uw.1 : ℕ) : ℝ) +
          (((h + 1 : ℕ) : ℝ) - ((h - uw.1 : ℕ) : ℝ)) * (a + b + c) ≤ t
      rw [Nat.cast_sub huw, Nat.cast_sub hu.le]; push_cast; linarith
    · rw [bmap3, ite_eq_right huw]
      have hwu : uw.2 ≤ uw.1 := by omega
      refine ⟨mem_cells.2 ⟨by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega⟩, Or.inr rfl, by dsimp only; omega, by dsimp only; omega, ?_⟩
      show a * ((uw.1 - uw.2 : ℕ) : ℝ) + b * ((0 : ℕ) : ℝ) + c * ((h - uw.2 : ℕ) : ℝ) +
          (((h + 1 : ℕ) : ℝ) - ((h - uw.2 : ℕ) : ℝ)) * (a + b + c) ≤ t
      rw [Nat.cast_sub hwu, Nat.cast_sub hw.le]; push_cast; linarith
  · intro uw huw uw' huw' heq
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 huw)
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 huw')
    simp only [Finset.mem_product, Finset.mem_range] at hm hm'
    unfold bmap3 at heq
    split_ifs at heq <;> simp only [Prod.mk.injEq] at heq <;> exact Prod.ext (by omega) (by omega)

/-- **Lemma T (inequality half):** For `v ≥ 0`, `a + b + c > 0`, and every real `t`,
`cutCount(h + 1) + (6 triangles) + h³ ≤ (h + 1)³`. -/
theorem lemmaT_le (h : ℕ) (a b c t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hW : 0 < a + b + c) :
    cutCount (h + 1) a b c t +
      ((tri b c ((b + c) * (h : ℝ) - t) h).card +
        (tri b c (t - (h : ℝ) * a - (b + c + a)) h).card) +
      ((tri a c ((a + c) * (h : ℝ) - t) h).card +
        (tri a c (t - (h : ℝ) * b - (a + c + b)) h).card) +
      ((tri a b ((a + b) * (h : ℝ) - t) h).card +
        (tri a b (t - (h : ℝ) * c - (a + b + c)) h).card) + h ^ 3 ≤ (h + 1) ^ 3 := by
  have L := lines_bound (n := h + 1) (t := t) ha hb hc hW
  have S := card_starts h
  have i1 := card_tri_le_A1 h a b c t
  have i2 := card_tri_le_A2 h a b c t
  have i3 := card_tri_le_A3 h a b c t
  have j1 := card_tri_le_B1 h a b c t
  have j2 := card_tri_le_B2 h a b c t
  have j3 := card_tri_le_B3 h a b c t
  omega

/-! ### Column bound U(1), central shift U(2), and Corollary U2 -/

/-- **U(1) (`column_bound`):** If `v ≥ 0` and `c ≥ a + b`, then `cutCount n a b c t ≤ 2 n²`. -/
theorem column_bound (n : ℕ) (a b c t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hcol : a + b ≤ c) : cutCount n a b c t ≤ 2 * n ^ 2 := by
  have hW : 0 < a + b + c := by linarith
  have two : ∀ x ∈ cutSet n a b c t, ∀ y ∈ cutSet n a b c t, x.1 = y.1 →
      x.2.1 = y.2.1 → ¬(x.2.2 + 2 ≤ y.2.2) := by
    intro x hx y hy e1 e2 hxy
    obtain ⟨_, hx2⟩ := (meets_iff_nonneg ha hb hc.le hW x).1 (mem_cutSet.1 hx).2
    obtain ⟨hy1, _⟩ := (meets_iff_nonneg ha hb hc.le hW y).1 (mem_cutSet.1 hy).2
    have hxy' : (x.2.2 : ℝ) + 2 ≤ (y.2.2 : ℝ) := by exact_mod_cast hxy
    have e1' : (x.1 : ℝ) = (y.1 : ℝ) := by exact_mod_cast e1
    have e2' : (x.2.1 : ℝ) = (y.2.1 : ℝ) := by exact_mod_cast e2
    unfold dot at hx2 hy1
    rw [e1', e2'] at hx2
    nlinarith [mul_le_mul_of_nonneg_left hxy' hc.le]
  unfold cutCount
  have key := Finset.card_le_mul_card_image (cutSet n a b c t) 2
    (f := fun z : Cell => (z.1, z.2.1)) (by
      intro p _
      by_contra hcon
      push Not at hcon
      obtain ⟨x, hx, y, hy, w, hw, hxy, hxw, hyw⟩ := Finset.two_lt_card.1 hcon
      rw [Finset.mem_filter] at hx hy hw
      have exy : x.1 = y.1 ∧ x.2.1 = y.2.1 := by
        have h := hx.2.trans hy.2.symm; simp only [Prod.mk.injEq] at h; exact h
      have exw : x.1 = w.1 ∧ x.2.1 = w.2.1 := by
        have h := hx.2.trans hw.2.symm; simp only [Prod.mk.injEq] at h; exact h
      have d1 : x.2.2 ≠ y.2.2 := fun h3 => hxy (Prod.ext exy.1 (Prod.ext exy.2 h3))
      have d2 : x.2.2 ≠ w.2.2 := fun h3 => hxw (Prod.ext exw.1 (Prod.ext exw.2 h3))
      have d3 : y.2.2 ≠ w.2.2 := fun h3 => hyw (Prod.ext (exy.1.symm.trans exw.1)
        (Prod.ext (exy.2.symm.trans exw.2) h3))
      have t1 := two x hx.1 y hy.1 exy.1 exy.2
      have t2 := two y hy.1 x hx.1 exy.1.symm exy.2.symm
      have t3 := two x hx.1 w hw.1 exw.1 exw.2
      have t4 := two w hw.1 x hx.1 exw.1.symm exw.2.symm
      have t5 := two y hy.1 w hw.1 (exy.1.symm.trans exw.1) (exy.2.symm.trans exw.2)
      have t6 := two w hw.1 y hy.1 (exw.1.symm.trans exy.1) (exw.2.symm.trans exy.2)
      omega)
  have him : ((cutSet n a b c t).image (fun z : Cell => (z.1, z.2.1))).card ≤ n ^ 2 := by
    calc ((cutSet n a b c t).image (fun z : Cell => (z.1, z.2.1))).card
        ≤ (range n ×ˢ range n).card := by
          apply Finset.card_le_card
          intro p hp
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
          have hzc := mem_cells.1 (mem_cutSet.1 hz).1
          exact Finset.mem_product.2 ⟨Finset.mem_range.2 hzc.1, Finset.mem_range.2 hzc.2.1⟩
      _ = n ^ 2 := by rw [Finset.card_product, Finset.card_range]; ring
  calc (cutSet n a b c t).card ≤ 2 * ((cutSet n a b c t).image
        (fun z : Cell => (z.1, z.2.1))).card := key
    _ ≤ 2 * n ^ 2 := by omega

private lemma shift_le (n : ℕ) (a b c t : ℝ) (j : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hj : t + (j : ℝ) * c < (n : ℝ) * c) :
    cutCount n a b c t ≤ cutCount n a b c (t + (j : ℝ) * c) := by
  have hW : 0 < a + b + c := by linarith
  unfold cutCount
  apply Finset.card_le_card_of_injOn (fun z : Cell => (z.1, z.2.1, z.2.2 + j))
  · intro z hz
    have hz' := mem_cutSet.1 (Finset.mem_coe.1 hz)
    obtain ⟨h1, h2⟩ := (meets_iff_nonneg ha hb hc.le hW z).1 hz'.2
    have hzc := mem_cells.1 hz'.1
    have hlt : z.2.2 + j < n := by
      have hd : (z.2.2 : ℝ) * c ≤ dot a b c z := by
        unfold dot
        have q1 := mul_nonneg ha (Nat.cast_nonneg (α := ℝ) z.1)
        have q2 := mul_nonneg hb (Nat.cast_nonneg (α := ℝ) z.2.1)
        nlinarith
      have h3 : ((z.2.2 + j : ℕ) : ℝ) * c < (n : ℝ) * c := by push_cast; nlinarith
      have h4 : ((z.2.2 + j : ℕ) : ℝ) < (n : ℝ) := lt_of_mul_lt_mul_right h3 hc.le
      exact_mod_cast h4
    refine Finset.mem_coe.2 (mem_cutSet.2 ⟨mem_cells.2 ⟨hzc.1, hzc.2.1, hlt⟩, ?_⟩)
    rw [meets_iff_nonneg ha hb hc.le hW]
    have e : dot a b c (z.1, z.2.1, z.2.2 + j) = dot a b c z + (j : ℝ) * c := by
      unfold dot; push_cast; ring
    show dot a b c (z.1, z.2.1, z.2.2 + j) < t + (j : ℝ) * c ∧
      t + (j : ℝ) * c < dot a b c (z.1, z.2.1, z.2.2 + j) + (a + b + c)
    rw [e]
    constructor <;> linarith
  · intro z _ z' _ hzz
    simp only [Prod.mk.injEq] at hzz
    exact Prod.ext hzz.1 (Prod.ext hzz.2.1 (by omega))

private lemma shift_central (h : ℕ) (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hc2 : 2 * c < a + b + c) (ht : t < (h : ℝ) * c) :
    ∃ t' : ℝ, (h : ℝ) * c ≤ t' ∧ t' ≤ ((h : ℝ) + 1) * (a + b + c) - (h : ℝ) * c ∧
      cutCount (h + 1) a b c t ≤ cutCount (h + 1) a b c t' := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌈((h : ℝ) * c - t) / c⌉₊ := ⟨_, rfl⟩
  have hx0 : 0 ≤ ((h : ℝ) * c - t) / c := div_nonneg (by linarith) hc.le
  have hj1 : ((h : ℝ) * c - t) / c ≤ (j : ℝ) := by rw [hj]; exact Nat.le_ceil _
  have hj2 : (j : ℝ) < ((h : ℝ) * c - t) / c + 1 := by rw [hj]; exact Nat.ceil_lt_add_one hx0
  rw [div_le_iff₀ hc] at hj1
  have hj2' : ((j : ℝ) - 1) * c < (h : ℝ) * c - t := by
    have : (j : ℝ) - 1 < ((h : ℝ) * c - t) / c := by linarith
    rwa [lt_div_iff₀ hc] at this
  have hup : t + (j : ℝ) * c < ((h + 1 : ℕ) : ℝ) * c := by push_cast; linarith
  refine ⟨t + (j : ℝ) * c, by linarith, ?_, shift_le (h + 1) a b c t j ha.le hb.le hc hup⟩
  have : ((h : ℝ) + 1) * (a + b + c - 2 * c) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- **U(2) (`exists_central`):** Any offset `t` can be replaced by a central offset
`h c ≤ t' ≤ (h + 1) W - h c` without decreasing `cutCount`. -/
theorem exists_central (h : ℕ) (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hc2 : 2 * c < a + b + c) :
    ∃ t' : ℝ, (h : ℝ) * c ≤ t' ∧ t' ≤ ((h : ℝ) + 1) * (a + b + c) - (h : ℝ) * c ∧
      cutCount (h + 1) a b c t ≤ cutCount (h + 1) a b c t' := by
  by_cases hlo : t < (h : ℝ) * c
  · exact shift_central h a b c t ha hb hc hc2 hlo
  push Not at hlo
  by_cases hhi : ((h : ℝ) + 1) * (a + b + c) - (h : ℝ) * c < t
  · have e := cutCount_mirror (h + 1) a b c t
    have hlo' : ((h + 1 : ℕ) : ℝ) * (a + b + c) - t < (h : ℝ) * c := by push_cast; linarith
    obtain ⟨t', h1, h2, h3⟩ := shift_central h a b c _ ha hb hc hc2 hlo'
    exact ⟨t', h1, h2, by rw [e]; exact h3⟩
  push Not at hhi
  exact ⟨t, hlo, hhi, le_refl _⟩

private def psiY (h y : ℝ) : ℝ :=
  if 0 < 2 * h - (h + 1) * y then (2 * h - (h + 1) * y) ^ 2 + (2 * h - (h + 1) * y)
  else 0

private lemma tangent_le_psiY (h y : ℝ) (hh : 3 ≤ h) (hy : 1 ≤ y) :
    Acoef h + Bcoef h * (2 / 3 - 1 / y) ≤ psiY h y := by
  unfold psiY
  split_ifs with hp
  · exact tangent_pos h y hh hy
  · push Not at hp; exact tangent_neg h y hh (by linarith)

private lemma pair_psi (h s r t Ca Cb : ℝ) (hs : 0 < s) (_hr : 0 < r)
    (h0a : 0 ≤ Ca) (h0b : 0 ≤ Cb)
    (ha : 0 < s * h - t → 2 * (s * h - t) ^ 2 / s ^ 2 + (s * h - t) / s ≤ Ca)
    (hb : 0 < t - h * r - (s + r) →
      2 * (t - h * r - (s + r)) ^ 2 / s ^ 2 + (t - h * r - (s + r)) / s ≤ Cb) :
    psiY h ((s + r) / s) ≤ Ca + Cb := by
  have hs' : s ≠ 0 := ne_of_gt hs
  obtain ⟨ua, hua⟩ : ∃ ua : ℝ, ua = (s * h - t) / s := ⟨_, rfl⟩
  obtain ⟨ub, hub⟩ : ∃ ub : ℝ, ub = (t - h * r - (s + r)) / s := ⟨_, rfl⟩
  have hrho : ua + ub = 2 * h - (h + 1) * ((s + r) / s) := by
    rw [hua, hub]; field_simp; ring
  have ea : 0 < ua → 2 * ua ^ 2 + ua ≤ Ca := by
    intro hu
    have hpos : 0 < s * h - t := by
      have := mul_pos hu hs; rwa [hua, div_mul_cancel₀ _ hs'] at this
    have := ha hpos
    have e : 2 * (s * h - t) ^ 2 / s ^ 2 + (s * h - t) / s = 2 * ua ^ 2 + ua := by rw [hua]; ring
    linarith
  have eb : 0 < ub → 2 * ub ^ 2 + ub ≤ Cb := by
    intro hu
    have hpos : 0 < t - h * r - (s + r) := by
      have := mul_pos hu hs; rwa [hub, div_mul_cancel₀ _ hs'] at this
    have := hb hpos
    have e : 2 * (t - h * r - (s + r)) ^ 2 / s ^ 2 + (t - h * r - (s + r)) / s =
        2 * ub ^ 2 + ub := by rw [hub]; ring
    linarith
  unfold psiY
  rw [← hrho]
  split_ifs with hpos
  · exact psi_lb Ca Cb ua ub h0a h0b ea eb hpos
  · linarith

private lemma central_psi (h : ℕ) (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hac : a ≤ c) (hbc : b ≤ c)
    (ht1 : (h : ℝ) * c ≤ t) (ht2 : t ≤ ((h : ℝ) + 1) * (a + b + c) - (h : ℝ) * c) :
    (cutCount (h + 1) a b c t : ℝ) +
      (psiY (h : ℝ) ((b + c + a) / (b + c)) + psiY (h : ℝ) ((a + c + b) / (a + c)) +
        psiY (h : ℝ) ((a + b + c) / (a + b))) + (h : ℝ) ^ 3 ≤ ((h : ℝ) + 1) ^ 3 := by
  have hW : 0 < a + b + c := by linarith
  have L : (cutCount (h + 1) a b c t : ℝ) +
      (((tri b c ((b + c) * (h : ℝ) - t) h).card : ℝ) +
        ((tri b c (t - (h : ℝ) * a - (b + c + a)) h).card : ℝ)) +
      (((tri a c ((a + c) * (h : ℝ) - t) h).card : ℝ) +
        ((tri a c (t - (h : ℝ) * b - (a + c + b)) h).card : ℝ)) +
      (((tri a b ((a + b) * (h : ℝ) - t) h).card : ℝ) +
        ((tri a b (t - (h : ℝ) * c - (a + b + c)) h).card : ℝ)) + (h : ℝ) ^ 3 ≤
      ((h : ℝ) + 1) ^ 3 := by
    exact_mod_cast lemmaT_le h a b c t ha.le hb.le hc.le hW
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have hhb : (h : ℝ) * b ≤ (h : ℝ) * c := mul_le_mul_of_nonneg_left hbc hh0
  have hha : (h : ℝ) * a ≤ (h : ℝ) * c := mul_le_mul_of_nonneg_left hac hh0
  have P1 := pair_psi (h : ℝ) (b + c) a t
    ((tri b c ((b + c) * (h : ℝ) - t) h).card : ℝ)
    ((tri b c (t - (h : ℝ) * a - (b + c + a)) h).card : ℝ) (by linarith) ha
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (fun hp => tri_lb_sym b c _ h hb hc hp (by linarith) (by linarith))
    (fun hp => tri_lb_sym b c _ h hb hc hp (by linarith) (by linarith))
  have P2 := pair_psi (h : ℝ) (a + c) b t
    ((tri a c ((a + c) * (h : ℝ) - t) h).card : ℝ)
    ((tri a c (t - (h : ℝ) * b - (a + c + b)) h).card : ℝ) (by linarith) hb
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (fun hp => tri_lb_sym a c _ h ha hc hp (by linarith) (by linarith))
    (fun hp => tri_lb_sym a c _ h ha hc hp (by linarith) (by linarith))
  have P3 := pair_psi (h : ℝ) (a + b) c t
    ((tri a b ((a + b) * (h : ℝ) - t) h).card : ℝ)
    ((tri a b (t - (h : ℝ) * c - (a + b + c)) h).card : ℝ) (by linarith) hc
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (fun hp => tri_lb_sym a b _ h ha hb hp (by linarith) (by linarith))
    (fun hp => tri_lb_sym a b _ h ha hb hp (by linarith) (by linarith))
  linarith

private lemma gap_small (h y : ℝ) (hh : 15 ≤ h) (hy : 1 ≤ y)
    (hg : psiY h y - (Acoef h + Bcoef h * (2 / 3 - 1 / y)) ≤ (h + 1) / 2) :
    2 / 3 - 1 / y ≤ 0 ∨ (2 / 3 - 1 / y) ^ 2 ≤ 8 / (27 * (h + 1 + 6)) := by
  have hy0 : 0 < y := by linarith
  have hy' : y ≠ 0 := ne_of_gt hy0
  unfold psiY at hg
  split_ifs at hg with hp
  · by_contra hcon
    push Not at hcon
    obtain ⟨he, he2⟩ := hcon
    have hy32 : 3 < 2 * y := by
      have h1 : 1 / y < 2 / 3 := by linarith
      rw [div_lt_iff₀ hy0] at h1; linarith
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 * y - 3 := ⟨_, rfl⟩
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (h + 1) * y - h + 2 := ⟨_, rfl⟩
    have key : (2 * h - (h + 1) * y) ^ 2 + (2 * h - (h + 1) * y) -
        (Acoef h + Bcoef h * (2 / 3 - 1 / y)) =
        (h + 1) * (2 * y - 3) ^ 2 * ((h + 1) * y - h + 2) / (4 * y) := by
      unfold Acoef Bcoef; field_simp; ring
    have heps : 2 / 3 - 1 / y = (2 * y - 3) / (3 * y) := by
      rw [eq_div_iff (mul_ne_zero (by norm_num) hy')]; field_simp
    rw [key, ← hu, ← hP, div_le_iff₀ (by linarith : (0 : ℝ) < 4 * y)] at hg
    rw [heps, ← hu, div_pow,
      div_lt_div_iff₀ (by linarith : (0 : ℝ) < 27 * (h + 1 + 6)) (pow_pos (by linarith) 2)]
      at he2
    have F1 : 3 * (h + 7) ≤ 4 * y * P := by
      have e : 4 * y * P - 3 * (h + 7) = u * (2 * (h + 1) * y + h + 7) := by rw [hu, hP]; ring
      have q : 0 ≤ u * (2 * (h + 1) * y + h + 7) :=
        mul_nonneg (by linarith) (by nlinarith)
      linarith
    have F3 : u ^ 2 * P ≤ 2 * y := by
      by_contra hc'; push Not at hc'
      have := mul_lt_mul_of_pos_left hc' (by linarith : (0 : ℝ) < h + 1); linarith
    have G1 : u ^ 2 * (3 * (h + 7)) ≤ u ^ 2 * (4 * y * P) :=
      mul_le_mul_of_nonneg_left F1 (sq_nonneg u)
    have G2 : (4 * y) * (u ^ 2 * P) ≤ (4 * y) * (2 * y) :=
      mul_le_mul_of_nonneg_left F3 (by linarith)
    linarith [G1, G2, he2]
  · exfalso
    push Not at hp
    have hYpos : 0 < (h + 1) * y := mul_pos (by linarith) hy0
    have key : (Acoef h + Bcoef h * (2 / 3 - 1 / y)) * ((h + 1) * y) =
        -(5 * h ^ 2 - 2 * h - 15) / 4 * ((h + 1) * y - 2 * h) -
          (h - 3) ^ 2 * (h + 2) / 4 := by
      unfold Acoef Bcoef; field_simp; ring
    have hg' : -(Acoef h + Bcoef h * (2 / 3 - 1 / y)) * ((h + 1) * y) ≤
        (h + 1) / 2 * ((h + 1) * y) :=
      mul_le_mul_of_nonneg_right (by linarith) hYpos.le
    have q1 : 0 ≤ (5 * h ^ 2 - 4 * h - 17) * ((h + 1) * y - 2 * h) :=
      mul_nonneg (by nlinarith) (by linarith)
    have q2 : 4 * h * (h + 1) < (h - 3) ^ 2 * (h + 2) := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ h) (by linarith : (0 : ℝ) ≤ h))
        (by linarith : (0 : ℝ) ≤ h - 15),
        mul_nonneg (by linarith : (0 : ℝ) ≤ h) (by linarith : (0 : ℝ) ≤ h - 1)]
    have e : -(Acoef h + Bcoef h * (2 / 3 - 1 / y)) * ((h + 1) * y) =
        -((Acoef h + Bcoef h * (2 / 3 - 1 / y)) * ((h + 1) * y)) := by ring
    rw [e, key] at hg'
    linarith [hg', q1, q2]

/-- The cone radius `r(n) = √(8 / (27 (n + 6)))`. -/
def rad (n : ℕ) : ℝ := Real.sqrt (8 / (27 * ((n : ℝ) + 6)))

lemma rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad
  exact Real.sqrt_pos.2 (by positivity)

lemma rad_sq (n : ℕ) : (rad n) ^ 2 = 8 / (27 * ((n : ℝ) + 6)) := by
  unfold rad
  exact Real.sq_sqrt (by positivity)

/-- **Corollary U2 (sorted cone bound):** For `n = h + 1 ≥ 16`, if `0 ≤ a ≤ b ≤ c` with `0 < c`
and `F(n) ≤ cutCount n a b c t`, then `c < a + b` and `c / (a + b + c) - 1/3 ≤ rad n`. -/
theorem u2_sorted_cone (h : ℕ) (hh : 15 ≤ h) (a b c t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 < c) (hac : a ≤ c) (hbc : b ≤ c) (hF : F (h + 1) ≤ cutCount (h + 1) a b c t) :
    c < a + b ∧ c / (a + b + c) - 1 / 3 ≤ rad (h + 1) := by
  have hcol : c < a + b := by
    by_contra hcon
    push Not at hcon
    have := column_bound (h + 1) a b c t ha hb hc hcon
    unfold F at hF
    omega
  refine ⟨hcol, ?_⟩
  have ha' : 0 < a := by linarith
  have hb' : 0 < b := by linarith
  have hc2 : 2 * c < a + b + c := by linarith
  have hW : 0 < a + b + c := by linarith
  have hW' : a + b + c ≠ 0 := ne_of_gt hW
  obtain ⟨t', ht1, ht2, hle⟩ := exists_central h a b c t ha' hb' hc hc2
  have hF' : F (h + 1) ≤ cutCount (h + 1) a b c t' := le_trans hF hle
  have hP := central_psi h a b c t' ha' hb' hc hac hbc ht1 ht2
  have hF4 : 9 * ((h : ℝ) + 1) ^ 2 + 4 * ((h : ℝ) + 1) ≤
      4 * (cutCount (h + 1) a b c t' : ℝ) + 20 := by
    have hn : 9 * (h + 1) ^ 2 + 4 * (h + 1) ≤ 4 * cutCount (h + 1) a b c t' + 20 := by
      unfold F at hF'; omega
    exact_mod_cast hn
  have hh15 : (15 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hy1 : 1 ≤ (b + c + a) / (b + c) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hy2 : 1 ≤ (a + c + b) / (a + c) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hy3 : 1 ≤ (a + b + c) / (a + b) := by rw [le_div_iff₀ (by linarith)]; linarith
  have T1 := tangent_le_psiY (h : ℝ) _ (by linarith) hy1
  have T2 := tangent_le_psiY (h : ℝ) _ (by linarith) hy2
  have T3 := tangent_le_psiY (h : ℝ) _ (by linarith) hy3
  have e1 : 2 / 3 - 1 / ((b + c + a) / (b + c)) = a / (a + b + c) - 1 / 3 := by
    rw [one_div_div, show b + c + a = a + b + c by ring]
    have : (b + c) / (a + b + c) + a / (a + b + c) = 1 := by
      rw [← add_div, show b + c + a = a + b + c by ring, div_self hW']
    linarith
  have e2 : 2 / 3 - 1 / ((a + c + b) / (a + c)) = b / (a + b + c) - 1 / 3 := by
    rw [one_div_div, show a + c + b = a + b + c by ring]
    have : (a + c) / (a + b + c) + b / (a + b + c) = 1 := by
      rw [← add_div, show a + c + b = a + b + c by ring, div_self hW']
    linarith
  have e3 : 2 / 3 - 1 / ((a + b + c) / (a + b)) = c / (a + b + c) - 1 / 3 := by
    rw [one_div_div]
    have : (a + b) / (a + b + c) + c / (a + b + c) = 1 := by rw [← add_div, div_self hW']
    linarith
  have hsum : a / (a + b + c) - 1 / 3 + (b / (a + b + c) - 1 / 3) +
      (c / (a + b + c) - 1 / 3) = 0 := by
    have : a / (a + b + c) + b / (a + b + c) + c / (a + b + c) = 1 := by
      rw [← add_div, ← add_div, div_self hW']
    linarith
  have hBs : Bcoef (h : ℝ) * (2 / 3 - 1 / ((b + c + a) / (b + c))) +
      Bcoef (h : ℝ) * (2 / 3 - 1 / ((a + c + b) / (a + c))) +
      Bcoef (h : ℝ) * (2 / 3 - 1 / ((a + b + c) / (a + b))) = 0 := by
    rw [e1, e2, e3]
    have e : Bcoef (h : ℝ) * (a / (a + b + c) - 1 / 3) +
        Bcoef (h : ℝ) * (b / (a + b + c) - 1 / 3) +
        Bcoef (h : ℝ) * (c / (a + b + c) - 1 / 3) =
        Bcoef (h : ℝ) * (a / (a + b + c) - 1 / 3 + (b / (a + b + c) - 1 / 3) +
          (c / (a + b + c) - 1 / 3)) := by ring
    rw [e, hsum, mul_zero]
  have hA : Acoef (h : ℝ) = ((h : ℝ) - 1) * ((h : ℝ) - 3) / 4 := by unfold Acoef; ring
  have G3 : psiY (h : ℝ) ((a + b + c) / (a + b)) -
      (Acoef (h : ℝ) + Bcoef (h : ℝ) * (2 / 3 - 1 / ((a + b + c) / (a + b)))) ≤
      ((h : ℝ) + 1) / 2 := by
    rw [hA] at T1 T2 T3 ⊢; linarith
  have U3 := gap_small (h : ℝ) _ hh15 hy3 G3
  rw [e3] at U3
  rcases U3 with hle0 | hsq
  · exact le_trans hle0 (rad_pos (h + 1)).le
  · have hrad_sq : (rad (h + 1)) ^ 2 = 8 / (27 * ((h : ℝ) + 1 + 6)) := by
      rw [rad_sq]; push_cast; ring
    rw [← hrad_sq] at hsq
    nlinarith [rad_pos (h + 1)]

/-- **Theorem U (`theoremU_bound`):** For every `n ≥ 16`, every nonzero real plane cuts at most
`Ubound n = ⌊(9n² + 6n - 20)/4⌋` cubes. -/
theorem theoremU_bound (n : ℕ) (hn : 16 ≤ n) (a b c t : ℝ) (hv : IsNormal a b c) :
    cutCount n a b c t ≤ Ubound n := by
  obtain ⟨a', b', c', t', ha, hab, hbc, hsum, heq⟩ := wlog_ordered_nonneg n a b c t hv
  rw [heq]
  obtain ⟨h, rfl⟩ : ∃ h : ℕ, n = h + 1 := ⟨n - 1, by omega⟩
  have hh : 15 ≤ h := by omega
  have hc : 0 < c' := by linarith
  by_cases hcol : a' + b' ≤ c'
  · have := column_bound (h + 1) a' b' c' t' ha (by linarith) hc hcol
    unfold Ubound; omega
  push Not at hcol
  have ha' : 0 < a' := by linarith
  have hb' : 0 < b' := by linarith
  have hc2 : 2 * c' < a' + b' + c' := by linarith
  obtain ⟨t1, ht1, ht2, hle⟩ := exists_central h a' b' c' t' ha' hb' hc hc2
  have hP := central_psi h a' b' c' t1 ha' hb' hc (by linarith) hbc ht1 ht2
  have hy1 : 1 ≤ (b' + c' + a') / (b' + c') := by rw [le_div_iff₀ (by linarith)]; linarith
  have hy2 : 1 ≤ (a' + c' + b') / (a' + c') := by rw [le_div_iff₀ (by linarith)]; linarith
  have hy3 : 1 ≤ (a' + b' + c') / (a' + b') := by rw [le_div_iff₀ (by linarith)]; linarith
  have hh3 : (3 : ℝ) ≤ (h : ℝ) := by exact_mod_cast (show 3 ≤ h by omega)
  have T1 := tangent_le_psiY (h : ℝ) _ hh3 hy1
  have T2 := tangent_le_psiY (h : ℝ) _ hh3 hy2
  have T3 := tangent_le_psiY (h : ℝ) _ hh3 hy3
  have e1 : 2 / 3 - 1 / ((b' + c' + a') / (b' + c')) = a' - 1 / 3 := by
    rw [one_div_div, show b' + c' + a' = 1 by linarith]; linarith
  have e2 : 2 / 3 - 1 / ((a' + c' + b') / (a' + c')) = b' - 1 / 3 := by
    rw [one_div_div, show a' + c' + b' = 1 by linarith]; linarith
  have e3 : 2 / 3 - 1 / ((a' + b' + c') / (a' + b')) = c' - 1 / 3 := by
    rw [one_div_div, show a' + b' + c' = 1 by linarith]; linarith
  rw [e1] at T1; rw [e2] at T2; rw [e3] at T3
  have hBs : Bcoef (h : ℝ) * (a' - 1 / 3) + Bcoef (h : ℝ) * (b' - 1 / 3) +
      Bcoef (h : ℝ) * (c' - 1 / 3) = 0 := by
    have : a' - 1 / 3 + (b' - 1 / 3) + (c' - 1 / 3) = 0 := by linarith
    calc Bcoef (h : ℝ) * (a' - 1 / 3) + Bcoef (h : ℝ) * (b' - 1 / 3) +
          Bcoef (h : ℝ) * (c' - 1 / 3)
        = Bcoef (h : ℝ) * ((a' - 1 / 3) + (b' - 1 / 3) + (c' - 1 / 3)) := by ring
      _ = 0 := by rw [this, mul_zero]
  have hA : Acoef (h : ℝ) = ((h : ℝ) - 1) * ((h : ℝ) - 3) / 4 := by unfold Acoef; ring
  rw [hA] at T1 T2 T3
  have hreal : 4 * (cutCount (h + 1) a' b' c' t1 : ℝ) ≤ 9 * (h : ℝ) ^ 2 + 24 * (h : ℝ) - 5 := by
    linarith
  have hnat : 4 * cutCount (h + 1) a' b' c' t1 + 5 ≤ 9 * h ^ 2 + 24 * h := by
    have : ((4 * cutCount (h + 1) a' b' c' t1 + 5 : ℕ) : ℝ) ≤
        ((9 * h ^ 2 + 24 * h : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hU : 9 * (h + 1) ^ 2 + 6 * (h + 1) - 20 = 9 * h ^ 2 + 24 * h - 5 := by
    have : 20 ≤ 9 * (h + 1) ^ 2 + 6 * (h + 1) := by nlinarith
    have : 5 ≤ 9 * h ^ 2 + 24 * h := by nlinarith
    zify [‹20 ≤ _›, ‹5 ≤ _›]; ring
  unfold Ubound
  omega

/-! ### Cone coordinates `(u, w)` and Reduction R -/

/-- Normalized sorted normal coordinates parameterized by `(u, w)`. -/
def x1 (u w : ℝ) : ℝ := (1 - 2 * u - w) / 3
def x2 (u w : ℝ) : ℝ := (1 + u - w) / 3
def x3 (u w : ℝ) : ℝ := (1 + u + 2 * w) / 3

/-- Pair weight sums `s_k = 1 - x_k`. -/
def s1 (u w : ℝ) : ℝ := 1 - x1 u w
def s2 (u w : ℝ) : ℝ := 1 - x2 u w
def s3 (u w : ℝ) : ℝ := 1 - x3 u w

/-- The six triangle thresholds `α_k = (1 - x_k) h - t` and `β_k = t - h x_k - 1` (`h = n - 1`). -/
def alpha1 (n : ℕ) (u w t : ℝ) : ℝ := s1 u w * ((n - 1 : ℕ) : ℝ) - t
def beta1  (n : ℕ) (u w t : ℝ) : ℝ := t - ((n - 1 : ℕ) : ℝ) * x1 u w - 1
def alpha2 (n : ℕ) (u w t : ℝ) : ℝ := s2 u w * ((n - 1 : ℕ) : ℝ) - t
def beta2  (n : ℕ) (u w t : ℝ) : ℝ := t - ((n - 1 : ℕ) : ℝ) * x2 u w - 1
def alpha3 (n : ℕ) (u w t : ℝ) : ℝ := s3 u w * ((n - 1 : ℕ) : ℝ) - t
def beta3  (n : ℕ) (u w t : ℝ) : ℝ := t - ((n - 1 : ℕ) : ℝ) * x3 u w - 1

/-- Total number of lattice points in the six triangles for direction `(u, w)` and offset `t`. -/
def missedCount (n : ℕ) (u w t : ℝ) : ℕ :=
  (Delta (x2 u w) (x3 u w) (alpha1 n u w t) + Delta (x2 u w) (x3 u w) (beta1 n u w t)) +
  (Delta (x1 u w) (x3 u w) (alpha2 n u w t) + Delta (x1 u w) (x3 u w) (beta2 n u w t)) +
  (Delta (x1 u w) (x2 u w) (alpha3 n u w t) + Delta (x1 u w) (x2 u w) (beta3 n u w t))

/-- Perturbation lemma: since meeting finitely many open cubes is an open condition,
any positive normal `0 < a ≤ b ≤ c` can be strictly separated to `0 < a < b' < c'`
without decreasing `cutCount`. -/
theorem perturb_strict_ordered (n : ℕ) (a b c t : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ ε : ℝ, 0 < ε ∧ cutCount n a b c t ≤ cutCount n a (b + ε) (c + 3 * ε) t := by
  by_cases hne : (cutSet n a b c t).Nonempty
  · let δ : ℝ := (cutSet n a b c t).inf' hne (fun z => t - dot a b c z)
    have hδ : 0 < δ := by
      rw [Finset.lt_inf'_iff]
      intro z hz
      have hm := (meets_iff_nonneg ha.le (by linarith) (by linarith) (by linarith) z).1
        (mem_cutSet.1 hz).2
      linarith [hm.1]
    let ε : ℝ := δ / (4 * (n : ℝ) + 1)
    have hε : 0 < ε := div_pos hδ (by positivity)
    refine ⟨ε, hε, ?_⟩
    unfold cutCount
    apply Finset.card_le_card
    intro z hz
    have hz' := mem_cutSet.1 hz
    have hzc := mem_cells.1 hz'.1
    have hm := (meets_iff_nonneg ha.le (by linarith) (by linarith) (by linarith) z).1 hz'.2
    refine mem_cutSet.2 ⟨hz'.1, ?_⟩
    rw [meets_iff_nonneg ha.le (by linarith) (by linarith) (by linarith)]
    have hδz : δ ≤ t - dot a b c z := Finset.inf'_le (fun z => t - dot a b c z) hz
    have hy : (z.2.1 : ℝ) < (n : ℝ) := by exact_mod_cast hzc.2.1
    have hw : (z.2.2 : ℝ) < (n : ℝ) := by exact_mod_cast hzc.2.2
    have hdot : dot a (b + ε) (c + 3 * ε) z =
        dot a b c z + ε * ((z.2.1 : ℝ) + 3 * (z.2.2 : ℝ)) := by
      unfold dot; ring
    have hsmall : ε * ((z.2.1 : ℝ) + 3 * (z.2.2 : ℝ)) < δ := by
      have hbd : (z.2.1 : ℝ) + 3 * (z.2.2 : ℝ) < 4 * (n : ℝ) + 1 := by linarith
      calc ε * ((z.2.1 : ℝ) + 3 * (z.2.2 : ℝ))
          < ε * (4 * (n : ℝ) + 1) := mul_lt_mul_of_pos_left hbd hε
        _ = δ := div_mul_cancel₀ δ (by positivity)
    have hnn : 0 ≤ ε * ((z.2.1 : ℝ) + 3 * (z.2.2 : ℝ)) :=
      mul_nonneg hε.le (by positivity)
    constructor <;> linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨1, zero_lt_one, ?_⟩
    unfold cutCount
    rw [hne, Finset.card_empty]
    exact Nat.zero_le _

/-- **Reduction R (`reduction_R`):** Unconditional over `ℝ` for every `n ≥ 16`:
if `missedCount n u w t ≥ D(n)` holds for all `u > 0, w > 0` with `u + 2w ≤ 3 r(n)`
and all real `t`, then EVERY nonzero real plane cuts at most `F(n)` open unit cubes. -/
theorem reduction_R (n : ℕ) (hn : 16 ≤ n)
    (hstar : ∀ u w t : ℝ, 0 < u → 0 < w → u + 2 * w ≤ 3 * rad n →
      D n ≤ missedCount n u w t) :
    ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n := by
  intro a b c t hv
  by_contra hgt
  push Not at hgt
  obtain ⟨h, rfl⟩ : ∃ h : ℕ, n = h + 1 := ⟨n - 1, by omega⟩
  have hh : 15 ≤ h := by omega
  obtain ⟨a1, b1, c1, t1, ha1, hab1, hbc1, hsum1, heq1⟩ := wlog_ordered_nonneg (h + 1) a b c t hv
  rw [heq1] at hgt
  have hc1_pos : 0 < c1 := by linarith
  have hcol1 : c1 < a1 + b1 := (u2_sorted_cone h hh a1 b1 c1 t1 ha1 (by linarith) hc1_pos
    (by linarith) hbc1 hgt.le).1
  have ha1_pos : 0 < a1 := by linarith
  obtain ⟨ε, hε, hpert⟩ := perturb_strict_ordered (h + 1) a1 b1 c1 t1 ha1_pos hab1 hbc1
  have hgt2 : F (h + 1) < cutCount (h + 1) a1 (b1 + ε) (c1 + 3 * ε) t1 :=
    lt_of_lt_of_le hgt hpert
  let W : ℝ := a1 + (b1 + ε) + (c1 + 3 * ε)
  have hW : 0 < W := by dsimp [W]; linarith
  let p1 : ℝ := a1 / W
  let p2 : ℝ := (b1 + ε) / W
  let p3 : ℝ := (c1 + 3 * ε) / W
  let t2 : ℝ := t1 / W
  have hscale : cutCount (h + 1) p1 p2 p3 t2 =
      cutCount (h + 1) a1 (b1 + ε) (c1 + 3 * ε) t1 := by
    have hinv : W⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hW)
    have hsc := cutCount_scale (n := h + 1) (a := a1) (b := b1 + ε) (c := c1 + 3 * ε)
      (t := t1) (lam := W⁻¹) hinv
    simpa [p1, p2, p3, t2, div_eq_inv_mul] using hsc
  rw [← hscale] at hgt2
  have hp1 : 0 < p1 := div_pos ha1_pos hW
  have hp12 : p1 < p2 := div_lt_div_of_pos_right (by linarith) hW
  have hp23 : p2 < p3 := div_lt_div_of_pos_right (by linarith) hW
  have hp_sum : p1 + p2 + p3 = 1 := by
    dsimp [p1, p2, p3]
    rw [← add_div, ← add_div]
    exact div_self (ne_of_gt hW)
  have hu2 := u2_sorted_cone h hh p1 p2 p3 t2 hp1.le (by linarith) (by linarith)
    (by linarith) hp23.le hgt2.le
  have hcol2 : 2 * p3 < p1 + p2 + p3 := by linarith [hu2.1]
  obtain ⟨t3, ht3_lo, ht3_hi, hcen⟩ :=
    exists_central h p1 p2 p3 t2 hp1 (by linarith) (by linarith) hcol2
  have hgt3 : F (h + 1) < cutCount (h + 1) p1 p2 p3 t3 := lt_of_lt_of_le hgt2 hcen
  let u : ℝ := p2 - p1
  let w : ℝ := p3 - p2
  have hu_pos : 0 < u := by dsimp [u]; linarith
  have hw_pos : 0 < w := by dsimp [w]; linarith
  have hx1 : x1 u w = p1 := by unfold x1; dsimp [u, w]; linarith
  have hx2 : x2 u w = p2 := by unfold x2; dsimp [u, w]; linarith
  have hx3 : x3 u w = p3 := by unfold x3; dsimp [u, w]; linarith
  have hcone : u + 2 * w ≤ 3 * rad (h + 1) := by
    have h3 : p3 / (p1 + p2 + p3) - 1 / 3 ≤ rad (h + 1) := hu2.2
    rw [hp_sum, div_one] at h3
    dsimp [u, w]
    linarith
  have hmiss : D (h + 1) ≤ missedCount (h + 1) u w t3 := hstar u w t3 hu_pos hw_pos hcone
  have hT := lemmaT_le h p1 p2 p3 t3 hp1.le (by linarith) (by linarith) (by linarith)
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have hp2_pos : 0 < p2 := by linarith
  have hp3_pos : 0 < p3 := by linarith
  -- Because `t3` is central, every bounded triangle `tri` equals the unbounded triangle `triNat`
  have ht3_hi' : t3 ≤ (h : ℝ) + 1 - (h : ℝ) * p3 := by rw [hp_sum, mul_one] at ht3_hi; exact ht3_hi
  have hp1_le_p2 : (h : ℝ) * p1 ≤ (h : ℝ) * p2 := mul_le_mul_of_nonneg_left hp12.le hh0
  have hp2_le_p3 : (h : ℝ) * p2 ≤ (h : ℝ) * p3 := mul_le_mul_of_nonneg_left hp23.le hh0
  have hp1_le_p3 : (h : ℝ) * p1 ≤ (h : ℝ) * p3 := le_trans hp1_le_p2 hp2_le_p3
  have eqA1 : tri p2 p3 ((p2 + p3) * (h : ℝ) - t3) h = triNat (x2 u w) (x3 u w) (alpha1 (h + 1) u w t3) := by
    rw [hx2, hx3]
    have ha_eq : alpha1 (h + 1) u w t3 = (p2 + p3) * (h : ℝ) - t3 := by
      unfold alpha1 s1; rw [hx1]; simp only [Nat.add_sub_cancel]
      have : 1 - p1 = p2 + p3 := by linarith
      rw [this]
    rw [ha_eq]
    exact tri_eq_triNat hp2_pos hp3_pos (by linarith) (by linarith)
  have eqB1 : tri p2 p3 (t3 - (h : ℝ) * p1 - (p2 + p3 + p1)) h =
      triNat (x2 u w) (x3 u w) (beta1 (h + 1) u w t3) := by
    rw [hx2, hx3]
    have hb_eq : beta1 (h + 1) u w t3 = t3 - (h : ℝ) * p1 - (p2 + p3 + p1) := by
      unfold beta1; rw [hx1]; simp only [Nat.add_sub_cancel]; linarith
    rw [hb_eq]
    have hsum_h : (h : ℝ) * p1 + (h : ℝ) * p2 + (h : ℝ) * p3 = (h : ℝ) := by
      calc (h : ℝ) * p1 + (h : ℝ) * p2 + (h : ℝ) * p3 = (h : ℝ) * (p1 + p2 + p3) := by ring
        _ = (h : ℝ) := by rw [hp_sum, mul_one]
    exact tri_eq_triNat hp2_pos hp3_pos (by linarith) (by linarith)
  have eqA2 : tri p1 p3 ((p1 + p3) * (h : ℝ) - t3) h = triNat (x1 u w) (x3 u w) (alpha2 (h + 1) u w t3) := by
    rw [hx1, hx3]
    have ha_eq : alpha2 (h + 1) u w t3 = (p1 + p3) * (h : ℝ) - t3 := by
      unfold alpha2 s2; rw [hx2]; simp only [Nat.add_sub_cancel]
      have : 1 - p2 = p1 + p3 := by linarith
      rw [this]
    rw [ha_eq]
    exact tri_eq_triNat hp1 hp3_pos (by linarith) (by linarith)
  have eqB2 : tri p1 p3 (t3 - (h : ℝ) * p2 - (p1 + p3 + p2)) h =
      triNat (x1 u w) (x3 u w) (beta2 (h + 1) u w t3) := by
    rw [hx1, hx3]
    have hb_eq : beta2 (h + 1) u w t3 = t3 - (h : ℝ) * p2 - (p1 + p3 + p2) := by
      unfold beta2; rw [hx2]; simp only [Nat.add_sub_cancel]; linarith
    rw [hb_eq]
    have hsum_h : (h : ℝ) * p1 + (h : ℝ) * p2 + (h : ℝ) * p3 = (h : ℝ) := by
      calc (h : ℝ) * p1 + (h : ℝ) * p2 + (h : ℝ) * p3 = (h : ℝ) * (p1 + p2 + p3) := by ring
        _ = (h : ℝ) := by rw [hp_sum, mul_one]
    exact tri_eq_triNat hp1 hp3_pos (by linarith) (by linarith)
  have eqA3 : tri p1 p2 ((p1 + p2) * (h : ℝ) - t3) h = triNat (x1 u w) (x2 u w) (alpha3 (h + 1) u w t3) := by
    rw [hx1, hx2]
    have ha_eq : alpha3 (h + 1) u w t3 = (p1 + p2) * (h : ℝ) - t3 := by
      unfold alpha3 s3; rw [hx3]; simp only [Nat.add_sub_cancel]
      have : 1 - p3 = p1 + p2 := by linarith
      rw [this]
    rw [ha_eq]
    exact tri_eq_triNat hp1 hp2_pos (by linarith) (by linarith)
  have eqB3 : tri p1 p2 (t3 - (h : ℝ) * p3 - (p1 + p2 + p3)) h =
      triNat (x1 u w) (x2 u w) (beta3 (h + 1) u w t3) := by
    rw [hx1, hx2]
    have hb_eq : beta3 (h + 1) u w t3 = t3 - (h : ℝ) * p3 - (p1 + p2 + p3) := by
      unfold beta3; rw [hx3]; simp only [Nat.add_sub_cancel]; linarith
    rw [hb_eq]
    have hsum_h : (h : ℝ) * p1 + (h : ℝ) * p2 + (h : ℝ) * p3 = (h : ℝ) := by
      calc (h : ℝ) * p1 + (h : ℝ) * p2 + (h : ℝ) * p3 = (h : ℝ) * (p1 + p2 + p3) := by ring
        _ = (h : ℝ) := by rw [hp_sum, mul_one]
    exact tri_eq_triNat hp1 hp2_pos (by linarith) (by linarith)
  rw [eqA1, eqB1, eqA2, eqB2, eqA3, eqB3] at hT
  have hcube : (h + 1) ^ 3 - h ^ 3 = 3 * (h + 1) ^ 2 - 3 * (h + 1) + 1 := by
    have h1 : h ^ 3 ≤ (h + 1) ^ 3 := by nlinarith
    have h2 : 3 * (h + 1) ≤ 3 * (h + 1) ^ 2 := by nlinarith
    zify [h1, h2]; ring
  have hF_le := F_le_diag (h + 1) (by omega)
  unfold missedCount Delta at hmiss
  unfold D at hmiss
  omega

end

end CheeseCutM
