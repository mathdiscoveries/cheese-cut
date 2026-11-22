module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Order.Lattice.Nat
public import CheeseCutM.CoreCount

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Real-Geometry Definitions, Symmetries, and Bárány–Frankl Lower Bound

Defines the `n × n × n` grid of open unit cubes in `ℝ³`, planes meeting open cubes,
the cut count `cutCount`, the maximum cut count `maxCutCount`, and Bárány–Frankl's
formula `F(n) = ⌊(9n² + 4n - 17)/4⌋` together with `D(n)`, `T2(m)`, and `T*(n)`.

Proves unconditionally over `ℝ`:
* `cuts_iff_range` / `meets_iff_nonneg`: exact open-interval characterization of when
  a plane meets an open unit cube (Lemma 1(a)).
* `wlog_ordered_nonneg`: symmetry reduction by reflections, coordinate permutations,
  and positive scaling to `0 ≤ a ≤ b ≤ c` with `a + b + c = 1`.
* `barany_frankl_lower_bound` and `F_le_maxCutCount`: for every `n ≥ 3`, the explicit
  plane `(n - 1, n - 1, n) · x = (n - 1)(⌊(3n - 4)/2⌋ + 3) + 1/2` cuts exactly `F(n)`
  open unit cubes.
* `D_eq_Tstar`: identity (1.1), `D(n) = T*(n) + [n even]` for all `n ≥ 3`.
-/

@[expose] public section

namespace CheeseCutM

open Finset

/-! ### Core real-geometry definitions -/

/-- A cell indexed by the lower corner `(i, j, k)` of its unit cube. -/
abbrev Cell := ℕ × ℕ × ℕ

/-- The plane `a x + b y + c z = t` in `ℝ³`. -/
def plane (a b c t : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | a * p.1 + b * p.2.1 + c * p.2.2 = t}

/-- The open unit cube `(i, i + 1) × (j, j + 1) × (k, k + 1)` in `ℝ³`. -/
def OpenCube (z : Cell) : Set (ℝ × ℝ × ℝ) :=
  {p | (z.1 : ℝ) < p.1 ∧ p.1 < (z.1 : ℝ) + 1 ∧
       (z.2.1 : ℝ) < p.2.1 ∧ p.2.1 < (z.2.1 : ℝ) + 1 ∧
       (z.2.2 : ℝ) < p.2.2 ∧ p.2.2 < (z.2.2 : ℝ) + 1}

/-- The plane `a x + b y + c z = t` cuts (meets the interior of) the unit cube `OpenCube z`. -/
def Meets (a b c t : ℝ) (z : Cell) : Prop :=
  (plane a b c t ∩ OpenCube z).Nonempty

/-- `(a, b, c)` is a nonzero normal vector in `ℝ³`. -/
def IsNormal (a b c : ℝ) : Prop := (a, b, c) ≠ (0, 0, 0)

/-- The `n³` unit cube indices `{0, …, n - 1}³`. -/
def cells (n : ℕ) : Finset Cell := range n ×ˢ range n ×ˢ range n

open Classical in
/-- The finite set of cells in the `n × n × n` box whose open unit cubes the plane meets. -/
noncomputable def cutSet (n : ℕ) (a b c t : ℝ) : Finset Cell :=
  (cells n).filter (Meets a b c t)

/-- The number of open unit cubes of the `n × n × n` box cut by `a x + b y + c z = t`. -/
noncomputable def cutCount (n : ℕ) (a b c t : ℝ) : ℕ :=
  (cutSet n a b c t).card

/-- `m(n)`: the maximum number of open unit cubes of the `n × n × n` box cut by one plane. -/
noncomputable def maxCutCount (n : ℕ) : ℕ :=
  sSup {k | ∃ a b c t : ℝ, IsNormal a b c ∧ cutCount n a b c t = k}

/-- Bárány–Frankl formula `F(n) = ⌊(9n² + 4n - 17)/4⌋`. -/
def F (n : ℕ) : ℕ := (9 * n ^ 2 + 4 * n - 17) / 4

/-- Target number of missed diagonal lines `D(n) = 3n² - 3n + 1 - F(n)`. -/
def D (n : ℕ) : ℕ := 3 * n ^ 2 - 3 * n + 1 - F n

/-- Tent-sum function `T2(m) = ⌊(m + 1)² / 4⌋` for `m ≥ 1`, `0` for `m ≤ 0`. -/
def T2 (m : ℤ) : ℕ :=
  if m ≤ 0 then 0 else (m + 1).toNat ^ 2 / 4

/-- Baseline pairing sum `T*(n) = T2(h - 2) + 2 T2(h - 3)` with `h = n - 1`. -/
def Tstar (n : ℕ) : ℕ :=
  T2 ((n : ℤ) - 3) + 2 * T2 ((n : ℤ) - 4)

/-- Theorem U upper bound `⌊(9n² + 6n - 20)/4⌋`. -/
def Ubound (n : ℕ) : ℕ := (9 * n ^ 2 + 6 * n - 20) / 4

theorem F_small_values : F 3 = 19 ∧ F 4 = 35 ∧ F 5 = 57 ∧ F 6 = 82 := by
  decide

/-! ### Identities for `T2`, `F`, `D`, and `T*` -/

lemma T2_nat (m : ℕ) : T2 (m : ℤ) = (m + 1) ^ 2 / 4 := by
  unfold T2
  by_cases hm : m = 0
  · subst hm
    simp
  · have hpos : ¬((m : ℤ) ≤ 0) := by omega
    rw [ite_eq_right hpos]
    have hEq : ((m : ℤ) + 1).toNat = m + 1 := by omega
    rw [hEq]

/-- For every integer `m ≥ -1`: `4 T2(m) = (m + 1)² - [m even]`. -/
theorem four_mul_T2 (m : ℤ) (hm : -1 ≤ m) :
    4 * (T2 m : ℤ) = (m + 1) ^ 2 - if Even m then 1 else 0 := by
  unfold T2
  by_cases h0 : m ≤ 0
  · rw [ite_eq_left h0]
    have hcase : m = -1 ∨ m = 0 := by omega
    rcases hcase with rfl | rfl
    · have hne : ¬Even (-1 : ℤ) := by decide
      rw [ite_eq_right hne]
      norm_num
    · have hev : Even (0 : ℤ) := by decide
      rw [ite_eq_left hev]
      norm_num
  · rw [ite_eq_right h0]
    have hm1 : 1 ≤ m := by omega
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, by omega⟩
    have hto : ((k : ℤ) + 1).toNat = k + 1 := by omega
    rw [hto]
    have hpar : Even (k : ℤ) ↔ k % 2 = 0 := by
      constructor
      · rintro ⟨r, hr⟩; omega
      · intro h; refine ⟨(k / 2 : ℕ), by omega⟩
    by_cases hev : Even (k : ℤ)
    · rw [ite_eq_left hev]
      have hk2 : k % 2 = 0 := hpar.1 hev
      obtain ⟨r, rfl⟩ : ∃ r : ℕ, k = 2 * r := ⟨k / 2, by omega⟩
      have hdiv : (2 * r + 1) ^ 2 / 4 = r ^ 2 + r := by
        have hsq : (2 * r + 1) ^ 2 = 4 * (r ^ 2 + r) + 1 := by ring
        rw [hsq]
        omega
      rw [hdiv]
      push_cast
      ring
    · rw [ite_eq_right hev]
      have hk2 : k % 2 = 1 := by
        have := hpar.not.1 hev
        omega
      obtain ⟨r, rfl⟩ : ∃ r : ℕ, k = 2 * r + 1 := ⟨k / 2, by omega⟩
      have hdiv : (2 * r + 1 + 1) ^ 2 / 4 = (r + 1) ^ 2 := by
        have hsq : (2 * r + 1 + 1) ^ 2 = 4 * (r + 1) ^ 2 := by ring
        rw [hsq]
        omega
      rw [hdiv]
      push_cast
      ring

/-- Identity `T2(k) - T2(k - 2) = k` for all `k ≥ 1`. -/
theorem T2_sub_two (k : ℕ) (hk : 1 ≤ k) :
    T2 (k : ℤ) = T2 ((k : ℤ) - 2) + k := by
  have h1 := four_mul_T2 (k : ℤ) (by omega)
  have h2 := four_mul_T2 ((k : ℤ) - 2) (by omega)
  have hev : Even ((k : ℤ) - 2) ↔ Even (k : ℤ) := by
    constructor
    · rintro ⟨r, hr⟩; exact ⟨r + 1, by omega⟩
    · rintro ⟨r, hr⟩; exact ⟨r - 1, by omega⟩
  by_cases h : Even (k : ℤ)
  · rw [ite_eq_left h] at h1
    rw [ite_eq_left (hev.2 h)] at h2
    have hdiff : 4 * (T2 (k : ℤ) : ℤ) = 4 * (T2 ((k : ℤ) - 2) : ℤ) + 4 * (k : ℤ) := by linarith
    omega
  · rw [ite_eq_right h] at h1
    rw [ite_eq_right (fun hh => h (hev.1 hh))] at h2
    have hdiff : 4 * (T2 (k : ℤ) : ℤ) = 4 * (T2 ((k : ℤ) - 2) : ℤ) + 4 * (k : ℤ) := by linarith
    omega

/-- `F(n) ≤ 3n² - 3n + 1` for all `n ≥ 3`. -/
lemma F_le_diag (n : ℕ) (hn : 3 ≤ n) : F n ≤ 3 * n ^ 2 - 3 * n + 1 := by
  unfold F
  have h1 : 3 * n ≤ 3 * n ^ 2 := by nlinarith
  have h2 : 17 ≤ 9 * n ^ 2 + 4 * n := by nlinarith
  have h3 : 9 * n ^ 2 + 4 * n - 17 ≤ 4 * (3 * n ^ 2 - 3 * n + 1) := by
    zify [h1, h2]
    nlinarith
  omega

/-- Identity (1.1): `D(n) = T*(n) + [n even]` for all `n ≥ 3`. -/
theorem D_eq_Tstar (n : ℕ) (hn : 3 ≤ n) :
    D n = Tstar n + if Even n then 1 else 0 := by
  unfold D F Tstar
  have h1 := four_mul_T2 ((n : ℤ) - 3) (by omega)
  have h2 := four_mul_T2 ((n : ℤ) - 4) (by omega)
  have hpar : Even n ↔ n % 2 = 0 := Nat.even_iff
  by_cases hev : Even n
  · rw [ite_eq_left hev]
    have hn2 : n % 2 = 0 := hpar.1 hev
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = 2 * m := ⟨n / 2, by omega⟩
    have hm : 2 ≤ m := by omega
    have hne1 : ¬Even ((2 * m : ℕ) - 3 : ℤ) := by rintro ⟨r, hr⟩; omega
    have hev2 : Even ((2 * m : ℕ) - 4 : ℤ) := ⟨(m : ℤ) - 2, by omega⟩
    rw [ite_eq_right hne1] at h1
    rw [ite_eq_left hev2] at h2
    have hF : (9 * (2 * m) ^ 2 + 4 * (2 * m) - 17) / 4 = 9 * m ^ 2 + 2 * m - 5 := by
      have h17 : 17 ≤ 9 * (2 * m) ^ 2 + 4 * (2 * m) := by nlinarith
      have h5 : 5 ≤ 9 * m ^ 2 + 2 * m := by nlinarith
      have hnum : 9 * (2 * m) ^ 2 + 4 * (2 * m) - 17 = 4 * (9 * m ^ 2 + 2 * m - 5) + 3 := by
        zify [h17, h5]; ring
      rw [hnum]; omega
    rw [hF]
    have hT : (T2 ((2 * m : ℕ) - 3 : ℤ) + 2 * T2 ((2 * m : ℕ) - 4 : ℤ) : ℤ) =
        3 * (m : ℤ) ^ 2 - 8 * (m : ℤ) + 5 := by
      push_cast at h1 h2 ⊢
      have hsum : 4 * ((T2 (2 * (m : ℤ) - 3) : ℤ) + 2 * (T2 (2 * (m : ℤ) - 4) : ℤ)) =
          4 * (3 * (m : ℤ) ^ 2 - 8 * (m : ℤ) + 5) := by
        calc 4 * ((T2 (2 * (m : ℤ) - 3) : ℤ) + 2 * (T2 (2 * (m : ℤ) - 4) : ℤ))
            = 4 * (T2 (2 * (m : ℤ) - 3) : ℤ) + 2 * (4 * (T2 (2 * (m : ℤ) - 4) : ℤ)) := by ring
          _ = (2 * (m : ℤ) - 3 + 1) ^ 2 - 0 + 2 * ((2 * (m : ℤ) - 4 + 1) ^ 2 - 1) := by
              rw [h1, h2]
          _ = 4 * (3 * (m : ℤ) ^ 2 - 8 * (m : ℤ) + 5) := by ring
      omega
    have ha : 3 * (2 * m) ≤ 3 * (2 * m) ^ 2 := by nlinarith
    have hb : 5 ≤ 9 * m ^ 2 + 2 * m := by nlinarith
    have hc : 9 * m ^ 2 + 2 * m - 5 ≤ 3 * (2 * m) ^ 2 - 3 * (2 * m) + 1 := by
      zify [ha, hb]; nlinarith
    zify [ha, hb, hc]
    push_cast at hT ⊢
    linarith
  · rw [ite_eq_right hev]
    have hn2 : n % 2 = 1 := by
      have := hpar.not.1 hev; omega
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hm : 1 ≤ m := by omega
    have hev1 : Even (((2 * m + 1 : ℕ) : ℤ) - 3) := ⟨(m : ℤ) - 1, by omega⟩
    have hne2 : ¬Even (((2 * m + 1 : ℕ) : ℤ) - 4) := by rintro ⟨r, hr⟩; omega
    rw [ite_eq_left hev1] at h1
    rw [ite_eq_right hne2] at h2
    have hF : (9 * (2 * m + 1) ^ 2 + 4 * (2 * m + 1) - 17) / 4 = 9 * m ^ 2 + 11 * m - 1 := by
      have h17 : 17 ≤ 9 * (2 * m + 1) ^ 2 + 4 * (2 * m + 1) := by nlinarith
      have h1' : 1 ≤ 9 * m ^ 2 + 11 * m := by nlinarith
      have hnum : 9 * (2 * m + 1) ^ 2 + 4 * (2 * m + 1) - 17 =
          4 * (9 * m ^ 2 + 11 * m - 1) := by
        zify [h17, h1']; ring
      rw [hnum]; omega
    rw [hF]
    have hT : (T2 (((2 * m + 1 : ℕ) : ℤ) - 3) + 2 * T2 (((2 * m + 1 : ℕ) : ℤ) - 4) : ℤ) =
        3 * (m : ℤ) ^ 2 - 5 * (m : ℤ) + 2 := by
      push_cast at h1 h2 ⊢
      have hsum : 4 * ((T2 (2 * (m : ℤ) + 1 - 3) : ℤ) +
          2 * (T2 (2 * (m : ℤ) + 1 - 4) : ℤ)) =
          4 * (3 * (m : ℤ) ^ 2 - 5 * (m : ℤ) + 2) := by
        calc 4 * ((T2 (2 * (m : ℤ) + 1 - 3) : ℤ) +
              2 * (T2 (2 * (m : ℤ) + 1 - 4) : ℤ))
            = 4 * (T2 (2 * (m : ℤ) + 1 - 3) : ℤ) +
              2 * (4 * (T2 (2 * (m : ℤ) + 1 - 4) : ℤ)) := by ring
          _ = (2 * (m : ℤ) + 1 - 3 + 1) ^ 2 - 1 + 2 * ((2 * (m : ℤ) + 1 - 4 + 1) ^ 2 - 0) := by
              rw [h1, h2]
          _ = 4 * (3 * (m : ℤ) ^ 2 - 5 * (m : ℤ) + 2) := by ring
      omega
    have ha : 3 * (2 * m + 1) ≤ 3 * (2 * m + 1) ^ 2 := by nlinarith
    have hb : 1 ≤ 9 * m ^ 2 + 11 * m := by nlinarith
    have hc : 9 * m ^ 2 + 11 * m - 1 ≤ 3 * (2 * m + 1) ^ 2 - 3 * (2 * m + 1) + 1 := by
      zify [ha, hb]; nlinarith
    zify [ha, hb, hc]
    push_cast at hT ⊢
    linarith

/-! ### Open-interval criterion (Lemma 1(a)) -/

noncomputable section

/-- Inner product `v · z` for a cell `z`. -/
def dot (a b c : ℝ) (z : Cell) : ℝ :=
  a * (z.1 : ℝ) + b * (z.2.1 : ℝ) + c * (z.2.2 : ℝ)

/-- `|v⁺|`, sum of positive parts of `(a, b, c)`. -/
def posSum (a b c : ℝ) : ℝ := max a 0 + max b 0 + max c 0

/-- `|v⁻|`, sum of negative parts of `(a, b, c)`. -/
def negSum (a b c : ℝ) : ℝ := max (-a) 0 + max (-b) 0 + max (-c) 0

lemma isNormal_iff (a b c : ℝ) : IsNormal a b c ↔ ¬(a = 0 ∧ b = 0 ∧ c = 0) := by
  unfold IsNormal
  simp [Prod.mk.injEq]

lemma mem_cells {n : ℕ} {z : Cell} :
    z ∈ cells n ↔ z.1 < n ∧ z.2.1 < n ∧ z.2.2 < n := by
  simp only [cells, Finset.mem_product, Finset.mem_range]

lemma mem_cutSet {n : ℕ} {a b c t : ℝ} {z : Cell} :
    z ∈ cutSet n a b c t ↔ z ∈ cells n ∧ Meets a b c t z := by
  unfold cutSet
  classical exact Finset.mem_filter

lemma card_cells (n : ℕ) : (cells n).card = n ^ 3 := by
  simp only [cells, Finset.card_product, Finset.card_range]
  ring

lemma cutCount_le_cube (n : ℕ) (a b c t : ℝ) : cutCount n a b c t ≤ n ^ 3 := by
  unfold cutCount cutSet
  rw [← card_cells n]
  classical exact Finset.card_filter_le _ _

lemma bddAbove_counts (n : ℕ) :
    BddAbove {k | ∃ a b c t : ℝ, IsNormal a b c ∧ cutCount n a b c t = k} := by
  refine ⟨n ^ 3, ?_⟩
  rintro k ⟨a, b, c, t, _, rfl⟩
  exact cutCount_le_cube n a b c t

private lemma coord_lo (a z x : ℝ) (h1 : z < x) (h2 : x < z + 1) :
    a * z - max (-a) 0 ≤ a * x := by
  rcases le_total 0 a with ha | ha
  · rw [max_eq_right (by linarith : -a ≤ 0)]
    nlinarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ -a)]
    nlinarith

private lemma coord_hi (a z x : ℝ) (h1 : z < x) (h2 : x < z + 1) :
    a * x ≤ a * z + max a 0 := by
  rcases le_total 0 a with ha | ha
  · rw [max_eq_left ha]
    nlinarith
  · rw [max_eq_right ha]
    nlinarith

private lemma coord_lo_strict (a z x : ℝ) (h1 : z < x) (h2 : x < z + 1)
    (ha : a ≠ 0) : a * z - max (-a) 0 < a * x := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ -a)]
    nlinarith
  · rw [max_eq_right (by linarith : -a ≤ 0)]
    nlinarith

private lemma coord_hi_strict (a z x : ℝ) (h1 : z < x) (h2 : x < z + 1)
    (ha : a ≠ 0) : a * x < a * z + max a 0 := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [max_eq_right ha.le]
    nlinarith
  · rw [max_eq_left ha.le]
    nlinarith

private def sel (a p : ℝ) : ℝ := if 0 ≤ a then p else 1 - p

private lemma sel_mul (a p : ℝ) :
    a * sel a p = p * max a 0 - (1 - p) * max (-a) 0 := by
  unfold sel
  split_ifs with h
  · rw [max_eq_left h, max_eq_right (by linarith : -a ≤ 0)]
    ring
  · push Not at h
    rw [max_eq_right h.le, max_eq_left (by linarith : (0 : ℝ) ≤ -a)]
    ring

private lemma sel_mem (a : ℝ) {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    0 < sel a p ∧ sel a p < 1 := by
  unfold sel
  split_ifs <;> constructor <;> linarith

private lemma part_facts (a : ℝ) :
    0 ≤ max a 0 ∧ 0 ≤ max (-a) 0 ∧ (a ≠ 0 → 0 < max a 0 + max (-a) 0) := by
  refine ⟨le_max_right _ _, le_max_right _ _, fun ha => ?_⟩
  rcases lt_or_gt_of_ne ha with h | h
  · have e : max (-a) 0 = -a := max_eq_left (by linarith)
    have f : 0 ≤ max a 0 := le_max_right _ _
    linarith
  · have e : max a 0 = a := max_eq_left h.le
    have f : 0 ≤ max (-a) 0 := le_max_right _ _
    linarith

lemma normal_pos {a b c : ℝ} (hv : IsNormal a b c) :
    0 < posSum a b c + negSum a b c := by
  rw [isNormal_iff] at hv
  unfold posSum negSum
  obtain ⟨a1, a2, a3⟩ := part_facts a
  obtain ⟨b1, b2, b3⟩ := part_facts b
  obtain ⟨c1, c2, c3⟩ := part_facts c
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · have hc : c ≠ 0 := fun hc => hv ⟨ha, hb, hc⟩
      have := c3 hc
      linarith
    · have := b3 hb
      linarith
  · have := a3 ha
    linarith

/-- **Lemma 1 (a) (`cuts_iff_range`):** A plane `v · x = t` with nonzero normal `v = (a, b, c)`
meets `OpenCube z` if and only if `v · z - |v⁻| < t < v · z + |v⁺|`. -/
theorem cuts_iff_range {a b c t : ℝ} (hv : IsNormal a b c) (z : Cell) :
    Meets a b c t z ↔
      dot a b c z - negSum a b c < t ∧ t < dot a b c z + posSum a b c := by
  have hv' := (isNormal_iff a b c).1 hv
  constructor
  · rintro ⟨p, hp, hq⟩
    simp only [plane, OpenCube, Set.mem_ofPred_eq] at hp hq
    obtain ⟨x1, x2, y1, y2, w1, w2⟩ := hq
    have l1 := coord_lo a _ _ x1 x2
    have l2 := coord_lo b _ _ y1 y2
    have l3 := coord_lo c _ _ w1 w2
    have u1 := coord_hi a _ _ x1 x2
    have u2 := coord_hi b _ _ y1 y2
    have u3 := coord_hi c _ _ w1 w2
    simp only [dot, posSum, negSum]
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · have hc : c ≠ 0 := fun hc => hv' ⟨ha, hb, hc⟩
        have s1 := coord_lo_strict c _ _ w1 w2 hc
        have s2 := coord_hi_strict c _ _ w1 w2 hc
        constructor <;> linarith
      · have s1 := coord_lo_strict b _ _ y1 y2 hb
        have s2 := coord_hi_strict b _ _ y1 y2 hb
        constructor <;> linarith
    · have s1 := coord_lo_strict a _ _ x1 x2 ha
      have s2 := coord_hi_strict a _ _ x1 x2 ha
      constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have hD := normal_pos hv
    have hD' : posSum a b c + negSum a b c ≠ 0 := ne_of_gt hD
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (t - dot a b c z + negSum a b c) /
        (posSum a b c + negSum a b c) := ⟨_, rfl⟩
    have hq0 : 0 < q := by
      rw [hq]
      exact div_pos (by linarith) hD
    have hq1 : q < 1 := by
      rw [hq, div_lt_one hD]
      linarith
    have hqD : q * (posSum a b c + negSum a b c) =
        t - dot a b c z + negSum a b c := by
      rw [hq]
      exact div_mul_cancel₀ _ hD'
    obtain ⟨sa0, sa1⟩ := sel_mem a hq0 hq1
    obtain ⟨sb0, sb1⟩ := sel_mem b hq0 hq1
    obtain ⟨sc0, sc1⟩ := sel_mem c hq0 hq1
    refine ⟨((z.1 : ℝ) + sel a q, (z.2.1 : ℝ) + sel b q,
      (z.2.2 : ℝ) + sel c q), Set.mem_inter ?_ ?_⟩
    · simp only [plane, Set.mem_ofPred_eq]
      have e1 := sel_mul a q
      have e2 := sel_mul b q
      have e3 := sel_mul c q
      simp only [dot, posSum, negSum] at hqD
      linarith
    · simp only [OpenCube, Set.mem_ofPred_eq]
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith⟩

lemma isNormal_of_pos_sum {a b c : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c)
    (hW : 0 < a + b + c) : IsNormal a b c := by
  rw [isNormal_iff]
  rintro ⟨h1, h2, h3⟩
  rw [h1, h2, h3] at hW
  linarith

/-- For a nonnegative normal `v ≥ 0` with `a + b + c > 0`: the plane meets `OpenCube z`
iff `v · z < t < v · z + (a + b + c)`. -/
theorem meets_iff_nonneg {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hW : 0 < a + b + c) (z : Cell) :
    Meets a b c t z ↔ dot a b c z < t ∧ t < dot a b c z + (a + b + c) := by
  rw [cuts_iff_range (isNormal_of_pos_sum ha hb hc hW)]
  have e1 : negSum a b c = 0 := by
    unfold negSum
    rw [max_eq_right (by linarith : -a ≤ 0), max_eq_right (by linarith : -b ≤ 0),
      max_eq_right (by linarith : -c ≤ 0)]
    ring
  have e2 : posSum a b c = a + b + c := by
    unfold posSum
    rw [max_eq_left ha, max_eq_left hb, max_eq_left hc]
  rw [e1, e2, sub_zero]

/-! ### Symmetries and scaling preserving `cutCount` -/

lemma cutCount_eq_of_maps {n : ℕ} {a b c t a' b' c' t' : ℝ} (f g : Cell → Cell)
    (hf : ∀ z ∈ cells n, f z ∈ cells n) (hg : ∀ z ∈ cells n, g z ∈ cells n)
    (hgf : ∀ z ∈ cells n, g (f z) = z) (hfg : ∀ z ∈ cells n, f (g z) = z)
    (h1 : ∀ z ∈ cells n, Meets a b c t z → Meets a' b' c' t' (f z))
    (h2 : ∀ z ∈ cells n, Meets a' b' c' t' z → Meets a b c t (g z)) :
    cutCount n a b c t = cutCount n a' b' c' t' := by
  unfold cutCount
  apply Finset.card_nbij' f g
  · intro z hz
    have hz' := mem_cutSet.1 (Finset.mem_coe.1 hz)
    exact Finset.mem_coe.2 (mem_cutSet.2 ⟨hf z hz'.1, h1 z hz'.1 hz'.2⟩)
  · intro z hz
    have hz' := mem_cutSet.1 (Finset.mem_coe.1 hz)
    exact Finset.mem_coe.2 (mem_cutSet.2 ⟨hg z hz'.1, h2 z hz'.1 hz'.2⟩)
  · intro z hz
    exact hgf z (mem_cutSet.1 (Finset.mem_coe.1 hz)).1
  · intro z hz
    exact hfg z (mem_cutSet.1 (Finset.mem_coe.1 hz)).1

private lemma meets_flip1 {n : ℕ} {a b c t a' t' : ℝ} {z : Cell} (hz : z.1 < n)
    (ha : a' = -a) (ht : t' = t - n * a) (h : Meets a b c t z) :
    Meets a' b c t' (n - 1 - z.1, z.2.1, z.2.2) := by
  obtain ⟨p, hp, hq⟩ := h
  simp only [plane, OpenCube, Set.mem_ofPred_eq] at hp hq
  obtain ⟨x1, x2, rest⟩ := hq
  have hc : ((n - 1 - z.1 : ℕ) : ℝ) + (z.1 : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast (show n - 1 - z.1 + z.1 + 1 = n by omega)
  refine ⟨((n : ℝ) - p.1, p.2.1, p.2.2), Set.mem_inter ?_ ?_⟩
  · simp only [plane, Set.mem_ofPred_eq]
    rw [ha, ht]
    linarith
  · simp only [OpenCube, Set.mem_ofPred_eq]
    exact ⟨by linarith, by linarith, rest⟩

private lemma meets_flip2 {n : ℕ} {a b c t b' t' : ℝ} {z : Cell} (hz : z.2.1 < n)
    (hb : b' = -b) (ht : t' = t - n * b) (h : Meets a b c t z) :
    Meets a b' c t' (z.1, n - 1 - z.2.1, z.2.2) := by
  obtain ⟨p, hp, hq⟩ := h
  simp only [plane, OpenCube, Set.mem_ofPred_eq] at hp hq
  obtain ⟨x1, x2, y1, y2, w1, w2⟩ := hq
  have hc : ((n - 1 - z.2.1 : ℕ) : ℝ) + (z.2.1 : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast (show n - 1 - z.2.1 + z.2.1 + 1 = n by omega)
  refine ⟨(p.1, (n : ℝ) - p.2.1, p.2.2), Set.mem_inter ?_ ?_⟩
  · simp only [plane, Set.mem_ofPred_eq]
    rw [hb, ht]
    linarith
  · simp only [OpenCube, Set.mem_ofPred_eq]
    exact ⟨x1, x2, by linarith, by linarith, w1, w2⟩

private lemma meets_flip3 {n : ℕ} {a b c t c' t' : ℝ} {z : Cell} (hz : z.2.2 < n)
    (hc' : c' = -c) (ht : t' = t - n * c) (h : Meets a b c t z) :
    Meets a b c' t' (z.1, z.2.1, n - 1 - z.2.2) := by
  obtain ⟨p, hp, hq⟩ := h
  simp only [plane, OpenCube, Set.mem_ofPred_eq] at hp hq
  obtain ⟨x1, x2, y1, y2, w1, w2⟩ := hq
  have hc : ((n - 1 - z.2.2 : ℕ) : ℝ) + (z.2.2 : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast (show n - 1 - z.2.2 + z.2.2 + 1 = n by omega)
  refine ⟨(p.1, p.2.1, (n : ℝ) - p.2.2), Set.mem_inter ?_ ?_⟩
  · simp only [plane, Set.mem_ofPred_eq]
    rw [hc', ht]
    linarith
  · simp only [OpenCube, Set.mem_ofPred_eq]
    exact ⟨x1, x2, y1, y2, by linarith, by linarith⟩

lemma cutCount_flip1 (n : ℕ) (a b c t : ℝ) :
    cutCount n a b c t = cutCount n (-a) b c (t - n * a) := by
  apply cutCount_eq_of_maps (fun z : Cell => (n - 1 - z.1, z.2.1, z.2.2))
    (fun z : Cell => (n - 1 - z.1, z.2.1, z.2.2))
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro z hz; rw [mem_cells] at hz; exact Prod.ext (by dsimp only; omega) rfl
  · intro z hz; rw [mem_cells] at hz; exact Prod.ext (by dsimp only; omega) rfl
  · intro z hz h; exact meets_flip1 (mem_cells.1 hz).1 rfl rfl h
  · intro z hz h; exact meets_flip1 (mem_cells.1 hz).1 (by ring) (by ring) h

lemma cutCount_flip2 (n : ℕ) (a b c t : ℝ) :
    cutCount n a b c t = cutCount n a (-b) c (t - n * b) := by
  apply cutCount_eq_of_maps (fun z : Cell => (z.1, n - 1 - z.2.1, z.2.2))
    (fun z : Cell => (z.1, n - 1 - z.2.1, z.2.2))
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro z hz; rw [mem_cells] at hz; exact Prod.ext rfl (Prod.ext (by dsimp only; omega) rfl)
  · intro z hz; rw [mem_cells] at hz; exact Prod.ext rfl (Prod.ext (by dsimp only; omega) rfl)
  · intro z hz h; exact meets_flip2 (mem_cells.1 hz).2.1 rfl rfl h
  · intro z hz h; exact meets_flip2 (mem_cells.1 hz).2.1 (by ring) (by ring) h

lemma cutCount_flip3 (n : ℕ) (a b c t : ℝ) :
    cutCount n a b c t = cutCount n a b (-c) (t - n * c) := by
  apply cutCount_eq_of_maps (fun z : Cell => (z.1, z.2.1, n - 1 - z.2.2))
    (fun z : Cell => (z.1, z.2.1, n - 1 - z.2.2))
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro z hz; rw [mem_cells] at hz; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega))
  · intro z hz; rw [mem_cells] at hz; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega))
  · intro z hz h; exact meets_flip3 (mem_cells.1 hz).2.2 rfl rfl h
  · intro z hz h; exact meets_flip3 (mem_cells.1 hz).2.2 (by ring) (by ring) h

private lemma meets_swap13 {a b c t : ℝ} {z : Cell} (h : Meets a b c t z) :
    Meets c b a t (z.2.2, z.2.1, z.1) := by
  obtain ⟨p, hp, hq⟩ := h
  simp only [plane, OpenCube, Set.mem_ofPred_eq] at hp hq
  obtain ⟨x1, x2, y1, y2, w1, w2⟩ := hq
  refine ⟨(p.2.2, p.2.1, p.1), Set.mem_inter ?_ ?_⟩
  · simp only [plane, Set.mem_ofPred_eq]; linarith
  · simp only [OpenCube, Set.mem_ofPred_eq]; exact ⟨w1, w2, y1, y2, x1, x2⟩

private lemma meets_swap23 {a b c t : ℝ} {z : Cell} (h : Meets a b c t z) :
    Meets a c b t (z.1, z.2.2, z.2.1) := by
  obtain ⟨p, hp, hq⟩ := h
  simp only [plane, OpenCube, Set.mem_ofPred_eq] at hp hq
  obtain ⟨x1, x2, y1, y2, w1, w2⟩ := hq
  refine ⟨(p.1, p.2.2, p.2.1), Set.mem_inter ?_ ?_⟩
  · simp only [plane, Set.mem_ofPred_eq]; linarith
  · simp only [OpenCube, Set.mem_ofPred_eq]; exact ⟨x1, x2, w1, w2, y1, y2⟩

private lemma meets_swap12 {a b c t : ℝ} {z : Cell} (h : Meets a b c t z) :
    Meets b a c t (z.2.1, z.1, z.2.2) := by
  obtain ⟨p, hp, hq⟩ := h
  simp only [plane, OpenCube, Set.mem_ofPred_eq] at hp hq
  obtain ⟨x1, x2, y1, y2, w1, w2⟩ := hq
  refine ⟨(p.2.1, p.1, p.2.2), Set.mem_inter ?_ ?_⟩
  · simp only [plane, Set.mem_ofPred_eq]; linarith
  · simp only [OpenCube, Set.mem_ofPred_eq]; exact ⟨y1, y2, x1, x2, w1, w2⟩

lemma cutCount_swap13 (n : ℕ) (a b c t : ℝ) :
    cutCount n a b c t = cutCount n c b a t := by
  apply cutCount_eq_of_maps (fun z : Cell => (z.2.2, z.2.1, z.1))
    (fun z : Cell => (z.2.2, z.2.1, z.1))
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _ h; exact meets_swap13 h
  · intro _ _ h; exact meets_swap13 h

lemma cutCount_swap23 (n : ℕ) (a b c t : ℝ) :
    cutCount n a b c t = cutCount n a c b t := by
  apply cutCount_eq_of_maps (fun z : Cell => (z.1, z.2.2, z.2.1))
    (fun z : Cell => (z.1, z.2.2, z.2.1))
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _ h; exact meets_swap23 h
  · intro _ _ h; exact meets_swap23 h

lemma cutCount_swap12 (n : ℕ) (a b c t : ℝ) :
    cutCount n a b c t = cutCount n b a c t := by
  apply cutCount_eq_of_maps (fun z : Cell => (z.2.1, z.1, z.2.2))
    (fun z : Cell => (z.2.1, z.1, z.2.2))
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro z hz; rw [mem_cells] at hz ⊢; dsimp only; omega
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _ h; exact meets_swap12 h
  · intro _ _ h; exact meets_swap12 h

lemma cutCount_scale {n : ℕ} {a b c t lam : ℝ} (hlam : lam ≠ 0) :
    cutCount n (lam * a) (lam * b) (lam * c) (lam * t) = cutCount n a b c t := by
  apply cutCount_eq_of_maps id id (fun _ h => h) (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)
  · intro z _ ⟨p, hp, hq⟩
    refine ⟨p, ?_, hq⟩
    simp only [plane, Set.mem_ofPred_eq] at hp ⊢
    apply mul_left_cancel₀ hlam
    linarith
  · intro z _ ⟨p, hp, hq⟩
    refine ⟨p, ?_, hq⟩
    simp only [plane, Set.mem_ofPred_eq] at hp ⊢
    calc lam * a * p.1 + lam * b * p.2.1 + lam * c * p.2.2
        = lam * (a * p.1 + b * p.2.1 + c * p.2.2) := by ring
      _ = lam * t := by rw [hp]

lemma cutCount_neg (n : ℕ) (a b c t : ℝ) :
    cutCount n (-a) (-b) (-c) (-t) = cutCount n a b c t := by
  have h := cutCount_scale (n := n) (a := a) (b := b) (c := c) (t := t) (lam := -1) (by norm_num)
  simpa using h

lemma cutCount_mirror (n : ℕ) (a b c t : ℝ) :
    cutCount n a b c t = cutCount n a b c (n * (a + b + c) - t) := by
  have e1 := cutCount_flip1 n a b c t
  have e2 := cutCount_flip2 n (-a) b c (t - n * a)
  have e3 := cutCount_flip3 n (-a) (-b) c (t - n * a - n * b)
  have e4 := cutCount_neg n a b c (n * (a + b + c) - t)
  rw [e1, e2, e3, ← e4]
  congr 1
  ring

/-- **Symmetry reduction (`wlog_ordered_nonneg`):** Every nonzero real plane has the same
`cutCount` as a normalized plane with `0 ≤ a' ≤ b' ≤ c'` and `a' + b' + c' = 1`. -/
theorem wlog_ordered_nonneg (n : ℕ) (a b c t : ℝ) (hv : IsNormal a b c) :
    ∃ a' b' c' t' : ℝ,
      0 ≤ a' ∧ a' ≤ b' ∧ b' ≤ c' ∧ a' + b' + c' = 1 ∧
        cutCount n a b c t = cutCount n a' b' c' t' := by
  obtain ⟨t1, e1⟩ : ∃ t1, cutCount n a b c t = cutCount n |a| b c t1 := by
    rcases le_total 0 a with h | h
    · exact ⟨t, by rw [abs_of_nonneg h]⟩
    · exact ⟨t - n * a, by rw [abs_of_nonpos h]; exact cutCount_flip1 n a b c t⟩
  obtain ⟨t2, e2⟩ : ∃ t2, cutCount n |a| b c t1 = cutCount n |a| |b| c t2 := by
    rcases le_total 0 b with h | h
    · exact ⟨t1, by rw [abs_of_nonneg h]⟩
    · exact ⟨t1 - n * b, by rw [abs_of_nonpos h]; exact cutCount_flip2 n |a| b c t1⟩
  obtain ⟨t3, e3⟩ : ∃ t3, cutCount n |a| |b| c t2 = cutCount n |a| |b| |c| t3 := by
    rcases le_total 0 c with h | h
    · exact ⟨t2, by rw [abs_of_nonneg h]⟩
    · exact ⟨t2 - n * c, by rw [abs_of_nonpos h]; exact cutCount_flip3 n |a| |b| c t2⟩
  have hW : 0 < |a| + |b| + |c| := by
    rw [isNormal_iff] at hv
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    have hc := abs_nonneg c
    by_contra hle
    push Not at hle
    have ha0 : a = 0 := abs_eq_zero.1 (by linarith)
    have hb0 : b = 0 := abs_eq_zero.1 (by linarith)
    have hc0 : c = 0 := abs_eq_zero.1 (by linarith)
    exact hv ⟨ha0, hb0, hc0⟩
  have sort3 : ∀ p q r : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ r →
      ∃ p' q' r' : ℝ, 0 ≤ p' ∧ p' ≤ q' ∧ q' ≤ r' ∧ p' + q' + r' = p + q + r ∧
        cutCount n p q r t3 = cutCount n p' q' r' t3 := by
    intro p q r hp hq hr
    rcases le_total p q with hpq | hqp
    · rcases le_total q r with hqr | hrq
      · exact ⟨p, q, r, hp, hpq, hqr, rfl, rfl⟩
      · rcases le_total p r with hpr | hrp
        · exact ⟨p, r, q, hp, hpr, hrq, by ring, cutCount_swap23 n p q r t3⟩
        · refine ⟨r, p, q, hr, hrp, hpq, by ring, ?_⟩
          rw [cutCount_swap23 n p q r t3, cutCount_swap12 n p r q t3]
    · rcases le_total p r with hpr | hrp
      · exact ⟨q, p, r, hq, hqp, hpr, by ring, cutCount_swap12 n p q r t3⟩
      · rcases le_total q r with hqr | hrq
        · refine ⟨q, r, p, hq, hqr, hrp, by ring, ?_⟩
          rw [cutCount_swap12 n p q r t3, cutCount_swap23 n q p r t3]
        · exact ⟨r, q, p, hr, hrq, hqp, by ring, cutCount_swap13 n p q r t3⟩
  obtain ⟨p, q, r, hp, hpq, hqr, hsum, hsort⟩ :=
    sort3 |a| |b| |c| (abs_nonneg a) (abs_nonneg b) (abs_nonneg c)
  have hW' : 0 < p + q + r := by linarith
  have hinv : (p + q + r)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hW')
  refine ⟨(p + q + r)⁻¹ * p, (p + q + r)⁻¹ * q, (p + q + r)⁻¹ * r, (p + q + r)⁻¹ * t3,
    mul_nonneg (inv_nonneg.2 hW'.le) hp,
    mul_le_mul_of_nonneg_left hpq (inv_nonneg.2 hW'.le),
    mul_le_mul_of_nonneg_left hqr (inv_nonneg.2 hW'.le), ?_, ?_⟩
  · calc (p + q + r)⁻¹ * p + (p + q + r)⁻¹ * q + (p + q + r)⁻¹ * r
        = (p + q + r)⁻¹ * (p + q + r) := by ring
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hW')
  · rw [e1, e2, e3, hsort, cutCount_scale hinv]

/-! ### Bárány–Frankl exact lower bound (`∀ n ≥ 3`, `m(n) ≥ F(n)`) -/

/-- Coordinate sum `i + j + k`. -/
def sigma (z : Cell) : ℕ := z.1 + z.2.1 + z.2.2

/-- The three full diagonal layers `s, s + 1, s + 2`. -/
def T3 (n s : ℕ) : Finset Cell :=
  (cells n).filter (fun z => s ≤ sigma z ∧ sigma z ≤ s + 2)

/-- Layer `s + 3` with `z₃ = 0`. -/
def X3 (n s : ℕ) : Finset Cell :=
  (cells n).filter (fun z => sigma z = s + 3 ∧ z.2.2 = 0)

/-- Layer `s - 1` with `z₃ = n - 1`. -/
def Y3 (n s : ℕ) : Finset Cell :=
  (cells n).filter (fun z => sigma z + 1 = s ∧ z.2.2 + 1 = n)

/-- Bárány–Frankl slab count `g(n, s) = |T3| + |X3| + |Y3|`. -/
def gCount (n s : ℕ) : ℕ := (T3 n s).card + (X3 n s).card + (Y3 n s).card

/-- The slab `{(i, j, k) : (n - 1) s ≤ (n - 1)(i + j + k) + k ≤ (n - 1)(s + 3)}`. -/
def slab (n s : ℕ) : Finset Cell :=
  (cells n).filter (fun z => (n - 1) * s ≤ (n - 1) * sigma z + z.2.2 ∧
    (n - 1) * sigma z + z.2.2 ≤ (n - 1) * (s + 3))

private lemma half_lt {N M : ℕ} : (N : ℝ) < (M : ℝ) + 1 / 2 ↔ N ≤ M := by
  constructor
  · intro h
    by_contra hc
    have : (M : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (show M + 1 ≤ N by omega)
    linarith
  · intro h
    have : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
    linarith

private lemma witness_cut (h s x y w : ℕ) :
    (dot (h : ℝ) (h : ℝ) ((h : ℝ) + 1) (x, y, w) < ((h * (s + 3) : ℕ) : ℝ) + 1 / 2 ∧
      ((h * (s + 3) : ℕ) : ℝ) + 1 / 2 <
        dot (h : ℝ) (h : ℝ) ((h : ℝ) + 1) (x, y, w) + ((h : ℝ) + (h : ℝ) + ((h : ℝ) + 1))) ↔
      (h * s ≤ h * (x + y + w) + w ∧ h * (x + y + w) + w ≤ h * (s + 3)) := by
  have eN : dot (h : ℝ) (h : ℝ) ((h : ℝ) + 1) (x, y, w) =
      ((h * (x + y + w) + w : ℕ) : ℝ) := by
    unfold dot
    push_cast
    ring
  have eM : ((h * (s + 3) : ℕ) : ℝ) = ((h * s : ℕ) : ℝ) + 3 * (h : ℝ) := by
    push_cast
    ring
  rw [eN]
  constructor
  · rintro ⟨h1, h2⟩
    have k1 := half_lt.1 h1
    have k2 : ((h * s : ℕ) : ℝ) < ((h * (x + y + w) + w : ℕ) : ℝ) + 1 / 2 := by
      rw [eM] at h2
      linarith
    exact ⟨half_lt.1 k2, k1⟩
  · rintro ⟨k3, k1⟩
    refine ⟨half_lt.2 k1, ?_⟩
    have k4 : ((h * s : ℕ) : ℝ) ≤ ((h * (x + y + w) + w : ℕ) : ℝ) := by exact_mod_cast k3
    rw [eM]
    linarith

private lemma witness_cutSet (h s : ℕ) (hh : 1 ≤ h) :
    cutSet (h + 1) (h : ℝ) (h : ℝ) ((h : ℝ) + 1) (((h * (s + 3) : ℕ) : ℝ) + 1 / 2) =
      slab (h + 1) s := by
  have h0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
  have h1 : (0 : ℝ) < (h : ℝ) + 1 := by linarith
  ext z
  rw [mem_cutSet, meets_iff_nonneg h0.le h0.le h1.le (by linarith)]
  unfold slab
  rw [Finset.mem_filter, Nat.add_sub_cancel]
  exact and_congr_right (fun _ => witness_cut h s z.1 z.2.1 z.2.2)

private lemma slab_cond (h s σ w : ℕ) (hh : 1 ≤ h) (hw : w ≤ h) :
    (h * s ≤ h * σ + w ∧ h * σ + w ≤ h * (s + 3)) ↔
      ((s ≤ σ ∧ σ ≤ s + 2) ∨ (σ = s + 3 ∧ w = 0) ∨ (σ + 1 = s ∧ w = h)) := by
  have e3 : h * (s + 3) = h * s + 3 * h := by ring
  constructor
  · rintro ⟨h1, h2⟩
    rcases (show σ + 2 ≤ s ∨ σ + 1 = s ∨ (s ≤ σ ∧ σ ≤ s + 2) ∨ σ = s + 3 ∨ s + 4 ≤ σ by
      omega) with c | c | c | c | c
    · have m := Nat.mul_le_mul_left h c
      have e : h * (σ + 2) = h * σ + 2 * h := by ring
      omega
    · have e : h * s = h * σ + h := by rw [← c]; ring
      exact Or.inr (Or.inr ⟨c, by omega⟩)
    · exact Or.inl c
    · have e : h * σ = h * s + 3 * h := by rw [c]; ring
      exact Or.inr (Or.inl ⟨c, by omega⟩)
    · have m := Nat.mul_le_mul_left h c
      have e : h * (s + 4) = h * s + 4 * h := by ring
      omega
  · rintro (⟨c1, c2⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩)
    · have m1 := Nat.mul_le_mul_left h c1
      have m2 := Nat.mul_le_mul_left h c2
      have e : h * (s + 2) = h * s + 2 * h := by ring
      omega
    · have e : h * σ = h * s + 3 * h := by rw [c1]; ring
      omega
    · have e : h * s = h * σ + h := by rw [← c1]; ring
      omega

private lemma slab_eq (h s : ℕ) (hh : 1 ≤ h) :
    slab (h + 1) s = (T3 (h + 1) s ∪ X3 (h + 1) s) ∪ Y3 (h + 1) s := by
  ext z
  have hslab : z ∈ slab (h + 1) s ↔ z ∈ cells (h + 1) ∧
      (h * s ≤ h * sigma z + z.2.2 ∧ h * sigma z + z.2.2 ≤ h * (s + 3)) := by
    unfold slab
    rw [Finset.mem_filter, Nat.add_sub_cancel]
  simp only [hslab, Finset.mem_union, T3, X3, Y3, Finset.mem_filter, mem_cells]
  constructor
  · rintro ⟨hz, hc⟩
    have hw : z.2.2 ≤ h := by omega
    rcases (slab_cond h s (sigma z) z.2.2 hh hw).1 hc with c | c | c
    · exact Or.inl (Or.inl ⟨hz, c⟩)
    · exact Or.inl (Or.inr ⟨hz, c.1, c.2⟩)
    · exact Or.inr ⟨hz, c.1, by omega⟩
  · rintro ((⟨hz, c⟩ | ⟨hz, c⟩) | ⟨hz, c⟩)
    · have hw : z.2.2 ≤ h := by omega
      exact ⟨hz, (slab_cond h s (sigma z) z.2.2 hh hw).2 (Or.inl c)⟩
    · have hw : z.2.2 ≤ h := by omega
      exact ⟨hz, (slab_cond h s (sigma z) z.2.2 hh hw).2 (Or.inr (Or.inl c))⟩
    · have hw : z.2.2 ≤ h := by omega
      exact ⟨hz, (slab_cond h s (sigma z) z.2.2 hh hw).2
        (Or.inr (Or.inr ⟨c.1, by omega⟩))⟩

private lemma card_slab (h s : ℕ) (hh : 1 ≤ h) : (slab (h + 1) s).card = gCount (h + 1) s := by
  have d1 : Disjoint (T3 (h + 1) s) (X3 (h + 1) s) := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    simp only [T3, X3, Finset.mem_filter] at h1 h2
    omega
  have d2 : Disjoint (T3 (h + 1) s ∪ X3 (h + 1) s) (Y3 (h + 1) s) := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    simp only [T3, X3, Y3, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1 <;> omega
  rw [slab_eq h s hh, Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1]
  rfl

private lemma sum_range_eq_rsum (f : ℕ → ℕ) (m : ℕ) :
    ∑ x ∈ range m, f x = Core.rsum f m := by
  induction m with
  | zero => rw [Finset.sum_range_zero]; rfl
  | succ m ih => rw [Finset.sum_range_succ, ih, Core.rsum_succ]

private lemma card_filter_cells (n : ℕ) (p : Cell → Prop) [DecidablePred p] :
    ((cells n).filter p).card =
      Core.rsum (fun x => Core.rsum (fun y =>
        Core.rsum (fun w => if p (x, y, w) then 1 else 0) n) n) n := by
  rw [Finset.card_filter]
  unfold cells
  rw [Finset.sum_product, sum_range_eq_rsum]
  apply Core.rsum_congr
  intro x _
  rw [Finset.sum_product, sum_range_eq_rsum]
  apply Core.rsum_congr
  intro y _
  rw [sum_range_eq_rsum]

theorem gCount_eq_core (n s : ℕ) :
    gCount n s = Core.tripleT n s + Core.tripleX n s + Core.tripleY n s := by
  unfold gCount T3 X3 Y3
  rw [card_filter_cells, card_filter_cells, card_filter_cells]; rfl

/-- **Exact Bárány–Frankl lower bound (`barany_frankl_lower_bound`):**
For every `n ≥ 3`, there exists a nonzero real plane cutting exactly `F(n)` open unit cubes. -/
theorem barany_frankl_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ a b c t : ℝ, IsNormal a b c ∧ cutCount n a b c t = F n := by
  obtain ⟨h, rfl⟩ : ∃ h : ℕ, n = h + 1 := ⟨n - 1, by omega⟩
  have hh : 1 ≤ h := by omega
  let s := (3 * (h + 1) - 4) / 2
  refine ⟨(h : ℝ), (h : ℝ), (h : ℝ) + 1, ((h * (s + 3) : ℕ) : ℝ) + 1 / 2, ?_, ?_⟩
  · rw [isNormal_iff]
    rintro ⟨h1, _, _⟩
    have hpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
    linarith
  · unfold cutCount
    rw [witness_cutSet h s hh, card_slab h s hh, gCount_eq_core]
    exact Core.G_eq (h + 1) hn

/-- Consequently, `F(n) ≤ maxCutCount(n)` for every `n ≥ 3`. -/
theorem F_le_maxCutCount (n : ℕ) (hn : 3 ≤ n) : F n ≤ maxCutCount n := by
  obtain ⟨a, b, c, t, hv, hcnt⟩ := barany_frankl_lower_bound n hn
  exact le_csSup (bddAbove_counts n) ⟨a, b, c, t, hv, hcnt⟩

end

end CheeseCutM
