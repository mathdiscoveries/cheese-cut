module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Lattice.Nat

/-!
# Maximum Open Unit Cubes Cut by a Plane in `[0, n]³`

This module defines the `n × n × n` grid of open unit cubes in `ℝ³`, the count
`cutCount n a b c t` of open unit cubes met by the plane `a x + b y + c z = t`,
the maximum `maxCutCount n` over all nonzero real planes, Bárány and Frankl's
formula `F n = ⌊(9n² + 4n - 17)/4⌋`, and the universal upper bound
`Ubound n = ⌊(9n² + 6n - 20)/4⌋`.

It states six unconditional theorems over `ℝ`:
1. `CheeseCutM.maxCutCount_eq_F_ge_700`: `maxCutCount n = F n` for every `n ≥ 700`.
2. `CheeseCutM.barany_frankl_plus_two_refuted_ge_700`: `maxCutCount n < F n + 2`
   for every `n ≥ 700` (refuting Bárány–Frankl's Section 5 "+2" remark).
3. `CheeseCutM.maxCutCount_eq_F_3_to_32`: `maxCutCount n = F n` for every `3 ≤ n ≤ 32`.
4. `CheeseCutM.maxCutCount_ten`: `maxCutCount 10 = 230` (settling Bárány–Frankl's
   explicitly stated open case `n = 10`).
5. `CheeseCutM.theoremU_bound_all_ge_2`: `cutCount n a b c t ≤ Ubound n` for every
   `n ≥ 2` and every nonzero real plane.
6. `CheeseCutM.barany_frankl_lower_bound`: for every `n ≥ 3`, an explicit plane
   cuts exactly `F n` open unit cubes.

Scope note: the remaining finite window `33 ≤ n ≤ 699` is not discharged inside
this Lean proof; it is checked by external exact-integer vertex certificates
referenced in `README.md` and `formalization.yaml`.
-/

@[expose] public section

namespace CheeseCutM

open Finset

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

/-- The plane `a x + b y + c z = t` cuts (meets the interior of) `OpenCube z`. -/
def Meets (a b c t : ℝ) (z : Cell) : Prop :=
  (plane a b c t ∩ OpenCube z).Nonempty

/-- `(a, b, c)` is a nonzero normal vector in `ℝ³`. -/
def IsNormal (a b c : ℝ) : Prop := (a, b, c) ≠ (0, 0, 0)

/-- The `n³` unit cube indices `{0, …, n - 1}³`. -/
def cells (n : ℕ) : Finset Cell := range n ×ˢ range n ×ˢ range n

open Classical in
/-- The finite set of cells in `[0, n]³` whose open unit cubes the plane meets. -/
noncomputable def cutSet (n : ℕ) (a b c t : ℝ) : Finset Cell :=
  (cells n).filter (Meets a b c t)

/-- The number of open unit cubes of `[0, n]³` cut by `a x + b y + c z = t`. -/
noncomputable def cutCount (n : ℕ) (a b c t : ℝ) : ℕ :=
  (cutSet n a b c t).card

/-- `m(n)`: the maximum number of open unit cubes of `[0, n]³` cut by one plane. -/
noncomputable def maxCutCount (n : ℕ) : ℕ :=
  sSup {k | ∃ a b c t : ℝ, IsNormal a b c ∧ cutCount n a b c t = k}

/-- Bárány–Frankl formula `F(n) = ⌊(9n² + 4n - 17)/4⌋`. -/
def F (n : ℕ) : ℕ := (9 * n ^ 2 + 4 * n - 17) / 4

/-- Universal upper bound `⌊(9n² + 6n - 20)/4⌋` for `n ≥ 2`. -/
def Ubound (n : ℕ) : ℕ := (9 * n ^ 2 + 6 * n - 20) / 4

/-- Exact formula `m(n) = ⌊(9n² + 4n - 17)/4⌋` for every `n ≥ 700`. -/
theorem maxCutCount_eq_F_ge_700 (n : ℕ) (hn : 700 ≤ n) :
    maxCutCount n = F n := by
  sorry

/-- Refutation of Bárány–Frankl's Section 5 "+2" remark for every `n ≥ 700`. -/
theorem barany_frankl_plus_two_refuted_ge_700 (n : ℕ) (hn : 700 ≤ n) :
    maxCutCount n < F n + 2 := by
  sorry

/-- Exact formula `m(n) = ⌊(9n² + 4n - 17)/4⌋` for every `3 ≤ n ≤ 32`. -/
theorem maxCutCount_eq_F_3_to_32 (n : ℕ) (hn3 : 3 ≤ n) (hn32 : n ≤ 32) :
    maxCutCount n = F n := by
  sorry

/-- Settling Bárány–Frankl's (2021) printed open case `n = 10`: `m(10) = 230`. -/
theorem maxCutCount_ten : maxCutCount 10 = 230 := by
  sorry

/-- Universal upper bound `cutCount n a b c t ≤ ⌊(9n² + 6n - 20)/4⌋` for every `n ≥ 2`. -/
theorem theoremU_bound_all_ge_2 (n : ℕ) (hn : 2 ≤ n) (a b c t : ℝ) (hv : IsNormal a b c) :
    cutCount n a b c t ≤ Ubound n := by
  sorry

/-- Bárány–Frankl lower bound: for every `n ≥ 3`, some plane cuts exactly `F n` cubes. -/
theorem barany_frankl_lower_bound (n : ℕ) (hn : 3 ≤ n) :
    ∃ a b c t : ℝ, IsNormal a b c ∧ cutCount n a b c t = F n := by
  sorry

end CheeseCutM
