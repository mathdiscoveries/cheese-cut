module

public import CheeseCutM.Pairing

import Mathlib.Tactic

/-!
# Half-Plane Form, Lemma H (Vertex Principle), and Proposition V (`arr_verify` Soundness)

100% unconditional proofs over `ℝ`:
* `lemma_H_vertex_principle`: 2D line-arrangement vertex principle over `ℝ²` proved directly
  by bounded ray-shooting in `Z(R₁) = {u ≥ 0, w ≥ 0, u + 2w ≤ R₁}`.
* Half-plane forms `N_k(S) - 3(L' - 1) d_k > 0` (`hpForm`) and exact equivalence with
  `L' ≤ L_k(S)` on `u > 0, w > 0`.
* Truncated pairing bound (`btPair`), full arrangement valuation (`arrVal`), step-(c) monotonicity
  (`arrVal_mono`), and **Proposition V (`prop_V_arr_verify_sound`)**:
  a passing arrangement-vertex certificate (`ArrVerifyPass`) for `n ≥ 16` unconditionally
  implies `∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n`.
-/

@[expose] public section

namespace CheeseCutM

open Finset

noncomputable section

/-! ### Lemma H: 2D Line-Arrangement Vertex Principle over `ℝ²` -/

/-- An affine form `(a, b, c)` representing `a u + b w + c`. -/
abbrev AffForm := ℝ × ℝ × ℝ

/-- Value of affine form `(a, b, c)` at `(u, w)`. -/
def evalForm (ℓ : AffForm) (p : ℝ × ℝ) : ℝ :=
  ℓ.1 * p.1 + ℓ.2.1 * p.2 + ℓ.2.2

/-- Directional derivative `a du + b dw` of affine form `(a, b, c)` along `(du, dw)`. -/
def dirEval (ℓ : AffForm) (d : ℝ × ℝ) : ℝ :=
  ℓ.1 * d.1 + ℓ.2.1 * d.2

/-- 2×2 determinant `a₁ b₂ - b₁ a₂` of two affine forms (nonzero iff non-parallel). -/
def detForm (ℓ₁ ℓ₂ : AffForm) : ℝ :=
  ℓ₁.1 * ℓ₂.2.1 - ℓ₁.2.1 * ℓ₂.1

/-- Non-degeneracy: the linear part `(a, b)` is nonzero (defines a genuine line). -/
def NonDegen (ℓ : AffForm) : Prop := (ℓ.1, ℓ.2.1) ≠ (0, 0)

/-- The closed cone triangle `Z(R₁) = {(u, w) ∈ ℝ² : u ≥ 0, w ≥ 0, u + 2w ≤ R₁}`. -/
def inZone (R1 : ℝ) (p : ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + 2 * p.2 ≤ R1

/-- The three boundary forms defining `Z(R₁)` as `{evalForm ℓ p ≤ 0}`. -/
def sideU : AffForm := (-1, 0, 0)
def sideW : AffForm := (0, -1, 0)
def sideTop (R1 : ℝ) : AffForm := (1, 2, -R1)

/-- A point `v ∈ Z(R₁)` is an arrangement vertex of `A` iff two non-parallel lines of `A`
meet at `v`. -/
def IsVertex (R1 : ℝ) (A : Finset AffForm) (v : ℝ × ℝ) : Prop :=
  inZone R1 v ∧ ∃ ℓ₁ ∈ A, ∃ ℓ₂ ∈ A, detForm ℓ₁ ℓ₂ ≠ 0 ∧ evalForm ℓ₁ v = 0 ∧ evalForm ℓ₂ v = 0

private lemma evalForm_add_smul (ℓ : AffForm) (q d : ℝ × ℝ) (t : ℝ) :
    evalForm ℓ (q.1 + t * d.1, q.2 + t * d.2) = evalForm ℓ q + t * dirEval ℓ d := by
  unfold evalForm dirEval; ring

private lemma exists_pos_dirEval {R1 : ℝ} {S : Finset AffForm}
    (hU : sideU ∈ S) (hW : sideW ∈ S) (hT : sideTop R1 ∈ S)
    {d : ℝ × ℝ} (hd : d ≠ (0, 0)) :
    ∃ ℓ ∈ S, 0 < dirEval ℓ d := by
  by_cases h1 : d.1 < 0
  · exact ⟨sideU, hU, by unfold dirEval sideU; linarith⟩
  · by_cases h2 : d.2 < 0
    · exact ⟨sideW, hW, by unfold dirEval sideW; linarith⟩
    · push Not at h1 h2
      have hpos : 0 < d.1 + 2 * d.2 := by
        by_contra hle
        push Not at hle
        have h10 : d.1 = 0 := by linarith
        have h20 : d.2 = 0 := by linarith
        exact hd (Prod.ext h10 h20)
      exact ⟨sideTop R1, hT, by unfold dirEval sideTop; linarith⟩

/-- Ray-shooting step: from any `q` in the closed cell `{∀ ℓ ∈ S, evalForm ℓ q ≤ 0}`
containing the three triangle sides, shooting in any nonzero direction `d` hits some
`ℓ* ∈ S` with `dirEval ℓ* d > 0` at a point `q' = q + t* · d` (`t* ≥ 0`) staying in the cell;
and `t* > 0` whenever every `ℓ ∈ S` with `dirEval ℓ d > 0` has `evalForm ℓ q < 0`. -/
private lemma shoot_ray {R1 : ℝ} {S : Finset AffForm}
    (hU : sideU ∈ S) (hW : sideW ∈ S) (hT : sideTop R1 ∈ S)
    {q : ℝ × ℝ} (hq : ∀ ℓ ∈ S, evalForm ℓ q ≤ 0)
    {d : ℝ × ℝ} (hd : d ≠ (0, 0)) :
    ∃ t : ℝ, 0 ≤ t ∧
      (∀ ℓ ∈ S, evalForm ℓ (q.1 + t * d.1, q.2 + t * d.2) ≤ 0) ∧
      (∃ ℓ ∈ S, 0 < dirEval ℓ d ∧ evalForm ℓ (q.1 + t * d.1, q.2 + t * d.2) = 0) ∧
      ((∀ ℓ ∈ S, 0 < dirEval ℓ d → evalForm ℓ q < 0) → 0 < t) := by
  classical
  let Spos : Finset AffForm := S.filter (fun ℓ => 0 < dirEval ℓ d)
  have hne : Spos.Nonempty := by
    obtain ⟨ℓ, hℓS, hℓd⟩ := exists_pos_dirEval hU hW hT hd
    exact ⟨ℓ, Finset.mem_filter.2 ⟨hℓS, hℓd⟩⟩
  obtain ⟨ℓs, hℓs_mem, hℓs_min⟩ :=
    Finset.exists_min_image Spos (fun ℓ => (-evalForm ℓ q) / dirEval ℓ d) hne
  have hℓsS : ℓs ∈ S := (Finset.mem_filter.1 hℓs_mem).1
  have hℓsd : 0 < dirEval ℓs d := (Finset.mem_filter.1 hℓs_mem).2
  let t : ℝ := (-evalForm ℓs q) / dirEval ℓs d
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hq ℓs hℓsS]) hℓsd.le
  refine ⟨t, ht0, ?_, ?_, ?_⟩
  · intro ℓ hℓ
    rw [evalForm_add_smul]
    by_cases hpos : 0 < dirEval ℓ d
    · have hmem : ℓ ∈ Spos := Finset.mem_filter.2 ⟨hℓ, hpos⟩
      have hle : t ≤ (-evalForm ℓ q) / dirEval ℓ d := hℓs_min ℓ hmem
      have hmul : t * dirEval ℓ d ≤ -evalForm ℓ q := (le_div_iff₀ hpos).1 hle
      linarith
    · push Not at hpos
      have : t * dirEval ℓ d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hpos
      linarith [hq ℓ hℓ]
  · refine ⟨ℓs, hℓsS, hℓsd, ?_⟩
    rw [evalForm_add_smul]
    dsimp [t]
    rw [div_mul_cancel₀ _ (ne_of_gt hℓsd)]
    ring
  · intro hstrict
    exact div_pos (by linarith [hstrict ℓs hℓsS hℓsd]) hℓsd

private lemma inZone_of_sides {R1 : ℝ} {S : Finset AffForm}
    (hU : sideU ∈ S) (hW : sideW ∈ S) (hT : sideTop R1 ∈ S)
    {q : ℝ × ℝ} (hq : ∀ ℓ ∈ S, evalForm ℓ q ≤ 0) : inZone R1 q := by
  have h1 := hq sideU hU
  have h2 := hq sideW hW
  have h3 := hq (sideTop R1) hT
  simp only [evalForm, sideU, sideW, sideTop] at h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith⟩

/-- From a point `q ≠ (0, 0)` in the closed cell lying on a nondegenerate line `ℓ₁ ∈ S`,
reach a vertex `v ≠ (0, 0)` of `A` in the closed cell. -/
private lemma vertex_from_line {R1 : ℝ} {A S : Finset AffForm} (hSA : S ⊆ A)
    (hU : sideU ∈ S) (hW : sideW ∈ S) (hT : sideTop R1 ∈ S)
    {q : ℝ × ℝ} (hq : ∀ ℓ ∈ S, evalForm ℓ q ≤ 0) (hq0 : q ≠ (0, 0))
    {ℓ₁ : AffForm} (hℓ₁S : ℓ₁ ∈ S) (hℓ₁nd : NonDegen ℓ₁) (hℓ₁q : evalForm ℓ₁ q = 0) :
    ∃ v : ℝ × ℝ, IsVertex R1 A v ∧ v ≠ (0, 0) ∧ (∀ ℓ ∈ S, evalForm ℓ v ≤ 0) := by
  by_cases hv : ∃ ℓ₂ ∈ S, detForm ℓ₁ ℓ₂ ≠ 0 ∧ evalForm ℓ₂ q = 0
  · obtain ⟨ℓ₂, hℓ₂S, hdet, hℓ₂q⟩ := hv
    exact ⟨q, ⟨inZone_of_sides hU hW hT hq, ℓ₁, hSA hℓ₁S, ℓ₂, hSA hℓ₂S, hdet, hℓ₁q, hℓ₂q⟩,
      hq0, hq⟩
  · push Not at hv
    let d : ℝ × ℝ := (-ℓ₁.2.1, ℓ₁.1)
    have hd : d ≠ (0, 0) := by
      intro h
      simp only [d, Prod.mk.injEq] at h
      exact hℓ₁nd (Prod.ext h.2 (by linarith))
    have hnd : (-d.1, -d.2) ≠ (0, 0) := by
      intro h
      simp only [Prod.mk.injEq] at h
      exact hd (Prod.ext (by linarith) (by linarith))
    have hdir_det : ∀ ℓ : AffForm, dirEval ℓ d = detForm ℓ₁ ℓ := by
      intro ℓ; unfold dirEval detForm; dsimp [d]; ring
    have hdir_neg_det : ∀ ℓ : AffForm, dirEval ℓ (-d.1, -d.2) = -detForm ℓ₁ ℓ := by
      intro ℓ; unfold dirEval detForm; dsimp [d]; ring
    have hdir1 : dirEval ℓ₁ d = 0 := by rw [hdir_det]; unfold detForm; ring
    have hdir1_neg : dirEval ℓ₁ (-d.1, -d.2) = 0 := by rw [hdir_neg_det]; unfold detForm; ring
    obtain ⟨tp, _, hqp_cell, ⟨ℓp, hℓpS, hℓpd, hℓpq⟩, htp_strict⟩ :=
      shoot_ray hU hW hT hq hd
    obtain ⟨tm, _, hqm_cell, ⟨ℓm, hℓmS, hℓmd, hℓmq⟩, htm_strict⟩ :=
      shoot_ray hU hW hT hq hnd
    have htp : 0 < tp := htp_strict (fun ℓ hℓS hpos => by
      have hne0 : detForm ℓ₁ ℓ ≠ 0 := by rw [← hdir_det]; exact ne_of_gt hpos
      exact lt_of_le_of_ne (hq ℓ hℓS) (hv ℓ hℓS hne0))
    have htm : 0 < tm := htm_strict (fun ℓ hℓS hpos => by
      have hne0 : detForm ℓ₁ ℓ ≠ 0 := by
        intro h0; rw [hdir_neg_det, h0, neg_zero] at hpos; linarith
      exact lt_of_le_of_ne (hq ℓ hℓS) (hv ℓ hℓS hne0))
    let vp : ℝ × ℝ := (q.1 + tp * d.1, q.2 + tp * d.2)
    let vm : ℝ × ℝ := (q.1 + tm * (-d.1), q.2 + tm * (-d.2))
    have hvp_ne_vm : vp ≠ vm := by
      intro heq
      simp only [vp, vm, Prod.mk.injEq] at heq
      have hsum : tp + tm ≠ 0 := ne_of_gt (by linarith)
      have h1 : (tp + tm) * d.1 = 0 := by linarith [heq.1]
      have h2 : (tp + tm) * d.2 = 0 := by linarith [heq.2]
      exact hd (Prod.ext ((mul_eq_zero.1 h1).resolve_left hsum)
        ((mul_eq_zero.1 h2).resolve_left hsum))
    have hvp_vert : IsVertex R1 A vp := by
      refine ⟨inZone_of_sides hU hW hT hqp_cell, ℓ₁, hSA hℓ₁S, ℓp, hSA hℓpS, ?_, ?_, hℓpq⟩
      · rw [← hdir_det]; exact ne_of_gt hℓpd
      · rw [evalForm_add_smul, hℓ₁q, hdir1]; ring
    have hvm_vert : IsVertex R1 A vm := by
      refine ⟨inZone_of_sides hU hW hT hqm_cell, ℓ₁, hSA hℓ₁S, ℓm, hSA hℓmS, ?_, ?_, hℓmq⟩
      · intro h0; rw [hdir_neg_det, h0, neg_zero] at hℓmd; linarith
      · show evalForm ℓ₁ (q.1 + tm * (-d.1, -d.2).1, q.2 + tm * (-d.1, -d.2).2) = 0
        rw [evalForm_add_smul, hℓ₁q, hdir1_neg]; ring
    by_cases hvp0 : vp = (0, 0)
    · exact ⟨vm, hvm_vert, fun h => hvp_ne_vm (hvp0.trans h.symm), hqm_cell⟩
    · exact ⟨vp, hvp_vert, hvp0, hqp_cell⟩

/-- Geometric core of Lemma H: every `p ∈ Z(R₁) \ {(0, 0)}` is dominated in all open
half-plane indicators of `A` by some arrangement vertex `v ∈ Z(R₁) \ {(0, 0)}`. -/
theorem exists_vertex_dominated (R1 : ℝ) (A : Finset AffForm)
    (hnd : ∀ ℓ ∈ A, NonDegen ℓ)
    (hU : sideU ∈ A) (hW : sideW ∈ A) (hT : sideTop R1 ∈ A)
    {p : ℝ × ℝ} (hp : inZone R1 p) (hp0 : p ≠ (0, 0)) :
    ∃ v : ℝ × ℝ, IsVertex R1 A v ∧ v ≠ (0, 0) ∧
      (∀ ℓ ∈ A, 0 < evalForm ℓ v → 0 < evalForm ℓ p) := by
  classical
  let S : Finset AffForm := A.filter (fun ℓ => evalForm ℓ p ≤ 0)
  have hSA : S ⊆ A := Finset.filter_subset _ _
  have hUS : sideU ∈ S := Finset.mem_filter.2 ⟨hU, by unfold evalForm sideU; linarith [hp.1]⟩
  have hWS : sideW ∈ S := Finset.mem_filter.2 ⟨hW, by unfold evalForm sideW; linarith [hp.2.1]⟩
  have hTS : sideTop R1 ∈ S :=
    Finset.mem_filter.2 ⟨hT, by unfold evalForm sideTop; linarith [hp.2.2]⟩
  have hpS : ∀ ℓ ∈ S, evalForm ℓ p ≤ 0 := fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2
  have finish : ∀ v : ℝ × ℝ, IsVertex R1 A v → v ≠ (0, 0) → (∀ ℓ ∈ S, evalForm ℓ v ≤ 0) →
      ∃ v' : ℝ × ℝ, IsVertex R1 A v' ∧ v' ≠ (0, 0) ∧
        (∀ ℓ ∈ A, 0 < evalForm ℓ v' → 0 < evalForm ℓ p) := by
    intro v hv hv0 hvS
    refine ⟨v, hv, hv0, fun ℓ hℓA hpos => ?_⟩
    by_contra hle
    push Not at hle
    have hℓS : ℓ ∈ S := Finset.mem_filter.2 ⟨hℓA, hle⟩
    linarith [hvS ℓ hℓS]
  by_cases hon : ∃ ℓ₁ ∈ S, evalForm ℓ₁ p = 0
  · obtain ⟨ℓ₁, hℓ₁S, hℓ₁p⟩ := hon
    obtain ⟨v, hv, hv0, hvS⟩ :=
      vertex_from_line hSA hUS hWS hTS hpS hp0 hℓ₁S (hnd ℓ₁ (hSA hℓ₁S)) hℓ₁p
    exact finish v hv hv0 hvS
  · push Not at hon
    have hp_strict : ∀ ℓ ∈ S, evalForm ℓ p < 0 := fun ℓ hℓ =>
      lt_of_le_of_ne (hpS ℓ hℓ) (hon ℓ hℓ)
    let d : ℝ × ℝ := (1, 0)
    have hd : d ≠ (0, 0) := by intro h; simp [d] at h
    have hnd_d : (-d.1, -d.2) ≠ (0, 0) := by intro h; simp [d] at h
    obtain ⟨tp, _, hqp_cell, ⟨ℓp, hℓpS, _, hℓpq⟩, htp_strict⟩ :=
      shoot_ray hUS hWS hTS hpS hd
    obtain ⟨tm, _, hqm_cell, ⟨ℓm, hℓmS, _, hℓmq⟩, htm_strict⟩ :=
      shoot_ray hUS hWS hTS hpS hnd_d
    have htp : 0 < tp := htp_strict (fun ℓ hℓS _ => hp_strict ℓ hℓS)
    have htm : 0 < tm := htm_strict (fun ℓ hℓS _ => hp_strict ℓ hℓS)
    let qp : ℝ × ℝ := (p.1 + tp * d.1, p.2 + tp * d.2)
    let qm : ℝ × ℝ := (p.1 + tm * (-d.1), p.2 + tm * (-d.2))
    have hqp_ne_qm : qp ≠ qm := by
      intro heq
      simp only [qp, qm, d, Prod.mk.injEq] at heq
      linarith [heq.1]
    by_cases hqp0 : qp = (0, 0)
    · have hqm0 : qm ≠ (0, 0) := fun h => hqp_ne_qm (hqp0.trans h.symm)
      obtain ⟨v, hv, hv0, hvS⟩ :=
        vertex_from_line hSA hUS hWS hTS hqm_cell hqm0 hℓmS (hnd ℓm (hSA hℓmS)) hℓmq
      exact finish v hv hv0 hvS
    · obtain ⟨v, hv, hv0, hvS⟩ :=
        vertex_from_line hSA hUS hWS hTS hqp_cell hqp0 hℓpS (hnd ℓp (hSA hℓpS)) hℓpq
      exact finish v hv hv0 hvS

/-- **Lemma H (`lemma_H_vertex_principle`):** Let `Z(R₁) = {u ≥ 0, w ≥ 0, u + 2w ≤ R₁}`,
let `A` be a finite arrangement of nondegenerate lines containing the three side lines of `Z(R₁)`,
and let `f : ℝ × ℝ → ℕ` be non-decreasing in the open half-plane indicators `{0 < evalForm ℓ}`
for `ℓ ∈ A`. Then for every `p ∈ Z(R₁) \ {(0, 0)}`, there exists an arrangement vertex
`v ∈ Z(R₁) \ {(0, 0)}` with `f v ≤ f p`. -/
theorem lemma_H_vertex_principle (R1 : ℝ) (A : Finset AffForm)
    (hnd : ∀ ℓ ∈ A, NonDegen ℓ)
    (hU : sideU ∈ A) (hW : sideW ∈ A) (hT : sideTop R1 ∈ A)
    (f : ℝ × ℝ → ℕ)
    (hf : ∀ q₁ q₂ : ℝ × ℝ, inZone R1 q₁ → inZone R1 q₂ →
      (∀ ℓ ∈ A, 0 < evalForm ℓ q₁ → 0 < evalForm ℓ q₂) → f q₁ ≤ f q₂)
    {p : ℝ × ℝ} (hp : inZone R1 p) (hp0 : p ≠ (0, 0)) :
    ∃ v : ℝ × ℝ, IsVertex R1 A v ∧ v ≠ (0, 0) ∧ f v ≤ f p := by
  obtain ⟨v, hv, hv0, hdom⟩ := exists_vertex_dominated R1 A hnd hU hW hT hp hp0
  exact ⟨v, hv, hv0, hf v p hv.1 hp hdom⟩

/-! ### Half-plane forms of Lemma P and `arr_verify` soundness (Proposition V) -/

/-- The affine form `N_k(S) - 3 (L' - 1) d_k` whose positive half-plane is `H_k(S, L')`
for pair `k ∈ {0, 1, 2}` (representing pairs 1, 2, 3), level `S`, and threshold `L' ≥ 1`. -/
def hpForm (k : Fin 3) (n S L' : ℕ) : AffForm :=
  let h : ℝ := ((n - 1 : ℕ) : ℝ)
  let Sr : ℝ := (S : ℝ)
  let Lm : ℝ := ((L' - 1 : ℕ) : ℝ)
  match k with
  | ⟨0, _⟩ => (4 * h - Sr, 2 * h + Sr - 3 * Lm, h - 3 - Sr)
  | ⟨1, _⟩ => (2 * Sr - 2 * h - 3 * Lm, 2 * h + Sr - 3 * Lm, h - 3 - Sr)
  | ⟨2, _⟩ => (2 * Sr - 2 * h - 3 * Lm, Sr - 4 * h, h - 3 - Sr)

/-- The two affine forms defining the open coupling region `K` for even `n = 2c + 4`. -/
def KForm1 (c : ℕ) : AffForm := (-(3 * (c : ℝ) + 8), 3 * (c : ℝ) + 5, 1)
def KForm2 (c : ℕ) : AffForm := (-(3 * (c : ℝ) + 5), -(6 * (c : ℝ) + 13), 1)

lemma KForm_nonDegen (c : ℕ) : NonDegen (KForm1 c) ∧ NonDegen (KForm2 c) := by
  constructor <;> intro h <;> simp only [KForm1, KForm2, Prod.mk.injEq] at h <;> linarith

lemma inK_iff_KForm (c : ℕ) (p : ℝ × ℝ) :
    inK c p.1 p.2 ↔ 0 < evalForm (KForm1 c) p ∧ 0 < evalForm (KForm2 c) p := by
  unfold inK evalForm KForm1 KForm2
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma eval_hpForm0 {n : ℕ} (hn : 1 ≤ n) (S L' : ℕ) (p : ℝ × ℝ) :
    evalForm (hpForm 0 n S L') p =
      3 * (gamma1 n p.1 p.2 - x2 p.1 p.2 * (S : ℝ) - ((L' - 1 : ℕ) : ℝ) * (x3 p.1 p.2 - x2 p.1 p.2)) := by
  unfold evalForm hpForm gamma1 s1 x1 x2 x3
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [hcast]; ring

lemma eval_hpForm1 {n : ℕ} (hn : 1 ≤ n) (S L' : ℕ) (p : ℝ × ℝ) :
    evalForm (hpForm 1 n S L') p =
      3 * (gamma2 n p.1 p.2 - x1 p.1 p.2 * (S : ℝ) - ((L' - 1 : ℕ) : ℝ) * (x3 p.1 p.2 - x1 p.1 p.2)) := by
  unfold evalForm hpForm gamma2 s2 x1 x2 x3
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [hcast]; ring

lemma eval_hpForm2 {n : ℕ} (hn : 1 ≤ n) (S L' : ℕ) (p : ℝ × ℝ) :
    evalForm (hpForm 2 n S L') p =
      3 * (gamma3 n p.1 p.2 - x1 p.1 p.2 * (S : ℝ) - ((L' - 1 : ℕ) : ℝ) * (x2 p.1 p.2 - x1 p.1 p.2)) := by
  unfold evalForm hpForm gamma3 s3 x1 x2 x3
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [hcast]; ring

/-- On `u > 0, w > 0`, `0 < evalForm (hpForm k n S L') (u, w)` holds iff `L' ≤ L_k(S)`
(for `1 ≤ L' ≤ cap S`). -/
lemma hpForm_iff_le_Lval {n : ℕ} (hn : 1 ≤ n) (k : Fin 3) (S L' : ℕ)
    (hL1 : 1 ≤ L') (hLcap : L' ≤ cap S) {u w : ℝ} (hu : 0 < u) (hw : 0 < w) :
    0 < evalForm (hpForm k n S L') (u, w) ↔
      L' ≤ match k with
        | ⟨0, _⟩ => Lval (x2 u w) (x3 u w) (gamma1 n u w) S
        | ⟨1, _⟩ => Lval (x1 u w) (x3 u w) (gamma2 n u w) S
        | ⟨2, _⟩ => Lval (x1 u w) (x2 u w) (gamma3 n u w) S := by
  fin_cases k
  · have hlt : x2 u w < x3 u w := by unfold x2 x3; linarith
    have hd : 0 < x3 u w - x2 u w := by linarith
    change 0 < evalForm (hpForm 0 n S L') (u, w) ↔ L' ≤ Lval (x2 u w) (x3 u w) (gamma1 n u w) S
    rw [eval_hpForm0 hn]
    unfold Lval; rw [ite_eq_left hlt]
    have hiff : L' ≤ min (cap S) ⌈(gamma1 n u w - x2 u w * (S : ℝ)) / (x3 u w - x2 u w)⌉₊ ↔
        L' - 1 < ⌈(gamma1 n u w - x2 u w * (S : ℝ)) / (x3 u w - x2 u w)⌉₊ := by omega
    rw [hiff, Nat.lt_ceil, lt_div_iff₀ hd]
    constructor <;> intro h <;> linarith
  · have hlt : x1 u w < x3 u w := by unfold x1 x3; linarith
    have hd : 0 < x3 u w - x1 u w := by linarith
    change 0 < evalForm (hpForm 1 n S L') (u, w) ↔ L' ≤ Lval (x1 u w) (x3 u w) (gamma2 n u w) S
    rw [eval_hpForm1 hn]
    unfold Lval; rw [ite_eq_left hlt]
    have hiff : L' ≤ min (cap S) ⌈(gamma2 n u w - x1 u w * (S : ℝ)) / (x3 u w - x1 u w)⌉₊ ↔
        L' - 1 < ⌈(gamma2 n u w - x1 u w * (S : ℝ)) / (x3 u w - x1 u w)⌉₊ := by omega
    rw [hiff, Nat.lt_ceil, lt_div_iff₀ hd]
    constructor <;> intro h <;> linarith
  · have hlt : x1 u w < x2 u w := by unfold x1 x2; linarith
    have hd : 0 < x2 u w - x1 u w := by linarith
    change 0 < evalForm (hpForm 2 n S L') (u, w) ↔ L' ≤ Lval (x1 u w) (x2 u w) (gamma3 n u w) S
    rw [eval_hpForm2 hn]
    unfold Lval; rw [ite_eq_left hlt]
    have hiff : L' ≤ min (cap S) ⌈(gamma3 n u w - x1 u w * (S : ℝ)) / (x2 u w - x1 u w)⌉₊ ↔
        L' - 1 < ⌈(gamma3 n u w - x1 u w * (S : ℝ)) / (x2 u w - x1 u w)⌉₊ := by omega
    rw [hiff, Nat.lt_ceil, lt_div_iff₀ hd]
    constructor <;> intro h <;> linarith

/-- Parameters of an `arr_verify` run for box size `n`. -/
structure ArrVerifyCfg where
  R1 : ℝ
  slo : Fin 3 → ℕ
  shi : Fin 3 → ℕ
  Fp : ℕ
  TUP : ℕ

open Classical in
/-- The finite line arrangement `A(cfg)` built by `arr_verify`: the 3 side lines of `Z(R₁)`,
all nondegenerate half-plane boundary lines in the 3 windows, and (for even `n`) the 2 lines of `K`. -/
def arrLines (n : ℕ) (cfg : ArrVerifyCfg) : Finset AffForm :=
  let hpAll : Finset AffForm :=
    (Finset.univ : Finset (Fin 3)).biUnion fun k =>
      (Finset.Icc (cfg.slo k) (cfg.shi k)).biUnion fun S =>
        (Finset.Icc (max 1 (cap S - cfg.Fp)) (cap S)).image fun L' => hpForm k n S L'
  let base : Finset AffForm :=
    {sideU, sideW, sideTop cfg.R1} ∪ hpAll.filter (fun ℓ => NonDegen ℓ)
  if Even n then base ∪ {KForm1 ((n - 4) / 2), KForm2 ((n - 4) / 2)} else base

lemma arrLines_nonDegen (n : ℕ) (cfg : ArrVerifyCfg) :
    ∀ ℓ ∈ arrLines n cfg, NonDegen ℓ := by
  classical
  intro ℓ hℓ
  unfold arrLines at hℓ
  dsimp only at hℓ
  have hbase : ∀ x ∈ ({sideU, sideW, sideTop cfg.R1} : Finset AffForm) ∪
      ((Finset.univ : Finset (Fin 3)).biUnion fun k =>
        (Finset.Icc (cfg.slo k) (cfg.shi k)).biUnion fun S =>
          (Finset.Icc (max 1 (cap S - cfg.Fp)) (cap S)).image fun L' => hpForm k n S L').filter
        (fun ℓ => NonDegen ℓ), NonDegen x := by
    intro x hx
    rcases Finset.mem_union.1 hx with hs | hf
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · intro h; simp [sideU] at h
      · intro h; simp [sideW] at h
      · intro h; simp [sideTop] at h
    · exact (Finset.mem_filter.1 hf).2
  by_cases hev : Even n
  · rw [ite_eq_left hev] at hℓ
    rcases Finset.mem_union.1 hℓ with hb | hk
    · exact hbase ℓ hb
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact (KForm_nonDegen _).1
      · exact (KForm_nonDegen _).2
  · rw [ite_eq_right hev] at hℓ
    exact hbase ℓ hℓ

lemma arrLines_sides (n : ℕ) (cfg : ArrVerifyCfg) :
    sideU ∈ arrLines n cfg ∧ sideW ∈ arrLines n cfg ∧ sideTop cfg.R1 ∈ arrLines n cfg := by
  classical
  unfold arrLines
  dsimp only
  by_cases hev : Even n
  · rw [ite_eq_left hev]; refine ⟨?_, ?_, ?_⟩ <;> simp
  · rw [ite_eq_right hev]; refine ⟨?_, ?_, ?_⟩ <;> simp

/-- Helper: if every nondegenerate line in `A` has indicator at `q₁` implying indicator at `q₂`,
then ANY form `ℓ` whose nondegenerate version lies in `A` also satisfies
`0 < evalForm ℓ q₁ → 0 < evalForm ℓ q₂` (since a degenerate form `(0, 0, c)` is constant!). -/
private lemma evalForm_mono_of_nonDegen {A : Finset AffForm} {q₁ q₂ : ℝ × ℝ}
    (hdom : ∀ ℓ ∈ A, 0 < evalForm ℓ q₁ → 0 < evalForm ℓ q₂)
    {ℓ : AffForm} (hmem : NonDegen ℓ → ℓ ∈ A) :
    0 < evalForm ℓ q₁ → 0 < evalForm ℓ q₂ := by
  by_cases hnd : NonDegen ℓ
  · exact hdom ℓ (hmem hnd)
  · unfold NonDegen at hnd
    push Not at hnd
    simp only [Prod.mk.injEq] at hnd
    obtain ⟨h1, h2⟩ := hnd
    intro hpos
    unfold evalForm at hpos ⊢
    rw [h1, h2] at hpos ⊢
    linarith

/-- Half-plane fullness indicator for pair `k` at level `S`. -/
def isFullHp (k : Fin 3) (n S : ℕ) (p : ℝ × ℝ) : Prop :=
  0 < evalForm (hpForm k n S (cap S)) p

open Classical in
/-- Truncated level height `L_trunc(k, S)` from the top `Fp + 1` half-planes at level `S`. -/
def Ltrunc (k : Fin 3) (n Fp S : ℕ) (p : ℝ × ℝ) : ℕ :=
  let lo := max 1 (cap S - Fp)
  if 0 < evalForm (hpForm k n S lo) p then
    (lo - 1) + ((Finset.Icc lo (cap S)).filter (fun L' => 0 < evalForm (hpForm k n S L') p)).card
  else 0

/-- Truncated pairing value `G_trunc(k, S) = T2(S + 1) - T2(S + 1 - 2 L_trunc(k, S))`. -/
def Gtrunc (k : Fin 3) (n Fp S : ℕ) (p : ℝ × ℝ) : ℕ :=
  T2 ((S : ℤ) + 1) - T2 ((S : ℤ) + 1 - 2 * (Ltrunc k n Fp S p : ℤ))

open Classical in
/-- Largest full level `S_k ∈ [slo, shi]` (returning `0` on window failure). -/
def lastFull (k : Fin 3) (n slo shi : ℕ) (p : ℝ × ℝ) : ℕ :=
  ((Finset.Icc slo shi).filter (fun S => isFullHp k n S p)).sup id

open Classical in
/-- `arr_verify`'s truncated pairing bound `bt_k(p)` for pair `k` (returns `0` on window failure). -/
def btPair (k : Fin 3) (n : ℕ) (cfg : ArrVerifyCfg) (p : ℝ × ℝ) : ℕ :=
  if isFullHp k n (cfg.slo k) p then
    let Sk := lastFull k n (cfg.slo k) (cfg.shi k) p
    max (T2 ((Sk : ℤ) + 1))
      ((Finset.Ioc Sk (min (cfg.shi k) (Sk + 1 + cfg.TUP))).sup (fun S => Gtrunc k n cfg.Fp S p))
  else 0

open Classical in
/-- `arr_verify`'s total valuation `val(p)`: `bt₁ + bt₂ + bt₃`, or for even `n`,
`max(bt₁ + bt₂ + bt₃, (T*(n) + 1) · [p ∈ K])` (and `0` if any window fails). -/
def arrVal (n : ℕ) (cfg : ArrVerifyCfg) (p : ℝ × ℝ) : ℕ :=
  if isFullHp 0 n (cfg.slo 0) p ∧ isFullHp 1 n (cfg.slo 1) p ∧ isFullHp 2 n (cfg.slo 2) p then
    let s := btPair 0 n cfg p + btPair 1 n cfg p + btPair 2 n cfg p
    if Even n then max s (if inK ((n - 4) / 2) p.1 p.2 then Tstar n + 1 else 0) else s
  else 0

/-- Passing condition of `arr_verify`: `R₁ ≥ 3 r(n)`, `slo k ≤ shi k`, and at every
arrangement vertex `v ≠ (0, 0)` of `A(cfg)` in `Z(R₁)`, `arrVal n cfg v ≥ D(n)`
(which forces zero window failures since `D(n) ≥ 1`). -/
def ArrVerifyPass (n : ℕ) (cfg : ArrVerifyCfg) : Prop :=
  3 * rad n ≤ cfg.R1 ∧
  (∀ k : Fin 3, cfg.slo k ≤ cfg.shi k) ∧
  (∀ v : ℝ × ℝ, IsVertex cfg.R1 (arrLines n cfg) v → v ≠ (0, 0) → D n ≤ arrVal n cfg v)

private lemma T2_mono_int {a b : ℤ} (h : a ≤ b) : T2 a ≤ T2 b := by
  unfold T2
  split_ifs with ha hb
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · omega
  · apply Nat.div_le_div_right; apply Nat.pow_le_pow_left; omega

private def Lpair (k : Fin 3) (n : ℕ) (u w : ℝ) (S : ℕ) : ℕ :=
  match k with
  | ⟨0, _⟩ => Lval (x2 u w) (x3 u w) (gamma1 n u w) S
  | ⟨1, _⟩ => Lval (x1 u w) (x3 u w) (gamma2 n u w) S
  | ⟨2, _⟩ => Lval (x1 u w) (x2 u w) (gamma3 n u w) S

private def Gpair (k : Fin 3) (n : ℕ) (u w : ℝ) (S : ℕ) : ℕ :=
  match k with
  | ⟨0, _⟩ => G1 n u w S
  | ⟨1, _⟩ => G2 n u w S
  | ⟨2, _⟩ => G3 n u w S

private def Bpair (k : Fin 3) (n : ℕ) (u w : ℝ) : ℕ :=
  match k with
  | ⟨0, _⟩ => B1 n u w
  | ⟨1, _⟩ => B2 n u w
  | ⟨2, _⟩ => B3 n u w

private lemma Ltrunc_le_Lval {n : ℕ} (hn : 1 ≤ n) (k : Fin 3) (Fp S : ℕ)
    {u w : ℝ} (hu : 0 < u) (hw : 0 < w) :
    Ltrunc k n Fp S (u, w) ≤ Lpair k n u w S := by
  classical
  unfold Ltrunc
  dsimp only
  set lo := max 1 (cap S - Fp)
  have hlo1 : 1 ≤ lo := le_max_left _ _
  have hlocap : lo ≤ cap S := by dsimp [lo]; unfold cap; omega
  by_cases h0 : 0 < evalForm (hpForm k n S lo) (u, w)
  · rw [ite_eq_left h0]
    have hlo_le : lo ≤ Lpair k n u w S := (hpForm_iff_le_Lval hn k S lo hlo1 hlocap hu hw).1 h0
    have hsub : (Finset.Icc lo (cap S)).filter (fun L' => 0 < evalForm (hpForm k n S L') (u, w)) ⊆
        Finset.Icc lo (Lpair k n u w S) := by
      intro L' hL'
      rw [Finset.mem_filter, Finset.mem_Icc] at hL'
      rw [Finset.mem_Icc]
      exact ⟨hL'.1.1, (hpForm_iff_le_Lval hn k S L' (by omega) hL'.1.2 hu hw).1 hL'.2⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    omega
  · rw [ite_eq_right h0]; exact Nat.zero_le _

private lemma Gtrunc_le_G {n : ℕ} (hn : 1 ≤ n) (k : Fin 3) (Fp S : ℕ)
    {u w : ℝ} (hu : 0 < u) (hw : 0 < w) :
    Gtrunc k n Fp S (u, w) ≤ Gpair k n u w S := by
  have hL := Ltrunc_le_Lval hn k Fp S hu hw
  unfold Lpair at hL
  unfold Gtrunc Gpair G1 G2 G3 Gval
  fin_cases k <;> dsimp only at hL ⊢ <;>
    exact Nat.sub_le_sub_left (T2_mono_int (by omega)) _

private lemma btPair_le_B {n : ℕ} (hn : 1 ≤ n) (k : Fin 3) (cfg : ArrVerifyCfg)
    (hwin : cfg.slo k ≤ cfg.shi k) {u w : ℝ} (hx1 : 0 < x1 u w) (hu : 0 < u) (hw : 0 < w) :
    btPair k n cfg (u, w) ≤ Bpair k n u w := by
  classical
  unfold btPair
  by_cases hfull_lo : isFullHp k n (cfg.slo k) (u, w)
  · rw [ite_eq_left hfull_lo]
    dsimp only
    set Sk := lastFull k n (cfg.slo k) (cfg.shi k) (u, w)
    have hne : ((Finset.Icc (cfg.slo k) (cfg.shi k)).filter
        (fun S => isFullHp k n S (u, w))).Nonempty :=
      ⟨cfg.slo k, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_refl _, hwin⟩, hfull_lo⟩⟩
    obtain ⟨Sm, hSm_mem, hSm_max⟩ := Finset.exists_max_image _ id hne
    have hSk_eq : Sk = Sm := by
      apply le_antisymm
      · exact Finset.sup_le (fun S hS => hSm_max S hS)
      · exact Finset.le_sup (f := id) hSm_mem
    have hSk_full : isFullHp k n Sk (u, w) := by
      rw [hSk_eq]; exact (Finset.mem_filter.1 hSm_mem).2
    have hT2_le : T2 ((Sk : ℤ) + 1) ≤ Bpair k n u w := by
      have hcap1 : 1 ≤ cap Sk := by unfold cap; omega
      have hfull_eq := (hpForm_iff_le_Lval hn k Sk (cap Sk) hcap1 (le_refl _) hu hw).1 hSk_full
      unfold Bpair
      fin_cases k <;> dsimp only at hfull_eq ⊢
      · have hEq : Lval (x2 u w) (x3 u w) (gamma1 n u w) Sk = cap Sk :=
          le_antisymm (Lval_le_cap _ _ _ _) hfull_eq
        have hG := G1_le_B1 hn hx1 hu.le hw.le Sk
        unfold G1 at hG; rwa [Gval_of_full hEq] at hG
      · have hEq : Lval (x1 u w) (x3 u w) (gamma2 n u w) Sk = cap Sk :=
          le_antisymm (Lval_le_cap _ _ _ _) hfull_eq
        have hG := G2_le_B2 hn hx1 hu.le hw.le Sk
        unfold G2 at hG; rwa [Gval_of_full hEq] at hG
      · have hEq : Lval (x1 u w) (x2 u w) (gamma3 n u w) Sk = cap Sk :=
          le_antisymm (Lval_le_cap _ _ _ _) hfull_eq
        have hG := G3_le_B3 hn hx1 hu.le hw.le Sk
        unfold G3 at hG; rwa [Gval_of_full hEq] at hG
    refine max_le hT2_le (Finset.sup_le fun S _ => ?_)
    have hG := Gtrunc_le_G hn k cfg.Fp S hu hw
    unfold Gpair at hG
    unfold Bpair
    fin_cases k <;> dsimp only at hG ⊢
    · exact le_trans hG (G1_le_B1 hn hx1 hu.le hw.le S)
    · exact le_trans hG (G2_le_B2 hn hx1 hu.le hw.le S)
    · exact le_trans hG (G3_le_B3 hn hx1 hu.le hw.le S)
  · rw [ite_eq_right hfull_lo]; exact Nat.zero_le _

/-- Proposition V step (c): `arrVal` is monotone non-decreasing in the open half-plane
indicators of `arrLines n cfg`. -/
lemma arrVal_mono (n : ℕ) (cfg : ArrVerifyCfg) (hwin : ∀ k : Fin 3, cfg.slo k ≤ cfg.shi k)
    {q₁ q₂ : ℝ × ℝ}
    (hdom : ∀ ℓ ∈ arrLines n cfg, 0 < evalForm ℓ q₁ → 0 < evalForm ℓ q₂) :
    arrVal n cfg q₁ ≤ arrVal n cfg q₂ := by
  classical
  have hhp_lo : ∀ k : Fin 3, isFullHp k n (cfg.slo k) q₁ → isFullHp k n (cfg.slo k) q₂ := by
    intro k
    apply evalForm_mono_of_nonDegen hdom
    intro hnd
    unfold arrLines; dsimp only
    have hin : hpForm k n (cfg.slo k) (cap (cfg.slo k)) ∈
        ((Finset.univ : Finset (Fin 3)).biUnion fun k' =>
          (Finset.Icc (cfg.slo k') (cfg.shi k')).biUnion fun S' =>
            (Finset.Icc (max 1 (cap S' - cfg.Fp)) (cap S')).image fun L'' =>
              hpForm k' n S' L'').filter (fun ℓ => NonDegen ℓ) := by
      refine Finset.mem_filter.2 ⟨?_, hnd⟩
      refine Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, ?_⟩
      refine Finset.mem_biUnion.2 ⟨cfg.slo k, Finset.mem_Icc.2 ⟨le_refl _, hwin k⟩, ?_⟩
      exact Finset.mem_image.2 ⟨cap (cfg.slo k),
        Finset.mem_Icc.2 ⟨by unfold cap; omega, le_refl _⟩, rfl⟩
    split_ifs
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hin)
    · exact Finset.mem_union_right _ hin
  have hbt : ∀ k : Fin 3, btPair k n cfg q₁ ≤ btPair k n cfg q₂ := fun k => by
    -- We already proved monotonicity whenever `slo k ≤ shi k`; let's inline cleanly via `hwin k`
    have hhp : ∀ S L', S ∈ Finset.Icc (cfg.slo k) (cfg.shi k) →
        L' ∈ Finset.Icc (max 1 (cap S - cfg.Fp)) (cap S) →
        0 < evalForm (hpForm k n S L') q₁ → 0 < evalForm (hpForm k n S L') q₂ := by
      intro S L' hS hL'
      apply evalForm_mono_of_nonDegen hdom
      intro hnd
      unfold arrLines; dsimp only
      have hin : hpForm k n S L' ∈
          ((Finset.univ : Finset (Fin 3)).biUnion fun k' =>
            (Finset.Icc (cfg.slo k') (cfg.shi k')).biUnion fun S' =>
              (Finset.Icc (max 1 (cap S' - cfg.Fp)) (cap S')).image fun L'' =>
                hpForm k' n S' L'').filter (fun ℓ => NonDegen ℓ) := by
        refine Finset.mem_filter.2 ⟨?_, hnd⟩
        refine Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, ?_⟩
        refine Finset.mem_biUnion.2 ⟨S, hS, ?_⟩
        exact Finset.mem_image.2 ⟨L', hL', rfl⟩
      split_ifs
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hin)
      · exact Finset.mem_union_right _ hin
    have hGmono : ∀ S ∈ Finset.Icc (cfg.slo k) (cfg.shi k),
        Gtrunc k n cfg.Fp S q₁ ≤ Gtrunc k n cfg.Fp S q₂ := by
      intro S hS
      have hLmono : Ltrunc k n cfg.Fp S q₁ ≤ Ltrunc k n cfg.Fp S q₂ := by
        unfold Ltrunc; dsimp only
        set lo := max 1 (cap S - cfg.Fp)
        have hlo_mem : lo ∈ Finset.Icc lo (cap S) :=
          Finset.mem_Icc.2 ⟨le_refl _, by dsimp [lo]; unfold cap; omega⟩
        by_cases h1 : 0 < evalForm (hpForm k n S lo) q₁
        · have h2 : 0 < evalForm (hpForm k n S lo) q₂ := hhp S lo hS hlo_mem h1
          rw [ite_eq_left h1, ite_eq_left h2]
          refine Nat.add_le_add_left (Finset.card_le_card ?_) _
          intro L' hL'
          rw [Finset.mem_filter] at hL' ⊢
          exact ⟨hL'.1, hhp S L' hS hL'.1 hL'.2⟩
        · rw [ite_eq_right h1]; exact Nat.zero_le _
      unfold Gtrunc
      exact Nat.sub_le_sub_left (T2_mono_int (by omega)) _
    unfold btPair
    by_cases h1 : isFullHp k n (cfg.slo k) q₁
    · have h2 : isFullHp k n (cfg.slo k) q₂ := hhp_lo k h1
      rw [ite_eq_left h1, ite_eq_left h2]
      dsimp only
      set S1 := lastFull k n (cfg.slo k) (cfg.shi k) q₁
      set S2 := lastFull k n (cfg.slo k) (cfg.shi k) q₂
      have hS1_le_S2 : S1 ≤ S2 := by
        unfold S1 S2 lastFull
        apply Finset.sup_le
        intro S hS
        have hSm := Finset.mem_filter.1 hS
        have hcap_mem : cap S ∈ Finset.Icc (max 1 (cap S - cfg.Fp)) (cap S) :=
          Finset.mem_Icc.2 ⟨by unfold cap; omega, le_refl _⟩
        exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hSm.1, hhp S (cap S) hSm.1 hcap_mem hSm.2⟩)
      have hlo_le : cfg.slo k ≤ S1 := by
        unfold S1 lastFull
        exact Finset.le_sup (f := id)
          (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_refl _, hwin k⟩, h1⟩)
      refine max_le (le_trans (T2_mono_int (by omega)) (le_max_left _ _))
        (Finset.sup_le fun S hS => ?_)
      rw [Finset.mem_Ioc] at hS
      by_cases hle : S ≤ S2
      · exact le_trans (Nat.sub_le _ _) (le_trans (T2_mono_int (by omega)) (le_max_left _ _))
      · push Not at hle
        have hS_Ioc : S ∈ Finset.Ioc S2 (min (cfg.shi k) (S2 + 1 + cfg.TUP)) :=
          Finset.mem_Ioc.2 ⟨hle, by omega⟩
        have hS_Icc : S ∈ Finset.Icc (cfg.slo k) (cfg.shi k) :=
          Finset.mem_Icc.2 ⟨by omega, le_trans hS.2 (min_le_left _ _)⟩
        exact le_trans (hGmono S hS_Icc)
          (le_trans (Finset.le_sup (f := fun S => Gtrunc k n cfg.Fp S q₂) hS_Ioc)
            (le_max_right _ _))
    · rw [ite_eq_right h1]; exact Nat.zero_le _
  unfold arrVal
  by_cases h1 : isFullHp 0 n (cfg.slo 0) q₁ ∧ isFullHp 1 n (cfg.slo 1) q₁ ∧ isFullHp 2 n (cfg.slo 2) q₁
  · have h2 : isFullHp 0 n (cfg.slo 0) q₂ ∧ isFullHp 1 n (cfg.slo 1) q₂ ∧ isFullHp 2 n (cfg.slo 2) q₂ :=
      ⟨hhp_lo 0 h1.1, hhp_lo 1 h1.2.1, hhp_lo 2 h1.2.2⟩
    rw [ite_eq_left h1, ite_eq_left h2]
    dsimp only
    have hsum : btPair 0 n cfg q₁ + btPair 1 n cfg q₁ + btPair 2 n cfg q₁ ≤
        btPair 0 n cfg q₂ + btPair 1 n cfg q₂ + btPair 2 n cfg q₂ := by
      have := hbt 0; have := hbt 1; have := hbt 2; omega
    by_cases hev : Even n
    · rw [ite_eq_left hev, ite_eq_left hev]
      have hK_mono : inK ((n - 4) / 2) q₁.1 q₁.2 → inK ((n - 4) / 2) q₂.1 q₂.2 := by
        rw [inK_iff_KForm, inK_iff_KForm]
        rintro ⟨ha, hb⟩
        have h1m : KForm1 ((n - 4) / 2) ∈ arrLines n cfg := by
          unfold arrLines; dsimp only; rw [ite_eq_left hev]; simp
        have h2m : KForm2 ((n - 4) / 2) ∈ arrLines n cfg := by
          unfold arrLines; dsimp only; rw [ite_eq_left hev]; simp
        exact ⟨hdom _ h1m ha, hdom _ h2m hb⟩
      by_cases hk1 : inK ((n - 4) / 2) q₁.1 q₁.2
      · rw [ite_eq_left hk1, ite_eq_left (hK_mono hk1)]
        exact max_le_max hsum (le_refl _)
      · rw [ite_eq_right hk1]
        exact max_le_max hsum (Nat.zero_le _)
    · rw [ite_eq_right hev, ite_eq_right hev]
      exact hsum
  · rw [ite_eq_right h1]; exact Nat.zero_le _

/-- **Proposition V (`prop_V_arr_verify_sound`):** For every `n ≥ 16`, if an `arr_verify`
configuration `cfg` passes at every arrangement vertex `v ≠ (0, 0)` of `A(cfg)` in `Z(cfg.R1)`,
then `(*)` holds on the entire cone and EVERY nonzero real plane cuts at most `F(n)` unit cubes. -/
theorem prop_V_arr_verify_sound (n : ℕ) (hn : 16 ≤ n) (cfg : ArrVerifyCfg)
    (hpass : ArrVerifyPass n cfg) :
    ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n := by
  apply reduction_R n hn
  intro u w t hu hw hcone
  obtain ⟨hR1, hwin, hver⟩ := hpass
  have hp_zone : inZone cfg.R1 (u, w) := ⟨hu.le, hw.le, le_trans hcone hR1⟩
  have hp_ne : (u, w) ≠ (0, 0) := fun h => by simp only [Prod.mk.injEq] at h; linarith
  have hsides := arrLines_sides n cfg
  obtain ⟨v, hv, hv0, hle⟩ := lemma_H_vertex_principle cfg.R1 (arrLines n cfg)
    (arrLines_nonDegen n cfg) hsides.1 hsides.2.1 hsides.2.2 (arrVal n cfg)
    (fun q₁ q₂ _ _ hdom => arrVal_mono n cfg hwin hdom) hp_zone hp_ne
  have hDv : D n ≤ arrVal n cfg v := hver v hv hv0
  have hDp : D n ≤ arrVal n cfg (u, w) := le_trans hDv hle
  -- `0 < x1 u w` because `n ≥ 16` gives `rad n < 1/6`, so `2u + w ≤ 2(u + 2w) ≤ 6 rad n < 1`
  have hx1_pos : 0 < x1 u w := by
    have hrad_lt : rad n < 1 / 6 := by
      have hsq : (rad n) ^ 2 < (1 / 6 : ℝ) ^ 2 := by
        rw [rad_sq]
        have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      nlinarith [rad_pos n]
    unfold x1
    linarith
  have hsumB : B1 n u w + B2 n u w + B3 n u w ≤ missedCount n u w t :=
    lemma_P_sum_B (by omega) hx1_pos hu.le hw.le t
  have hbt0 : btPair 0 n cfg (u, w) ≤ B1 n u w :=
    btPair_le_B (by omega) 0 cfg (hwin 0) hx1_pos hu hw
  have hbt1 : btPair 1 n cfg (u, w) ≤ B2 n u w :=
    btPair_le_B (by omega) 1 cfg (hwin 1) hx1_pos hu hw
  have hbt2 : btPair 2 n cfg (u, w) ≤ B3 n u w :=
    btPair_le_B (by omega) 2 cfg (hwin 2) hx1_pos hu hw
  unfold arrVal at hDp
  by_cases hfull : isFullHp 0 n (cfg.slo 0) (u, w) ∧ isFullHp 1 n (cfg.slo 1) (u, w) ∧
      isFullHp 2 n (cfg.slo 2) (u, w)
  · rw [ite_eq_left hfull] at hDp
    dsimp only at hDp
    by_cases hev : Even n
    · rw [ite_eq_left hev] at hDp
      by_cases hK : inK ((n - 4) / 2) u w
      · obtain ⟨m, hm⟩ := hev
        have hc_eq : n = 2 * ((n - 4) / 2) + 4 := by omega
        have hc1 : 1 ≤ (n - 4) / 2 := by omega
        have hC := lemma_C_coupling ((n - 4) / 2) hc1 u w t hu.le hw.le hp_ne hK
        rwa [← hc_eq] at hC
      · rw [ite_eq_right hK, max_eq_left (Nat.zero_le _)] at hDp
        omega
    · rw [ite_eq_right hev] at hDp
      omega
  · rw [ite_eq_right hfull] at hDp
    -- `D n ≥ 1` for `n ≥ 16`, contradicting `D n ≤ 0`
    have hD_pos : 1 ≤ D n := by
      unfold D F
      have h1 : 3 * n ≤ 3 * n ^ 2 := by nlinarith
      have h2 : 17 ≤ 9 * n ^ 2 + 4 * n := by nlinarith
      have h3 : (9 * n ^ 2 + 4 * n - 17) / 4 < 3 * n ^ 2 - 3 * n + 1 := by
        have h4 : 9 * n ^ 2 + 4 * n - 17 + 4 ≤ 4 * (3 * n ^ 2 - 3 * n + 1) := by
          zify [h1, h2]; nlinarith
        omega
      omega
    omega

end

end CheeseCutM
