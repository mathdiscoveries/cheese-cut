module

public import CheeseCutM.VertexPrinciple

import Mathlib.Tactic

/-!
# Theorem A (`n ≥ 700` Unconditional Proof)

Proves unconditionally over `ℝ` for every `n ≥ 700`:
* `theorem_A_ge_700`: for every `(u, w)` in `{u > 0, w > 0, u + 2w ≤ 3 r(n)}`, either
  `B₁(u, w) + B₂(u, w) + B₃(u, w) ≥ D(n)` or `n` is even and `(u, w) ∈ K((n - 4)/2)`.
* `theorem_A_upper_bound_ge_700`: combining `theorem_A_ge_700` with `lemma_P_sum_B`,
  `lemma_C_coupling`, and `reduction_R`, EVERY nonzero real plane cuts at most `F(n)`
  open unit cubes of the `n × n × n` box for all `n ≥ 700`.

Also publicly re-exports `lemma_H_vertex_principle` and `prop_V_arr_verify_sound` from
`CheeseCutM.VertexPrinciple`.
-/

@[expose] public section

namespace CheeseCutM

noncomputable section

/-! ### Step 1: Identity (A0) and integer-rounding threshold -/

/-- Identity (A0): for `n ≥ 3` (`h = n - 1`) and integers `M_k = h - 3 + μ_k ≥ -1`,
`4 (T2(M₁) + T2(M₂) + T2(M₃) - T*(n)) = 2(h - 2)(μ₁ + μ₂ + μ₃ - 1) + μ₁² + μ₂² + μ₃² - 1 - π`. -/
theorem identity_A0 (n : ℕ) (hn : 3 ≤ n) (μ₁ μ₂ μ₃ : ℤ)
    (h1 : -1 ≤ (n : ℤ) - 4 + μ₁) (h2 : -1 ≤ (n : ℤ) - 4 + μ₂) (h3 : -1 ≤ (n : ℤ) - 4 + μ₃) :
    let h : ℤ := (n : ℤ) - 1
    let M₁ : ℤ := h - 3 + μ₁
    let M₂ : ℤ := h - 3 + μ₂
    let M₃ : ℤ := h - 3 + μ₃
    let pi : ℤ :=
      (if Even M₁ then (1 : ℤ) else 0) + (if Even M₂ then (1 : ℤ) else 0) +
      (if Even M₃ then (1 : ℤ) else 0) - (if Even h then (1 : ℤ) else 2)
    4 * ((T2 M₁ : ℤ) + (T2 M₂ : ℤ) + (T2 M₃ : ℤ) - (Tstar n : ℤ)) =
      2 * (h - 2) * (μ₁ + μ₂ + μ₃ - 1) + (μ₁ ^ 2 + μ₂ ^ 2 + μ₃ ^ 2) - 1 - pi := by
  intro h M₁ M₂ M₃ pi
  have hM1 := four_mul_T2 M₁ (by dsimp [M₁, h]; omega)
  have hM2 := four_mul_T2 M₂ (by dsimp [M₂, h]; omega)
  have hM3 := four_mul_T2 M₃ (by dsimp [M₃, h]; omega)
  have hTa := four_mul_T2 ((n : ℤ) - 3) (by omega)
  have hTb := four_mul_T2 ((n : ℤ) - 4) (by omega)
  have hpar : (if Even ((n : ℤ) - 3) then (1 : ℤ) else 0) +
      2 * (if Even ((n : ℤ) - 4) then (1 : ℤ) else 0) =
      if Even h then (1 : ℤ) else 2 := by
    have e1 : Even ((n : ℤ) - 3) ↔ Even h := by
      dsimp [h]; constructor <;> rintro ⟨r, hr⟩
      · exact ⟨r + 1, by omega⟩
      · exact ⟨r - 1, by omega⟩
    have e2 : Even ((n : ℤ) - 4) ↔ ¬Even h := by
      dsimp [h]; constructor
      · rintro ⟨r, hr⟩ ⟨s, hs⟩; omega
      · intro hne
        have : (n : ℤ) % 2 = 0 := by
          by_contra h1; exact hne ⟨((n : ℤ) - 1) / 2, by omega⟩
        exact ⟨((n : ℤ) - 4) / 2, by omega⟩
    by_cases hev : Even h
    · rw [ite_eq_left hev, ite_eq_left (e1.2 hev), ite_eq_right (fun hh => (e2.1 hh) hev)]
      norm_num
    · rw [ite_eq_right hev, ite_eq_right (fun hh => hev (e1.1 hh)), ite_eq_left (e2.2 hev)]
      norm_num
  have hTstar : 4 * (Tstar n : ℤ) =
      3 * (h - 2) ^ 2 + 2 * (h - 2) + 1 - (if Even h then (1 : ℤ) else 2) := by
    unfold Tstar; push_cast; dsimp [h] at hpar ⊢; linarith
  dsimp [M₁, M₂, M₃, pi] at hM1 hM2 hM3 ⊢
  linarith

/-- Parity threshold: if `4 (V - T*(n)) ≥ Psi - π` with `Psi > 1`, then `V ≥ D(n)`. -/
private lemma ge_D_of_psi_gt_one {n V : ℕ} (hn : 3 ≤ n) (M₁ M₂ M₃ : ℤ) (Psi : ℝ)
    (hPsi : 1 < Psi)
    (hV : Psi - (((if Even M₁ then (1 : ℤ) else 0) + (if Even M₂ then (1 : ℤ) else 0) +
      (if Even M₃ then (1 : ℤ) else 0) -
      (if Even ((n : ℤ) - 1) then (1 : ℤ) else 2) : ℤ) : ℝ) ≤
      4 * ((V : ℝ) - (Tstar n : ℝ))) :
    D n ≤ V := by
  rw [D_eq_Tstar n hn]
  have he : ((if Even M₁ then (1 : ℤ) else 0) + (if Even M₂ then (1 : ℤ) else 0) +
      (if Even M₃ then (1 : ℤ) else 0)) ≤ 3 := by
    split_ifs <;> omega
  have he' : (((if Even M₁ then (1 : ℤ) else 0) + (if Even M₂ then (1 : ℤ) else 0) +
      (if Even M₃ then (1 : ℤ) else 0) : ℤ) : ℝ) ≤ 3 := by exact_mod_cast he
  by_cases hev : Even n
  · rw [ite_eq_left hev]
    have hodd : ¬Even ((n : ℤ) - 1) := by rcases hev with ⟨k, rfl⟩; rintro ⟨r, hr⟩; omega
    rw [ite_eq_right hodd] at hV
    push_cast at hV he'
    have hlt : (Tstar n : ℝ) < (V : ℝ) := by linarith
    have hlt' : Tstar n < V := by exact_mod_cast hlt
    omega
  · rw [ite_eq_right hev]
    have hev_h : Even ((n : ℤ) - 1) := by
      rcases Nat.not_even_iff_odd.1 hev with ⟨k, rfl⟩
      exact ⟨(k : ℤ), by push_cast; ring⟩
    rw [ite_eq_left hev_h] at hV
    push_cast at hV he'
    have hlt : (Tstar n : ℝ) < (V : ℝ) + 1 := by linarith
    have hlt' : Tstar n < V + 1 := by exact_mod_cast hlt
    omega

/-! ### Algebraic helper lemmas for Step 3–5 -/

private lemma gamma_over_s (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s) :
    2 * (2 * ((n - 1 : ℕ) : ℝ) * s - (n : ℝ)) / s =
      ((n : ℝ) - 4) + 3 * (n : ℝ) * (s - 2 / 3) / s := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [hcast]
  field_simp [ne_of_gt hs]
  ring

/-- Purely algebraic proof of estimate `(e5)`: for `phi ∈ [-1/3, 1/3]`, `d₂ ≥ 0`,
and `s₃ = 2/3 - (1 + phi) d₂ / 2 > 0`,
`(9/4) (1 + 3 phi²) (2/3 + phi d₂)² / s₃ - 2 ≤ d₂ (8 + d₂) / (3 s₃)`. -/
theorem estimate_e5_alg (phi d₂ : ℝ) (hphi_lo : -1 / 3 ≤ phi) (hphi_hi : phi ≤ 1 / 3)
    (hd₂ : 0 ≤ d₂) (hs₃ : 0 < 2 / 3 - (1 + phi) * d₂ / 2) :
    (9 / 4) * (1 + 3 * phi ^ 2) * (2 / 3 + phi * d₂) ^ 2 / (2 / 3 - (1 + phi) * d₂ / 2) - 2 ≤
      d₂ * (8 + d₂) / (3 * (2 / 3 - (1 + phi) * d₂ / 2)) := by
  set s : ℝ := 2 / 3 - (1 + phi) * d₂ / 2
  have hs_ne : s ≠ 0 := ne_of_gt hs₃
  rw [sub_le_iff_le_add]
  have h1 : (9 / 4) * (1 + 3 * phi ^ 2) * (2 / 3 + phi * d₂) ^ 2 ≤
      d₂ * (8 + d₂) / 3 + 2 * s := by
    have hc0 : 9 / 4 * (1 + 3 * phi ^ 2) * (4 / 9) - 4 / 3 ≤ 0 := by nlinarith
    have hc1 : 9 / 4 * (1 + 3 * phi ^ 2) * (4 / 3 * phi) + (1 + phi) ≤ 8 / 3 := by
      have hexp : 8 / 3 - (9 / 4 * (1 + 3 * phi ^ 2) * (4 / 3 * phi) + (1 + phi)) =
          (1 / 3 - phi) * (5 + 3 * phi + 9 * phi ^ 2) := by ring
      have hquad : 0 ≤ 5 + 3 * phi + 9 * phi ^ 2 := by nlinarith [sq_nonneg (3 * phi + 1 / 2)]
      nlinarith
    have hc2 : 9 / 4 * (1 + 3 * phi ^ 2) * phi ^ 2 ≤ 1 / 3 := by
      have hsq : phi ^ 2 ≤ 1 / 9 := by nlinarith
      nlinarith
    have hdiff : (d₂ * (8 + d₂) / 3 + 2 * s) -
        (9 / 4) * (1 + 3 * phi ^ 2) * (2 / 3 + phi * d₂) ^ 2 =
        -(9 / 4 * (1 + 3 * phi ^ 2) * (4 / 9) - 4 / 3) +
        d₂ * (8 / 3 - (9 / 4 * (1 + 3 * phi ^ 2) * (4 / 3 * phi) + (1 + phi))) +
        d₂ ^ 2 * (1 / 3 - 9 / 4 * (1 + 3 * phi ^ 2) * phi ^ 2) := by
      dsimp [s]; ring
    nlinarith [sq_nonneg d₂]
  have hrhs : d₂ * (8 + d₂) / (3 * s) + 2 = (d₂ * (8 + d₂) / 3 + 2 * s) / s := by
    rw [add_div, ← div_div, mul_div_cancel_right₀ _ hs_ne]
  rw [hrhs]
  exact div_le_div_of_nonneg_right h1 hs₃.le

/-- Concave quadratic minimum on `[0, e]`. -/
theorem concave_quad_min {eps e A B : ℝ} (heps0 : 0 ≤ eps) (hepse : eps ≤ e) (hB : 0 ≤ B) :
    min 0 (e * (A - B * e)) ≤ eps * (A - B * eps) := by
  by_cases h1 : 0 ≤ A - B * eps
  · exact le_trans (min_le_left _ _) (mul_nonneg heps0 h1)
  · push Not at h1
    have h2 : A - B * e ≤ A - B * eps := by nlinarith
    have h3 : e * (A - B * e) ≤ eps * (A - B * eps) := by nlinarith
    exact le_trans (min_le_right _ _) h3

/-- Helper for Case II-1 numerical inequality: `2.627 sh X² - 10.486 X - 8 - 2.8306 n / X > 1`. -/
private lemma caseII1_numeric {n : ℕ} (hn : 700 ≤ n) {sh X : ℝ}
    (hsh_lo : 1 ≤ sh) (hsh_hi : sh ≤ 4 / 3) (hX_pos : 0 < X)
    (hshX2 : (n : ℝ) / 3.4821 ≤ sh * X ^ 2) :
    1 < 2.627 * sh * X ^ 2 - 10.486 * X - 8 - 2.8306 * (n : ℝ) / X := by
  have hn_r : (700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let sr : ℝ := Real.sqrt (n : ℝ)
  have hsr_pos : 0 < sr := Real.sqrt_pos.2 (by linarith)
  have hsr_sq : sr ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have hsr_ge : 26 ≤ sr := by
    have : (26 : ℝ) ^ 2 ≤ sr ^ 2 := by rw [hsr_sq]; linarith
    nlinarith
  have hX_lb : 0.464 * sr ≤ X := by
    have h0 : (n : ℝ) ≤ sh * X ^ 2 * 3.4821 := (div_le_iff₀ (by norm_num)).1 hshX2
    have h1 : (n : ℝ) ≤ 3.4821 * (4 / 3) * X ^ 2 := by nlinarith only [h0, hsh_hi, sq_nonneg X]
    have hsq : (0.464 * sr) ^ 2 ≤ X ^ 2 := by
      have h2 : (0.464 * sr) ^ 2 * (3.4821 * (4 / 3)) ≤ (n : ℝ) := by
        rw [← hsr_sq]; nlinarith only [sq_nonneg sr]
      nlinarith only [h1, h2]
    nlinarith only [hsq, hsr_pos, hX_pos]
  have hterm_inv : 2.8306 * (n : ℝ) / X ≤ 6.101 * sr := by
    rw [div_le_iff₀ hX_pos]
    have : 2.8306 * sr ^ 2 ≤ 6.101 * sr * (0.464 * sr) := by nlinarith [sq_nonneg sr]
    nlinarith [hsr_sq]
  have hquad_X : 0.7544 * (n : ℝ) - 5.62 * sr ≤ 2.627 * sh * X ^ 2 - 10.486 * X := by
    by_cases hX_split : X ≤ 0.5359 * sr
    · have h1 : 0.7544 * (n : ℝ) ≤ 2.627 * sh * X ^ 2 := by
        have h2 := mul_le_mul_of_nonneg_left hshX2 (by norm_num : (0 : ℝ) ≤ 2.627)
        have h3 : 2.627 * ((n : ℝ) / 3.4821) = (2.627 / 3.4821) * (n : ℝ) := by ring
        have h4 : (0.7544 : ℝ) ≤ 2.627 / 3.4821 := by norm_num
        nlinarith
      nlinarith
    · push Not at hX_split
      have h1 : 2.627 * X ^ 2 - 10.486 * X ≤ 2.627 * sh * X ^ 2 - 10.486 * X := by
        nlinarith [sq_nonneg X]
      have h3 : (X - 0.5359 * sr) * (2.627 * (X + 0.5359 * sr) - 10.486) ≥ 0 :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hsr_sq]
  nlinarith [hsr_sq]

/-- Helper for Case II-2a numerical inequality (`X ≥ 6`). -/
private lemma caseII2a_numeric {n : ℕ} (hn : 700 ≤ n)
    {s2 s3 Q E g2 Gamma2 eps2 kappa2 d2 X phi sh : ℝ}
    (hs2_lo : 0.6595 ≤ s2) (hs2_hi : s2 ≤ 0.6738) (hs3_lo : 0.6525 ≤ s3)
    (hQ_lb : 3.097 * sh * X ^ 2 ≤ Q)
    (hE_pos : 0 < E) (hE_ub : E ≤ 3.4483 * sh * X ^ 2 / (n : ℝ))
    (heps2_lo : 0 ≤ eps2) (heps2_le_E : eps2 ≤ E)
    (hGamma2 : Gamma2 = ((n : ℝ) - 4) + g2)
    (hg2_eq : g2 = 3 * phi * X / s2)
    (hkap2_eq : kappa2 = s2 * (n : ℝ) / X)
    (hkap2_sq_E : kappa2 ^ 2 * E ≤ (n : ℝ) * (d2 * (8 + d2) / (3 * s3) + 2))
    (hd2_pos : 0 < d2) (hd2_sharp : d2 < 0.0212) (hX_eq : X = (n : ℝ) * d2)
    (hX6 : 6 ≤ X) (hphi_lo : -1 / 3 ≤ phi) (hsh_lo : 1 ≤ sh) :
    ∃ Psi : ℝ, 1 < Psi ∧
      Psi ≤ Q + 2 * g2 - 4 + eps2 * (2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * eps2) := by
  have hn_r : (700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hX_pos : 0 < X := by linarith
  have hs2_pos : 0 < s2 := by linarith
  have hs3_pos : 0 < s3 := by linarith
  have hkap_nn : 0 ≤ kappa2 := by rw [hkap2_eq]; positivity
  have hpsi_sharp : (n : ℝ) * (d2 * (8 + d2) / (3 * s3)) ≤ 4.2 * X := by
    have hfrac : (8 + d2) / (3 * s3) ≤ 4.2 := by rw [div_le_iff₀ (by positivity)]; linarith
    have heq : (n : ℝ) * (d2 * (8 + d2) / (3 * s3)) = X * ((8 + d2) / (3 * s3)) := by rw [hX_eq]; ring
    have hmul := mul_le_mul_of_nonneg_left hfrac hX_pos.le
    linarith
  have hkap2_sharp : kappa2 ≤ 0.6738 * (n : ℝ) / X := by
    rw [hkap2_eq]; exact div_le_div_of_nonneg_right (by nlinarith) hX_pos.le
  have hE_psi : E * (4.2 * X + 4) ≤ 0.3268 * sh * X ^ 2 := by
    have h1 : E * (4.2 * X + 4) ≤ (3.4483 * sh * X ^ 2 / (n : ℝ)) * (4.2 * X + 4) :=
      mul_le_mul_of_nonneg_right hE_ub (by linarith)
    have h2 : (3.4483 * sh * X ^ 2 / (n : ℝ)) * (4.2 * X + 4) =
        (3.4483 * (4.2 * d2 + 4 / (n : ℝ))) * (sh * X ^ 2) := by
      rw [hX_eq]; field_simp [show (n : ℝ) ≠ 0 by linarith]
    have h3 : 4 / (n : ℝ) ≤ 4 / 700 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn_r
    have h4 : 3.4483 * (4.2 * d2 + 4 / (n : ℝ)) ≤ 0.3268 := by linarith
    have h5 : 0 ≤ sh * X ^ 2 := by positivity
    nlinarith only [h1, h2, h4, h5]
  have h4Ek : 4 * E * kappa2 ≤ 9.294 * sh * X := by
    have h1 : 4 * E * kappa2 ≤ 4 * (3.4483 * sh * X ^ 2 / (n : ℝ)) * (0.6738 * (n : ℝ) / X) := by
      calc 4 * E * kappa2
          ≤ 4 * (3.4483 * sh * X ^ 2 / (n : ℝ)) * kappa2 := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE_ub (by norm_num)) hkap_nn
        _ ≤ 4 * (3.4483 * sh * X ^ 2 / (n : ℝ)) * (0.6738 * (n : ℝ) / X) :=
            mul_le_mul_of_nonneg_left hkap2_sharp (by positivity)
    have h2 : 4 * (3.4483 * sh * X ^ 2 / (n : ℝ)) * (0.6738 * (n : ℝ) / X) =
        (4 * 3.4483 * 0.6738) * sh * X := by
      field_simp [ne_of_gt hX_pos, show (n : ℝ) ≠ 0 by linarith]
    have hshX : 0 < sh * X := mul_pos (by linarith) hX_pos
    nlinarith only [h1, h2, hshX]
  have hquad := concave_quad_min (eps := eps2) (e := E)
    (A := 2 * Gamma2 + 4 - 4 * kappa2) (B := kappa2 ^ 2) heps2_lo heps2_le_E (sq_nonneg _)
  have hA_eq : 2 * Gamma2 + 4 = 2 * (n : ℝ) - 4 + 2 * g2 := by linarith
  by_cases hphi0 : 0 ≤ phi
  · have hg2_nn : 0 ≤ g2 := by rw [hg2_eq]; exact div_nonneg (by nlinarith) hs2_pos.le
    have hmin_ge : -(E * (4.2 * X + 4) + 4 * E * kappa2) ≤
        min 0 (E * (2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * E)) := by
      have hnonpos : -(E * (4.2 * X + 4) + 4 * E * kappa2) ≤ 0 := by
        nlinarith only [hE_pos, hX_pos, hkap_nn]
      have hdiff_ge : -(4.2 * X + 4) - 4 * kappa2 ≤
          2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * E := by
        linarith only [hA_eq, hkap2_sq_E, hpsi_sharp, hg2_nn]
      have hmul_ge : E * (-(4.2 * X + 4) - 4 * kappa2) ≤
          E * (2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * E) :=
        mul_le_mul_of_nonneg_left hdiff_ge hE_pos.le
      exact le_min hnonpos (by linarith only [hmul_ge])
    refine ⟨sh * (2.7702 * X ^ 2 - 9.294 * X) - 4, ?_, ?_⟩
    · have hinner : 2.7702 * 36 - 9.294 * 6 ≤ 2.7702 * X ^ 2 - 9.294 * X := by
        have hfac : (X - 6) * (2.7702 * (X + 6) - 9.294) ≥ 0 :=
          mul_nonneg (by linarith only [hX6]) (by linarith only [hX6])
        linarith only [hfac]
      nlinarith only [hinner, hsh_lo]
    · linarith only [hQ_lb, hE_psi, h4Ek, hquad, hmin_ge, hg2_nn]
  · push Not at hphi0
    let tau : ℝ := -phi
    have htau_pos : 0 < tau := by dsimp [tau]; linarith
    have htau_le : tau ≤ 1 / 3 := by dsimp [tau]; linarith
    have hg2_tau : g2 = -3 * tau * X / s2 := by rw [hg2_eq]; dsimp [tau]; ring
    have hg2_neg : g2 < 0 := by rw [hg2_tau]; exact div_neg_of_neg_of_pos (by nlinarith) hs2_pos
    have hg2_lb : -4.549 * tau * X ≤ g2 := by
      rw [hg2_tau, le_div_iff₀ hs2_pos]
      have htauX : 0 ≤ tau * X := mul_nonneg htau_pos.le hX_pos.le
      nlinarith only [hs2_lo, htauX]
    have h2Eg2 : 2 * E * (-g2) ≤ 0.2218 * sh * X ^ 2 := by
      have h1 : 2 * E * (-g2) ≤ 2 * (3.4483 * sh * X ^ 2 / (n : ℝ)) * (4.549 * tau * X) := by
        calc 2 * E * (-g2)
            ≤ 2 * (3.4483 * sh * X ^ 2 / (n : ℝ)) * (-g2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE_ub (by norm_num))
                (by linarith only [hg2_neg])
          _ ≤ 2 * (3.4483 * sh * X ^ 2 / (n : ℝ)) * (4.549 * tau * X) :=
              mul_le_mul_of_nonneg_left (by linarith only [hg2_lb]) (by positivity)
      have h2 : 2 * (3.4483 * sh * X ^ 2 / (n : ℝ)) * (4.549 * tau * X) =
          (2 * 3.4483 * 4.549 * tau * d2) * (sh * X ^ 2) := by
        rw [hX_eq]; field_simp [show (n : ℝ) ≠ 0 by linarith]
      have h3 : 2 * 3.4483 * 4.549 * tau * d2 ≤ 0.2218 := by
        nlinarith only [htau_pos, htau_le, hd2_pos, hd2_sharp]
      have h4 : 0 ≤ sh * X ^ 2 := by positivity
      nlinarith only [h1, h2, h3, h4]
    have hmin_ge : -(E * (4.2 * X + 4) + 2 * E * (-g2) + 4 * E * kappa2) ≤
        min 0 (E * (2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * E)) := by
      have hnonpos : -(E * (4.2 * X + 4) + 2 * E * (-g2) + 4 * E * kappa2) ≤ 0 := by
        nlinarith only [hE_pos, hX_pos, hg2_neg, hkap_nn]
      have hdiff_ge : -(4.2 * X + 4) - 2 * (-g2) - 4 * kappa2 ≤
          2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * E := by
        linarith only [hA_eq, hkap2_sq_E, hpsi_sharp]
      have hmul_ge : E * (-(4.2 * X + 4) - 2 * (-g2) - 4 * kappa2) ≤
          E * (2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * E) :=
        mul_le_mul_of_nonneg_left hdiff_ge hE_pos.le
      exact le_min hnonpos (by linarith only [hmul_ge])
    have h2g2 : -3.033 * X ≤ 2 * g2 := by
      have h1 : -3.033 * X ≤ -2 * 4.549 * tau * X := by nlinarith only [htau_le, hX_pos]
      linarith only [h1, hg2_lb]
    refine ⟨sh * (2.5484 * X ^ 2 - 9.294 * X) - 3.033 * X - 4, ?_, ?_⟩
    · have hpos_in : 0 ≤ 2.5484 * X ^ 2 - 9.294 * X := by nlinarith only [hX6]
      have hsh_drop : 2.5484 * X ^ 2 - 9.294 * X ≤ sh * (2.5484 * X ^ 2 - 9.294 * X) := by
        nlinarith only [hsh_lo, hpos_in]
      have hq6 : (X - 6) * (2.5484 * (X + 6) - 12.327) ≥ 0 :=
        mul_nonneg (by linarith only [hX6]) (by linarith only [hX6])
      linarith only [hsh_drop, hq6]
    · linarith only [hQ_lb, hE_psi, h2Eg2, h4Ek, hquad, hmin_ge, h2g2]

/-- Helper for Case I (`N ≥ 1`): proves `D n ≤ T2 J1 + T2 J2 + T2 J3 ∨ (Even n ∧ inK)`. -/
private lemma caseI_proof {n : ℕ} (hn : 700 ≤ n) {u w : ℝ}
    (hu : 0 < u) (hw : 0 < w) (hr_lt : rad n < 0.0204862) (hcone : u + 2 * w ≤ 3 * rad n)
    {g1 g3 : ℝ} {j1 j2 j3 : ℤ}
    (hg1_def : g1 = 3 * (n : ℝ) * ((2 * u + w) / 3) / s1 u w)
    (hg3_def : g3 = 3 * (n : ℝ) * (-(u + 2 * w) / 3) / s3 u w)
    (hg1_pos : 0 < g1) (hg3_neg : g3 < 0)
    (hj1_def : j1 = ⌈g1⌉) (hj3_def : j3 = ⌈g3⌉)
    (hJ1_ge : 1 ≤ (n : ℤ) - 4 + j1) (hJ2_ge : 1 ≤ (n : ℤ) - 4 + j2)
    (hJ3_ge : 1 ≤ (n : ℤ) - 4 + j3)
    (hN1 : 1 ≤ j1 + j2 + j3) :
    D n ≤ T2 ((n : ℤ) - 4 + j1) + T2 ((n : ℤ) - 4 + j2) + T2 ((n : ℤ) - 4 + j3) ∨
      (Even n ∧ inK ((n - 4) / 2) u w) := by
  set J1 : ℤ := (n : ℤ) - 4 + j1
  set J2 : ℤ := (n : ℤ) - 4 + j2
  set J3 : ℤ := (n : ℤ) - 4 + j3
  have hA0 := identity_A0 n (by omega) j1 j2 j3 (by omega) (by omega) (by omega)
  dsimp only at hA0
  have hJeq1 : (n : ℤ) - 1 - 3 + j1 = J1 := by dsimp [J1]; omega
  have hJeq2 : (n : ℤ) - 1 - 3 + j2 = J2 := by dsimp [J2]; omega
  have hJeq3 : (n : ℤ) - 1 - 3 + j3 = J3 := by dsimp [J3]; omega
  rw [hJeq1, hJeq2, hJeq3] at hA0
  by_cases hN2 : 2 ≤ j1 + j2 + j3
  · left
    have hpi_le : (if Even J1 then (1 : ℤ) else 0) + (if Even J2 then (1 : ℤ) else 0) +
        (if Even J3 then (1 : ℤ) else 0) - (if Even ((n : ℤ) - 1) then (1 : ℤ) else 2) ≤ 2 := by
      split_ifs <;> omega
    have hsq_nn : 0 ≤ j1 ^ 2 + j2 ^ 2 + j3 ^ 2 := by positivity
    have hgt : 4 ≤ 4 * ((T2 J1 : ℤ) + (T2 J2 : ℤ) + (T2 J3 : ℤ) - (Tstar n : ℤ)) := by
      nlinarith
    rw [D_eq_Tstar n (by omega)]
    split_ifs <;> omega
  · have hsum_j : j1 + j2 + j3 = 1 := by omega
    by_cases hev : Even n
    · have hodd_h : ¬Even ((n : ℤ) - 1) := by
        rcases hev with ⟨k, rfl⟩; rintro ⟨r, hr⟩; omega
      rw [ite_eq_right hodd_h] at hA0
      have hev_J : ∀ j : ℤ, Even ((n : ℤ) - 4 + j) ↔ Even j := by
        intro j; rcases hev with ⟨k, hk⟩; subst hk
        constructor <;> rintro ⟨r, hr⟩
        · exact ⟨r - (k : ℤ) + 2, by omega⟩
        · exact ⟨r + (k : ℤ) - 2, by omega⟩
      have he1 : (if Even J1 then (1 : ℤ) else 0) = if Even j1 then 1 else 0 := by
        dsimp [J1]; by_cases h : Even j1
        · rw [ite_eq_left ((hev_J j1).2 h), ite_eq_left h]
        · rw [ite_eq_right (fun hh => h ((hev_J j1).1 hh)), ite_eq_right h]
      have he2 : (if Even J2 then (1 : ℤ) else 0) = if Even j2 then 1 else 0 := by
        dsimp [J2]; by_cases h : Even j2
        · rw [ite_eq_left ((hev_J j2).2 h), ite_eq_left h]
        · rw [ite_eq_right (fun hh => h ((hev_J j2).1 hh)), ite_eq_right h]
      have he3 : (if Even J3 then (1 : ℤ) else 0) = if Even j3 then 1 else 0 := by
        dsimp [J3]; by_cases h : Even j3
        · rw [ite_eq_left ((hev_J j3).2 h), ite_eq_left h]
        · rw [ite_eq_right (fun hh => h ((hev_J j3).1 hh)), ite_eq_right h]
      rw [he1, he2, he3] at hA0
      have hnot_all_even : (if Even j1 then (1 : ℤ) else 0) + (if Even j2 then (1 : ℤ) else 0) +
          (if Even j3 then (1 : ℤ) else 0) ≤ 2 := by
        by_cases h1 : Even j1 <;> by_cases h2 : Even j2 <;> by_cases h3 : Even j3
        · rcases h1 with ⟨a, rfl⟩; rcases h2 with ⟨b, rfl⟩; rcases h3 with ⟨c, rfl⟩; omega
        all_goals simp [h1, h2, h3]
      by_cases hsq2 : 2 ≤ j1 ^ 2 + j2 ^ 2 + j3 ^ 2
      · left
        have hpos : 0 < 4 * ((T2 J1 : ℤ) + (T2 J2 : ℤ) + (T2 J3 : ℤ) - (Tstar n : ℤ)) := by
          nlinarith
        rw [D_eq_Tstar n (by omega), ite_eq_left hev]
        omega
      · right
        refine ⟨hev, ?_⟩
        have hj1_ge : 1 ≤ j1 := by
          have : (0 : ℝ) < (j1 : ℝ) := by rw [hj1_def]; exact lt_of_lt_of_le hg1_pos (Int.le_ceil g1)
          have : (0 : ℤ) < j1 := by exact_mod_cast this
          omega
        have hj3_le : j3 ≤ 0 := by rw [hj3_def]; exact Int.ceil_le.2 (by exact_mod_cast hg3_neg.le)
        have hj1_eq : j1 = 1 := by nlinarith
        have hj3_eq : j3 = 0 := by nlinarith
        let c : ℕ := (n - 4) / 2
        have hc_eq : (n : ℝ) = 2 * (c : ℝ) + 4 := by
          rcases hev with ⟨m, hm⟩
          have : n = 2 * c + 4 := by dsimp [c]; omega
          exact_mod_cast this
        have hs1_eq : s1 u w = 2 / 3 + (2 * u + w) / 3 := by unfold s1 x1; ring
        have hs3_eq : s3 u w = 2 / 3 - (u + 2 * w) / 3 := by unfold s3 x3; ring
        have hs1_pos : 0 < s1 u w := by linarith
        have hs3_pos : 0 < s3 u w := by linarith
        have hg1_le1 : g1 ≤ 1 := by
          have := Int.le_ceil g1
          rw [← hj1_def] at this
          have : (j1 : ℝ) = 1 := by exact_mod_cast hj1_eq
          linarith
        have hg3_gt : -1 < g3 := by
          have := Int.ceil_lt_add_one g3
          rw [← hj3_def] at this
          have : (j3 : ℝ) = 0 := by exact_mod_cast hj3_eq
          linarith
        have hK2 : (3 * (c : ℝ) + 5) * u + (6 * (c : ℝ) + 13) * w < 1 := by
          rw [hg3_def, lt_div_iff₀ hs3_pos, hs3_eq, hc_eq] at hg3_gt
          nlinarith
        have hK1 : (3 * (c : ℝ) + 8) * u - (3 * (c : ℝ) + 5) * w < 1 := by
          by_contra hge
          push Not at hge
          have h1 : (n : ℝ) * (u - w) ≥ 2 * x1 u w := by unfold x1; rw [hc_eq]; linarith
          have h2 : (n : ℝ) * (2 * u + w) ≤ s1 u w := by
            rw [hg1_def, div_le_iff₀ hs1_pos] at hg1_le1; linarith
          have h3 : 4 * x1 u w ≤ s1 u w := by nlinarith
          have hx1_s1 : x1 u w = 1 - s1 u w := by unfold s1; ring
          linarith
        exact ⟨hK1, hK2⟩
    · left
      have hev_h : Even ((n : ℤ) - 1) := by
        rcases Nat.not_even_iff_odd.1 hev with ⟨k, rfl⟩
        exact ⟨(k : ℤ), by push_cast; ring⟩
      rw [ite_eq_left hev_h] at hA0
      have hev_J : ∀ j : ℤ, Even ((n : ℤ) - 4 + j) ↔ ¬Even j := by
        intro j; rcases Nat.not_even_iff_odd.1 hev with ⟨k, rfl⟩
        constructor
        · rintro ⟨r, hr⟩ ⟨s, hs⟩; omega
        · intro hne
          have : j % 2 = 1 := by by_contra h0; exact hne ⟨j / 2, by omega⟩
          exact ⟨(k : ℤ) + j / 2 - 1, by omega⟩
      have hodd_sq : ∀ j : ℤ, (if Even ((n : ℤ) - 4 + j) then (1 : ℤ) else 0) ≤ j ^ 2 := by
        intro j
        by_cases h : Even ((n : ℤ) - 4 + j)
        · rw [ite_eq_left h]
          have hne : ¬Even j := (hev_J j).1 h
          have hj0 : j ≠ 0 := fun h0 => hne (by rw [h0]; exact ⟨0, rfl⟩)
          have hcase : j ≤ -1 ∨ 1 ≤ j := by omega
          rcases hcase with hle | hge
          · nlinarith only [hle]
          · nlinarith only [hge]
        · rw [ite_eq_right h]; positivity
      have h1 := hodd_sq j1
      have h2 := hodd_sq j2
      have h3 := hodd_sq j3
      have hnn : 0 ≤ 4 * ((T2 J1 : ℤ) + (T2 J2 : ℤ) + (T2 J3 : ℤ) - (Tstar n : ℤ)) := by
        dsimp [J1, J2, J3] at hA0
        rw [hsum_j] at hA0
        linarith only [hA0, h1, h2, h3]
      rw [D_eq_Tstar n (by omega), ite_eq_right hev]
      omega

/-- Helper for `(S1)` deduction from `(A0)` and `(A3)`. -/
private lemma deduce_from_S1 {n B1v B2v B3v : ℕ} (hn : 3 ≤ n)
    {j1 j2 j3 : ℤ} {g2 Gamma1 Gamma2 Gamma3 eps1 eps2 eps3 kappa2 z2 Q Psi : ℝ}
    (hJ1_ge : 1 ≤ (n : ℤ) - 4 + j1) (hJ2_ge : 1 ≤ (n : ℤ) - 4 + j2)
    (hJ3_ge : 1 ≤ (n : ℤ) - 4 + j3)
    (hB1_T : T2 ((n : ℤ) - 4 + j1) ≤ B1v)
    (hB2_Q : (T2 ((n : ℤ) - 4 + j2 + 1) : ℝ) - (z2 + 2) ^ 2 / 4 ≤ (B2v : ℝ))
    (hB3_T : T2 ((n : ℤ) - 4 + j3) ≤ B3v)
    (hG1 : 0 ≤ Gamma1 + 1) (hG3 : 0 ≤ Gamma3 + 1)
    (heps1 : 0 ≤ eps1) (heps3 : 0 ≤ eps3)
    (hj2 : (j2 : ℝ) = g2 + eps2) (hz2 : z2 = kappa2 * eps2)
    (hA3 : 2 * ((n : ℝ) - 3) * ((j1 + j2 + j3 : ℤ) : ℝ) +
        ((j1 : ℝ) ^ 2 + (j2 : ℝ) ^ 2 + (j3 : ℝ) ^ 2) =
      Q + 2 * ((Gamma1 + 1) * eps1 + (Gamma2 + 1) * eps2 + (Gamma3 + 1) * eps3) +
        (eps1 ^ 2 + eps2 ^ 2 + eps3 ^ 2))
    (hPsi : 1 < Psi)
    (hPsi_le : Psi ≤ Q + 2 * g2 - 4 +
      eps2 * (2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * eps2)) :
    D n ≤ B1v + B2v + B3v := by
  set J1 : ℤ := (n : ℤ) - 4 + j1
  set J2 : ℤ := (n : ℤ) - 4 + j2
  set J3 : ℤ := (n : ℤ) - 4 + j3
  have hA0 := identity_A0 n hn j1 (j2 + 1) j3 (by omega) (by omega) (by omega)
  dsimp only at hA0
  have hJeq1 : (n : ℤ) - 1 - 3 + j1 = J1 := by dsimp [J1]; omega
  have hJeq2 : (n : ℤ) - 1 - 3 + (j2 + 1) = J2 + 1 := by dsimp [J2]; omega
  have hJeq3 : (n : ℤ) - 1 - 3 + j3 = J3 := by dsimp [J3]; omega
  rw [hJeq1, hJeq2, hJeq3] at hA0
  have hA0_r : 4 * ((T2 J1 : ℝ) + (T2 (J2 + 1) : ℝ) + (T2 J3 : ℝ) - (Tstar n : ℝ)) =
      2 * ((n : ℝ) - 3) * ((j1 + j2 + j3 : ℤ) : ℝ) +
        ((j1 : ℝ) ^ 2 + (j2 : ℝ) ^ 2 + (j3 : ℝ) ^ 2) + 2 * (j2 : ℝ) -
        (((if Even J1 then (1 : ℤ) else 0) + (if Even (J2 + 1) then (1 : ℤ) else 0) +
          (if Even J3 then (1 : ℤ) else 0) -
          (if Even ((n : ℤ) - 1) then (1 : ℤ) else 2) : ℤ) : ℝ) := by
    have hcast : (4 * ((T2 J1 : ℤ) + (T2 (J2 + 1) : ℤ) + (T2 J3 : ℤ) - (Tstar n : ℤ)) : ℝ) =
        ((2 * ((n : ℤ) - 1 - 2) * (j1 + (j2 + 1) + j3 - 1) +
          (j1 ^ 2 + (j2 + 1) ^ 2 + j3 ^ 2) - 1 -
          ((if Even J1 then (1 : ℤ) else 0) + (if Even (J2 + 1) then (1 : ℤ) else 0) +
            (if Even J3 then (1 : ℤ) else 0) -
            (if Even ((n : ℤ) - 1) then (1 : ℤ) else 2)) : ℤ) : ℝ) := by
      exact_mod_cast hA0
    push_cast at hcast ⊢
    linarith
  have hBsum : (T2 J1 : ℝ) + (T2 (J2 + 1) : ℝ) + (T2 J3 : ℝ) - (z2 + 2) ^ 2 / 4 ≤
      ((B1v + B2v + B3v : ℕ) : ℝ) := by
    push_cast
    have h1' : (T2 J1 : ℝ) ≤ (B1v : ℝ) := by exact_mod_cast hB1_T
    have h3' : (T2 J3 : ℝ) ≤ (B3v : ℝ) := by exact_mod_cast hB3_T
    linarith [hB2_Q]
  have hdrop : 0 ≤ 2 * (Gamma1 + 1) * eps1 + 2 * (Gamma3 + 1) * eps3 +
      (eps1 ^ 2 + eps2 ^ 2 + eps3 ^ 2) := by
    nlinarith [sq_nonneg eps1, sq_nonneg eps2, sq_nonneg eps3]
  apply ge_D_of_psi_gt_one hn J1 (J2 + 1) J3 Psi hPsi
  rw [hA3, hj2] at hA0_r
  have hexp : (z2 + 2) ^ 2 = kappa2 ^ 2 * eps2 ^ 2 + 4 * kappa2 * eps2 + 4 := by rw [hz2]; ring
  have hPsi_exp : Psi ≤ Q + 2 * g2 - 4 + 2 * Gamma2 * eps2 + 4 * eps2 -
      4 * kappa2 * eps2 - kappa2 ^ 2 * eps2 ^ 2 := by linarith only [hPsi_le]
  linarith only [hBsum, hA0_r, hPsi_exp, hdrop, hexp]

/-- Helper for `(S2)` deduction (pairs 1+2 or 2+3) from `(A0)` and `(A3)`. -/
private lemma deduce_from_S2_12 {n B1v B2v B3v : ℕ} (hn : 700 ≤ n)
    {j1 j2 j3 : ℤ} {g1 g2 Gamma1 Gamma2 Gamma3 eps1 eps2 eps3 z1 z2 Q : ℝ}
    (hJ1_ge : 1 ≤ (n : ℤ) - 4 + j1) (hJ2_ge : 1 ≤ (n : ℤ) - 4 + j2)
    (hJ3_ge : 1 ≤ (n : ℤ) - 4 + j3)
    (hB1_Q : (T2 ((n : ℤ) - 4 + j1 + 1) : ℝ) - (z1 + 2) ^ 2 / 4 ≤ (B1v : ℝ))
    (hB2_Q : (T2 ((n : ℤ) - 4 + j2 + 1) : ℝ) - (z2 + 2) ^ 2 / 4 ≤ (B2v : ℝ))
    (hB3_T : T2 ((n : ℤ) - 4 + j3) ≤ B3v)
    (hG1 : 0 ≤ Gamma1 + 1) (hG2 : 0 ≤ Gamma2 + 1) (hG3 : 0 ≤ Gamma3 + 1)
    (heps1 : 0 ≤ eps1) (heps2 : 0 ≤ eps2) (heps3 : 0 ≤ eps3)
    (hj1 : (j1 : ℝ) = g1 + eps1) (hj2 : (j2 : ℝ) = g2 + eps2)
    (hQ : 0 ≤ Q) (hg1 : 0 < g1) (hg2 : -9.098 ≤ g2)
    (hz : z2 ^ 2 + 4 * z2 + z1 ^ 2 + 4 * z1 ≤ 428.3)
    (hA3 : 2 * ((n : ℝ) - 3) * ((j1 + j2 + j3 : ℤ) : ℝ) +
        ((j1 : ℝ) ^ 2 + (j2 : ℝ) ^ 2 + (j3 : ℝ) ^ 2) =
      Q + 2 * ((Gamma1 + 1) * eps1 + (Gamma2 + 1) * eps2 + (Gamma3 + 1) * eps3) +
        (eps1 ^ 2 + eps2 ^ 2 + eps3 ^ 2)) :
    D n ≤ B1v + B2v + B3v := by
  have hn_r : (700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set J1 : ℤ := (n : ℤ) - 4 + j1
  set J2 : ℤ := (n : ℤ) - 4 + j2
  set J3 : ℤ := (n : ℤ) - 4 + j3
  have hA0 := identity_A0 n (by omega) (j1 + 1) (j2 + 1) j3 (by omega) (by omega) (by omega)
  dsimp only at hA0
  have hJeq1 : (n : ℤ) - 1 - 3 + (j1 + 1) = J1 + 1 := by dsimp [J1]; omega
  have hJeq2 : (n : ℤ) - 1 - 3 + (j2 + 1) = J2 + 1 := by dsimp [J2]; omega
  have hJeq3 : (n : ℤ) - 1 - 3 + j3 = J3 := by dsimp [J3]; omega
  rw [hJeq1, hJeq2, hJeq3] at hA0
  have hA0_r : 4 * ((T2 (J1 + 1) : ℝ) + (T2 (J2 + 1) : ℝ) + (T2 J3 : ℝ) - (Tstar n : ℝ)) =
      2 * ((n : ℝ) - 3) +
      (2 * ((n : ℝ) - 3) * ((j1 + j2 + j3 : ℤ) : ℝ) +
        ((j1 : ℝ) ^ 2 + (j2 : ℝ) ^ 2 + (j3 : ℝ) ^ 2)) +
      2 * (j1 : ℝ) + 2 * (j2 : ℝ) + 1 -
      (((if Even (J1 + 1) then (1 : ℤ) else 0) + (if Even (J2 + 1) then (1 : ℤ) else 0) +
        (if Even J3 then (1 : ℤ) else 0) -
        (if Even ((n : ℤ) - 1) then (1 : ℤ) else 2) : ℤ) : ℝ) := by
    have hcast : (4 * ((T2 (J1 + 1) : ℤ) + (T2 (J2 + 1) : ℤ) + (T2 J3 : ℤ) -
        (Tstar n : ℤ)) : ℝ) =
        ((2 * ((n : ℤ) - 1 - 2) * ((j1 + 1) + (j2 + 1) + j3 - 1) +
          ((j1 + 1) ^ 2 + (j2 + 1) ^ 2 + j3 ^ 2) - 1 -
          ((if Even (J1 + 1) then (1 : ℤ) else 0) + (if Even (J2 + 1) then (1 : ℤ) else 0) +
            (if Even J3 then (1 : ℤ) else 0) -
            (if Even ((n : ℤ) - 1) then (1 : ℤ) else 2)) : ℤ) : ℝ) := by
      exact_mod_cast hA0
    push_cast at hcast ⊢; linarith
  have hBsum : (T2 (J1 + 1) : ℝ) + (T2 (J2 + 1) : ℝ) + (T2 J3 : ℝ) -
      (z1 + 2) ^ 2 / 4 - (z2 + 2) ^ 2 / 4 ≤ ((B1v + B2v + B3v : ℕ) : ℝ) := by
    push_cast
    have h3' : (T2 J3 : ℝ) ≤ (B3v : ℝ) := by exact_mod_cast hB3_T
    linarith [hB1_Q, hB2_Q]
  have hdrop : 0 ≤ 2 * ((Gamma1 + 1) * eps1 + (Gamma2 + 1) * eps2 + (Gamma3 + 1) * eps3) +
      (eps1 ^ 2 + eps2 ^ 2 + eps3 ^ 2) := by
    nlinarith [sq_nonneg eps1, sq_nonneg eps2, sq_nonneg eps3]
  rw [hA3, hj1, hj2] at hA0_r
  apply ge_D_of_psi_gt_one (by omega) (J1 + 1) (J2 + 1) J3
    (2 * ((n : ℝ) - 3) - 54.98 - 7 - 428.3) (by linarith)
  nlinarith

private lemma deduce_from_S2_23 {n B1v B2v B3v : ℕ} (hn : 700 ≤ n)
    {j1 j2 j3 : ℤ} {g2 g3 Gamma1 Gamma2 Gamma3 eps1 eps2 eps3 z2 z3 Q : ℝ}
    (hJ1_ge : 1 ≤ (n : ℤ) - 4 + j1) (hJ2_ge : 1 ≤ (n : ℤ) - 4 + j2)
    (hJ3_ge : 1 ≤ (n : ℤ) - 4 + j3)
    (hB1_T : T2 ((n : ℤ) - 4 + j1) ≤ B1v)
    (hB2_Q : (T2 ((n : ℤ) - 4 + j2 + 1) : ℝ) - (z2 + 2) ^ 2 / 4 ≤ (B2v : ℝ))
    (hB3_Q : (T2 ((n : ℤ) - 4 + j3 + 1) : ℝ) - (z3 + 2) ^ 2 / 4 ≤ (B3v : ℝ))
    (hG1 : 0 ≤ Gamma1 + 1) (hG2 : 0 ≤ Gamma2 + 1) (hG3 : 0 ≤ Gamma3 + 1)
    (heps1 : 0 ≤ eps1) (heps2 : 0 ≤ eps2) (heps3 : 0 ≤ eps3)
    (hj2 : (j2 : ℝ) = g2 + eps2) (hj3 : (j3 : ℝ) = g3 + eps3)
    (hQ : 0 ≤ Q) (hg2 : -9.098 ≤ g2) (hg3 : -18.391 ≤ g3)
    (hz : z2 ^ 2 + 4 * z2 + z3 ^ 2 + 4 * z3 ≤ 428.3)
    (hA3 : 2 * ((n : ℝ) - 3) * ((j1 + j2 + j3 : ℤ) : ℝ) +
        ((j1 : ℝ) ^ 2 + (j2 : ℝ) ^ 2 + (j3 : ℝ) ^ 2) =
      Q + 2 * ((Gamma1 + 1) * eps1 + (Gamma2 + 1) * eps2 + (Gamma3 + 1) * eps3) +
        (eps1 ^ 2 + eps2 ^ 2 + eps3 ^ 2)) :
    D n ≤ B1v + B2v + B3v := by
  have hn_r : (700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set J1 : ℤ := (n : ℤ) - 4 + j1
  set J2 : ℤ := (n : ℤ) - 4 + j2
  set J3 : ℤ := (n : ℤ) - 4 + j3
  have hA0 := identity_A0 n (by omega) j1 (j2 + 1) (j3 + 1) (by omega) (by omega) (by omega)
  dsimp only at hA0
  have hJeq1 : (n : ℤ) - 1 - 3 + j1 = J1 := by dsimp [J1]; omega
  have hJeq2 : (n : ℤ) - 1 - 3 + (j2 + 1) = J2 + 1 := by dsimp [J2]; omega
  have hJeq3 : (n : ℤ) - 1 - 3 + (j3 + 1) = J3 + 1 := by dsimp [J3]; omega
  rw [hJeq1, hJeq2, hJeq3] at hA0
  have hA0_r : 4 * ((T2 J1 : ℝ) + (T2 (J2 + 1) : ℝ) + (T2 (J3 + 1) : ℝ) - (Tstar n : ℝ)) =
      2 * ((n : ℝ) - 3) +
      (2 * ((n : ℝ) - 3) * ((j1 + j2 + j3 : ℤ) : ℝ) +
        ((j1 : ℝ) ^ 2 + (j2 : ℝ) ^ 2 + (j3 : ℝ) ^ 2)) +
      2 * (j2 : ℝ) + 2 * (j3 : ℝ) + 1 -
      (((if Even J1 then (1 : ℤ) else 0) + (if Even (J2 + 1) then (1 : ℤ) else 0) +
        (if Even (J3 + 1) then (1 : ℤ) else 0) -
        (if Even ((n : ℤ) - 1) then (1 : ℤ) else 2) : ℤ) : ℝ) := by
    have hcast : (4 * ((T2 J1 : ℤ) + (T2 (J2 + 1) : ℤ) + (T2 (J3 + 1) : ℤ) -
        (Tstar n : ℤ)) : ℝ) =
        ((2 * ((n : ℤ) - 1 - 2) * (j1 + (j2 + 1) + (j3 + 1) - 1) +
          (j1 ^ 2 + (j2 + 1) ^ 2 + (j3 + 1) ^ 2) - 1 -
          ((if Even J1 then (1 : ℤ) else 0) + (if Even (J2 + 1) then (1 : ℤ) else 0) +
            (if Even (J3 + 1) then (1 : ℤ) else 0) -
            (if Even ((n : ℤ) - 1) then (1 : ℤ) else 2)) : ℤ) : ℝ) := by
      exact_mod_cast hA0
    push_cast at hcast ⊢; linarith
  have hBsum : (T2 J1 : ℝ) + (T2 (J2 + 1) : ℝ) + (T2 (J3 + 1) : ℝ) -
      (z2 + 2) ^ 2 / 4 - (z3 + 2) ^ 2 / 4 ≤ ((B1v + B2v + B3v : ℕ) : ℝ) := by
    push_cast
    have h1' : (T2 J1 : ℝ) ≤ (B1v : ℝ) := by exact_mod_cast hB1_T
    linarith [hB2_Q, hB3_Q]
  have hdrop : 0 ≤ 2 * ((Gamma1 + 1) * eps1 + (Gamma2 + 1) * eps2 + (Gamma3 + 1) * eps3) +
      (eps1 ^ 2 + eps2 ^ 2 + eps3 ^ 2) := by
    nlinarith [sq_nonneg eps1, sq_nonneg eps2, sq_nonneg eps3]
  rw [hA3, hj2, hj3] at hA0_r
  apply ge_D_of_psi_gt_one (by omega) J1 (J2 + 1) (J3 + 1)
    (2 * ((n : ℝ) - 3) - 54.98 - 7 - 428.3) (by linarith)
  nlinarith

/-- Helper for quadratic `Q` lower bound from a uniform lower bound `c ≤ (1 - s_k) / s_k²`. -/
private lemma Q_lower_bound {n : ℕ} {s1v s2v s3v eta1 eta2 eta3 sh d2 X Q c : ℝ}
    (hs1 : 0 < s1v) (hs2 : 0 < s2v) (hs3 : 0 < s3v) (_hn0 : 0 ≤ (n : ℝ))
    (hc1 : c ≤ (1 - s1v) / s1v ^ 2) (hc2 : c ≤ (1 - s2v) / s2v ^ 2)
    (hc3 : c ≤ (1 - s3v) / s3v ^ 2)
    (heta_sq : eta1 ^ 2 + eta2 ^ 2 + eta3 ^ 2 = sh * d2 ^ 2 / 2)
    (hX : X = (n : ℝ) * d2)
    (hQ : Q = 9 * (n : ℝ) *
      (eta1 ^ 2 / s1v * ((n : ℝ) * (1 - s1v) / s1v + 3) +
       eta2 ^ 2 / s2v * ((n : ℝ) * (1 - s2v) / s2v + 3) +
       eta3 ^ 2 / s3v * ((n : ℝ) * (1 - s3v) / s3v + 3))) :
    (9 / 2) * c * sh * X ^ 2 ≤ Q := by
  have hQ_ge : 9 * (n : ℝ) ^ 2 *
      (eta1 ^ 2 * ((1 - s1v) / s1v ^ 2) +
       eta2 ^ 2 * ((1 - s2v) / s2v ^ 2) +
       eta3 ^ 2 * ((1 - s3v) / s3v ^ 2)) ≤ Q := by
    rw [hQ]
    have t1 : 0 ≤ eta1 ^ 2 / s1v := div_nonneg (sq_nonneg _) hs1.le
    have t2 : 0 ≤ eta2 ^ 2 / s2v := div_nonneg (sq_nonneg _) hs2.le
    have t3 : 0 ≤ eta3 ^ 2 / s3v := div_nonneg (sq_nonneg _) hs3.le
    have hexp : 9 * (n : ℝ) *
        (eta1 ^ 2 / s1v * ((n : ℝ) * (1 - s1v) / s1v + 3) +
         eta2 ^ 2 / s2v * ((n : ℝ) * (1 - s2v) / s2v + 3) +
         eta3 ^ 2 / s3v * ((n : ℝ) * (1 - s3v) / s3v + 3)) -
        9 * (n : ℝ) ^ 2 *
        (eta1 ^ 2 * ((1 - s1v) / s1v ^ 2) +
         eta2 ^ 2 * ((1 - s2v) / s2v ^ 2) +
         eta3 ^ 2 * ((1 - s3v) / s3v ^ 2)) =
        27 * (n : ℝ) * (eta1 ^ 2 / s1v + eta2 ^ 2 / s2v + eta3 ^ 2 / s3v) := by
      field_simp [ne_of_gt hs1, ne_of_gt hs2, ne_of_gt hs3]; ring
    nlinarith
  have hmul : 9 * (n : ℝ) ^ 2 * (c * (eta1 ^ 2 + eta2 ^ 2 + eta3 ^ 2)) ≤
      9 * (n : ℝ) ^ 2 *
        (eta1 ^ 2 * ((1 - s1v) / s1v ^ 2) +
         eta2 ^ 2 * ((1 - s2v) / s2v ^ 2) +
         eta3 ^ 2 * ((1 - s3v) / s3v ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [sq_nonneg eta1, sq_nonneg eta2, sq_nonneg eta3]
  rw [heta_sq] at hmul
  have heq : 9 * (n : ℝ) ^ 2 * (c * (sh * d2 ^ 2 / 2)) = (9 / 2) * c * sh * X ^ 2 := by
    rw [hX]; ring
  linarith

/-! ### Case II-2 Helper (`E < 1`) -/

private lemma caseII2_proof {n B1v B2v B3v : ℕ} (hn : 700 ≤ n)
    {u w eta1 eta2 eta3 d2 kappa1 kappa2 kappa3 g1 g2 g3 Gamma1 Gamma2 Gamma3 : ℝ}
    {j1 j2 j3 : ℤ} {eps1 eps2 eps3 z1 z2 z3 E Q X phi sh : ℝ}
    (hu : 0 < u) (hw : 0 < w)
    (hs1_eq : s1 u w = 2 / 3 + (2 * u + w) / 3)
    (hs2_eq : s2 u w = 2 / 3 + (w - u) / 3)
    (hs3_eq : s3 u w = 2 / 3 - (u + 2 * w) / 3)
    (hs3_lt_s2 : s3 u w < s2 u w) (hs2_lt_s1 : s2 u w < s1 u w)
    (hs1_pos : 0 < s1 u w) (hs2_pos : 0 < s2 u w) (hs3_pos : 0 < s3 u w)
    (heta2_def : eta2 = (w - u) / 3) (heta3_def : eta3 = -(u + 2 * w) / 3)
    (hd2_def : d2 = u + w) (hd2_pos : 0 < d2)
    (hkap1_def : kappa1 = s1 u w / w) (hkap2_def : kappa2 = s2 u w / d2)
    (hkap3_def : kappa3 = s3 u w / u)
    (hg1_pos : 0 < g1) (hg3_def : g3 = 3 * (n : ℝ) * eta3 / s3 u w)
    (hGam2_def : Gamma2 = ((n : ℝ) - 4) + g2)
    (hGamma1_pos : 500 < Gamma1) (hGamma2_pos : 500 < Gamma2) (hGamma3_pos : 500 < Gamma3)
    (hJ1_ge : 1 ≤ (n : ℤ) - 4 + j1) (hJ2_ge : 1 ≤ (n : ℤ) - 4 + j2)
    (hJ3_ge : 1 ≤ (n : ℤ) - 4 + j3)
    (hB1_T : T2 ((n : ℤ) - 4 + j1) ≤ B1v) (hB3_T : T2 ((n : ℤ) - 4 + j3) ≤ B3v)
    (hB1_Q : (T2 ((n : ℤ) - 4 + j1 + 1) : ℝ) - (z1 + 2) ^ 2 / 4 ≤ (B1v : ℝ))
    (hB2_Q : (T2 ((n : ℤ) - 4 + j2 + 1) : ℝ) - (z2 + 2) ^ 2 / 4 ≤ (B2v : ℝ))
    (hB3_Q : (T2 ((n : ℤ) - 4 + j3 + 1) : ℝ) - (z3 + 2) ^ 2 / 4 ≤ (B3v : ℝ))
    (heps1_def : eps1 = (j1 : ℝ) - g1) (heps2_def : eps2 = (j2 : ℝ) - g2)
    (heps3_def : eps3 = (j3 : ℝ) - g3)
    (heps1_lo : 0 ≤ eps1) (heps2_lo : 0 ≤ eps2) (heps3_lo : 0 ≤ eps3)
    (hz1_def : z1 = kappa1 * eps1) (hz2_def : z2 = kappa2 * eps2) (hz3_def : z3 = kappa3 * eps3)
    (hN1 : j1 + j2 + j3 < 1)
    (hE_pos : 0 < E) (hE1 : E < 1)
    (hN_eq : ((j1 + j2 + j3 : ℤ) : ℝ) = eps1 + eps2 + eps3 - E)
    (hQ_eq : Q = 9 * (n : ℝ) *
        (eta1 ^ 2 / s1 u w * ((n : ℝ) * (1 - s1 u w) / s1 u w + 3) +
         eta2 ^ 2 / s2 u w * ((n : ℝ) * (1 - s2 u w) / s2 u w + 3) +
         eta3 ^ 2 / s3 u w * ((n : ℝ) * (1 - s3 u w) / s3 u w + 3)))
    (hQ_nn : 0 ≤ Q)
    (hA3 : 2 * ((n : ℝ) - 3) * ((j1 + j2 + j3 : ℤ) : ℝ) +
        ((j1 : ℝ) ^ 2 + (j2 : ℝ) ^ 2 + (j3 : ℝ) ^ 2) =
      Q + 2 * ((Gamma1 + 1) * eps1 + (Gamma2 + 1) * eps2 + (Gamma3 + 1) * eps3) +
        (eps1 ^ 2 + eps2 ^ 2 + eps3 ^ 2))
    (hX_def : X = (n : ℝ) * d2) (hX_pos : 0 < X)
    (hphi_def : phi = eta2 / d2) (hphi_lo : -1 / 3 ≤ phi) (hphi_hi : phi ≤ 1 / 3)
    (hsh_lo : 1 ≤ sh) (hsh_hi : sh ≤ 4 / 3)
    (heta_sq_sum : eta1 ^ 2 + eta2 ^ 2 + eta3 ^ 2 = sh * d2 ^ 2 / 2)
    (hE_exact_ub : E ≤ (9 / (4 * s3 u w)) * sh * X ^ 2 / (n : ℝ))
    (hE_lb : 3.1795 * sh * X ^ 2 / (n : ℝ) ≤ E)
    (hkap2_eq : kappa2 = s2 u w * (n : ℝ) / X)
    (hg2_phi_eq : g2 = 3 * phi * X / s2 u w)
    (hkap2_sq_E : kappa2 ^ 2 * E ≤ (n : ℝ) * (d2 * (8 + d2) / (3 * s3 u w) + 2)) :
    D n ≤ B1v + B2v + B3v := by
  have hn_r : (700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN_eq0 : j1 + j2 + j3 = 0 := by
    have : (-1 : ℝ) < ((j1 + j2 + j3 : ℤ) : ℝ) := by
      linarith only [hN_eq, heps1_lo, heps2_lo, heps3_lo, hE1]
    have : (-1 : ℤ) < j1 + j2 + j3 := by exact_mod_cast this
    omega
  have heps_sum : eps1 + eps2 + eps3 = E := by
    have : ((j1 + j2 + j3 : ℤ) : ℝ) = 0 := by exact_mod_cast hN_eq0
    linarith only [hN_eq, this]
  have heps2_le_E : eps2 ≤ E := by linarith only [heps_sum, heps1_lo, heps3_lo]
  have hd2_sharp : d2 < 0.0212 := by
    have hshX2_lt : sh * X ^ 2 < (n : ℝ) / 3.1795 := by
      have h1 := (div_lt_iff₀ (by linarith only [hn_r] : (0 : ℝ) < (n : ℝ))).1 (lt_of_le_of_lt hE_lb hE1)
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3.1795)]; linarith only [h1]
    have hsq : d2 ^ 2 < 0.0212 ^ 2 := by
      have h1 : (n : ℝ) ^ 2 * d2 ^ 2 = X ^ 2 := by rw [hX_def]; ring
      have h2 : X ^ 2 < (n : ℝ) / 3.1795 := by nlinarith only [hshX2_lt, hsh_lo, sq_nonneg X]
      have h3m : (n : ℝ) * ((n : ℝ) * d2 ^ 2) < (n : ℝ) * (1 / 3.1795) := by
        have ha : (n : ℝ) * ((n : ℝ) * d2 ^ 2) = (n : ℝ) ^ 2 * d2 ^ 2 := by ring
        have hb : (n : ℝ) * (1 / 3.1795) = (n : ℝ) / 3.1795 := by ring
        linarith only [h1, h2, ha, hb]
      have h3 : (n : ℝ) * d2 ^ 2 < 1 / 3.1795 := lt_of_mul_lt_mul_left h3m (by linarith only [hn_r])
      nlinarith only [h3, hn_r, sq_nonneg d2]
    nlinarith only [hsq, hd2_pos]
  have hs1_sharp : s1 u w ≤ 0.6809 := by rw [hs1_eq]; linarith only [hd2_def, hd2_sharp, hw]
  have hs3_sharp : 0.6525 ≤ s3 u w := by rw [hs3_eq]; linarith only [hd2_def, hd2_sharp, hu]
  have hs2_lo_sharp : 0.6595 ≤ s2 u w := by rw [hs2_eq]; linarith only [hd2_def, hd2_sharp, hw]
  have hs2_hi_sharp : s2 u w ≤ 0.6738 := by rw [hs2_eq]; linarith only [hd2_def, hd2_sharp, hu]
  have hE_ub_sharp : E ≤ 3.4483 * sh * X ^ 2 / (n : ℝ) := by
    have hc : 9 / (4 * s3 u w) ≤ 3.4483 := by
      rw [div_le_iff₀ (by linarith only [hs3_pos])]; linarith only [hs3_sharp]
    have hmul := mul_le_mul_of_nonneg_right hc
      (div_nonneg (mul_nonneg (by linarith only [hsh_lo]) (sq_nonneg X)) (by linarith only [hn_r]))
    have hrw2 : 9 / (4 * s3 u w) * (sh * X ^ 2 / (n : ℝ)) =
        9 / (4 * s3 u w) * sh * X ^ 2 / (n : ℝ) := by ring
    have hrw3 : 3.4483 * (sh * X ^ 2 / (n : ℝ)) = 3.4483 * sh * X ^ 2 / (n : ℝ) := by ring
    linarith only [hE_exact_ub, hmul, hrw2, hrw3]
  by_cases hX6 : 6 ≤ X
  · -- Case II-2a: X ≥ 6
    have hQ_sharp : 3.097 * sh * X ^ 2 ≤ Q := by
      have hQ0 := Q_lower_bound (c := 0.68823) hs1_pos hs2_pos hs3_pos (by linarith only [hn_r])
        (by rw [le_div_iff₀ (sq_pos_of_pos hs1_pos)]; nlinarith only [hs1_sharp, hs1_pos])
        (by rw [le_div_iff₀ (sq_pos_of_pos hs2_pos)]; nlinarith only [hs2_hi_sharp, hs2_pos])
        (by rw [le_div_iff₀ (sq_pos_of_pos hs3_pos)]; nlinarith only [hs3_lt_s2, hs2_hi_sharp, hs3_pos])
        heta_sq_sum hX_def hQ_eq
      have : (3.097 : ℝ) ≤ (9 / 2) * 0.68823 := by norm_num
      have hnn : 0 ≤ sh * X ^ 2 := mul_nonneg (by linarith only [hsh_lo]) (sq_nonneg X)
      nlinarith only [hQ0, this, hnn]
    obtain ⟨Psi, hgt1, hPsi_val⟩ := caseII2a_numeric hn hs2_lo_sharp hs2_hi_sharp hs3_sharp
      hQ_sharp hE_pos hE_ub_sharp heps2_lo heps2_le_E hGam2_def hg2_phi_eq hkap2_eq hkap2_sq_E
      hd2_pos hd2_sharp hX_def hX6 hphi_lo hsh_lo
    exact deduce_from_S1 (by omega) hJ1_ge hJ2_ge hJ3_ge hB1_T hB2_Q hB3_T
      (by linarith only [hGamma1_pos]) (by linarith only [hGamma3_pos])
      heps1_lo heps3_lo (by linarith only [heps2_def]) hz2_def hA3 hgt1 hPsi_val
  · -- Case II-2b: X < 6
    push Not at hX6
    have hmin_zw : (u + w) * min (eps1 / w) (eps3 / u) ≤ eps1 + eps3 := by
      have h1 : w * min (eps1 / w) (eps3 / u) ≤ w * (eps1 / w) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hw.le
      have h2 : u * min (eps1 / w) (eps3 / u) ≤ u * (eps3 / u) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hu.le
      rw [mul_div_cancel₀ _ (ne_of_gt hw)] at h1
      rw [mul_div_cancel₀ _ (ne_of_gt hu)] at h2
      linarith only [h1, h2]
    have hE_over_d2 : E / d2 ≤ 3 * X / s3 u w := by
      have h1 : E / d2 = (n : ℝ) * E / X := by
        rw [hX_def]; field_simp [ne_of_gt hd2_pos, show (n : ℝ) ≠ 0 by linarith only [hn_r]]
      rw [h1, div_le_iff₀ hX_pos]
      have h2 : (n : ℝ) * E ≤ (9 / (4 * s3 u w)) * sh * X ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hE_exact_ub (by linarith only [hn_r] : (0 : ℝ) ≤ (n : ℝ))
        have hcancel : (n : ℝ) * (9 / (4 * s3 u w) * sh * X ^ 2 / (n : ℝ)) =
            9 / (4 * s3 u w) * sh * X ^ 2 := by
          field_simp [show (n : ℝ) ≠ 0 by linarith only [hn_r]]
        linarith only [hmul, hcancel]
      have h3 : 9 / (4 * s3 u w) * sh ≤ 3 / s3 u w := by
        have : (9 / 4 : ℝ) * sh ≤ 3 := by linarith only [hsh_hi]
        calc 9 / (4 * s3 u w) * sh = (9 / 4 * sh) / s3 u w := by ring
          _ ≤ 3 / s3 u w := div_le_div_of_nonneg_right this hs3_pos.le
      have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg X)
      have h5 : 3 / s3 u w * X ^ 2 = 3 * X / s3 u w * X := by ring
      linarith only [h2, h4, h5]
    have h3Xs : 3 * X * (s1 u w / s3 u w) ≤ 18.79 := by
      have hratio : s1 u w / s3 u w ≤ 0.6809 / 0.6525 := by
        rw [div_le_div_iff₀ hs3_pos (by norm_num)]; nlinarith only [hs1_sharp, hs3_sharp]
      have h1 : 3 * X * (s1 u w / s3 u w) ≤ 3 * 6 * (0.6809 / 0.6525) := by
        calc 3 * X * (s1 u w / s3 u w)
            ≤ 3 * X * (0.6809 / 0.6525) :=
              mul_le_mul_of_nonneg_left hratio (by linarith only [hX_pos])
          _ ≤ 3 * 6 * (0.6809 / 0.6525) := by nlinarith only [hX6]
      linarith only [h1]
    have hg2_lb_6 : -9.098 ≤ g2 := by
      rw [hg2_phi_eq, le_div_iff₀ hs2_pos]
      nlinarith only [hphi_lo, hX_pos, hX6, hs2_lo_sharp]
    have hg3_lb_6 : -18.391 ≤ g3 := by
      have hg3_phi : g3 = -3 * (1 + phi) * X / (2 * s3 u w) := by
        rw [hg3_def, hphi_def, heta2_def, heta3_def, hX_def, hd2_def]
        field_simp [ne_of_gt (by linarith only [hu, hw] : 0 < u + w), ne_of_gt hs3_pos]; ring
      rw [hg3_phi, le_div_iff₀ (by linarith only [hs3_pos] : 0 < 2 * s3 u w)]
      nlinarith only [hphi_hi, hX_pos, hX6, hs3_sharp]
    have hz1_nn : 0 ≤ z1 := by rw [hz1_def, hkap1_def]; exact mul_nonneg (div_nonneg hs1_pos.le hw.le) heps1_lo
    have hz2_nn : 0 ≤ z2 := by rw [hz2_def, hkap2_def]; exact mul_nonneg (div_nonneg hs2_pos.le hd2_pos.le) heps2_lo
    have hz3_nn : 0 ≤ z3 := by rw [hz3_def, hkap3_def]; exact mul_nonneg (div_nonneg hs3_pos.le hu.le) heps3_lo
    rcases le_total (eps1 / w) (eps3 / u) with h13 | h31
    · have hsum_z : z2 + z1 ≤ 18.79 := by
        have h1 : z2 / s2 u w + z1 / s1 u w ≤ E / d2 := by
          have hz2s : z2 / s2 u w = eps2 / d2 := by
            rw [hz2_def, hkap2_def]; field_simp [ne_of_gt hs2_pos, ne_of_gt hd2_pos]
          have hz1s : z1 / s1 u w = eps1 / w := by
            rw [hz1_def, hkap1_def]; field_simp [ne_of_gt hs1_pos, ne_of_gt hw]
          rw [hz2s, hz1s]
          rw [min_eq_left h13] at hmin_zw
          have hdiv : eps1 / w ≤ (eps1 + eps3) / d2 := by
            rw [le_div_iff₀ hd2_pos, hd2_def]; linarith only [hmin_zw]
          have heq : eps2 / d2 + (eps1 + eps3) / d2 = E / d2 := by
            rw [← add_div, ← heps_sum]; ring
          linarith only [hdiv, heq]
        have h2 : z2 + z1 ≤ s1 u w * (z2 / s2 u w + z1 / s1 u w) := by
          have ha : z2 ≤ s1 u w * (z2 / s2 u w) := by
            rw [mul_div_assoc', le_div_iff₀ hs2_pos]; nlinarith only [hs2_lt_s1, hz2_nn]
          have hb : z1 = s1 u w * (z1 / s1 u w) := by
            rw [mul_div_cancel₀ _ (ne_of_gt hs1_pos)]
          linarith only [ha, hb]
        have h3 : s1 u w * (E / d2) ≤ 3 * X * (s1 u w / s3 u w) := by
          have hmul := mul_le_mul_of_nonneg_left hE_over_d2 hs1_pos.le
          have hrw : s1 u w * (3 * X / s3 u w) = 3 * X * (s1 u w / s3 u w) := by ring
          linarith only [hmul, hrw]
        nlinarith only [h1, h2, h3, hs1_pos, h3Xs]
      have hz_quad : z2 ^ 2 + 4 * z2 + z1 ^ 2 + 4 * z1 ≤ 428.3 := by
        have hsq : z2 ^ 2 + z1 ^ 2 ≤ (z2 + z1) ^ 2 := by nlinarith only [hz1_nn, hz2_nn]
        nlinarith only [hsq, hsum_z, hz1_nn, hz2_nn]
      exact deduce_from_S2_12 hn hJ1_ge hJ2_ge hJ3_ge hB1_Q hB2_Q hB3_T
        (by linarith only [hGamma1_pos]) (by linarith only [hGamma2_pos])
        (by linarith only [hGamma3_pos]) heps1_lo heps2_lo heps3_lo
        (by linarith only [heps1_def]) (by linarith only [heps2_def]) hQ_nn hg1_pos hg2_lb_6
        hz_quad hA3
    · have hsum_z : z2 + z3 ≤ 18.79 := by
        have h1 : z2 / s2 u w + z3 / s3 u w ≤ E / d2 := by
          have hz2s : z2 / s2 u w = eps2 / d2 := by
            rw [hz2_def, hkap2_def]; field_simp [ne_of_gt hs2_pos, ne_of_gt hd2_pos]
          have hz3s : z3 / s3 u w = eps3 / u := by
            rw [hz3_def, hkap3_def]; field_simp [ne_of_gt hs3_pos, ne_of_gt hu]
          rw [hz2s, hz3s]
          rw [min_eq_right h31] at hmin_zw
          have hdiv : eps3 / u ≤ (eps1 + eps3) / d2 := by
            rw [le_div_iff₀ hd2_pos, hd2_def]; linarith only [hmin_zw]
          have heq : eps2 / d2 + (eps1 + eps3) / d2 = E / d2 := by
            rw [← add_div, ← heps_sum]; ring
          linarith only [hdiv, heq]
        have h2 : z2 + z3 ≤ s1 u w * (z2 / s2 u w + z3 / s3 u w) := by
          have ha : z2 ≤ s1 u w * (z2 / s2 u w) := by
            rw [mul_div_assoc', le_div_iff₀ hs2_pos]; nlinarith only [hs2_lt_s1, hz2_nn]
          have hb : z3 ≤ s1 u w * (z3 / s3 u w) := by
            rw [mul_div_assoc', le_div_iff₀ hs3_pos]; nlinarith only [hs3_lt_s2, hs2_lt_s1, hz3_nn]
          linarith only [ha, hb]
        have h3 : s1 u w * (E / d2) ≤ 3 * X * (s1 u w / s3 u w) := by
          have hmul := mul_le_mul_of_nonneg_left hE_over_d2 hs1_pos.le
          have hrw : s1 u w * (3 * X / s3 u w) = 3 * X * (s1 u w / s3 u w) := by ring
          linarith only [hmul, hrw]
        nlinarith only [h1, h2, h3, hs1_pos, h3Xs]
      have hz_quad : z2 ^ 2 + 4 * z2 + z3 ^ 2 + 4 * z3 ≤ 428.3 := by
        have hsq : z2 ^ 2 + z3 ^ 2 ≤ (z2 + z3) ^ 2 := by nlinarith only [hz2_nn, hz3_nn]
        nlinarith only [hsq, hsum_z, hz2_nn, hz3_nn]
      exact deduce_from_S2_23 hn hJ1_ge hJ2_ge hJ3_ge hB1_T hB2_Q hB3_Q
        (by linarith only [hGamma1_pos]) (by linarith only [hGamma2_pos])
        (by linarith only [hGamma3_pos]) heps1_lo heps2_lo heps3_lo
        (by linarith only [heps2_def]) (by linarith only [heps3_def]) hQ_nn hg2_lb_6 hg3_lb_6
        hz_quad hA3

/-! ### Case II-1 Helper (`E ≥ 1`) -/

private lemma caseII1_proof {n B1v B2v B3v : ℕ} (hn : 700 ≤ n)
    {u w d2 kappa2 g2 Gamma1 Gamma2 Gamma3 : ℝ}
    {j1 j2 j3 : ℤ} {eps1 eps2 eps3 z2 E Q X phi sh : ℝ}
    (hr_lt : rad n < 0.0204862)
    (hs1_hi : s1 u w ≤ 0.70764) (hs3_lo : 0.64618 ≤ s3 u w)
    (hs3_lt_s2 : s3 u w < s2 u w) (hs2_lt_s1 : s2 u w < s1 u w)
    (hs2_pos : 0 < s2 u w) (hs3_pos : 0 < s3 u w)
    (hd2_pos : 0 < d2) (hd2_hi : d2 ≤ 3 * rad n)
    (hkap2_def : kappa2 = s2 u w / d2)
    (hGam2_def : Gamma2 = ((n : ℝ) - 4) + g2)
    (hGamma1_pos : 500 < Gamma1) (hGamma3_pos : 500 < Gamma3)
    (hJ1_ge : 1 ≤ (n : ℤ) - 4 + j1) (hJ2_ge : 1 ≤ (n : ℤ) - 4 + j2)
    (hJ3_ge : 1 ≤ (n : ℤ) - 4 + j3)
    (hB1_T : T2 ((n : ℤ) - 4 + j1) ≤ B1v) (hB3_T : T2 ((n : ℤ) - 4 + j3) ≤ B3v)
    (hB2_Q : (T2 ((n : ℤ) - 4 + j2 + 1) : ℝ) - (z2 + 2) ^ 2 / 4 ≤ (B2v : ℝ))
    (heps2_def : eps2 = (j2 : ℝ) - g2)
    (heps1_lo : 0 ≤ eps1) (heps2_lo : 0 ≤ eps2) (heps2_hi : eps2 < 1) (heps3_lo : 0 ≤ eps3)
    (hz2_def : z2 = kappa2 * eps2)
    (hE1 : 1 ≤ E)
    (hA3 : 2 * ((n : ℝ) - 3) * ((j1 + j2 + j3 : ℤ) : ℝ) +
        ((j1 : ℝ) ^ 2 + (j2 : ℝ) ^ 2 + (j3 : ℝ) ^ 2) =
      Q + 2 * ((Gamma1 + 1) * eps1 + (Gamma2 + 1) * eps2 + (Gamma3 + 1) * eps3) +
        (eps1 ^ 2 + eps2 ^ 2 + eps3 ^ 2))
    (hX_def : X = (n : ℝ) * d2) (hX_pos : 0 < X)
    (hphi_lo : -1 / 3 ≤ phi) (hphi_hi : phi ≤ 1 / 3)
    (hsh_lo : 1 ≤ sh) (hsh_hi : sh ≤ 4 / 3)
    (hQ_lb : 2.627 * sh * X ^ 2 ≤ Q)
    (hE_ub : E ≤ 3.4821 * sh * X ^ 2 / (n : ℝ))
    (hkap2_eq : kappa2 = s2 u w * (n : ℝ) / X)
    (hg2_phi_eq : g2 = 3 * phi * X / s2 u w)
    (hkap2_sq_E : kappa2 ^ 2 * E ≤ (n : ℝ) * (d2 * (8 + d2) / (3 * s3 u w) + 2)) :
    D n ≤ B1v + B2v + B3v := by
  have hn_r : (700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpsi_ub : (n : ℝ) * (d2 * (8 + d2) / (3 * s3 u w)) ≤ 4.295 * X := by
    have hfrac : (8 + d2) / (3 * s3 u w) ≤ 4.295 := by
      rw [div_le_iff₀ (by linarith only [hs3_pos])]; linarith only [hd2_hi, hr_lt, hs3_lo]
    have heq : (n : ℝ) * (d2 * (8 + d2) / (3 * s3 u w)) = X * ((8 + d2) / (3 * s3 u w)) := by
      rw [hX_def]; ring
    have hmul := mul_le_mul_of_nonneg_left hfrac hX_pos.le
    linarith only [heq, hmul]
  have hkap_sub : kappa2 ^ 2 - 2 * (n : ℝ) ≤ 4.295 * X := by
    have : kappa2 ^ 2 ≤ kappa2 ^ 2 * E := by nlinarith only [hE1, sq_nonneg kappa2]
    linarith only [this, hkap2_sq_E, hpsi_ub]
  have hkap2_ub : kappa2 ≤ 0.70764 * (n : ℝ) / X := by
    rw [hkap2_eq]
    exact div_le_div_of_nonneg_right (by nlinarith only [hs2_lt_s1, hs1_hi, hn_r]) hX_pos.le
  have hg2_abs : |g2| ≤ 1.5476 * X := by
    rw [hg2_phi_eq, abs_div, abs_of_pos hs2_pos, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos hX_pos, div_le_iff₀ hs2_pos]
    have hphi_abs : |phi| ≤ 1 / 3 := abs_le.2 ⟨by linarith only [hphi_lo], hphi_hi⟩
    nlinarith only [hphi_abs, hs3_lt_s2, hs3_lo, hX_pos]
  have hquad := concave_quad_min (eps := eps2) (e := 1)
    (A := 2 * Gamma2 + 4 - 4 * kappa2) (B := kappa2 ^ 2) heps2_lo heps2_hi.le (sq_nonneg _)
  have hA_eq : 2 * Gamma2 + 4 = 2 * (n : ℝ) - 4 + 2 * g2 := by linarith only [hGam2_def]
  have hmin_ge : -(4.295 * X + 4 + 2 * |g2| + 4 * kappa2) ≤
      min 0 (1 * (2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * 1)) := by
    have hg2_ge : -|g2| ≤ g2 := neg_abs_le g2
    have hkap_nn : 0 ≤ kappa2 := by rw [hkap2_def]; exact div_nonneg hs2_pos.le hd2_pos.le
    apply le_min
    · linarith only [abs_nonneg g2, hX_pos, hkap_nn]
    · linarith only [hA_eq, hkap_sub, hg2_ge]
  have hPsi_val : 2.627 * sh * X ^ 2 - 10.486 * X - 8 - 2.8306 * (n : ℝ) / X ≤
      Q + 2 * g2 - 4 + eps2 * (2 * Gamma2 + 4 - 4 * kappa2 - kappa2 ^ 2 * eps2) := by
    have hg2_ge : -|g2| ≤ g2 := neg_abs_le g2
    have h4k : 4 * kappa2 ≤ 2.8306 * (n : ℝ) / X := by
      have h1 := mul_le_mul_of_nonneg_left hkap2_ub (by norm_num : (0 : ℝ) ≤ 4)
      have h2 : 4 * (0.70764 * (n : ℝ) / X) = 2.83056 * (n : ℝ) / X := by ring
      have h3 : 2.83056 * (n : ℝ) / X ≤ 2.8306 * (n : ℝ) / X :=
        div_le_div_of_nonneg_right (by linarith only [hn_r]) hX_pos.le
      linarith only [h1, h2, h3]
    linarith only [hQ_lb, hg2_ge, hg2_abs, hquad, hmin_ge, h4k, hX_pos]
  have hshX2 : (n : ℝ) / 3.4821 ≤ sh * X ^ 2 := by
    have h1 := (le_div_iff₀ (by linarith only [hn_r] : (0 : ℝ) < (n : ℝ))).1 (le_trans hE1 hE_ub)
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3.4821)]; linarith only [h1]
  have hgt1 := caseII1_numeric hn hsh_lo hsh_hi hX_pos hshX2
  exact deduce_from_S1 (by omega) hJ1_ge hJ2_ge hJ3_ge hB1_T hB2_Q hB3_T
    (by linarith only [hGamma1_pos]) (by linarith only [hGamma3_pos])
    heps1_lo heps3_lo (by linarith only [heps2_def]) hz2_def hA3 hgt1 hPsi_val

/-! ### Main Proof of Theorem A (`n ≥ 700`) -/

/-- **Theorem A (`theorem_A_ge_700`):** For every `n ≥ 700` and every `(u, w)` with
`u > 0`, `w > 0`, `u + 2w ≤ 3 r(n)`: either `B₁(u, w) + B₂(u, w) + B₃(u, w) ≥ D(n)`,
or `n` is even and `(u, w) ∈ K((n - 4)/2)`. -/
theorem theorem_A_ge_700 (n : ℕ) (hn : 700 ≤ n) (u w : ℝ)
    (hu : 0 < u) (hw : 0 < w) (hcone : u + 2 * w ≤ 3 * rad n) :
    D n ≤ B1 n u w + B2 n u w + B3 n u w ∨ (Even n ∧ inK ((n - 4) / 2) u w) := by
  have hn_r : (700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr_pos : 0 < rad n := rad_pos n
  have hr_lt : rad n < 0.0204862 := by
    have hsq : (rad n) ^ 2 < (0.0204862 : ℝ) ^ 2 := by
      rw [rad_sq, div_lt_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hs1_eq : s1 u w = 2 / 3 + (2 * u + w) / 3 := by unfold s1 x1; ring
  have hs2_eq : s2 u w = 2 / 3 + (w - u) / 3 := by unfold s2 x2; ring
  have hs3_eq : s3 u w = 2 / 3 - (u + 2 * w) / 3 := by unfold s3 x3; ring
  have hs1_hi : s1 u w ≤ 0.70764 := by linarith
  have hs3_lo : 0.64618 ≤ s3 u w := by linarith
  have hs3_lt_s2 : s3 u w < s2 u w := by linarith
  have hs2_lt_s1 : s2 u w < s1 u w := by linarith
  have hs1_pos : 0 < s1 u w := by linarith
  have hs2_pos : 0 < s2 u w := by linarith
  have hs3_pos : 0 < s3 u w := by linarith
  have hx1_pos : 0 < x1 u w := by unfold s1 at hs1_hi; linarith
  have hx12 : x1 u w < x2 u w := by unfold x1 x2; linarith
  have hx23 : x2 u w < x3 u w := by unfold x2 x3; linarith
  have hx2_pos : 0 < x2 u w := by linarith
  -- Introduce opaque free variables with defining equations (avoids exponential `set` unfolding!)
  obtain ⟨eta1, heta1_def⟩ : ∃ x : ℝ, x = (2 * u + w) / 3 := ⟨_, rfl⟩
  obtain ⟨eta2, heta2_def⟩ : ∃ x : ℝ, x = (w - u) / 3 := ⟨_, rfl⟩
  obtain ⟨eta3, heta3_def⟩ : ∃ x : ℝ, x = -(u + 2 * w) / 3 := ⟨_, rfl⟩
  obtain ⟨d2, hd2_def⟩ : ∃ x : ℝ, x = u + w := ⟨_, rfl⟩
  obtain ⟨kappa1, hkap1_def⟩ : ∃ x : ℝ, x = s1 u w / w := ⟨_, rfl⟩
  obtain ⟨kappa2, hkap2_def⟩ : ∃ x : ℝ, x = s2 u w / d2 := ⟨_, rfl⟩
  obtain ⟨kappa3, hkap3_def⟩ : ∃ x : ℝ, x = s3 u w / u := ⟨_, rfl⟩
  obtain ⟨g1, hg1_def⟩ : ∃ x : ℝ, x = 3 * (n : ℝ) * eta1 / s1 u w := ⟨_, rfl⟩
  obtain ⟨g2, hg2_def⟩ : ∃ x : ℝ, x = 3 * (n : ℝ) * eta2 / s2 u w := ⟨_, rfl⟩
  obtain ⟨g3, hg3_def⟩ : ∃ x : ℝ, x = 3 * (n : ℝ) * eta3 / s3 u w := ⟨_, rfl⟩
  obtain ⟨Gamma1, hGam1_def⟩ : ∃ x : ℝ, x = ((n : ℝ) - 4) + g1 := ⟨_, rfl⟩
  obtain ⟨Gamma2, hGam2_def⟩ : ∃ x : ℝ, x = ((n : ℝ) - 4) + g2 := ⟨_, rfl⟩
  obtain ⟨Gamma3, hGam3_def⟩ : ∃ x : ℝ, x = ((n : ℝ) - 4) + g3 := ⟨_, rfl⟩
  obtain ⟨j1, hj1_def⟩ : ∃ x : ℤ, x = ⌈g1⌉ := ⟨_, rfl⟩
  obtain ⟨j2, hj2_def⟩ : ∃ x : ℤ, x = ⌈g2⌉ := ⟨_, rfl⟩
  obtain ⟨j3, hj3_def⟩ : ∃ x : ℤ, x = ⌈g3⌉ := ⟨_, rfl⟩
  obtain ⟨J1, hJ1_def⟩ : ∃ x : ℤ, x = (n : ℤ) - 4 + j1 := ⟨_, rfl⟩
  obtain ⟨J2, hJ2_def⟩ : ∃ x : ℤ, x = (n : ℤ) - 4 + j2 := ⟨_, rfl⟩
  obtain ⟨J3, hJ3_def⟩ : ∃ x : ℤ, x = (n : ℤ) - 4 + j3 := ⟨_, rfl⟩
  obtain ⟨eps1, heps1_def⟩ : ∃ x : ℝ, x = (j1 : ℝ) - g1 := ⟨_, rfl⟩
  obtain ⟨eps2, heps2_def⟩ : ∃ x : ℝ, x = (j2 : ℝ) - g2 := ⟨_, rfl⟩
  obtain ⟨eps3, heps3_def⟩ : ∃ x : ℝ, x = (j3 : ℝ) - g3 := ⟨_, rfl⟩
  obtain ⟨z1, hz1_def⟩ : ∃ x : ℝ, x = kappa1 * eps1 := ⟨_, rfl⟩
  obtain ⟨z2, hz2_def⟩ : ∃ x : ℝ, x = kappa2 * eps2 := ⟨_, rfl⟩
  obtain ⟨z3, hz3_def⟩ : ∃ x : ℝ, x = kappa3 * eps3 := ⟨_, rfl⟩
  obtain ⟨E, hE_def⟩ : ∃ x : ℝ, x = -(g1 + g2 + g3) := ⟨_, rfl⟩
  obtain ⟨N, hN_def⟩ : ∃ x : ℤ, x = j1 + j2 + j3 := ⟨_, rfl⟩
  obtain ⟨Q, hQ_def⟩ : ∃ x : ℝ, x = g1 ^ 2 + g2 ^ 2 + g3 ^ 2 - 2 * ((n : ℝ) - 3) * E := ⟨_, rfl⟩
  -- Basic identities
  have heta_sum : eta1 + eta2 + eta3 = 0 := by rw [heta1_def, heta2_def, heta3_def]; ring
  have hs1_eta : s1 u w - 2 / 3 = eta1 := by rw [hs1_eq, heta1_def]; ring
  have hs2_eta : s2 u w - 2 / 3 = eta2 := by rw [hs2_eq, heta2_def]; ring
  have hs3_eta : s3 u w - 2 / 3 = eta3 := by rw [hs3_eq, heta3_def]; ring
  have hg1_pos : 0 < g1 := by
    rw [hg1_def]; exact div_pos (by rw [heta1_def]; nlinarith only [hu, hw, hn_r]) hs1_pos
  have hg3_neg : g3 < 0 := by
    rw [hg3_def]; exact div_neg_of_neg_of_pos (by rw [heta3_def]; nlinarith only [hu, hw, hn_r]) hs3_pos
  have hGamma1_eq : 2 * gamma1 n u w / s1 u w = Gamma1 := by
    unfold gamma1; rw [gamma_over_s n (by omega) (s1 u w) hs1_pos, hs1_eta, ← hg1_def, ← hGam1_def]
  have hGamma2_eq : 2 * gamma2 n u w / s2 u w = Gamma2 := by
    unfold gamma2; rw [gamma_over_s n (by omega) (s2 u w) hs2_pos, hs2_eta, ← hg2_def, ← hGam2_def]
  have hGamma3_eq : 2 * gamma3 n u w / s3 u w = Gamma3 := by
    unfold gamma3; rw [gamma_over_s n (by omega) (s3 u w) hs3_pos, hs3_eta, ← hg3_def, ← hGam3_def]
  have heps1_lo : 0 ≤ eps1 := by rw [heps1_def, hj1_def]; exact sub_nonneg.2 (Int.le_ceil g1)
  have heps2_lo : 0 ≤ eps2 := by rw [heps2_def, hj2_def]; exact sub_nonneg.2 (Int.le_ceil g2)
  have heps3_lo : 0 ≤ eps3 := by rw [heps3_def, hj3_def]; exact sub_nonneg.2 (Int.le_ceil g3)
  have heps1_hi : eps1 < 1 := by
    rw [heps1_def, hj1_def]; exact sub_lt_iff_lt_add'.2 (Int.ceil_lt_add_one g1)
  have heps2_hi : eps2 < 1 := by
    rw [heps2_def, hj2_def]; exact sub_lt_iff_lt_add'.2 (Int.ceil_lt_add_one g2)
  have heps3_hi : eps3 < 1 := by
    rw [heps3_def, hj3_def]; exact sub_lt_iff_lt_add'.2 (Int.ceil_lt_add_one g3)
  have hJ1_sub : (J1 : ℝ) - Gamma1 = eps1 := by rw [hJ1_def, hGam1_def, heps1_def]; push_cast; ring
  have hJ2_sub : (J2 : ℝ) - Gamma2 = eps2 := by rw [hJ2_def, hGam2_def, heps2_def]; push_cast; ring
  have hJ3_sub : (J3 : ℝ) - Gamma3 = eps3 := by rw [hJ3_def, hGam3_def, heps3_def]; push_cast; ring
  have hg3_lb : -0.1 * (n : ℝ) < g3 := by
    rw [hg3_def, heta3_def, lt_div_iff₀ hs3_pos]; nlinarith only [hs3_lo, hcone, hr_lt, hn_r, hu, hw]
  have hg2_gt_g3 : g3 < g2 := by
    rw [hg2_def, hg3_def, div_lt_div_iff₀ hs3_pos hs2_pos, heta2_def, heta3_def, hs2_eq, hs3_eq]
    nlinarith only [hu, hw, hn_r]
  have hGamma3_pos : 500 < Gamma3 := by linarith only [hGam3_def, hg3_lb, hn_r]
  have hGamma2_pos : 500 < Gamma2 := by linarith only [hGam2_def, hg2_gt_g3, hg3_lb, hn_r]
  have hGamma1_pos : 500 < Gamma1 := by linarith only [hGam1_def, hg1_pos, hn_r]
  have hJ1_ge : 1 ≤ J1 := by
    have : (1 : ℝ) < (J1 : ℝ) := by linarith only [hJ1_sub, hGamma1_pos, heps1_lo]
    exact_mod_cast this.le
  have hJ2_ge : 1 ≤ J2 := by
    have : (1 : ℝ) < (J2 : ℝ) := by linarith only [hJ2_sub, hGamma2_pos, heps2_lo]
    exact_mod_cast this.le
  have hJ3_ge : 1 ≤ J3 := by
    have : (1 : ℝ) < (J3 : ℝ) := by linarith only [hJ3_sub, hGamma3_pos, heps3_lo]
    exact_mod_cast this.le
  have hn1 : 1 ≤ n := by omega
  -- Step 0: B_k ≥ T2(J_k) and B_k ≥ T2(J_k + 1) - (z_k + 2)^2 / 4
  have hB1_T : T2 J1 ≤ B1 n u w := by
    have hlt : ((J1.toNat - 1 : ℕ) : ℝ) < 2 * gamma1 n u w / (x2 u w + x3 u w) := by
      have hx23_s : x2 u w + x3 u w = s1 u w := by unfold s1 x1 x2 x3; ring
      rw [hx23_s, hGamma1_eq]
      have hcast : ((J1.toNat - 1 : ℕ) : ℝ) = (J1 : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ J1.toNat)]; push_cast
        have : (J1.toNat : ℤ) = J1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast congrArg (fun x : ℤ => x - 1) this
      linarith only [hcast, hJ1_sub, heps1_hi]
    have hfull := cor_P1_full_of_lt hx2_pos hx23.le hlt
    have hG := G1_le_B1 hn1 hx1_pos hu.le hw.le (J1.toNat - 1)
    unfold G1 at hG; rw [Gval_of_full hfull] at hG
    have heq : ((J1.toNat - 1 : ℕ) : ℤ) + 1 = J1 := by omega
    rwa [heq] at hG
  have hB2_T : T2 J2 ≤ B2 n u w := by
    have hlt : ((J2.toNat - 1 : ℕ) : ℝ) < 2 * gamma2 n u w / (x1 u w + x3 u w) := by
      have hx13_s : x1 u w + x3 u w = s2 u w := by unfold s2 x1 x2 x3; ring
      rw [hx13_s, hGamma2_eq]
      have hcast : ((J2.toNat - 1 : ℕ) : ℝ) = (J2 : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ J2.toNat)]; push_cast
        have : (J2.toNat : ℤ) = J2 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast congrArg (fun x : ℤ => x - 1) this
      linarith only [hcast, hJ2_sub, heps2_hi]
    have hfull := cor_P1_full_of_lt hx1_pos (le_trans hx12.le hx23.le) hlt
    have hG := G2_le_B2 hn1 hx1_pos hu.le hw.le (J2.toNat - 1)
    unfold G2 at hG; rw [Gval_of_full hfull] at hG
    have heq : ((J2.toNat - 1 : ℕ) : ℤ) + 1 = J2 := by omega
    rwa [heq] at hG
  have hB3_T : T2 J3 ≤ B3 n u w := by
    have hlt : ((J3.toNat - 1 : ℕ) : ℝ) < 2 * gamma3 n u w / (x1 u w + x2 u w) := by
      have hx12_s : x1 u w + x2 u w = s3 u w := by unfold s3 x1 x2 x3; ring
      rw [hx12_s, hGamma3_eq]
      have hcast : ((J3.toNat - 1 : ℕ) : ℝ) = (J3 : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ J3.toNat)]; push_cast
        have : (J3.toNat : ℤ) = J3 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast congrArg (fun x : ℤ => x - 1) this
      linarith only [hcast, hJ3_sub, heps3_hi]
    have hfull := cor_P1_full_of_lt hx1_pos hx12.le hlt
    have hG := G3_le_B3 hn1 hx1_pos hu.le hw.le (J3.toNat - 1)
    unfold G3 at hG; rw [Gval_of_full hfull] at hG
    have heq : ((J3.toNat - 1 : ℕ) : ℤ) + 1 = J3 := by omega
    rwa [heq] at hG
  have hB1_Q : (T2 (J1 + 1) : ℝ) - (z1 + 2) ^ 2 / 4 ≤ (B1 n u w : ℝ) := by
    have hq := cor_P1_quad_bound (g := gamma1 n u w) hx2_pos hx23 J1.toNat
    have hG : (G1 n u w J1.toNat : ℝ) ≤ (B1 n u w : ℝ) := by
      exact_mod_cast G1_le_B1 hn1 hx1_pos hu.le hw.le J1.toNat
    have heqJ : (J1.toNat : ℤ) = J1 := Int.toNat_of_nonneg (by omega)
    have heqJr : (J1.toNat : ℝ) = (J1 : ℝ) := by exact_mod_cast heqJ
    have hsum : x2 u w + x3 u w = s1 u w := by unfold s1 x1 x2 x3; ring
    have hdiff : x3 u w - x2 u w = w := by unfold x2 x3; ring
    rw [heqJ] at hq; dsimp only at hq
    rw [hsum, hdiff, hGamma1_eq, heqJr, hJ1_sub, ← hkap1_def, ← hz1_def] at hq
    unfold G1 at hG; linarith only [hq, hG]
  have hB2_Q : (T2 (J2 + 1) : ℝ) - (z2 + 2) ^ 2 / 4 ≤ (B2 n u w : ℝ) := by
    have hq := cor_P1_quad_bound (g := gamma2 n u w) hx1_pos (lt_trans hx12 hx23) J2.toNat
    have hG : (G2 n u w J2.toNat : ℝ) ≤ (B2 n u w : ℝ) := by
      exact_mod_cast G2_le_B2 hn1 hx1_pos hu.le hw.le J2.toNat
    have heqJ : (J2.toNat : ℤ) = J2 := Int.toNat_of_nonneg (by omega)
    have heqJr : (J2.toNat : ℝ) = (J2 : ℝ) := by exact_mod_cast heqJ
    have hsum : x1 u w + x3 u w = s2 u w := by unfold s2 x1 x2 x3; ring
    have hdiff : x3 u w - x1 u w = d2 := by unfold x1 x3; rw [hd2_def]; ring
    rw [heqJ] at hq; dsimp only at hq
    rw [hsum, hdiff, hGamma2_eq, heqJr, hJ2_sub, ← hkap2_def, ← hz2_def] at hq
    unfold G2 at hG; linarith only [hq, hG]
  have hB3_Q : (T2 (J3 + 1) : ℝ) - (z3 + 2) ^ 2 / 4 ≤ (B3 n u w : ℝ) := by
    have hq := cor_P1_quad_bound (g := gamma3 n u w) hx1_pos hx12 J3.toNat
    have hG : (G3 n u w J3.toNat : ℝ) ≤ (B3 n u w : ℝ) := by
      exact_mod_cast G3_le_B3 hn1 hx1_pos hu.le hw.le J3.toNat
    have heqJ : (J3.toNat : ℤ) = J3 := Int.toNat_of_nonneg (by omega)
    have heqJr : (J3.toNat : ℝ) = (J3 : ℝ) := by exact_mod_cast heqJ
    have hsum : x1 u w + x2 u w = s3 u w := by unfold s3 x1 x2 x3; ring
    have hdiff : x2 u w - x1 u w = u := by unfold x1 x2; ring
    rw [heqJ] at hq; dsimp only at hq
    rw [hsum, hdiff, hGamma3_eq, heqJr, hJ3_sub, ← hkap3_def, ← hz3_def] at hq
    unfold G3 at hG; linarith only [hq, hG]
  -- Case I (`N ≥ 1`)
  by_cases hN1 : 1 ≤ N
  · have hg1' : g1 = 3 * (n : ℝ) * ((2 * u + w) / 3) / s1 u w := by rw [hg1_def, heta1_def]
    have hg3' : g3 = 3 * (n : ℝ) * (-(u + 2 * w) / 3) / s3 u w := by rw [hg3_def, heta3_def]
    rcases caseI_proof hn hu hw hr_lt hcone hg1' hg3' hg1_pos hg3_neg hj1_def hj3_def
        (by rw [← hJ1_def]; exact hJ1_ge) (by rw [← hJ2_def]; exact hJ2_ge)
        (by rw [← hJ3_def]; exact hJ3_ge) (by rw [← hN_def]; exact hN1) with hD | hK
    · left; rw [← hJ1_def, ← hJ2_def, ← hJ3_def] at hD; omega
    · right; exact hK
  -- Case II (`N ≤ 0`)
  · left
    push Not at hN1
    -- Step 1 identities (A1), (A2), (A3)
    have hE_eq : E = (9 * (n : ℝ) / 2) *
        (eta1 ^ 2 / s1 u w + eta2 ^ 2 / s2 u w + eta3 ^ 2 / s3 u w) := by
      have k1 : eta1 / s1 u w = (3 / 2) * eta1 - (3 / 2) * eta1 ^ 2 / s1 u w := by
        field_simp [ne_of_gt hs1_pos]
        have hs1' : s1 u w = 2 / 3 + eta1 := by linarith only [hs1_eta]
        rw [hs1']; ring
      have k2 : eta2 / s2 u w = (3 / 2) * eta2 - (3 / 2) * eta2 ^ 2 / s2 u w := by
        field_simp [ne_of_gt hs2_pos]
        have hs2' : s2 u w = 2 / 3 + eta2 := by linarith only [hs2_eta]
        rw [hs2']; ring
      have k3 : eta3 / s3 u w = (3 / 2) * eta3 - (3 / 2) * eta3 ^ 2 / s3 u w := by
        field_simp [ne_of_gt hs3_pos]
        have hs3' : s3 u w = 2 / 3 + eta3 := by linarith only [hs3_eta]
        rw [hs3']; ring
      rw [hE_def, hg1_def, hg2_def, hg3_def]
      have hfac : 3 * (n : ℝ) * eta1 / s1 u w + 3 * (n : ℝ) * eta2 / s2 u w +
          3 * (n : ℝ) * eta3 / s3 u w =
          3 * (n : ℝ) * (eta1 / s1 u w + eta2 / s2 u w + eta3 / s3 u w) := by ring
      rw [hfac, k1, k2, k3]
      have hsum3 : (3 / 2) * eta1 - (3 / 2) * eta1 ^ 2 / s1 u w +
          ((3 / 2) * eta2 - (3 / 2) * eta2 ^ 2 / s2 u w) +
          ((3 / 2) * eta3 - (3 / 2) * eta3 ^ 2 / s3 u w) =
          -(3 / 2) * (eta1 ^ 2 / s1 u w + eta2 ^ 2 / s2 u w + eta3 ^ 2 / s3 u w) := by
        linear_combination (3 / 2) * heta_sum
      rw [hsum3]; ring
    have hE_pos : 0 < E := by
      rw [hE_eq]
      have h1 : 0 < eta1 ^ 2 / s1 u w :=
        div_pos (sq_pos_of_pos (by rw [heta1_def]; linarith only [hu, hw])) hs1_pos
      have h2 : 0 ≤ eta2 ^ 2 / s2 u w := div_nonneg (sq_nonneg _) hs2_pos.le
      have h3 : 0 ≤ eta3 ^ 2 / s3 u w := div_nonneg (sq_nonneg _) hs3_pos.le
      nlinarith only [hn_r, h1, h2, h3]
    have hN_eq : (N : ℝ) = eps1 + eps2 + eps3 - E := by
      rw [hN_def, heps1_def, heps2_def, heps3_def, hE_def]; push_cast; ring
    have hQ_eq : Q = 9 * (n : ℝ) *
        (eta1 ^ 2 / s1 u w * ((n : ℝ) * (1 - s1 u w) / s1 u w + 3) +
         eta2 ^ 2 / s2 u w * ((n : ℝ) * (1 - s2 u w) / s2 u w + 3) +
         eta3 ^ 2 / s3 u w * ((n : ℝ) * (1 - s3 u w) / s3 u w + 3)) := by
      rw [hQ_def, hE_eq, hg1_def, hg2_def, hg3_def]
      field_simp [ne_of_gt hs1_pos, ne_of_gt hs2_pos, ne_of_gt hs3_pos]; ring
    have hQ_nn : 0 ≤ Q := by
      rw [hQ_eq]
      have h1 : 0 ≤ eta1 ^ 2 / s1 u w * ((n : ℝ) * (1 - s1 u w) / s1 u w + 3) :=
        mul_nonneg (div_nonneg (sq_nonneg _) hs1_pos.le)
          (by have : 0 ≤ (n : ℝ) * (1 - s1 u w) / s1 u w :=
                div_nonneg (mul_nonneg (by linarith only [hn_r]) (by linarith only [hs1_hi])) hs1_pos.le
              linarith only [this])
      have h2 : 0 ≤ eta2 ^ 2 / s2 u w * ((n : ℝ) * (1 - s2 u w) / s2 u w + 3) :=
        mul_nonneg (div_nonneg (sq_nonneg _) hs2_pos.le)
          (by have : 0 ≤ (n : ℝ) * (1 - s2 u w) / s2 u w :=
                div_nonneg (mul_nonneg (by linarith only [hn_r]) (by linarith only [hs2_lt_s1, hs1_hi])) hs2_pos.le
              linarith only [this])
      have h3 : 0 ≤ eta3 ^ 2 / s3 u w * ((n : ℝ) * (1 - s3 u w) / s3 u w + 3) :=
        mul_nonneg (div_nonneg (sq_nonneg _) hs3_pos.le)
          (by have : 0 ≤ (n : ℝ) * (1 - s3 u w) / s3 u w :=
                div_nonneg (mul_nonneg (by linarith only [hn_r]) (by linarith only [hs3_lt_s2, hs2_lt_s1, hs1_hi])) hs3_pos.le
              linarith only [this])
      nlinarith only [hn_r, h1, h2, h3]
    have hA3 : 2 * ((n : ℝ) - 3) * (N : ℝ) + ((j1 : ℝ) ^ 2 + (j2 : ℝ) ^ 2 + (j3 : ℝ) ^ 2) =
        Q + 2 * ((Gamma1 + 1) * eps1 + (Gamma2 + 1) * eps2 + (Gamma3 + 1) * eps3) +
          (eps1 ^ 2 + eps2 ^ 2 + eps3 ^ 2) := by
      have hj1 : (j1 : ℝ) = g1 + eps1 := by linarith only [heps1_def]
      have hj2 : (j2 : ℝ) = g2 + eps2 := by linarith only [heps2_def]
      have hj3 : (j3 : ℝ) = g3 + eps3 := by linarith only [heps3_def]
      rw [hN_eq, hj1, hj2, hj3, hQ_def, hGam1_def, hGam2_def, hGam3_def, hE_def]; ring
    -- Step 3 estimates in X, phi, sh
    have hd2_pos : 0 < d2 := by linarith only [hd2_def, hu, hw]
    have hd2_hi : d2 ≤ 3 * rad n := by linarith only [hd2_def, hw, hcone]
    obtain ⟨X, hX_def⟩ : ∃ x : ℝ, x = (n : ℝ) * d2 := ⟨_, rfl⟩
    obtain ⟨phi, hphi_def⟩ : ∃ x : ℝ, x = eta2 / d2 := ⟨_, rfl⟩
    obtain ⟨sh, hsh_def⟩ : ∃ x : ℝ, x = 1 + 3 * phi ^ 2 := ⟨_, rfl⟩
    have hX_pos : 0 < X := by rw [hX_def]; exact mul_pos (by linarith only [hn_r]) hd2_pos
    have hphi_lo : -1 / 3 ≤ phi := by
      rw [hphi_def, heta2_def, hd2_def, le_div_iff₀ (by linarith only [hu, hw] : 0 < u + w)]
      linarith only [hw]
    have hphi_hi : phi ≤ 1 / 3 := by
      rw [hphi_def, heta2_def, hd2_def, div_le_iff₀ (by linarith only [hu, hw] : 0 < u + w)]
      linarith only [hu]
    have hsh_lo : 1 ≤ sh := by rw [hsh_def]; nlinarith only [sq_nonneg phi]
    have hsh_hi : sh ≤ 4 / 3 := by rw [hsh_def]; nlinarith only [hphi_lo, hphi_hi]
    have heta_sq_sum : eta1 ^ 2 + eta2 ^ 2 + eta3 ^ 2 = sh * d2 ^ 2 / 2 := by
      rw [hsh_def, hphi_def, heta1_def, heta2_def, heta3_def, hd2_def]
      field_simp [ne_of_gt (by linarith only [hu, hw] : 0 < u + w)]; ring
    have hs2_phi : s2 u w = 2 / 3 + phi * d2 := by
      rw [hphi_def, div_mul_cancel₀ _ (ne_of_gt hd2_pos)]; linarith only [hs2_eta]
    have hs3_phi : s3 u w = 2 / 3 - (1 + phi) * d2 / 2 := by
      rw [hphi_def, heta2_def, hd2_def, hs3_eq]
      field_simp [ne_of_gt (by linarith only [hu, hw] : 0 < u + w)]; ring
    have hQ_lb : 2.627 * sh * X ^ 2 ≤ Q := by
      have hQ0 := Q_lower_bound (c := 0.58383) hs1_pos hs2_pos hs3_pos (by linarith only [hn_r])
        (by rw [le_div_iff₀ (sq_pos_of_pos hs1_pos)]; nlinarith only [hs1_hi, hs1_pos])
        (by rw [le_div_iff₀ (sq_pos_of_pos hs2_pos)]; nlinarith only [hs2_lt_s1, hs1_hi, hs2_pos])
        (by rw [le_div_iff₀ (sq_pos_of_pos hs3_pos)]; nlinarith only [hs3_lt_s2, hs2_lt_s1, hs1_hi, hs3_pos])
        heta_sq_sum hX_def hQ_eq
      have : (2.627 : ℝ) ≤ (9 / 2) * 0.58383 := by norm_num
      have hnn : 0 ≤ sh * X ^ 2 := mul_nonneg (by linarith only [hsh_lo]) (sq_nonneg X)
      nlinarith only [hQ0, this, hnn]
    have hE_exact_ub : E ≤ (9 / (4 * s3 u w)) * sh * X ^ 2 / (n : ℝ) := by
      rw [hE_eq]
      have hinv1 : eta1 ^ 2 / s1 u w ≤ eta1 ^ 2 / s3 u w :=
        div_le_div_of_nonneg_left (sq_nonneg _) hs3_pos (le_trans hs3_lt_s2.le hs2_lt_s1.le)
      have hinv2 : eta2 ^ 2 / s2 u w ≤ eta2 ^ 2 / s3 u w :=
        div_le_div_of_nonneg_left (sq_nonneg _) hs3_pos hs3_lt_s2.le
      have hsum_le : eta1 ^ 2 / s1 u w + eta2 ^ 2 / s2 u w + eta3 ^ 2 / s3 u w ≤
          (eta1 ^ 2 + eta2 ^ 2 + eta3 ^ 2) / s3 u w := by
        rw [add_div, add_div]; linarith only [hinv1, hinv2]
      rw [heta_sq_sum] at hsum_le
      have hstep := mul_le_mul_of_nonneg_left hsum_le (by linarith only [hn_r] : 0 ≤ 9 * (n : ℝ) / 2)
      have hrw : 9 * (n : ℝ) / 2 * (sh * d2 ^ 2 / 2 / s3 u w) =
          9 / (4 * s3 u w) * sh * X ^ 2 / (n : ℝ) := by
        rw [hX_def]; field_simp [ne_of_gt hs3_pos, show (n : ℝ) ≠ 0 by linarith only [hn_r]]; ring
      linarith only [hstep, hrw]
    have hE_lb : 3.1795 * sh * X ^ 2 / (n : ℝ) ≤ E := by
      rw [hE_eq]
      have hinv2 : eta2 ^ 2 / s1 u w ≤ eta2 ^ 2 / s2 u w :=
        div_le_div_of_nonneg_left (sq_nonneg _) hs2_pos hs2_lt_s1.le
      have hinv3 : eta3 ^ 2 / s1 u w ≤ eta3 ^ 2 / s3 u w :=
        div_le_div_of_nonneg_left (sq_nonneg _) hs3_pos (le_trans hs3_lt_s2.le hs2_lt_s1.le)
      have hsum_ge : (eta1 ^ 2 + eta2 ^ 2 + eta3 ^ 2) / s1 u w ≤
          eta1 ^ 2 / s1 u w + eta2 ^ 2 / s2 u w + eta3 ^ 2 / s3 u w := by
        rw [add_div, add_div]; linarith only [hinv2, hinv3]
      rw [heta_sq_sum] at hsum_ge
      have hstep := mul_le_mul_of_nonneg_left hsum_ge (by linarith only [hn_r] : 0 ≤ 9 * (n : ℝ) / 2)
      have hrw : 9 * (n : ℝ) / 2 * (sh * d2 ^ 2 / 2 / s1 u w) =
          9 / (4 * s1 u w) * sh * X ^ 2 / (n : ℝ) := by
        rw [hX_def]; field_simp [ne_of_gt hs1_pos, show (n : ℝ) ≠ 0 by linarith only [hn_r]]; ring
      have hc : 3.1795 ≤ 9 / (4 * s1 u w) := by
        rw [le_div_iff₀ (by linarith only [hs1_pos])]; linarith only [hs1_hi]
      have hmul := mul_le_mul_of_nonneg_right hc
        (div_nonneg (mul_nonneg (by linarith only [hsh_lo]) (sq_nonneg X)) (by linarith only [hn_r]))
      have hrw2 : 9 / (4 * s1 u w) * (sh * X ^ 2 / (n : ℝ)) =
          9 / (4 * s1 u w) * sh * X ^ 2 / (n : ℝ) := by ring
      have hrw3 : 3.1795 * (sh * X ^ 2 / (n : ℝ)) = 3.1795 * sh * X ^ 2 / (n : ℝ) := by ring
      linarith only [hstep, hrw, hmul, hrw2, hrw3]
    have hE_ub : E ≤ 3.4821 * sh * X ^ 2 / (n : ℝ) := by
      have hc : 9 / (4 * s3 u w) ≤ 3.4821 := by
        rw [div_le_iff₀ (by linarith only [hs3_pos])]; linarith only [hs3_lo]
      have hmul := mul_le_mul_of_nonneg_right hc
        (div_nonneg (mul_nonneg (by linarith only [hsh_lo]) (sq_nonneg X)) (by linarith only [hn_r]))
      have hrw2 : 9 / (4 * s3 u w) * (sh * X ^ 2 / (n : ℝ)) =
          9 / (4 * s3 u w) * sh * X ^ 2 / (n : ℝ) := by ring
      have hrw3 : 3.4821 * (sh * X ^ 2 / (n : ℝ)) = 3.4821 * sh * X ^ 2 / (n : ℝ) := by ring
      linarith only [hE_exact_ub, hmul, hrw2, hrw3]
    have hkap2_eq : kappa2 = s2 u w * (n : ℝ) / X := by
      rw [hkap2_def, hX_def]; field_simp [ne_of_gt hd2_pos, show (n : ℝ) ≠ 0 by linarith only [hn_r]]
    have hg2_phi_eq : g2 = 3 * phi * X / s2 u w := by
      rw [hg2_def, hphi_def, hX_def]; field_simp [ne_of_gt hd2_pos, ne_of_gt hs2_pos]
    have hkap2_sq_E : kappa2 ^ 2 * E ≤ (n : ℝ) * (d2 * (8 + d2) / (3 * s3 u w) + 2) := by
      have h1 : kappa2 ^ 2 * E ≤
          kappa2 ^ 2 * ((9 / (4 * s3 u w)) * sh * X ^ 2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hE_exact_ub (sq_nonneg _)
      have h2 : kappa2 ^ 2 * ((9 / (4 * s3 u w)) * sh * X ^ 2 / (n : ℝ)) =
          (n : ℝ) * ((9 / 4) * sh * (s2 u w) ^ 2 / s3 u w) := by
        rw [hkap2_eq]; field_simp [ne_of_gt hX_pos, ne_of_gt hs3_pos, show (n : ℝ) ≠ 0 by linarith only [hn_r]]
      have h3 := estimate_e5_alg phi d2 hphi_lo hphi_hi hd2_pos.le (by rw [← hs3_phi]; exact hs3_pos)
      rw [← hs2_phi, ← hs3_phi] at h3
      have h4 : (9 / 4) * sh * (s2 u w) ^ 2 / s3 u w ≤ d2 * (8 + d2) / (3 * s3 u w) + 2 := by
        rw [hsh_def]; linarith only [h3]
      nlinarith only [h1, h2, h4, hn_r]
    -- Step 4: Case II-1 (`E ≥ 1`)
    by_cases hE1 : 1 ≤ E
    · exact caseII1_proof hn hr_lt hs1_hi hs3_lo hs3_lt_s2 hs2_lt_s1 hs2_pos hs3_pos
        hd2_pos hd2_hi hkap2_def hGam2_def hGamma1_pos hGamma3_pos
        (by rw [← hJ1_def]; exact hJ1_ge) (by rw [← hJ2_def]; exact hJ2_ge)
        (by rw [← hJ3_def]; exact hJ3_ge)
        (by rw [← hJ1_def]; exact hB1_T) (by rw [← hJ3_def]; exact hB3_T)
        (by rw [← hJ2_def]; exact hB2_Q)
        heps2_def heps1_lo heps2_lo heps2_hi heps3_lo hz2_def hE1
        (by rw [← hN_def]; exact hA3) hX_def hX_pos hphi_lo hphi_hi
        hsh_lo hsh_hi hQ_lb hE_ub hkap2_eq hg2_phi_eq hkap2_sq_E
    -- Step 5: Case II-2 (`E < 1`, hence `N = 0`, `eps1 + eps2 + eps3 = E`)
    · push Not at hE1
      exact caseII2_proof hn hu hw hs1_eq hs2_eq hs3_eq hs3_lt_s2 hs2_lt_s1
        hs1_pos hs2_pos hs3_pos heta2_def heta3_def hd2_def hd2_pos
        hkap1_def hkap2_def hkap3_def hg1_pos hg3_def hGam2_def
        hGamma1_pos hGamma2_pos hGamma3_pos
        (by rw [← hJ1_def]; exact hJ1_ge) (by rw [← hJ2_def]; exact hJ2_ge)
        (by rw [← hJ3_def]; exact hJ3_ge)
        (by rw [← hJ1_def]; exact hB1_T) (by rw [← hJ3_def]; exact hB3_T)
        (by rw [← hJ1_def]; exact hB1_Q) (by rw [← hJ2_def]; exact hB2_Q)
        (by rw [← hJ3_def]; exact hB3_Q)
        heps1_def heps2_def heps3_def heps1_lo heps2_lo heps3_lo
        hz1_def hz2_def hz3_def (by rw [← hN_def]; exact hN1)
        hE_pos hE1 (by rw [← hN_def]; exact hN_eq) hQ_eq hQ_nn
        (by rw [← hN_def]; exact hA3) hX_def hX_pos hphi_def hphi_lo hphi_hi
        hsh_lo hsh_hi heta_sq_sum hE_exact_ub hE_lb hkap2_eq hg2_phi_eq hkap2_sq_E

/-- **Unconditional upper bound for all `n ≥ 700` (`theorem_A_upper_bound_ge_700`):**
Combining Theorem A (`theorem_A_ge_700`), Lemma P (`lemma_P_sum_B`), Lemma C
(`lemma_C_coupling`), and Reduction R (`reduction_R`), EVERY nonzero real plane cuts at
most `F(n) = ⌊(9n² + 4n - 17)/4⌋` open unit cubes for all `n ≥ 700`. -/
theorem theorem_A_upper_bound_ge_700 (n : ℕ) (hn : 700 ≤ n) :
    ∀ a b c t : ℝ, IsNormal a b c → cutCount n a b c t ≤ F n := by
  apply reduction_R n (by omega)
  intro u w t hu hw hcone
  have hx1_pos : 0 < x1 u w := by
    have hr_lt : rad n < 0.0204862 := by
      have hsq : (rad n) ^ 2 < (0.0204862 : ℝ) ^ 2 := by
        rw [rad_sq, div_lt_iff₀ (by positivity)]
        have hn_r : (700 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      nlinarith [rad_pos n]
    unfold x1; linarith
  rcases theorem_A_ge_700 n hn u w hu hw hcone with hB | ⟨hev, hK⟩
  · exact le_trans hB (lemma_P_sum_B (by omega) hx1_pos hu.le hw.le t)
  · rcases hev with ⟨m, hm⟩
    have hc_eq : n = 2 * ((n - 4) / 2) + 4 := by omega
    have hc1 : 1 ≤ (n - 4) / 2 := by omega
    have hne : (u, w) ≠ (0, 0) := fun h => by simp only [Prod.mk.injEq] at h; linarith
    have hC := lemma_C_coupling ((n - 4) / 2) hc1 u w t hu.le hw.le hne hK
    rwa [← hc_eq] at hC

end

end CheeseCutM
