module

/-!
# Core Natural-Number Counting Lemmas for Cheese-Cutting

Pure `Nat`/`Int` counting for diagonal layers `i + j + k = σ` in `{0, …, n - 1}³`
and for the Bárány–Frankl slab sets `T3`, `X3`, `Y3`.
-/

@[expose] public section

namespace CheeseCutM.Core

/-- `rsum f m = f 0 + ⋯ + f (m - 1)`. -/
def rsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => rsum f m + f m

theorem rsum_succ (f : Nat → Nat) (m : Nat) : rsum f (m + 1) = rsum f m + f m := rfl

theorem rsum_congr {f g : Nat → Nat} {m : Nat} (h : ∀ x, x < m → f x = g x) :
    rsum f m = rsum g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [rsum_succ, rsum_succ, ih (fun x hx => h x (by omega)), h m (by omega)]

theorem rsum_add (f g : Nat → Nat) (m : Nat) :
    rsum (fun x => f x + g x) m = rsum f m + rsum g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [rsum_succ, rsum_succ, rsum_succ, ih]
    omega

theorem rsum_split (f : Nat → Nat) (a b : Nat) :
    rsum f (a + b) = rsum f a + rsum (fun x => f (a + x)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← Nat.add_assoc, rsum_succ, rsum_succ, ih]
    omega

/-- The number of `w < m` with `a ≤ p + w ≤ b`. -/
theorem rsum_window (p a b m : Nat) :
    rsum (fun w => if a ≤ p + w ∧ p + w ≤ b then 1 else 0) m =
      min (b + 1) (p + m) - max a p := by
  induction m with
  | zero => simp only [rsum]; omega
  | succ m ih =>
    rw [rsum_succ, ih]
    split <;> omega

/-- `2 (c + (c + 1) + ⋯ + (c + m - 1)) + m = 2 c m + m²`. -/
theorem rsum_up (c m : Nat) : 2 * rsum (fun x => c + x) m + m = 2 * c * m + m * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [rsum_succ]
    grind

/-- `2 (d + (d - 1) + ⋯ + (d - m + 1)) + m² = 2 d m + m`, for `m ≤ d + 1`. -/
theorem rsum_down (d m : Nat) (hm : m ≤ d + 1) :
    2 * rsum (fun x => d - x) m + m * m = 2 * d * m + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [rsum_succ]
    have ih' := ih (by omega)
    have e : d - m + m = d := by omega
    grind

/-! ### One diagonal layer -/

/-- The number of cells of `{0, …, n - 1}³` with coordinate sum `σ`. -/
def layerCount (n σ : Nat) : Nat :=
  rsum (fun x => rsum (fun y => rsum (fun w => if x + y + w = σ then 1 else 0) n) n) n

/-- After the two inner sums: the cells `(x, ·, ·)` of the layer. -/
def M (n σ x : Nat) : Nat := min (σ + 1) (x + n) - max (σ + 1 - n) x

theorem layerCount_eq_rsum_M (n σ : Nat) : layerCount n σ = rsum (M n σ) n := by
  unfold layerCount
  apply rsum_congr
  intro x _
  have inner : ∀ y, rsum (fun w => if x + y + w = σ then 1 else 0) n =
      (if σ + 1 - n ≤ x + y ∧ x + y ≤ σ then 1 else 0) := by
    intro y
    have h1 : rsum (fun w => if x + y + w = σ then 1 else 0) n =
        rsum (fun w => if σ ≤ (x + y) + w ∧ (x + y) + w ≤ σ then 1 else 0) n := by
      apply rsum_congr
      intro w _
      by_cases h : x + y + w = σ
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
    rw [h1, rsum_window]
    split <;> omega
  rw [rsum_congr (fun y _ => inner y)]
  have h2 : rsum (fun y => if σ + 1 - n ≤ x + y ∧ x + y ≤ σ then 1 else 0) n =
      min (σ + 1) (x + n) - max (σ + 1 - n) x := rsum_window x (σ + 1 - n) σ n
  rw [h2]
  rfl

theorem layerCount_alg_end (n σ B : Int) (hn : n = σ + 2)
    (d : 2 * B + n * n = 2 * (σ + 1) * n + n) :
    4 * B + (2 * σ + 3 - 3 * n) ^ 2 = 3 * n ^ 2 + 1 := by
  subst hn
  grind

theorem layerCount_alg_mid (n σ k c A B : Int) (hk : k = σ + 1 - n) (hc : c = 2 * n - σ - 1)
    (u : 2 * A + k = 2 * c * k + k * k) (d : 2 * B + c * c = 2 * n * c + c) :
    4 * (A + B) + (2 * σ + 3 - 3 * n) ^ 2 = 3 * n ^ 2 + 1 := by
  subst hk hc
  grind

/-- The layer count: `4 · layerCount(n, σ) + (2σ + 3 - 3n)² = 3n² + 1` for
`n - 2 ≤ σ ≤ 2n - 1`. -/
theorem layerCount_closed (n σ : Nat) (h1 : n ≤ σ + 2) (h2 : σ + 1 ≤ 2 * n) :
    4 * (layerCount n σ : Int) + (2 * (σ : Int) + 3 - 3 * (n : Int)) ^ 2 =
      3 * (n : Int) ^ 2 + 1 := by
  rw [layerCount_eq_rsum_M]
  by_cases hs : σ + 2 = n
  · have e : rsum (M n σ) n = rsum (fun x => (σ + 1) - x) n := by
      apply rsum_congr
      intro x hx
      unfold M
      omega
    have d := rsum_down (σ + 1) n (by omega)
    rw [e]
    generalize rsum (fun x => (σ + 1) - x) n = B at d ⊢
    have d' : 2 * (B : Int) + (n : Int) * (n : Int) =
        2 * ((σ : Int) + 1) * (n : Int) + (n : Int) := by
      exact_mod_cast d
    exact layerCount_alg_end (n : Int) (σ : Int) (B : Int) (by omega) d'
  · obtain ⟨k, hk⟩ : ∃ k, k = σ + 1 - n := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = n - k := ⟨_, rfl⟩
    have hkn : k + c = n := by omega
    have e1 : rsum (M n σ) n = rsum (M n σ) k + rsum (fun x => M n σ (k + x)) c := by
      rw [← rsum_split, hkn]
    have e2 : rsum (M n σ) k = rsum (fun x => c + x) k := by
      apply rsum_congr
      intro x hx
      unfold M
      omega
    have e3 : rsum (fun x => M n σ (k + x)) c = rsum (fun x => n - x) c := by
      apply rsum_congr
      intro x hx
      unfold M
      omega
    have u := rsum_up c k
    have d := rsum_down n c (by omega)
    rw [e1, e2, e3]
    generalize rsum (fun x => c + x) k = A at u ⊢
    generalize rsum (fun x => n - x) c = B at d ⊢
    have u' : 2 * (A : Int) + (k : Int) = 2 * (c : Int) * (k : Int) + (k : Int) * (k : Int) := by
      exact_mod_cast u
    have d' : 2 * (B : Int) + (c : Int) * (c : Int) = 2 * (n : Int) * (c : Int) + (c : Int) := by
      exact_mod_cast d
    have hk' : (k : Int) = (σ : Int) + 1 - (n : Int) := by omega
    have hc' : (c : Int) = 2 * (n : Int) - (σ : Int) - 1 := by omega
    have := layerCount_alg_mid (n : Int) (σ : Int) (k : Int) (c : Int) (A : Int) (B : Int)
      hk' hc' u' d'
    push_cast
    exact this

/-! ### Pairs, and the sets `X3`, `Y3` -/

theorem pair_count (n u : Nat) :
    rsum (fun x => rsum (fun y => if x + y = u then 1 else 0) n) n =
      min (u + 1) n - (u + 1 - n) := by
  have inner : ∀ x, rsum (fun y => if x + y = u then 1 else 0) n =
      (if u + 1 - n ≤ 0 + x ∧ 0 + x ≤ u then 1 else 0) := by
    intro x
    have h1 : rsum (fun y => if x + y = u then 1 else 0) n =
        rsum (fun y => if u ≤ x + y ∧ x + y ≤ u then 1 else 0) n := by
      apply rsum_congr
      intro y _
      by_cases h : x + y = u
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
    rw [h1, rsum_window]
    split <;> omega
  rw [rsum_congr (fun x _ => inner x), rsum_window]
  omega

/-- The cells of `T3`: three full diagonal layers. -/
def tripleT (n s : Nat) : Nat :=
  rsum (fun x => rsum (fun y => rsum (fun w =>
    if s ≤ x + y + w ∧ x + y + w ≤ s + 2 then 1 else 0) n) n) n

/-- The cells of `X3`: layer `s + 3` with `w = 0`. -/
def tripleX (n s : Nat) : Nat :=
  rsum (fun x => rsum (fun y => rsum (fun w =>
    if x + y + w = s + 3 ∧ w = 0 then 1 else 0) n) n) n

/-- The cells of `Y3`: layer `s - 1` with `w = n - 1`. -/
def tripleY (n s : Nat) : Nat :=
  rsum (fun x => rsum (fun y => rsum (fun w =>
    if x + y + w + 1 = s ∧ w + 1 = n then 1 else 0) n) n) n

theorem tripleT_eq (n s : Nat) :
    tripleT n s = layerCount n s + layerCount n (s + 1) + layerCount n (s + 2) := by
  unfold tripleT layerCount
  have pt : ∀ x y w : Nat, (if s ≤ x + y + w ∧ x + y + w ≤ s + 2 then 1 else 0) =
      (if x + y + w = s then 1 else 0) + (if x + y + w = s + 1 then 1 else 0) +
        (if x + y + w = s + 2 then 1 else 0) := by
    intro x y w
    by_cases a : x + y + w = s
    · rw [ite_eq_left (by omega), ite_eq_left a, ite_eq_right (by omega), ite_eq_right (by omega)]
    · by_cases b : x + y + w = s + 1
      · rw [ite_eq_left (by omega), ite_eq_right a, ite_eq_left b, ite_eq_right (by omega)]
      · by_cases c : x + y + w = s + 2
        · rw [ite_eq_left (by omega), ite_eq_right a, ite_eq_right b, ite_eq_left c]
        · rw [ite_eq_right (by omega), ite_eq_right a, ite_eq_right b, ite_eq_right c]
  simp only [pt, rsum_add]

theorem tripleX_eq (n s : Nat) (hn : 1 ≤ n) : tripleX n s = min (s + 4) n - (s + 4 - n) := by
  unfold tripleX
  have inner : ∀ x y, rsum (fun w => if x + y + w = s + 3 ∧ w = 0 then 1 else 0) n =
      (if x + y = s + 3 then 1 else 0) := by
    intro x y
    have h1 : rsum (fun w => if x + y + w = s + 3 ∧ w = 0 then 1 else 0) n =
        rsum (fun w => if s + 3 ≤ (x + y) + w ∧ (x + y) + w ≤ min (s + 3) (x + y)
          then 1 else 0) n := by
      apply rsum_congr
      intro w _
      by_cases h : x + y + w = s + 3 ∧ w = 0
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
    rw [h1, rsum_window]
    split <;> omega
  rw [rsum_congr (fun x _ => rsum_congr (fun y _ => inner x y)), pair_count]

theorem tripleY_eq (n s : Nat) (hs : s + 2 ≤ 2 * n) : tripleY n s = s + 1 - n := by
  unfold tripleY
  have inner : ∀ x y, rsum (fun w => if x + y + w + 1 = s ∧ w + 1 = n then 1 else 0) n =
      (if x + y = s - n ∧ n ≤ s then 1 else 0) := by
    intro x y
    have h1 : rsum (fun w => if x + y + w + 1 = s ∧ w + 1 = n then 1 else 0) n =
        rsum (fun w => if max s (x + y + n) ≤ (x + y + 1) + w ∧
          (x + y + 1) + w ≤ min s (x + y + n) then 1 else 0) n := by
      apply rsum_congr
      intro w _
      by_cases h : x + y + w + 1 = s ∧ w + 1 = n
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
    rw [h1, rsum_window]
    split <;> omega
  by_cases hns : n ≤ s
  · have e : ∀ x y, (if x + y = s - n ∧ n ≤ s then 1 else 0) =
        (if x + y = s - n then 1 else 0) := by
      intro x y
      by_cases h : x + y = s - n
      · rw [ite_eq_left ⟨h, hns⟩, ite_eq_left h]
      · rw [ite_eq_right (fun hh => h hh.1), ite_eq_right h]
    rw [rsum_congr (fun x _ => rsum_congr (fun y _ => (inner x y).trans (e x y))), pair_count]
    omega
  · have e : ∀ x y, (if x + y = s - n ∧ n ≤ s then 1 else 0) = 0 := by
      intro x y
      rw [ite_eq_right (fun hh => hns hh.2)]
    rw [rsum_congr (fun x _ => rsum_congr (fun y _ => (inner x y).trans (e x y)))]
    have z : ∀ m : Nat, rsum (fun _ => 0) m = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [rsum_succ, ih]
    have z2 : rsum (fun _ => rsum (fun _ => 0) n) n = 0 := by
      rw [rsum_congr (fun x _ => z n), z]
    rw [z2]
    omega

/-- `g(s)` written with the closed forms, times four. -/
theorem G_four (n s : Nat) (hn : 3 ≤ n) (h1 : n ≤ s + 2) (h2 : s + 3 ≤ 2 * n) :
    4 * ((tripleT n s + tripleX n s + tripleY n s : Nat) : Int) =
      3 * (3 * (n : Int) ^ 2 + 1) - (2 * (s : Int) + 3 - 3 * (n : Int)) ^ 2 -
        (2 * (s : Int) + 5 - 3 * (n : Int)) ^ 2 - (2 * (s : Int) + 7 - 3 * (n : Int)) ^ 2 +
        4 * ((2 * n - (s + 4) : Nat) : Int) + 4 * ((s + 1 - n : Nat) : Int) := by
  rw [tripleT_eq, tripleX_eq n s (by omega), tripleY_eq n s (by omega)]
  have d0 := layerCount_closed n s h1 (by omega)
  have d1 := layerCount_closed n (s + 1) (by omega) (by omega)
  have d2 := layerCount_closed n (s + 2) (by omega) (by omega)
  have ex : min (s + 4) n - (s + 4 - n) = 2 * n - (s + 4) := by omega
  rw [ex]
  push_cast at d1 d2 ⊢
  grind

theorem G_le (n s : Nat) (hn : 3 ≤ n) (h1 : n ≤ s + 2) (h2 : s + 3 ≤ 2 * n) :
    tripleT n s + tripleX n s + tripleY n s ≤ (9 * n ^ 2 + 4 * n - 17) / 4 := by
  have h := G_four n s hn h1 h2
  obtain ⟨u, hu⟩ : ∃ u : Int, u = 2 * (s : Int) + 5 - 3 * (n : Int) := ⟨_, rfl⟩
  have hsq : 0 ≤ u ^ 2 := Int.sq_nonneg u
  have hnn : 3 * (n : Int) ≤ (n : Int) ^ 2 := by
    have : 3 * n ≤ n * n := Nat.mul_le_mul_right n hn
    have h' : ((3 * n : Nat) : Int) ≤ ((n * n : Nat) : Int) := by omega
    push_cast at h'
    grind
  have expand : 3 * (3 * (n : Int) ^ 2 + 1) - (2 * (s : Int) + 3 - 3 * (n : Int)) ^ 2 -
      (2 * (s : Int) + 5 - 3 * (n : Int)) ^ 2 - (2 * (s : Int) + 7 - 3 * (n : Int)) ^ 2 =
      9 * (n : Int) ^ 2 - 5 - 3 * u ^ 2 := by
    rw [hu]
    grind
  rw [expand] at h
  have hp : ((n ^ 2 : Nat) : Int) = (n : Int) ^ 2 := by push_cast; rfl
  by_cases hend : s + 2 = n ∨ s + 3 = 2 * n
  · have hu2 : u ^ 2 = (n : Int) ^ 2 - 2 * (n : Int) + 1 := by
      rcases hend with e | e
      · have : u = 1 - (n : Int) := by omega
        rw [this]
        grind
      · have : u = (n : Int) - 1 := by omega
        rw [this]
        grind
    omega
  · omega

theorem G_eq (n : Nat) (hn : 3 ≤ n) :
    tripleT n ((3 * n - 4) / 2) + tripleX n ((3 * n - 4) / 2) + tripleY n ((3 * n - 4) / 2) =
      (9 * n ^ 2 + 4 * n - 17) / 4 := by
  have h := G_four n ((3 * n - 4) / 2) hn (by omega) (by omega)
  obtain ⟨u, hu⟩ : ∃ u : Int, u = 2 * (((3 * n - 4) / 2 : Nat) : Int) + 5 - 3 * (n : Int) :=
    ⟨_, rfl⟩
  have hu01 : u = 0 ∨ u = 1 := by omega
  have hu2 : u ^ 2 = u := by
    rcases hu01 with e | e <;> rw [e] <;> rfl
  have expand : 3 * (3 * (n : Int) ^ 2 + 1) -
      (2 * (((3 * n - 4) / 2 : Nat) : Int) + 3 - 3 * (n : Int)) ^ 2 -
      (2 * (((3 * n - 4) / 2 : Nat) : Int) + 5 - 3 * (n : Int)) ^ 2 -
      (2 * (((3 * n - 4) / 2 : Nat) : Int) + 7 - 3 * (n : Int)) ^ 2 =
      9 * (n : Int) ^ 2 - 5 - 3 * u ^ 2 := by
    rw [hu]
    grind
  rw [expand, hu2] at h
  have hp : ((n ^ 2 : Nat) : Int) = (n : Int) ^ 2 := by push_cast; rfl
  have hnn : 3 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have hpow : n ^ 2 = n * n := Nat.pow_two n
  omega

/-! ### Inverses of the triangle maps for Lemma T equality -/

theorem b1_inv (h x y w : Nat) (hx : x ≤ h) (hy : y < x) (hw : w < x) (h0 : y = 0 ∨ w = 0) :
    (if y + h - x ≤ w + h - x then (h - (y + h - x), 0, (w + h - x) - (y + h - x))
      else (h - (w + h - x), (y + h - x) - (w + h - x), 0)) = (x, y, w) := by
  split
  · have e1 : h - (y + h - x) = x := by omega
    have e2 : y = 0 := by omega
    have e3 : (w + h - x) - (y + h - x) = w := by omega
    rw [e1, e3, e2]
  · have e1 : h - (w + h - x) = x := by omega
    have e2 : w = 0 := by omega
    have e3 : (y + h - x) - (w + h - x) = y := by omega
    rw [e1, e3, e2]

theorem b2_inv (h x y w : Nat) (hy : y ≤ h) (hx : x < y) (hw : w < y) (h0 : x = 0 ∨ w = 0) :
    (if x + h - y ≤ w + h - y then (0, h - (x + h - y), (w + h - y) - (x + h - y))
      else ((x + h - y) - (w + h - y), h - (w + h - y), 0)) = (x, y, w) := by
  split
  · have e1 : h - (x + h - y) = y := by omega
    have e2 : x = 0 := by omega
    have e3 : (w + h - y) - (x + h - y) = w := by omega
    rw [e1, e3, e2]
  · have e1 : h - (w + h - y) = y := by omega
    have e2 : w = 0 := by omega
    have e3 : (x + h - y) - (w + h - y) = x := by omega
    rw [e1, e3, e2]

theorem b3_inv (h x y w : Nat) (hw : w ≤ h) (hx : x < w) (hy : y < w) (h0 : x = 0 ∨ y = 0) :
    (if x + h - w ≤ y + h - w then (0, (y + h - w) - (x + h - w), h - (x + h - w))
      else ((x + h - w) - (y + h - w), 0, h - (y + h - w))) = (x, y, w) := by
  split
  · have e1 : h - (x + h - w) = w := by omega
    have e2 : x = 0 := by omega
    have e3 : (y + h - w) - (x + h - w) = y := by omega
    rw [e1, e3, e2]
  · have e1 : h - (y + h - w) = w := by omega
    have e2 : y = 0 := by omega
    have e3 : (x + h - w) - (y + h - w) = x := by omega
    rw [e1, e3, e2]

theorem order_cases (x y w : Nat) :
    (y < x ∧ w < x) ∨ (x < y ∧ w < y) ∨ (x < w ∧ y < w) ∨
      (x = y ∧ w ≤ x) ∨ (x = w ∧ y ≤ x) ∨ (y = w ∧ x ≤ y) := by
  omega

end CheeseCutM.Core
