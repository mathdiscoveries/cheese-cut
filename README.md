# Maximum Unit Cubes Cut by a Plane in `[0, n]³` (`CheeseCutM`)

Lean 4 + Mathlib formalization of the exact maximum number `m(n)` of open unit
cubes `(i, i + 1) × (j, j + 1) × (k, k + 1)` inside `[0, n]³` that a single
real plane `a x + b y + c z = t` in `ℝ³` can meet.

## Headline Unconditional Theorems (`Challenge.lean`)

All six compared declarations in `Challenge.lean` are proved unconditionally
over `ℝ` in `Solution.lean` / `CheeseCutM` using only Lean's three standard
axioms (`propext`, `Quot.sound`, `Classical.choice`), with zero `sorry` and
zero `native_decide`:

1. `CheeseCutM.maxCutCount_eq_F_ge_700`: `m(n) = F(n) = ⌊(9n² + 4n - 17)/4⌋` for every `n ≥ 700`.
2. `CheeseCutM.barany_frankl_plus_two_refuted_ge_700`: `m(n) < F(n) + 2` for every `n ≥ 700` (refuting Bárány and Frankl's Section 5 "+2" remark).
3. `CheeseCutM.maxCutCount_eq_F_3_to_32`: `m(n) = F(n)` for every `3 ≤ n ≤ 32` (via pure-kernel `ℕ` Farkas-BSP certificates).
4. `CheeseCutM.maxCutCount_ten`: `m(10) = 230` (settling the open case `230 ≤ m(10) ≤ 246` stated in Bárány and Frankl, *Amer. Math. Monthly* 128, 2021, 543–552).
5. `CheeseCutM.theoremU_bound_all_ge_2`: `cutCount n a b c t ≤ ⌊(9n² + 6n - 20)/4⌋` for every `n ≥ 2` and every nonzero real plane.
6. `CheeseCutM.barany_frankl_lower_bound`: for every `n ≥ 3`, an explicit plane cuts exactly `F(n)` open unit cubes.

## Scope and Limitations

- **Unconditional in Lean:** `3 ≤ n ≤ 32`, `n ≥ 700`, universal upper bound for `n ≥ 2`, and lower-bound construction for `n ≥ 3`.
- **Outside Lean (`33 ≤ n ≤ 699`):** `CheeseCutM.VertexPrinciple` proves Proposition V (soundness of the vertex-certificate verifier) unconditionally, while the 667 finite certificates for `33 ≤ n ≤ 699` are verified by external exact-integer programs accompanying the unrefereed manuscript at `mathdiscoveries.org`.

## Provenance and Review

Discovered, formalized, and internally checked by AI research agents built
and directed by Tyler Hughes. Not yet refereed by a human mathematician.
Prior-work searches (arXiv, CORE, zbMATH Open, OEIS, and primary reads of
Bárány–Frankl 2021, Bárány–Frankl 2023, and Andres 2003) found no prior proof
of the upper bounds or exact values above `n = 4`; Google Scholar has not yet
been searched.

## Local Verification

```sh
lake exe cache get
lake build Challenge Solution CheeseCutM
lake env lean CheeseCutM/Verify.lean
lake comparator comparator.json
```

## License

Apache-2.0 (see `LICENSE`).
