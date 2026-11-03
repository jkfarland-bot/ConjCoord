# ConjCoord

Lean 4 / Mathlib formalization of the proof of Conjecture coord (Conjecture 5.3) of Paper V of the
K Project series. The proof goes through a new class number congruence: for every prime
`p ≡ 5 (mod 16)`, written `p = a² + b²` with `b` even,

```
h(-8p) ≡ h(-4p) + 8·[b ≡ ±6 (mod 16)]   (mod 16).
```

Companion note: J. S. Farland, *The first derivative bit at p ≡ 5 (mod 16): a proof of Conjecture
coord of Paper V* (draft, 2 November 2026).

## What is proved

- **The finite check** (`tCoeff_check`, `phi_check`): every coefficient of
  `Φ = 4 θ(1)(F₅ - 8 G θ(16))` up to `q^512`, the Sturm bound, is divisible by `256`. This is a
  kernel computation (`decide +kernel`, no `native_decide`). `count_eq_cntL` proves that the
  fast count used by the computation, over `0 ≤ x, y ≤ √n` with an integer square root for `z`,
  equals the count over the box `[-n, n]³` in the definitions.
- **Proposition 5** (`phi_dvd`): `Φ ≡ 0 (mod 256)`, by running Sturm's theorem modulo `2` eight
  times (`sturm_iter`), dividing by `2` at each step.
- **Inverting `θ(1)`** (`tCoeff_dvd`): `F₅ ≡ 8 G θ(16) (mod 64)`, coefficientwise, by strong
  induction (`phi_eq` writes `Φ(n) = 4(T(n) + ∑_{k≥1} 2 T(n - k²))`).
- **Lemma 3** (`lemma3`, with `r3_eq_three_mul_reps122`, `r3_two_mul_eq`, `reps112_eq`):
  `r₃(p) = 3 r_{1,2,2}(p)` and `r₃(2p) = 6 r_{1,2,4}(p)`. These are explicit bijections,
  together with the count of which coordinate is odd.
- **The coefficient of `G θ(16)` at `p`** (`gCount_prime`): `≡ 4A (mod 8)`. The sign changes act
  without fixed points, and the representation of `p` as a sum of two squares is unique
  (`two_sq_unique`).
- **Theorem 1**:
  - `reps_congruence`: `2 r_{1,2,4}(p) - r_{1,2,2}(p) ≡ 32A (mod 64)`.
  - `r3_congruence`: `r₃(2p) - r₃(p) ≡ 96A (mod 192)`.
  - `class_number_congruence`: `h(-8p) ≡ h(-4p) + 8A (mod 16)`.
- **Corollary 2** (`conjecture_coord`): Conjecture 5.3 of Paper V, given Paper V's
  Theorem 5.2(iv).
- **Corollary 6** (`octant_sum`, `octant_nonresidues`):
  - `∑_{0<x<p/8} (x/p) ≡ 2A (mod 4)`;
  - the number of nonresidues in `(0, p/8)` is `≡ (p-5)/16 + A (mod 2)`.
- **Corollary 7** (`desnoux_corollary`): combined with Desnoux's Theorem B,
  `c₂R(S/2)h⁺(p) + 17R′(S′/2)h⁺(2p) ≡ 2h(-4p) + 8A (mod 16)`.

Here `A = octA b = [b ≡ ±6 (mod 16)]`.

## What is assumed

Mathlib has no half-integral weight modular forms, no Serre–Stark theorem, no Sturm bound and no
three-square class number formula. These inputs are hypotheses in the statements:

- **The modular input** `SturmInput phi 512`: a set `M` of integer `q`-expansions containing
  `phi`, closed under division by `2` when all coefficients are even, and satisfying Sturm's
  theorem modulo `2` with bound `512`. In the note:
  - `M` is the set of integer `q`-expansions of `M₂(Γ')`, `Γ' = Γ₀(1024) ∩ ker χ₈`, of index
    `3072`;
  - membership of `Φ` is Proposition 4 (Serre–Stark);
  - the bound is `2 · 3072 / 12 = 512` (Sturm, Theorem 1).
- **Gauss's theorem** `r₃(m) = 12 h(-4m)` for squarefree `m ≡ 1, 2 (mod 4)`. It enters as
  `r3 p = 12 * h` and `r3 (2 * p) = 12 * h'`, so `h` and `h'` are natural numbers characterized by
  it rather than Mathlib's `NumberField.classNumber`.
- **For the corollaries:**
  - Paper V, Theorem 5.2(iv), as the equivalence `hV`;
  - Berndt's formula (7.3) for the octant sum, as `hBerndt`;
  - Desnoux's Theorem B (§6), as `hD`.

The rest is formalized, including the passage from the finite check to all coefficients, the
inversion of `θ(1)`, the bijections of Lemma 3, and the uniqueness argument at `p`.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

```
lake exe cache get
lake build
scripts/verify-comparator.sh
```

There is no `sorry` and no `native_decide`. Every result depends only on `propext`,
`Classical.choice` and `Quot.sound`. Comparator accepts `Solution` against `Challenge` under the
Lean, NanoDa and con-ron kernels, including the replay of the finite check. The structure
`SturmInput` is compared as well: a modified copy in `Challenge.lean` is rejected.

## Layout

- `ConjCoord/Defs.lean`: the definitions.
  - `box3`, `reps`, `r3`, `gCount`, `tCoeff`, `phi`, `octA`;
  - the structure `SturmInput`.
- `ConjCoord/Compute.lean`: the fast count `cntL`, its identification with the box count, and the
  finite check.
- `ConjCoord/Reps.lean`: Lemma 3.
- `ConjCoord/TwoSquares.lean`: `gCount p ≡ 4A (mod 8)`, with the uniqueness of `p = a² + b²`.
- `ConjCoord/Main.lean`: Sturm iteration, Proposition 5, Theorem 1, Corollaries 2, 6 and 7.
- `Challenge.lean` / `Solution.lean` / `comparator.json`: the Palomar statement surface.
