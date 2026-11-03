module

public import Mathlib

@[expose] public section

/-!
# Definitions

Representation numbers of diagonal ternary forms, the sieved coefficient `tCoeff`, the weight-two
coefficient `phi`, the indicator `octA`, and the package `SturmInput` for the two modular inputs
of the proof (the Serre–Stark modularity of `Φ` and Sturm's theorem).
-/

open Finset

namespace ConjCoord

/-- The box `[-n, n]³` in `ℤ³`. Every representation of `n` by a positive diagonal form lies in
it. -/
def box3 (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  Icc (-(n : ℤ)) n ×ˢ (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n)

/-- `r_{a,b,c}(n)`: the number of `(x, y, z) ∈ ℤ³` with `a x² + b y² + c z² = n`. -/
def reps (a b c n : ℕ) : ℕ :=
  ((box3 n).filter fun v => (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n).card

/-- `r₃(n)`: the number of representations of `n` as a sum of three squares. -/
def r3 (n : ℕ) : ℕ := reps 1 1 1 n

/-- The coefficient of `q^m` in `G θ(16)`, where `G = ∑ q^{α² + β²}` over `α² + β² ≡ 5 (mod 16)`
and `β ≡ ±6 (mod 16)`: the number of `(α, β, k)` with `α² + β² + 16 k² = m` and these
conditions. -/
def gCount (m : ℕ) : ℕ :=
  ((box3 m).filter fun v => v.1 ^ 2 + v.2.1 ^ 2 + 16 * v.2.2 ^ 2 = (m : ℤ) ∧
    (v.1 ^ 2 + v.2.1 ^ 2) % 16 = 5 ∧ (v.2.1 % 16 = 6 ∨ v.2.1 % 16 = 10)).card

/-- The coefficient of `q^m` in `F₅ - 8 G θ(16)`, where `F₅ = 2 F₁₂₄ - F₁₂₂` and `F₁₂₄`, `F₁₂₂`
are the parts of the theta series of `x² + 2y² + 4z²` and `x² + 2y² + 2z²` supported on
`m ≡ 5 (mod 16)`. -/
def tCoeff (m : ℕ) : ℤ :=
  if m % 16 = 5 then 2 * (reps 1 2 4 m : ℤ) - reps 1 2 2 m - 8 * gCount m else 0

/-- The coefficient of `q^n` in `Φ = 4 θ(1) (F₅ - 8 G θ(16))`, with `θ(1) = ∑_{w ∈ ℤ} q^{w²}`. -/
def phi (n : ℕ) : ℤ :=
  4 * ∑ w ∈ Icc (-(n : ℤ)) n, if w ^ 2 ≤ n then tCoeff (n - (w ^ 2).toNat) else 0

/-- `A = 1` if `b ≡ ±6 (mod 16)`, and `0` otherwise. -/
def octA (b : ℤ) : ℤ := if b % 16 = 6 ∨ b % 16 = 10 then 1 else 0

/-- The modular input of the proof, for a sequence `f` (the `q`-expansion of `Φ`) and a Sturm
bound `B`: a set `M` of integer `q`-expansions (those of the weight-two forms on
`Γ' = Γ₀(1024) ∩ ker χ₈` with integer coefficients) that contains `f` (Serre–Stark), is closed
under division by `2` when every coefficient is even (it comes from a complex vector space), and
satisfies Sturm's theorem modulo `2` with bound `B` (for `Γ'`, `B = 2 · 3072 / 12 = 512`). -/
structure SturmInput (f : ℕ → ℤ) (B : ℕ) where
  /-- The integer `q`-expansions of the modular forms in the space. -/
  M : Set (ℕ → ℤ)
  /-- `f` lies in the space (Serre–Stark). -/
  mem : f ∈ M
  /-- Dividing a form with even coefficients by `2` stays in the space. -/
  half_mem : ∀ g ∈ M, (∀ n, 2 ∣ g n) → (fun n => g n / 2) ∈ M
  /-- Sturm's theorem modulo `2`. -/
  sturm : ∀ g ∈ M, (∀ n ≤ B, 2 ∣ g n) → ∀ n, 2 ∣ g n

end ConjCoord
