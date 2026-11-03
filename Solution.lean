module

public import ConjCoord

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `ConjCoord/`. The definitions used in the statements come from
`ConjCoord/Defs.lean` and are compared with the copies in `Challenge.lean`.
-/

open Finset

namespace ConjCoord

/-- The finite check: `64 ∣ tCoeff m` for `m ≤ 512` (a kernel computation). -/
theorem tCoeff_check (m : ℕ) (hm : m ≤ 512) : (64 : ℤ) ∣ tCoeff m :=
  Proof.tCoeff_check m hm

/-- The coefficients of `Φ = 4 θ(1) T`: `Φ(n) = 4 (T(n) + ∑_{k ≥ 1} 2 T(n - k²))`. -/
theorem phi_eq (n : ℕ) :
    phi n = 4 * (tCoeff n + ∑ k ∈ range n,
      2 * (if (k + 1) ^ 2 ≤ n then tCoeff (n - (k + 1) ^ 2) else 0)) :=
  Proof.phi_eq n

/-- The finite check for `Φ`: `256 ∣ Φ(n)` for `n ≤ 512`, the Sturm bound. -/
theorem phi_check (n : ℕ) (hn : n ≤ 512) : (256 : ℤ) ∣ phi n :=
  Proof.phi_check n hn

/-- Sturm's theorem modulo `2`, applied `k` times. -/
theorem sturm_iter {f : ℕ → ℤ} {B : ℕ} (S : SturmInput f B) (k : ℕ) :
    ∀ g ∈ S.M, (∀ n ≤ B, (2 : ℤ) ^ k ∣ g n) → ∀ n, (2 : ℤ) ^ k ∣ g n :=
  Proof.sturm_iter S k

/-- **Proposition 5**: `Φ ≡ 0 (mod 256)`, given the modular input. -/
theorem phi_dvd (S : SturmInput phi 512) (n : ℕ) : (256 : ℤ) ∣ phi n :=
  Proof.phi_dvd S n

/-- Inverting `θ(1)` in `ℤ[[q]]`: `F₅ ≡ 8 G θ(16) (mod 64)`, coefficientwise. -/
theorem tCoeff_dvd (S : SturmInput phi 512) (m : ℕ) : (64 : ℤ) ∣ tCoeff m :=
  Proof.tCoeff_dvd S m

/-- Lemma 3, first part: `r₃(n) = 3 r_{1,2,2}(n)` for `n ≡ 1 (mod 4)`. -/
theorem r3_eq_three_mul_reps122 {n : ℕ} (hn : n % 4 = 1) : r3 n = 3 * reps 1 2 2 n :=
  Proof.r3_eq_three_mul_reps122 hn

/-- Lemma 3: `r₃(2n) = 3 r_{1,1,2}(n)` for odd `n`. -/
theorem r3_two_mul_eq {n : ℕ} (hn : n % 2 = 1) : r3 (2 * n) = 3 * reps 1 1 2 n :=
  Proof.r3_two_mul_eq hn

/-- Lemma 3: `r_{1,1,2}(n) = 2 r_{1,2,4}(n)` for odd `n`. -/
theorem reps112_eq {n : ℕ} (hn : n % 2 = 1) : reps 1 1 2 n = 2 * reps 1 2 4 n :=
  Proof.reps112_eq hn

/-- **Lemma 3**, combinatorial part: for `p ≡ 5 (mod 16)`, `r₃(p) = 3 r_{1,2,2}(p)` and
`r₃(2p) = 6 r_{1,2,4}(p)`. With Gauss's `r₃(m) = 12 h(-4m)` these are `r_{1,2,2}(p) = 4 h(-4p)`
and `r_{1,2,4}(p) = 2 h(-8p)`. -/
theorem lemma3 {p : ℕ} (hp : p % 16 = 5) :
    r3 p = 3 * reps 1 2 2 p ∧ r3 (2 * p) = 6 * reps 1 2 4 p :=
  Proof.lemma3 hp

/-- Uniqueness of the representation of an odd prime as a sum of two squares, with the even
square second. -/
theorem two_sq_unique {p : ℤ} (hp : Prime p) (hodd : p % 2 = 1) {α β γ δ : ℤ} (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) (h1 : α ^ 2 + β ^ 2 = p) (h2 : γ ^ 2 + δ ^ 2 = p)
    (hβe : Even β) (hδe : Even δ) : α = γ ∧ β = δ :=
  Proof.two_sq_unique hp hodd hα hβ hγ hδ h1 h2 hβe hδe

/-- The coefficient of `G θ(16)` at `p`: `gCount p ≡ 4 A (mod 8)`. -/
theorem gCount_prime {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5) {a b : ℤ}
    (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    (gCount p : ℤ) ≡ 4 * octA b [ZMOD 8] :=
  Proof.gCount_prime hp h5 hab hb

/-- The congruence for representation numbers: `2 r_{1,2,4}(p) - r_{1,2,2}(p) ≡ 32 A (mod 64)`. -/
theorem reps_congruence (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    2 * (reps 1 2 4 p : ℤ) - reps 1 2 2 p ≡ 32 * octA b [ZMOD 64] :=
  Proof.reps_congruence S hp h5 hab hb

/-- The congruence for sums of three squares: `r₃(2p) - r₃(p) ≡ 96 A (mod 192)`. -/
theorem r3_congruence (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    (r3 (2 * p) : ℤ) - r3 p ≡ 96 * octA b [ZMOD 192] :=
  Proof.r3_congruence S hp h5 hab hb

/-- **Theorem 1.** For a prime `p ≡ 5 (mod 16)`, `p = a² + b²` with `b` even, and `h = h(-4p)`,
`h' = h(-8p)` given through Gauss's `r₃(p) = 12 h(-4p)` and `r₃(2p) = 12 h(-8p)`:
`h(-8p) ≡ h(-4p) + 8 A (mod 16)`. -/
theorem class_number_congruence (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime)
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') :
    (h' : ℤ) ≡ h + 8 * octA b [ZMOD 16] :=
  Proof.class_number_congruence S hp h5 hab hb hG hG'

/-- **Corollary 2 (Conjecture 5.3 of Paper V).** If `V` is equivalent to
`h(-8p) - h(-4p) ≡ 8·[p ≡ 5 (mod 32)] (mod 16)` (Paper V, Theorem 5.2(iv), for
`V = (v_λ(u₁) ≥ 2)`), then `V` holds exactly when one and only one of `b ≡ ±6 (mod 16)` and
`p ≡ 21 (mod 32)` holds. -/
theorem conjecture_coord (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (V : Prop)
    (hV : V ↔ (h' : ℤ) - h ≡ 8 * (if p % 32 = 5 then 1 else 0) [ZMOD 16]) :
    V ↔ ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) :=
  Proof.conjecture_coord S hp h5 hab hb hG hG' V hV

/-- **Corollary 6 (the octant sum).** With Berndt's formula
`∑_{0<x<p/8} (x/p) = (h(-8p) - h(-4p))/4` for `p ≡ 5 (mod 8)` as a hypothesis,
`∑_{0<x<p/8} (x/p) ≡ 2 A (mod 4)`. -/
theorem octant_sum (S : SturmInput phi 512) {p : ℕ} [Fact p.Prime] (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h')
    (hBerndt : 4 * ∑ x ∈ Icc 1 (p / 8), legendreSym p x = (h' : ℤ) - h) :
    ∑ x ∈ Icc 1 (p / 8), legendreSym p x ≡ 2 * octA b [ZMOD 4] :=
  Proof.octant_sum S h5 hab hb hG hG' hBerndt

/-- **Corollary 6, second form**: the number of quadratic nonresidues in `(0, p/8)` is
`≡ (p - 5)/16 + A (mod 2)`. -/
theorem octant_nonresidues (S : SturmInput phi 512) {p : ℕ} [Fact p.Prime]
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h')
    (hBerndt : 4 * ∑ x ∈ Icc 1 (p / 8), legendreSym p x = (h' : ℤ) - h) :
    (((Icc 1 (p / 8)).filter fun x : ℕ => legendreSym p (x : ℤ) = -1).card : ℤ) ≡
      ((p - 5) / 16 : ℕ) + octA b [ZMOD 2] :=
  Proof.octant_nonresidues S h5 hab hb hG hG' hBerndt

/-- **Corollary 7 (with Desnoux).** Desnoux's Theorem B, §6, for `p ≡ 5 (mod 8)`,
`h(-4p) - c₂ R (S/2) h⁺(p) + h(-8p) - 17 R' (S'/2) h⁺(2p) ≡ 32·[p ≡ 5, 29 (mod 32)] (mod 64)`,
taken as a hypothesis, gives
`c₂ R (S/2) h⁺(p) + 17 R' (S'/2) h⁺(2p) ≡ 2 h(-4p) + 8 A (mod 16)`. -/
theorem desnoux_corollary (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (c₂ R S₀ R' S₀' hplus hplus2 : ℤ)
    (hD : (h : ℤ) - c₂ * R * (S₀ / 2) * hplus + h' - 17 * R' * (S₀' / 2) * hplus2 ≡
      32 * (if p % 32 = 5 ∨ p % 32 = 29 then 1 else 0) [ZMOD 64]) :
    c₂ * R * (S₀ / 2) * hplus + 17 * R' * (S₀' / 2) * hplus2 ≡ 2 * h + 8 * octA b [ZMOD 16] :=
  Proof.desnoux_corollary S hp h5 hab hb hG hG' c₂ R S₀ R' S₀' hplus hplus2 hD

end ConjCoord
