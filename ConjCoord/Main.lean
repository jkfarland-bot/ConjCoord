module

public import ConjCoord.Compute
public import ConjCoord.TwoSquares

@[expose] public section

/-!
# The congruence `h(-8p) ≡ h(-4p) + 8A (mod 16)` and its corollaries

`sturm_iter` runs Sturm's theorem eight times; with the finite check `tCoeff_check` it gives
`256 ∣ Φ` (Proposition 5). Inverting `θ(1)` gives `64 ∣ tCoeff m` for all `m`, and at a prime
`p ≡ 5 (mod 16)` this is `2 r_{1,2,4}(p) - r_{1,2,2}(p) ≡ 32 A (mod 64)` (`reps_congruence`).
Gauss's theorem turns it into the class number congruence (`class_number_congruence`), which
gives Conjecture 5.3 of Paper V (`conjecture_coord`), the octant sum (`octant_sum`,
`octant_nonresidues`) and the combination with Desnoux (`desnoux_halves_exact`,
`desnoux_corollary`).
-/

open Finset

namespace ConjCoord.Proof

/-- Sturm's theorem applied `k` times. -/
theorem sturm_iter {f : ℕ → ℤ} {B : ℕ} (S : SturmInput f B) (k : ℕ) :
    ∀ g ∈ S.M, (∀ n ≤ B, (2 : ℤ) ^ k ∣ g n) → ∀ n, (2 : ℤ) ^ k ∣ g n := by
  induction k with
  | zero => intro g _ _ n; simp
  | succ k ih =>
    intro g hg hB n
    have h2 : ∀ n, (2 : ℤ) ∣ g n := S.sturm g hg fun n hn =>
      (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hB n hn)
    have hg' := S.half_mem g hg h2
    have hB' : ∀ n ≤ B, (2 : ℤ) ^ k ∣ (fun n => g n / 2) n := by
      intro n hn
      obtain ⟨c, hc⟩ := hB n hn
      refine ⟨c, ?_⟩
      simp only [hc, pow_succ]
      rw [mul_comm ((2 : ℤ) ^ k) 2, mul_assoc, Int.mul_ediv_cancel_left _ two_ne_zero]
    obtain ⟨c, hc⟩ := ih _ hg' hB' n
    obtain ⟨d, hd⟩ := h2 n
    refine ⟨c, ?_⟩
    rw [hd, Int.mul_ediv_cancel_left _ two_ne_zero] at hc
    rw [hd, hc, pow_succ]; ring

/-- `Φ = 4 θ(1) T` with `T = F₅ - 8 G θ(16)`, coefficientwise:
`Φ(n) = 4 (T(n) + ∑_{1 ≤ k} 2 T(n - k²))`. -/
theorem phi_eq (n : ℕ) :
    phi n = 4 * (tCoeff n + ∑ k ∈ range n,
      2 * (if (k + 1) ^ 2 ≤ n then tCoeff (n - (k + 1) ^ 2) else 0)) := by
  unfold phi
  set F : ℕ → ℤ := fun k => if k ^ 2 ≤ n then tCoeff (n - k ^ 2) else 0 with hF
  have hw : ∀ w : ℤ, (if w ^ 2 ≤ (n : ℤ) then tCoeff (n - (w ^ 2).toNat) else 0) = F w.natAbs := by
    intro w
    have hc : w ^ 2 = ((w.natAbs ^ 2 : ℕ) : ℤ) := by push_cast; exact (sq_abs w).symm
    simp only [hF, hc, Int.toNat_natCast, Nat.cast_le]
  simp_rw [hw]
  rw [sum_Icc_natAbs n F, sum_range_succ']
  simp only [wt, Nat.add_one_ne_zero, ite_false, ite_true, one_smul, hF, zero_pow two_ne_zero,
    zero_le, Nat.sub_zero, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma phi_dvd_of {n : ℕ} (h : ∀ m ≤ n, (64 : ℤ) ∣ tCoeff m) : (256 : ℤ) ∣ phi n := by
  rw [phi_eq]
  have h1 : (128 : ℤ) ∣ ∑ k ∈ range n, 2 * (if (k + 1) ^ 2 ≤ n then tCoeff (n - (k + 1) ^ 2) else 0) := by
    refine dvd_sum fun k _ => ?_
    split_ifs
    · obtain ⟨c, hc⟩ := h (n - (k + 1) ^ 2) (Nat.sub_le _ _)
      exact ⟨c, by rw [hc]; ring⟩
    · simp
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h n le_rfl
  exact ⟨d + 2 * c, by rw [hc, hd]; ring⟩

/-- The finite check for `Φ`: `256 ∣ Φ(n)` for `n ≤ 512`. -/
theorem phi_check (n : ℕ) (hn : n ≤ 512) : (256 : ℤ) ∣ phi n :=
  phi_dvd_of fun m hm => tCoeff_check m (hm.trans hn)

/-- **Proposition 5**: `Φ ≡ 0 (mod 256)`, from the modular input. -/
theorem phi_dvd (S : SturmInput phi 512) (n : ℕ) : (256 : ℤ) ∣ phi n := by
  have := sturm_iter S 8 phi S.mem (fun n hn => by norm_num; exact phi_check n hn) n
  norm_num at this; exact this

/-- Inverting `θ(1)`: `64 ∣ T(m)` for all `m`. -/
theorem tCoeff_dvd (S : SturmInput phi 512) (m : ℕ) : (64 : ℤ) ∣ tCoeff m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hphi := phi_dvd S m
    rw [phi_eq] at hphi
    have h1 : (128 : ℤ) ∣ ∑ k ∈ range m,
        2 * (if (k + 1) ^ 2 ≤ m then tCoeff (m - (k + 1) ^ 2) else 0) := by
      refine dvd_sum fun k _ => ?_
      split_ifs with hk
      · obtain ⟨c, hc⟩ := ih (m - (k + 1) ^ 2) (by
          have : 0 < (k + 1) ^ 2 := by positivity
          omega)
        exact ⟨c, by rw [hc]; ring⟩
      · simp
    obtain ⟨c, hc⟩ := h1
    obtain ⟨d, hd⟩ := hphi
    rw [hc] at hd
    exact ⟨d - 2 * c, by linarith⟩

/-- **The congruence for representation numbers**: for a prime `p ≡ 5 (mod 16)` with
`p = a² + b²`, `b` even, `2 r_{1,2,4}(p) - r_{1,2,2}(p) ≡ 32 A (mod 64)`. -/
theorem reps_congruence (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    2 * (reps 1 2 4 p : ℤ) - reps 1 2 2 p ≡ 32 * octA b [ZMOD 64] := by
  have hT := tCoeff_dvd S p
  have hG := gCount_prime hp h5 hab hb
  unfold tCoeff at hT
  rw [ite_eq_left h5] at hT
  unfold Int.ModEq at *
  omega

/-- The same congruence for sums of three squares: `r₃(2p) - r₃(p) ≡ 96 A (mod 192)`. -/
theorem r3_congruence (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    (r3 (2 * p) : ℤ) - r3 p ≡ 96 * octA b [ZMOD 192] := by
  have h := reps_congruence S hp h5 hab hb
  obtain ⟨h1, h2⟩ := lemma3 h5
  have e1 : (r3 p : ℤ) = 3 * reps 1 2 2 p := by exact_mod_cast h1
  have e2 : (r3 (2 * p) : ℤ) = 6 * reps 1 2 4 p := by exact_mod_cast h2
  rw [e1, e2]
  unfold Int.ModEq at *
  omega

/-- **Theorem 1.** For a prime `p ≡ 5 (mod 16)`, `p = a² + b²` with `b` even, and `h = h(-4p)`,
`h' = h(-8p)` given by Gauss's `r₃(p) = 12 h(-4p)` and `r₃(2p) = 12 h(-8p)`:
`h(-8p) ≡ h(-4p) + 8 A (mod 16)`. -/
theorem class_number_congruence (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime)
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') :
    (h' : ℤ) ≡ h + 8 * octA b [ZMOD 16] := by
  have hc := reps_congruence S hp h5 hab hb
  obtain ⟨h1, h2⟩ := lemma3 h5
  have e1 : (reps 1 2 2 p : ℤ) = 4 * h := by
    have : reps 1 2 2 p = 4 * h := by omega
    exact_mod_cast this
  have e2 : (reps 1 2 4 p : ℤ) = 2 * h' := by
    have : reps 1 2 4 p = 2 * h' := by omega
    exact_mod_cast this
  rw [e1, e2] at hc
  unfold Int.ModEq at *
  omega

/-- **Corollary 2 (Conjecture 5.3 of Paper V).** If `V` is equivalent to
`h(-8p) - h(-4p) ≡ 8·[p ≡ 5 (mod 32)] (mod 16)` (Paper V, Theorem 5.2(iv), for
`V = (v_λ(u₁) ≥ 2)`), then `V` holds exactly when one and only one of `b ≡ ±6 (mod 16)` and
`p ≡ 21 (mod 32)` holds. -/
theorem conjecture_coord (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (V : Prop)
    (hV : V ↔ (h' : ℤ) - h ≡ 8 * (if p % 32 = 5 then 1 else 0) [ZMOD 16]) :
    V ↔ ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) := by
  have hc := class_number_congruence S hp h5 hab hb hG hG'
  rw [hV]
  unfold Int.ModEq at *
  unfold octA at hc
  have h32 : p % 32 = 5 ∨ p % 32 = 21 := by omega
  by_cases hA : b % 16 = 6 ∨ b % 16 = 10
  · rw [ite_eq_left hA] at hc
    rcases h32 with h32 | h32
    · rw [ite_eq_left h32]
      have e : ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) ↔ True := by
        rw [iff_true]; constructor <;> intro <;> omega
      rw [e, iff_true]; omega
    · rw [ite_eq_right (by omega)]
      have e : ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) ↔ False := by
        rw [iff_false]; intro h; exact (h.mp hA) h32
      rw [e, iff_false]; omega
  · rw [ite_eq_right hA] at hc
    rcases h32 with h32 | h32
    · rw [ite_eq_left h32]
      have e : ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) ↔ False := by
        rw [iff_false]; intro h; exact hA (h.mpr (by omega))
      rw [e, iff_false]; omega
    · rw [ite_eq_right (by omega)]
      have e : ((b % 16 = 6 ∨ b % 16 = 10) ↔ ¬ p % 32 = 21) ↔ True := by
        rw [iff_true]; constructor
        · intro h; exact absurd h hA
        · intro h; exact absurd h32 h
      rw [e, iff_true]; omega

/-- **Corollary 6 (the octant sum).** With Berndt's formula
`∑_{0<x<p/8} (x/p) = (h(-8p) - h(-4p))/4` for `p ≡ 5 (mod 8)` as a hypothesis,
`∑_{0<x<p/8} (x/p) ≡ 2 A (mod 4)`. -/
theorem octant_sum (S : SturmInput phi 512) {p : ℕ} [hpF : Fact p.Prime] (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h')
    (hBerndt : 4 * ∑ x ∈ Icc 1 (p / 8), legendreSym p x = (h' : ℤ) - h) :
    ∑ x ∈ Icc 1 (p / 8), legendreSym p x ≡ 2 * octA b [ZMOD 4] := by
  have hc := class_number_congruence S hpF.out h5 hab hb hG hG'
  unfold Int.ModEq at *
  omega

/-- **Corollary 6, second form**: the number of quadratic nonresidues in `(0, p/8)` is
`≡ (p - 5)/16 + A (mod 2)`. -/
theorem octant_nonresidues (S : SturmInput phi 512) {p : ℕ} [hpF : Fact p.Prime]
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h')
    (hBerndt : 4 * ∑ x ∈ Icc 1 (p / 8), legendreSym p x = (h' : ℤ) - h) :
    (((Icc 1 (p / 8)).filter fun x : ℕ => legendreSym p (x : ℤ) = -1).card : ℤ) ≡
      ((p - 5) / 16 : ℕ) + octA b [ZMOD 2] := by
  have hs := octant_sum S h5 hab hb hG hG' hBerndt
  have hval : ∀ x ∈ Icc 1 (p / 8), legendreSym p (x : ℤ) =
      1 - 2 * (if legendreSym p (x : ℤ) = -1 then 1 else 0) := by
    intro x hx
    rw [mem_Icc] at hx
    have hx0 : ((x : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hd
      have : (p : ℤ) ≤ x := Int.le_of_dvd (by omega) hd
      have : p / 8 < p := Nat.div_lt_self hpF.out.pos (by norm_num)
      omega
    rcases legendreSym.eq_one_or_neg_one p hx0 with h1 | h1 <;> simp [h1]
  rw [sum_congr rfl hval, sum_sub_distrib, ← mul_sum, sum_boole] at hs
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel] at hs
  unfold Int.ModEq at *
  have : ((p / 8 : ℕ) : ℤ) = 2 * (((p - 5) / 16 : ℕ) : ℤ) := by omega
  rw [nsmul_eq_mul, mul_one] at hs
  omega

/-- The Pell equation `R² - p S² = 1` with `p ≡ 5 (mod 8)` forces `S` to be even: if `S` were odd,
then `R² ≡ 1 + p ≡ 6 (mod 8)`. -/
theorem pell_even {p : ℕ} (h5 : p % 16 = 5) {R S : ℤ} (hP : R ^ 2 - (p : ℤ) * S ^ 2 = 1) :
    Even S := by
  by_contra hS
  rw [Int.not_even_iff_odd] at hS
  obtain ⟨k, rfl⟩ := hS
  have hp : (p : ℤ) = 8 * ((p / 8 : ℕ) : ℤ) + 5 := by omega
  have := congrArg (Int.cast : ℤ → ZMod 8) hP
  rw [hp] at this
  push_cast at this
  have h8 : (8 : ZMod 8) = 0 := by decide
  rw [h8, zero_mul, zero_add] at this
  generalize (R : ZMod 8) = x at this
  generalize (k : ZMod 8) = y at this
  revert x y this
  decide

/-- The Pell equation `R'² - 2p S'² = 1` with `p ≡ 5 (mod 8)` forces `S'` to be even: if `S'` were
odd, then `R'² ≡ 1 + 2p ≡ 3 (mod 8)`. -/
theorem pell2_even {p : ℕ} (h5 : p % 16 = 5) {R S : ℤ}
    (hP : R ^ 2 - 2 * (p : ℤ) * S ^ 2 = 1) : Even S := by
  by_contra hS
  rw [Int.not_even_iff_odd] at hS
  obtain ⟨k, rfl⟩ := hS
  have hp : (p : ℤ) = 8 * ((p / 8 : ℕ) : ℤ) + 5 := by omega
  have := congrArg (Int.cast : ℤ → ZMod 8) hP
  rw [hp] at this
  push_cast at this
  have h8 : (8 : ZMod 8) = 0 := by decide
  rw [h8, zero_mul, zero_add] at this
  generalize (R : ZMod 8) = x at this
  generalize (k : ZMod 8) = y at this
  revert x y this
  decide

/-- **The halves in Desnoux's formula are exact.** For `p ≡ 5 (mod 16)`, any solutions of
`R² - p S₀² = 1` and `R'² - 2p S₀'² = 1` have `S₀` and `S₀'` even, so the integer quotients `S₀ / 2`
and `S₀' / 2` are the halves `S/2` and `S'/2` of Desnoux's Theorem B. -/
theorem desnoux_halves_exact {p : ℕ} (h5 : p % 16 = 5) {R S₀ R' S₀' : ℤ}
    (hPell : R ^ 2 - (p : ℤ) * S₀ ^ 2 = 1) (hPell' : R' ^ 2 - 2 * (p : ℤ) * S₀' ^ 2 = 1) :
    2 * (S₀ / 2) = S₀ ∧ 2 * (S₀' / 2) = S₀' :=
  ⟨Int.mul_ediv_cancel' (even_iff_two_dvd.1 (pell_even h5 hPell)),
    Int.mul_ediv_cancel' (even_iff_two_dvd.1 (pell2_even h5 hPell'))⟩

/-- **Corollary 7 (with Desnoux).** Let `(R, S₀)` and `(R', S₀')` solve the Pell equations
`R² - p S₀² = 1` and `R'² - 2p S₀'² = 1` (Desnoux takes the least positive solutions; the corollary
holds for any). The integer quotients `S₀ / 2` and `S₀' / 2` are then the exact halves `S/2` and
`S'/2` (first two conjuncts, from `desnoux_halves_exact`), so the hypothesis `hD` is Desnoux's
Theorem B, §6, for `p ≡ 5 (mod 8)`,
`h(-4p) - c₂ R (S/2) h⁺(p) + h(-8p) - 17 R' (S'/2) h⁺(2p) ≡ 32·[p ≡ 5, 29 (mod 32)] (mod 64)`,
and the conclusion is
`c₂ R (S/2) h⁺(p) + 17 R' (S'/2) h⁺(2p) ≡ 2 h(-4p) + 8 A (mod 16)`. -/
theorem desnoux_corollary (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') (c₂ R S₀ R' S₀' hplus hplus2 : ℤ)
    (hPell : R ^ 2 - (p : ℤ) * S₀ ^ 2 = 1) (hPell' : R' ^ 2 - 2 * (p : ℤ) * S₀' ^ 2 = 1)
    (hD : (h : ℤ) - c₂ * R * (S₀ / 2) * hplus + h' - 17 * R' * (S₀' / 2) * hplus2 ≡
      32 * (if p % 32 = 5 ∨ p % 32 = 29 then 1 else 0) [ZMOD 64]) :
    2 * (S₀ / 2) = S₀ ∧ 2 * (S₀' / 2) = S₀' ∧
      c₂ * R * (S₀ / 2) * hplus + 17 * R' * (S₀' / 2) * hplus2 ≡ 2 * h + 8 * octA b [ZMOD 16] := by
  refine ⟨(desnoux_halves_exact h5 hPell hPell').1, (desnoux_halves_exact h5 hPell hPell').2, ?_⟩
  have hc := class_number_congruence S hp h5 hab hb hG hG'
  unfold Int.ModEq at *
  split_ifs at hD <;> omega

end ConjCoord.Proof
