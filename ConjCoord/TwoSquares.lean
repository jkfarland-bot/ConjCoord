module

public import ConjCoord.Reps

@[expose] public section

/-!
# The coefficient of `G θ(16)` at `p`

For `m ≡ 5 (mod 16)` the maps `α ↦ -α`, `β ↦ -β`, `k ↦ -k` act without fixed points on the
triples counted by `gCount m` with `k ≠ 0`, so their number is divisible by `8`. At a prime
`p = a² + b²` with `b` even, the triples with `k = 0` are `(±a, ±b, 0)` when `b ≡ ±6 (mod 16)`,
and there are none otherwise (uniqueness of the representation as a sum of two squares). So
`gCount p ≡ 4 A (mod 8)`.
-/

open Finset

namespace ConjCoord.Proof

lemma sq_mod16_ne5 (x : ℤ) : x ^ 2 % 16 ≠ 5 := by
  have h := Int.emod_add_mul_ediv x 16
  have h0 : 0 ≤ x % 16 := Int.emod_nonneg x (by norm_num)
  have h1 : x % 16 < 16 := Int.emod_lt_of_pos x (by norm_num)
  generalize x % 16 = r at h h0 h1
  generalize x / 16 = q at h
  subst h
  interval_cases r <;> ring_nf <;> omega

/-- Uniqueness of the representation of an odd prime as a sum of two squares, with the even
square second. -/
lemma two_sq_unique {p : ℤ} (hp : Prime p) (hodd : p % 2 = 1) {α β γ δ : ℤ} (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) (h1 : α ^ 2 + β ^ 2 = p) (h2 : γ ^ 2 + δ ^ 2 = p)
    (hβe : Even β) (hδe : Even δ) : α = γ ∧ β = δ := by
  subst h1
  set p := α ^ 2 + β ^ 2 with hpdef
  have hp0 : 0 < p := by positivity
  have key : p ∣ (α * δ - β * γ) * (α * δ + β * γ) :=
    ⟨α ^ 2 + δ ^ 2 - p, by linear_combination (-β ^ 2) * h2⟩
  have hαδ : α * δ < p := by nlinarith [sq_nonneg (α - δ)]
  have hβγ : β * γ < p := by nlinarith [sq_nonneg (β - γ)]
  have pos1 : 0 < α * δ := mul_pos hα hδ
  have pos2 : 0 < β * γ := mul_pos hβ hγ
  rcases hp.dvd_or_dvd key with hd | hd
  · have e : α * δ - β * γ = 0 :=
      Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    have e2 : p * (β ^ 2 - δ ^ 2) = 0 := by
      linear_combination (-(α * δ + β * γ)) * e + (-β ^ 2) * h2
    have e3 : β ^ 2 - δ ^ 2 = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · omega
      · exact h
    have hbd : β = δ := by nlinarith [sq_nonneg (β - δ), sq_nonneg (β + δ)]
    subst hbd
    refine ⟨?_, rfl⟩
    have : α ^ 2 = γ ^ 2 := by linarith
    nlinarith [sq_nonneg (α - γ), sq_nonneg (α + γ)]
  · obtain ⟨k, hk⟩ := hd
    have hk1 : k = 1 := by
      have : 0 < k := by
        by_contra hc; push Not at hc; nlinarith
      have : k < 2 := by
        by_contra hc; push Not at hc; nlinarith
      omega
    subst hk1
    have hsum : (α * γ - β * δ) ^ 2 + (α * δ + β * γ) ^ 2 = p * p := by
      linear_combination (α ^ 2 + β ^ 2) * h2
    have e : (α * γ - β * δ) ^ 2 = 0 := by rw [hk] at hsum; linarith
    have e' : α * γ - β * δ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e
    have e2 : p * (β ^ 2 - γ ^ 2) = 0 := by
      linear_combination (-(α * γ + β * δ)) * e' + (-β ^ 2) * h2
    have e3 : β ^ 2 - γ ^ 2 = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · omega
      · exact h
    have hbg : γ = β := by nlinarith [sq_nonneg (γ - β), sq_nonneg (γ + β)]
    subst hbg
    have hda : δ = α := by
      have : δ ^ 2 = α ^ 2 := by linarith
      nlinarith [sq_nonneg (δ - α), sq_nonneg (δ + α)]
    subst hda
    obtain ⟨s, hs⟩ := hδe
    obtain ⟨t, ht⟩ := hβe
    exfalso
    have : p = 4 * (s ^ 2 + t ^ 2) := by rw [hpdef, hs, ht]; ring
    omega

/-- The set counted by `gCount m`. -/
def gset (m : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (box3 m).filter fun v => v.1 ^ 2 + v.2.1 ^ 2 + 16 * v.2.2 ^ 2 = (m : ℤ) ∧
    (v.1 ^ 2 + v.2.1 ^ 2) % 16 = 5 ∧ (v.2.1 % 16 = 6 ∨ v.2.1 % 16 = 10)

lemma gCount_eq_card (m : ℕ) : gCount m = (gset m).card := rfl

lemma mem_gset {m : ℕ} (v : ℤ × ℤ × ℤ) :
    v ∈ gset m ↔ v.1 ^ 2 + v.2.1 ^ 2 + 16 * v.2.2 ^ 2 = (m : ℤ) ∧
      (v.1 ^ 2 + v.2.1 ^ 2) % 16 = 5 ∧ (v.2.1 % 16 = 6 ∨ v.2.1 % 16 = 10) := by
  unfold gset box3
  rw [mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have e1 := sq_nonneg v.1
  have e2 := sq_nonneg v.2.1
  have e3 := sq_nonneg v.2.2
  exact mem_product.mpr ⟨mem_Icc_of_sq_le (by linarith), mem_product.mpr
    ⟨mem_Icc_of_sq_le (by linarith), mem_Icc_of_sq_le (by linarith)⟩⟩

lemma neg_cond (β : ℤ) : ((-β) % 16 = 6 ∨ (-β) % 16 = 10) ↔ (β % 16 = 6 ∨ β % 16 = 10) := by
  omega

/-- The triples with `k ≠ 0` come in groups of `8`. -/
lemma eight_dvd_card_k_ne {m : ℕ} :
    8 ∣ ((gset m).filter fun v => ¬ v.2.2 = 0).card := by
  set S1 := (gset m).filter fun v => ¬ v.2.2 = 0
  have hS1 : ∀ v ∈ S1, v ∈ gset m ∧ ¬ v.2.2 = 0 := fun v hv => mem_filter.mp hv
  rw [card_eq_two_mul_filter S1 (fun v => (v.1, v.2.1, -v.2.2)) (fun v => 0 < v.2.2) ?_ ?_ ?_]
  · set S2 := S1.filter fun v => 0 < v.2.2
    have hS2 : ∀ v ∈ S2, v ∈ gset m ∧ 0 < v.2.2 := fun v hv =>
      ⟨(hS1 v (mem_filter.mp hv).1).1, (mem_filter.mp hv).2⟩
    rw [card_eq_two_mul_filter S2 (fun v => (-v.1, v.2.1, v.2.2)) (fun v => 0 < v.1) ?_ ?_ ?_]
    · set S3 := S2.filter fun v => 0 < v.1
      have hS3 : ∀ v ∈ S3, v ∈ gset m ∧ 0 < v.2.2 ∧ 0 < v.1 := fun v hv =>
        ⟨(hS2 v (mem_filter.mp hv).1).1, (hS2 v (mem_filter.mp hv).1).2, (mem_filter.mp hv).2⟩
      rw [card_eq_two_mul_filter S3 (fun v => (v.1, -v.2.1, v.2.2)) (fun v => 0 < v.2.1) ?_ ?_ ?_]
      · exact ⟨_, by ring⟩
      · intro v hv
        obtain ⟨hg, hk, ha⟩ := hS3 v hv
        rw [mem_gset] at hg
        simp only [S3, S2, S1, mem_filter, mem_gset, neg_sq, neg_cond]
        exact ⟨⟨⟨hg, by omega⟩, hk⟩, ha⟩
      · intro v _; simp
      · intro v hv
        obtain ⟨hg, -, -⟩ := hS3 v hv
        rw [mem_gset] at hg
        have : v.2.1 ≠ 0 := by rintro h; rw [h] at hg; omega
        simp only; constructor <;> intro h <;> omega
    · intro v hv
      obtain ⟨hg, hk⟩ := hS2 v hv
      rw [mem_gset] at hg
      simp only [S2, S1, mem_filter, mem_gset, neg_sq]
      exact ⟨⟨hg, by omega⟩, hk⟩
    · intro v _; simp
    · intro v hv
      obtain ⟨hg, -⟩ := hS2 v hv
      rw [mem_gset] at hg
      have : v.1 ≠ 0 := by
        rintro h; rw [h] at hg; have := sq_mod16_ne5 v.2.1; simp at hg; omega
      simp only; constructor <;> intro h <;> omega
  · intro v hv
    obtain ⟨hg, hk⟩ := hS1 v hv
    rw [mem_gset] at hg
    simp only [S1, mem_filter, mem_gset, neg_sq]
    exact ⟨hg, by omega⟩
  · intro v _; simp
  · intro v hv
    obtain ⟨-, hk⟩ := hS1 v hv
    simp only; constructor <;> intro h <;> omega

/-- `gCount p ≡ 4 A (mod 8)` for a prime `p ≡ 5 (mod 16)`, `p = a² + b²`, `b` even. -/
theorem gCount_prime {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5) {a b : ℤ}
    (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    (gCount p : ℤ) ≡ 4 * octA b [ZMOD 8] := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hodd : (p : ℤ) % 2 = 1 := by omega
  have ha0 : a ≠ 0 := by
    rintro rfl; have := sq_mod16_ne5 b; simp at hab; omega
  have hb0 : b ≠ 0 := by
    rintro rfl; have := sq_mod16_ne5 a; simp at hab; omega
  rw [gCount_eq_card, ← card_filter_add_card_filter_not (s := gset p) (p := fun v => ¬ v.2.2 = 0)]
  obtain ⟨c, hc⟩ := eight_dvd_card_k_ne (m := p)
  set S0 := (gset p).filter fun v => ¬ ¬ v.2.2 = 0
  have hS0 : ∀ v ∈ S0, v ∈ gset p ∧ v.2.2 = 0 := fun v hv =>
    ⟨(mem_filter.mp hv).1, not_not.mp (mem_filter.mp hv).2⟩
  have h4 : S0.card = 4 * ((S0.filter fun v => 0 < v.1).filter fun v => 0 < v.2.1).card := by
    rw [card_eq_two_mul_filter S0 (fun v => (-v.1, v.2.1, v.2.2)) (fun v => 0 < v.1) ?_ ?_ ?_]
    · rw [card_eq_two_mul_filter _ (fun v => (v.1, -v.2.1, v.2.2)) (fun v => 0 < v.2.1) ?_ ?_ ?_]
      · ring
      · intro v hv
        simp only [mem_filter] at hv
        obtain ⟨hg, hk⟩ := hS0 v hv.1
        rw [mem_gset] at hg
        simp only [S0, mem_filter, mem_gset, neg_sq, neg_cond]
        exact ⟨⟨hg, by simpa using hk⟩, hv.2⟩
      · intro v _; simp
      · intro v hv
        simp only [mem_filter] at hv
        obtain ⟨hg, -⟩ := hS0 v hv.1
        rw [mem_gset] at hg
        have : v.2.1 ≠ 0 := by rintro h; rw [h] at hg; omega
        simp only; constructor <;> intro h <;> omega
    · intro v hv
      obtain ⟨hg, hk⟩ := hS0 v hv
      rw [mem_gset] at hg
      simp only [S0, mem_filter, mem_gset, neg_sq]
      exact ⟨hg, by simpa using hk⟩
    · intro v _; simp
    · intro v hv
      obtain ⟨hg, -⟩ := hS0 v hv
      rw [mem_gset] at hg
      have : v.1 ≠ 0 := by
        rintro h; rw [h] at hg; have := sq_mod16_ne5 v.2.1; simp at hg; omega
      simp only; constructor <;> intro h <;> omega
  set T := (S0.filter fun v => 0 < v.1).filter fun v => 0 < v.2.1
  have hT : ∀ v ∈ T, v.1 = |a| ∧ v.2.1 = |b| ∧ v.2.2 = 0 ∧ (v.2.1 % 16 = 6 ∨ v.2.1 % 16 = 10) := by
    intro v hv
    simp only [T, mem_filter] at hv
    obtain ⟨⟨hv0, h1⟩, h2⟩ := hv
    obtain ⟨hg, hk⟩ := hS0 v hv0
    rw [mem_gset, hk] at hg
    have hβe : Even v.2.1 := by
      rcases hg.2.2 with h | h <;> exact ⟨v.2.1 / 2, by omega⟩
    have hbe : Even |b| := (even_abs).mpr hb
    have := two_sq_unique hpZ hodd h1 h2 (abs_pos.mpr ha0) (abs_pos.mpr hb0)
      (by simpa using hg.1) (by rw [sq_abs, sq_abs]; exact hab) hβe hbe
    exact ⟨this.1, this.2, hk, hg.2.2⟩
  have habs : (|b| % 16 = 6 ∨ |b| % 16 = 10) ↔ (b % 16 = 6 ∨ b % 16 = 10) := by
    rcases abs_cases b with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h]; omega
  have hTcard : (T.card : ℤ) = octA b := by
    unfold octA
    split_ifs with hcond
    · have : T = {(|a|, |b|, 0)} := by
        ext v
        rw [mem_singleton]
        constructor
        · intro hv
          obtain ⟨h1, h2, h3, -⟩ := hT v hv
          ext <;> simp [h1, h2, h3]
        · rintro rfl
          simp only [T, S0, mem_filter, mem_gset]
          refine ⟨⟨⟨⟨?_, ?_, habs.mpr hcond⟩, by simp⟩, abs_pos.mpr ha0⟩, abs_pos.mpr hb0⟩
          · rw [sq_abs, sq_abs]; simpa using hab
          · rw [sq_abs, sq_abs, hab]; omega
      rw [this, card_singleton]; rfl
    · have : T = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro v hv
        obtain ⟨-, h2, -, h4⟩ := hT v hv
        rw [h2] at h4
        exact hcond (habs.mp h4)
      rw [this, card_empty]; rfl
  push_cast
  rw [hc, h4]
  push_cast
  rw [hTcard]
  exact Int.modEq_iff_dvd.mpr ⟨-c, by ring⟩

end ConjCoord.Proof
