module

public import ConjCoord.Defs

@[expose] public section

/-!
# Computing the representation numbers

`cntL` counts the representations of `n` by `a x² + b y² + c z²` (with a condition on `|x|, |y|`)
from the nonnegative `x, y ≤ √n`, with weights `1` or `2` for the signs and `z` found by an
integer square root. `count_eq_cntL` identifies it with the count over the box. This makes the
finite check `tCoeff_check` (`64 ∣ tCoeff m` for `m ≤ 512`) a small kernel computation.
-/

open Finset

namespace ConjCoord.Proof

/-- The number of signs of a nonnegative integer: `1` for `0`, `2` otherwise. -/
def wt (x : ℕ) : ℕ := if x = 0 then 1 else 2

/-- The number of `z ∈ ℤ` with `c z² = r`. -/
def zc (c r : ℕ) : ℕ :=
  if r % c = 0 ∧ Nat.sqrt (r / c) * Nat.sqrt (r / c) = r / c then (if r = 0 then 1 else 2) else 0

/-- The count of `(x, y, z) ∈ ℤ³` with `a x² + b y² + c z² = n` and `Q |x| |y|`, computed from
`0 ≤ x, y ≤ √n`. -/
def cntL (a b c n : ℕ) (Q : ℕ → ℕ → Bool) : ℕ :=
  ∑ x ∈ range (Nat.sqrt n + 1), ∑ y ∈ range (Nat.sqrt n + 1),
    if a * x ^ 2 + b * y ^ 2 ≤ n ∧ Q x y = true then wt x * wt y * zc c (n - a * x ^ 2 - b * y ^ 2)
    else 0

lemma card_zfilter (c : ℕ) (hc : 0 < c) (n : ℕ) (r : ℤ) (hr : r ≤ n) :
    ((Icc (-(n : ℤ)) n).filter fun z => (c : ℤ) * z ^ 2 = r).card =
      if 0 ≤ r then zc c r.toNat else 0 := by
  split_ifs with h0
  · obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s := ⟨r.toNat, (Int.toNat_of_nonneg h0).symm⟩
    simp only [Int.toNat_natCast]
    have hsn : s ≤ n := by exact_mod_cast hr
    unfold zc
    by_cases hs : s % c = 0 ∧ Nat.sqrt (s / c) * Nat.sqrt (s / c) = s / c
    · rw [ite_eq_left hs]
      set t := Nat.sqrt (s / c) with ht
      have hct : c * (t * t) = s := by
        rw [hs.2]; exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hs.1)
      have hts : t ≤ s :=
        calc t ≤ t * t := Nat.le_mul_self t
          _ ≤ c * (t * t) := Nat.le_mul_of_pos_left _ hc
          _ = s := hct
      have hctZ : (c : ℤ) * (t : ℤ) ^ 2 = s := by
        rw [← hct]; push_cast; ring
      have key : ∀ z : ℤ, (c : ℤ) * z ^ 2 = s ↔ z = t ∨ z = -t := by
        intro z
        rw [← hctZ]
        constructor
        · intro h
          have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
          have := mul_left_cancel₀ hc0 h
          exact sq_eq_sq_iff_eq_or_eq_neg.mp this
        · rintro (rfl | rfl) <;> ring
      have hfil : ((Icc (-(n : ℤ)) n).filter fun z => (c : ℤ) * z ^ 2 = s) =
          {(t : ℤ), -(t : ℤ)} := by
        ext z
        simp only [mem_filter, mem_Icc, key, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl) <;> refine ⟨⟨by omega, by omega⟩, by simp⟩
      rw [hfil]
      split_ifs with hs0
      · have : t = 0 := by
          rcases Nat.eq_zero_of_le_zero (hts.trans hs0.le) with h; exact h
        simp [this]
      · have ht0 : t ≠ 0 := by
          rintro h; apply hs0; rw [← hct, h]; simp
        rw [card_insert_of_notMem (by simp; omega), card_singleton]
    · rw [ite_eq_right hs]
      rw [card_eq_zero, filter_eq_empty_iff]
      intro z _ h
      apply hs
      have hz : c * (z.natAbs * z.natAbs) = s := by
        have : ((c * (z.natAbs * z.natAbs) : ℕ) : ℤ) = s := by
          push_cast; rw [abs_mul_abs_self, ← h]; ring
        exact_mod_cast this
      refine ⟨?_, ?_⟩
      · rw [← hz]; exact Nat.mul_mod_right _ _
      · rw [← hz, Nat.mul_div_cancel_left _ hc, Nat.sqrt_eq]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro z _ h
    have : (0 : ℤ) ≤ (c : ℤ) * z ^ 2 := by positivity
    omega

lemma sum_Icc_natAbs {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ x ∈ Icc (-(n : ℤ)) n, f x.natAbs = ∑ k ∈ range (n + 1), wt k • f k := by
  induction n with
  | zero => simp [wt]
  | succ n ih =>
    have hset : Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Icc (-(n : ℤ)) n)) := by
      ext x; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [hset, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ih,
      sum_range_succ (fun k => wt k • f k) (n + 1)]
    have h1 : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    have h2 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    have hw : wt (n + 1) = 2 := by simp [wt]
    rw [h1, h2, hw, two_smul]; abel

/-- The box count equals the computed count. -/
theorem count_eq_cntL (a b c n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (P : ℤ → ℤ → Prop) [DecidableRel P] (Q : ℕ → ℕ → Bool)
    (hPQ : ∀ x y, P x y ↔ Q x.natAbs y.natAbs = true) :
    ((box3 n).filter fun v =>
        (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n ∧ P v.1 v.2.1).card =
      cntL a b c n Q := by
  set g : ℕ → ℕ → ℕ := fun i j =>
    if a * i ^ 2 + b * j ^ 2 ≤ n ∧ Q i j = true then zc c (n - a * i ^ 2 - b * j ^ 2) else 0
    with hg
  -- the inner count over `z`
  have inner : ∀ x y : ℤ,
      (∑ z ∈ Icc (-(n : ℤ)) n,
        if (a : ℤ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = n ∧ P x y then 1 else 0) =
        g x.natAbs y.natAbs := by
    intro x y
    rw [← card_filter]
    have hx : ((x.natAbs ^ 2 : ℕ) : ℤ) = x ^ 2 := by push_cast; exact sq_abs x
    have hy : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by push_cast; exact sq_abs y
    simp only [hg]
    by_cases hP : P x y
    · have hQ := (hPQ x y).mp hP
      have hfil : ((Icc (-(n : ℤ)) n).filter fun z =>
            (a : ℤ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = n ∧ P x y) =
          (Icc (-(n : ℤ)) n).filter fun z => (c : ℤ) * z ^ 2 = (n : ℤ) - a * x ^ 2 - b * y ^ 2 := by
        refine filter_congr fun z _ => ?_
        constructor
        · rintro ⟨h, -⟩; linarith
        · intro h; exact ⟨by linarith, hP⟩
      rw [hfil, card_zfilter c hc n _ (by nlinarith [sq_nonneg x, sq_nonneg y])]
      by_cases hle : a * x.natAbs ^ 2 + b * y.natAbs ^ 2 ≤ n
      · have h0 : (0 : ℤ) ≤ (n : ℤ) - a * x ^ 2 - b * y ^ 2 := by
          rw [← hx, ← hy]; have : ((a * x.natAbs ^ 2 + b * y.natAbs ^ 2 : ℕ) : ℤ) ≤ n := by
            exact_mod_cast hle
          push_cast at this ⊢; linarith
        rw [ite_eq_left h0, ite_eq_left ⟨hle, hQ⟩]
        congr 1
        rw [← hx, ← hy]
        have : ((n - a * x.natAbs ^ 2 - b * y.natAbs ^ 2 : ℕ) : ℤ) =
            (n : ℤ) - a * (x.natAbs ^ 2 : ℕ) - b * (y.natAbs ^ 2 : ℕ) := by
          push_cast [Nat.sub_sub, Nat.cast_sub hle]; ring
        omega
      · have h0 : ¬ (0 : ℤ) ≤ (n : ℤ) - a * x ^ 2 - b * y ^ 2 := by
          rw [← hx, ← hy]; have : ¬ ((a * x.natAbs ^ 2 + b * y.natAbs ^ 2 : ℕ) : ℤ) ≤ n := by
            exact_mod_cast hle
          push_cast at this ⊢; linarith
        rw [ite_eq_right h0, ite_eq_right (fun h => hle h.1)]
    · have hQ : ¬ Q x.natAbs y.natAbs = true := fun h => hP ((hPQ x y).mpr h)
      rw [ite_eq_right (fun h => hQ h.2), card_eq_zero, filter_eq_empty_iff]
      exact fun z _ h => hP h.2
  rw [card_filter, box3, sum_product]
  simp_rw [sum_product]
  simp_rw [inner]
  rw [sum_Icc_natAbs n (fun i => ∑ y ∈ Icc (-(n : ℤ)) n, g i y.natAbs)]
  have hrow : ∀ i, ∑ y ∈ Icc (-(n : ℤ)) n, g i y.natAbs = ∑ j ∈ range (n + 1), wt j • g i j :=
    fun i => sum_Icc_natAbs n (g i)
  simp_rw [hrow]
  -- truncate the ranges
  have hvan : ∀ i j, Nat.sqrt n < i ∨ Nat.sqrt n < j → g i j = 0 := by
    intro i j hij
    simp only [hg]
    rw [ite_eq_right]
    rintro ⟨hle, -⟩
    rcases hij with h | h
    · have := Nat.sqrt_lt'.mp h
      nlinarith [Nat.zero_le (b * j ^ 2)]
    · have := Nat.sqrt_lt'.mp h
      nlinarith [Nat.zero_le (a * i ^ 2)]
  have hsub : range (Nat.sqrt n + 1) ⊆ range (n + 1) := by
    intro k hk; simp only [mem_range] at hk ⊢; have := Nat.sqrt_le_self n; omega
  have hinner : ∀ i, ∑ j ∈ range (n + 1), wt j • g i j =
      ∑ j ∈ range (Nat.sqrt n + 1), wt j • g i j := by
    intro i
    refine (sum_subset hsub fun j _ hj => ?_).symm
    simp only [mem_range, not_lt] at hj
    rw [hvan i j (Or.inr (by omega)), smul_zero]
  simp_rw [hinner]
  rw [← sum_subset hsub fun i _ hi => ?_]
  · unfold cntL
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [hg, smul_eq_mul]
    split_ifs <;> ring
  · simp only [mem_range, not_lt] at hi
    rw [sum_eq_zero fun j _ => by rw [hvan i j (Or.inl (by omega)), smul_zero], smul_zero]

/-- The condition of `gCount` on `|α|, |β|`. -/
def qG (i j : ℕ) : Bool := (i ^ 2 + j ^ 2) % 16 == 5 && (j % 16 == 6 || j % 16 == 10)

lemma reps_eq_cntL (a b c n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    reps a b c n = cntL a b c n (fun _ _ => true) := by
  rw [← count_eq_cntL a b c n ha hb hc (fun _ _ => True) _ (fun _ _ => by simp)]
  unfold reps
  congr 1
  exact filter_congr fun v _ => by simp

lemma gCount_eq_cntL (m : ℕ) : gCount m = cntL 1 1 16 m qG := by
  rw [← count_eq_cntL 1 1 16 m one_pos one_pos (by norm_num)
    (fun x y => (x ^ 2 + y ^ 2) % 16 = 5 ∧ (y % 16 = 6 ∨ y % 16 = 10)) qG ?_]
  · unfold gCount
    congr 1
    exact filter_congr fun v _ => by push_cast; simp only [one_mul]
  · intro x y
    have hx : ((x.natAbs ^ 2 : ℕ) : ℤ) = x ^ 2 := by push_cast; exact sq_abs x
    have hy : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by push_cast; exact sq_abs y
    simp only [qG, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    rw [← hx, ← hy]
    rcases Int.natAbs_eq y with hy' | hy' <;>
    · constructor <;> intro h <;> omega

/-- The computed form of `tCoeff`. -/
def tCoeffL (m : ℕ) : ℤ :=
  if m % 16 = 5 then
    2 * (cntL 1 2 4 m (fun _ _ => true) : ℤ) - cntL 1 2 2 m (fun _ _ => true) - 8 * cntL 1 1 16 m qG
  else 0

lemma tCoeff_eq_tCoeffL (m : ℕ) : tCoeff m = tCoeffL m := by
  unfold tCoeff tCoeffL
  rw [reps_eq_cntL 1 2 4 m (by norm_num) (by norm_num) (by norm_num),
    reps_eq_cntL 1 2 2 m (by norm_num) (by norm_num) (by norm_num), gCount_eq_cntL]

lemma tCoeffL_check : ∀ m < 513, (64 : ℤ) ∣ tCoeffL m := by decide +kernel

/-- **The finite check**: `64 ∣ tCoeff m` for `m ≤ 512`. -/
theorem tCoeff_check (m : ℕ) (hm : m ≤ 512) : (64 : ℤ) ∣ tCoeff m := by
  rw [tCoeff_eq_tCoeffL]; exact tCoeffL_check m (by omega)

end ConjCoord.Proof
