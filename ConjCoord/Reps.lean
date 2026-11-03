module

public import ConjCoord.Defs

@[expose] public section

/-!
# Lemma 3: the two ternary forms and sums of three squares

For `n ≡ 1 (mod 4)`, `r₃(n) = 3 r_{1,2,2}(n)`; for odd `n`, `r₃(2n) = 3 r_{1,1,2}(n)` and
`r_{1,1,2}(n) = 2 r_{1,2,4}(n)`. With Gauss's `r₃(m) = 12 h(-4m)` these give
`r_{1,2,2}(p) = 4 h(-4p)` and `r_{1,2,4}(p) = 2 h(-8p)`.
-/

open Finset

namespace ConjCoord.Proof

/-- The representations of `n` by `a x² + b y² + c z²`. -/
def sol (a b c n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (box3 n).filter fun v => (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n

lemma reps_eq_card_sol (a b c n : ℕ) : reps a b c n = (sol a b c n).card := rfl

lemma mem_Icc_of_sq_le {x : ℤ} {n : ℕ} (h : x ^ 2 ≤ n) : x ∈ Icc (-(n : ℤ)) n := by
  have h1 := Int.le_self_sq x
  have h2 := Int.le_self_sq (-x)
  rw [neg_sq] at h2
  simp only [mem_Icc]; constructor <;> linarith

lemma mem_sol {a b c n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (v : ℤ × ℤ × ℤ) :
    v ∈ sol a b c n ↔ (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n := by
  unfold sol box3
  rw [mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hc' : (1 : ℤ) ≤ c := by exact_mod_cast hc
  have e1 := mul_nonneg (by linarith : (0 : ℤ) ≤ a) (sq_nonneg v.1)
  have e2 := mul_nonneg (by linarith : (0 : ℤ) ≤ b) (sq_nonneg v.2.1)
  have e3 := mul_nonneg (by linarith : (0 : ℤ) ≤ c) (sq_nonneg v.2.2)
  have f1 : v.1 ^ 2 ≤ (a : ℤ) * v.1 ^ 2 := le_mul_of_one_le_left (sq_nonneg _) ha'
  have f2 : v.2.1 ^ 2 ≤ (b : ℤ) * v.2.1 ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hb'
  have f3 : v.2.2 ^ 2 ≤ (c : ℤ) * v.2.2 ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hc'
  refine mem_product.mpr ⟨mem_Icc_of_sq_le (by linarith), mem_product.mpr
    ⟨mem_Icc_of_sq_le (by linarith), mem_Icc_of_sq_le (by linarith)⟩⟩

lemma sq_mod4 (x : ℤ) : (Even x ∧ x ^ 2 % 4 = 0) ∨ (Odd x ∧ x ^ 2 % 4 = 1) := by
  rcases Int.even_or_odd x with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · left; refine ⟨⟨r, rfl⟩, ?_⟩; ring_nf; omega
  · right; refine ⟨⟨r, rfl⟩, ?_⟩; ring_nf; omega

/-- A finset with a fixed-point-free involution exchanging `P` and `¬P` has twice as many
elements as its `P`-part. -/
lemma card_eq_two_mul_filter {α : Type*} (S : Finset α) (σ : α → α) (P : α → Prop)
    [DecidablePred P] (hS : ∀ x ∈ S, σ x ∈ S) (hσ : ∀ x ∈ S, σ (σ x) = x)
    (hP : ∀ x ∈ S, P (σ x) ↔ ¬ P x) : S.card = 2 * (S.filter P).card := by
  rw [← card_filter_add_card_filter_not (s := S) (p := P)]
  have : (S.filter fun x => ¬ P x).card = (S.filter P).card := by
    refine card_nbij' σ σ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_coe, mem_filter] at hx ⊢
      exact ⟨hS x hx.1, (hP x hx.1).mpr hx.2⟩
    · intro x hx
      simp only [mem_coe, mem_filter] at hx ⊢
      refine ⟨hS x hx.1, fun h => ?_⟩
      exact ((hP x hx.1).mp h) hx.2
    · intro x hx; simp only [mem_coe, mem_filter] at hx; exact hσ x hx.1
    · intro x hx; simp only [mem_coe, mem_filter] at hx; exact hσ x hx.1
  omega

/-- Splitting a count according to which of three exclusive and exhaustive conditions holds. -/
lemma card_eq_three {α : Type*} (S : Finset α) (P Q R : α → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R]
    (h : ∀ x ∈ S, (P x ∧ ¬ Q x ∧ ¬ R x) ∨ (¬ P x ∧ Q x ∧ ¬ R x) ∨ (¬ P x ∧ ¬ Q x ∧ R x)) :
    S.card = (S.filter P).card + (S.filter Q).card + (S.filter R).card := by
  rw [card_filter, card_filter, card_filter, card_eq_sum_ones, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun x hx => ?_
  rcases h x hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2, h3]

section ThreeSquares

variable {n : ℕ}

lemma mem_sol111 {m : ℕ} (v : ℤ × ℤ × ℤ) :
    v ∈ sol 1 1 1 m ↔ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = m := by
  rw [mem_sol one_pos one_pos one_pos]; push_cast; simp only [one_mul]

lemma one_odd (hn : n % 4 = 1) {X U V : ℤ} (h : X ^ 2 + U ^ 2 + V ^ 2 = n) :
    (Odd X ∧ ¬ Odd U ∧ ¬ Odd V) ∨ (¬ Odd X ∧ Odd U ∧ ¬ Odd V) ∨
      (¬ Odd X ∧ ¬ Odd U ∧ Odd V) := by
  simp only [Int.not_odd_iff_even]
  rcases sq_mod4 X with ⟨hX, hX'⟩ | ⟨hX, hX'⟩ <;>
  rcases sq_mod4 U with ⟨hU, hU'⟩ | ⟨hU, hU'⟩ <;>
  rcases sq_mod4 V with ⟨hV, hV'⟩ | ⟨hV, hV'⟩ <;>
  first
    | exact Or.inl ⟨hX, hU, hV⟩
    | exact Or.inr (Or.inl ⟨hX, hU, hV⟩)
    | exact Or.inr (Or.inr ⟨hX, hU, hV⟩)
    | (exfalso; omega)

lemma one_even (hn : n % 2 = 1) {X U V : ℤ} (h : X ^ 2 + U ^ 2 + V ^ 2 = 2 * n) :
    (Even X ∧ ¬ Even U ∧ ¬ Even V) ∨ (¬ Even X ∧ Even U ∧ ¬ Even V) ∨
      (¬ Even X ∧ ¬ Even U ∧ Even V) := by
  simp only [Int.not_even_iff_odd]
  rcases sq_mod4 X with ⟨hX, hX'⟩ | ⟨hX, hX'⟩ <;>
  rcases sq_mod4 U with ⟨hU, hU'⟩ | ⟨hU, hU'⟩ <;>
  rcases sq_mod4 V with ⟨hV, hV'⟩ | ⟨hV, hV'⟩ <;>
  first
    | exact Or.inl ⟨hX, hU, hV⟩
    | exact Or.inr (Or.inl ⟨hX, hU, hV⟩)
    | exact Or.inr (Or.inr ⟨hX, hU, hV⟩)
    | (exfalso; omega)

/-- `r₃(n) = 3 r_{1,2,2}(n)` for `n ≡ 1 (mod 4)`. -/
theorem r3_eq_three_mul_reps122 (hn : n % 4 = 1) : r3 n = 3 * reps 1 2 2 n := by
  unfold r3
  rw [reps_eq_card_sol, reps_eq_card_sol]
  set S := sol 1 1 1 n
  have hS : ∀ v ∈ S, v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = n := fun v hv => (mem_sol111 v).mp hv
  rw [card_eq_three S (fun v => Odd v.1) (fun v => Odd v.2.1) (fun v => Odd v.2.2)
    (fun v hv => one_odd hn (hS v hv))]
  have e2 : (S.filter fun v => Odd v.2.1).card = (S.filter fun v => Odd v.1).card := by
    refine card_nbij' (fun v => (v.2.1, v.1, v.2.2)) (fun v => (v.2.1, v.1, v.2.2)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v _; rfl
    · intro v _; rfl
  have e3 : (S.filter fun v => Odd v.2.2).card = (S.filter fun v => Odd v.1).card := by
    refine card_nbij' (fun v => (v.2.2, v.2.1, v.1)) (fun v => (v.2.2, v.2.1, v.1)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v _; rfl
    · intro v _; rfl
  have e1 : (S.filter fun v => Odd v.1).card = (sol 1 2 2 n).card := by
    symm
    refine card_nbij' (fun v => (v.1, v.2.1 + v.2.2, v.2.1 - v.2.2))
      (fun v => (v.1, (v.2.1 + v.2.2) / 2, (v.2.1 - v.2.2) / 2)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      rw [mem_sol one_pos two_pos two_pos] at hv
      push_cast at hv
      refine ⟨by linarith, ?_⟩
      rcases sq_mod4 v.1 with ⟨_, h1⟩ | ⟨h1, _⟩
      · exfalso; omega
      · exact h1
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv
      rw [mem_coe, mem_sol one_pos two_pos two_pos]
      push_cast
      rcases one_odd hn hv.1 with ⟨-, hU, hV⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · rw [Int.not_odd_iff_even] at hU hV
        obtain ⟨u, hu⟩ := hU; obtain ⟨w, hw⟩ := hV
        have e1 : (v.2.1 + v.2.2) / 2 = u + w := by omega
        have e2 : (v.2.1 - v.2.2) / 2 = u - w := by omega
        rw [e1, e2]; rw [hu, hw] at hv; linarith [hv.1]
      · exact absurd hv.2 h
      · exact absurd hv.2 h
    · intro v _
      ext <;> simp <;> omega
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv
      rcases one_odd hn hv.1 with ⟨-, hU, hV⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
      · rw [Int.not_odd_iff_even] at hU hV
        obtain ⟨u, hu⟩ := hU; obtain ⟨w, hw⟩ := hV
        ext <;> simp <;> omega
      · exact absurd hv.2 h
      · exact absurd hv.2 h
  omega

/-- `r₃(2n) = 3 r_{1,1,2}(n)` for odd `n`. -/
theorem r3_two_mul_eq (hn : n % 2 = 1) : r3 (2 * n) = 3 * reps 1 1 2 n := by
  unfold r3
  rw [reps_eq_card_sol, reps_eq_card_sol]
  set S := sol 1 1 1 (2 * n)
  have hS : ∀ v ∈ S, v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = 2 * n := by
    intro v hv; have := (mem_sol111 v).mp hv; push_cast at this; exact this
  rw [card_eq_three S (fun v => Even v.1) (fun v => Even v.2.1) (fun v => Even v.2.2)
    (fun v hv => one_even hn (hS v hv))]
  have e1 : (S.filter fun v => Even v.1).card = (S.filter fun v => Even v.2.2).card := by
    refine card_nbij' (fun v => (v.2.2, v.2.1, v.1)) (fun v => (v.2.2, v.2.1, v.1)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v _; rfl
    · intro v _; rfl
  have e2 : (S.filter fun v => Even v.2.1).card = (S.filter fun v => Even v.2.2).card := by
    refine card_nbij' (fun v => (v.1, v.2.2, v.2.1)) (fun v => (v.1, v.2.2, v.2.1)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      exact ⟨by linarith [hv.1], hv.2⟩
    · intro v _; rfl
    · intro v _; rfl
  have e3 : (S.filter fun v => Even v.2.2).card = (sol 1 1 2 n).card := by
    symm
    refine card_nbij' (fun v => (v.1 + v.2.1, v.1 - v.2.1, 2 * v.2.2))
      (fun v => ((v.1 + v.2.1) / 2, (v.1 - v.2.1) / 2, v.2.2 / 2)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv ⊢
      rw [mem_sol one_pos one_pos two_pos] at hv
      push_cast at hv ⊢
      exact ⟨by linarith, even_two_mul _⟩
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv
      rw [mem_coe, mem_sol one_pos one_pos two_pos]
      push_cast at hv ⊢
      rcases one_even hn hv.1 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨hX, hU, hV⟩
      · exact absurd hv.2 h
      · exact absurd hv.2 h
      · rw [Int.not_even_iff_odd] at hX hU
        obtain ⟨s, hs⟩ := hX; obtain ⟨t, ht⟩ := hU; obtain ⟨r, hr⟩ := hV
        have e1 : (v.1 + v.2.1) / 2 = s + t + 1 := by omega
        have e2 : (v.1 - v.2.1) / 2 = s - t := by omega
        have e3 : v.2.2 / 2 = r := by omega
        rw [e1, e2, e3]
        have h := hv.1
        rw [hs, ht, hr] at h
        ring_nf at h ⊢
        linarith
    · intro v _
      ext <;> simp <;> omega
    · intro v hv
      simp only [mem_coe, mem_filter, S, mem_sol111] at hv
      push_cast at hv
      rcases one_even hn hv.1 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨hX, hU, hV⟩
      · exact absurd hv.2 h
      · exact absurd hv.2 h
      · rw [Int.not_even_iff_odd] at hX hU
        obtain ⟨s, hs⟩ := hX; obtain ⟨t, ht⟩ := hU; obtain ⟨r, hr⟩ := hV
        ext <;> simp <;> omega
  omega

/-- `r_{1,1,2}(n) = 2 r_{1,2,4}(n)` for odd `n`. -/
theorem reps112_eq (hn : n % 2 = 1) : reps 1 1 2 n = 2 * reps 1 2 4 n := by
  rw [reps_eq_card_sol, reps_eq_card_sol]
  set S := sol 1 1 2 n
  have hS : ∀ v ∈ S, v.1 ^ 2 + v.2.1 ^ 2 + 2 * v.2.2 ^ 2 = n := by
    intro v hv; have := (mem_sol one_pos one_pos two_pos v).mp hv; push_cast at this; linarith
  have par : ∀ v ∈ S, (Even v.1 ↔ ¬ Even v.2.1) := by
    intro v hv
    have := hS v hv
    rw [Int.not_even_iff_odd]
    rcases sq_mod4 v.1 with ⟨hX, hX'⟩ | ⟨hX, hX'⟩ <;>
    rcases sq_mod4 v.2.1 with ⟨hU, hU'⟩ | ⟨hU, hU'⟩
    · exfalso; omega
    · exact ⟨fun _ => hU, fun _ => hX⟩
    · exact ⟨fun h => absurd h (Int.not_even_iff_odd.mpr hX), fun h => absurd hU (Int.not_even_iff_odd.mpr h)⟩
    · exfalso; omega
  rw [card_eq_two_mul_filter S (fun v => (v.2.1, v.1, v.2.2)) (fun v => Even v.2.1) ?_ ?_ ?_]
  · congr 1
    refine card_nbij' (fun v => (v.1, v.2.2, v.2.1 / 2)) (fun v => (v.1, 2 * v.2.2, v.2.1)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [mem_coe, mem_filter] at hv
      rw [mem_coe, mem_sol one_pos two_pos (by norm_num)]
      obtain ⟨r, hr⟩ := hv.2
      have e : v.2.1 / 2 = r := by omega
      dsimp only; rw [e]; have := hS v hv.1; rw [hr] at this; push_cast; linarith
    · intro v hv
      rw [mem_coe, mem_sol one_pos two_pos (by norm_num)] at hv
      simp only [mem_coe, mem_filter, S]
      refine ⟨?_, even_two_mul _⟩
      rw [mem_sol one_pos one_pos two_pos]; push_cast at hv ⊢; linarith
    · intro v hv
      simp only [mem_coe, mem_filter] at hv
      obtain ⟨r, hr⟩ := hv.2
      ext <;> simp; omega
    · intro v _
      ext <;> simp
  · intro v hv
    have := hS v hv
    rw [mem_sol one_pos one_pos two_pos]; push_cast; linarith
  · intro v _; rfl
  · intro v hv
    exact par v hv

/-- Lemma 3, combinatorial part: for `p ≡ 5 (mod 16)`, `r₃(p) = 3 r_{1,2,2}(p)` and
`r₃(2p) = 6 r_{1,2,4}(p)`. -/
theorem lemma3 {p : ℕ} (hp : p % 16 = 5) :
    r3 p = 3 * reps 1 2 2 p ∧ r3 (2 * p) = 6 * reps 1 2 4 p := by
  refine ⟨r3_eq_three_mul_reps122 (by omega), ?_⟩
  rw [r3_two_mul_eq (by omega), reps112_eq (by omega)]; ring

end ThreeSquares

end ConjCoord.Proof
