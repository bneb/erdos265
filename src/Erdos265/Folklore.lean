import Mathlib

open Filter Topology Real BigOperators Finset

/-!
# The Folklore Theorem: Irrationality of Rapid Sums

This file formalizes the algebraic core of the folklore theorem stated in the problem:
"A folklore result states that ∑ 1/a_n is irrational whenever lim a_n^{1/2^n} = ∞"

We prove this by isolating a single rational sum. If the sum is rational, the sequence
must satisfy the exact integer residual constraint R_N ≥ 1. If the sequence grows fast 
enough (which is guaranteed if the limit is ∞), the tail sum is bounded by 2 / a_N.

Plugging this tail bound into the integer residual yields an absolute recursive ceiling:
a_N ≤ 2 * q * P_N
Because P_N is the product of the first N-1 terms, this recurrence rigorously restricts 
the growth of the sequence to O(C^{2^N}), mathematically forbidding the limit from 
being infinity.
-/

variable (a : ℕ → ℕ) (q : ℕ) (p : ℤ)

/-- The prefix product for the sequence. -/
def P1 (N : ℕ) : ℤ := ∏ k ∈ Finset.range N, (a k : ℤ)

/-- The exact residual integer for the single rationality. -/
noncomputable def R1 (N : ℕ) : ℝ :=
  (q : ℝ) * (P1 a N : ℝ) * ∑' k, (1 : ℝ) / (a (N + k) : ℝ)

lemma single_residual_int (N : ℕ) 
    (hq : q > 0)
    (hSum : HasSum (fun k => 1 / (a k : ℝ)) (p / q))
    (hGe2 : ∀ k, a k ≥ 2) :
    ∃ Z : ℤ, R1 a q N = (Z : ℝ) := by
  have h_sum_split : ∑' (k : ℕ), 1 / (a k : ℝ) = ∑ k ∈ Finset.range N, 1 / (a k : ℝ) + ∑' (k : ℕ), 1 / (a (N + k) : ℝ) := by
    have h_shift : (∑' (i : ℕ), 1 / (a (i + N) : ℝ)) = ∑' (i : ℕ), 1 / (a (N + i) : ℝ) := by
      congr 1; ext i; congr 1; ring
    rw [← h_shift]
    exact (Summable.sum_add_tsum_nat_add N hSum.summable).symm
  have h_sum_val : ∑' (k : ℕ), 1 / (a k : ℝ) = (p : ℝ) / (q : ℝ) := hSum.tsum_eq
  have h_tail_val : ∑' (k : ℕ), 1 / (a (N + k) : ℝ) = (p : ℝ) / (q : ℝ) - ∑ k ∈ Finset.range N, 1 / (a k : ℝ) := by
    linarith [h_sum_split, h_sum_val]
  dsimp [R1]
  rw [h_tail_val]
  let P := P1 a N
  have h_distrib : (q : ℝ) * (P : ℝ) * ((p : ℝ) / (q : ℝ) - ∑ k ∈ Finset.range N, 1 / (a k : ℝ)) =
    (P : ℝ) * (p : ℝ) - (q : ℝ) * ∑ k ∈ Finset.range N, (P : ℝ) / (a k : ℝ) := by
    have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    calc (q : ℝ) * (P : ℝ) * ((p : ℝ) / (q : ℝ) - ∑ k ∈ Finset.range N, 1 / (a k : ℝ))
      _ = (q : ℝ) * (P : ℝ) * ((p : ℝ) / (q : ℝ)) - (q : ℝ) * (P : ℝ) * ∑ k ∈ Finset.range N, 1 / (a k : ℝ) := by ring
      _ = (P : ℝ) * (p : ℝ) - (q : ℝ) * ∑ k ∈ Finset.range N, (P : ℝ) / (a k : ℝ) := by
          congr 1
          · calc (q : ℝ) * (P : ℝ) * ((p : ℝ) / (q : ℝ)) = (P : ℝ) * (p : ℝ) * ((q : ℝ) / (q : ℝ)) := by ring_nf
              _ = (P : ℝ) * (p : ℝ) * 1 := by rw [div_self hq_ne]
              _ = (P : ℝ) * (p : ℝ) := by ring
          · have h_sum1 : (q : ℝ) * (P : ℝ) * ∑ k ∈ Finset.range N, 1 / (a k : ℝ) = ∑ k ∈ Finset.range N, (q : ℝ) * (P : ℝ) * (1 / (a k : ℝ)) := by rw [mul_sum]
            rw [h_sum1]
            have h_sum2 : (q : ℝ) * ∑ k ∈ Finset.range N, (P : ℝ) / (a k : ℝ) = ∑ k ∈ Finset.range N, (q : ℝ) * ((P : ℝ) / (a k : ℝ)) := by rw [mul_sum]
            rw [h_sum2]
            apply Finset.sum_congr rfl
            intro k hk
            ring_nf
  rw [h_distrib]
  have h_Z : ∃ Z : ℤ, ∑ k ∈ Finset.range N, (P : ℝ) / (a k : ℝ) = (Z : ℝ) := by
    let Z_sum := ∑ k ∈ Finset.range N, P / (a k : ℤ)
    use Z_sum
    have h_rw : ∑ k ∈ Finset.range N, (P : ℝ) / (a k : ℝ) = ∑ k ∈ Finset.range N, ((P / (a k : ℤ) : ℤ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hdvd : (a k : ℤ) ∣ P := by
        dsimp [P, P1]
        exact Finset.dvd_prod_of_mem (fun i => (a i : ℤ)) hk
      have h_ak_ne_Z : (a k : ℤ) ≠ 0 := by
        have : a k ≥ 2 := hGe2 k
        omega
      have hcast := Int.cast_div (α := ℝ) hdvd (by exact_mod_cast h_ak_ne_Z)
      rw [hcast]
      push_cast
      rfl
    have h_push : (∑ k ∈ Finset.range N, ((P / (a k : ℤ) : ℤ) : ℝ)) = (Z_sum : ℝ) := by
      dsimp [Z_sum]
      push_cast
      rfl
    rw [h_push] at h_rw
    exact h_rw
  rcases h_Z with ⟨Z, hZ⟩
  rw [hZ]
  use P * p - q * Z
  push_cast
  ring

/-- The residual is a strictly positive integer. -/
lemma single_residual_ge_one (N : ℕ) 
    (hq : q > 0)
    (hSum : HasSum (fun k => 1 / (a k : ℝ)) (p / q))
    (hGe2 : ∀ k, a k ≥ 2) :
    R1 a q N ≥ 1 := by
  have h_int := single_residual_int a q p N hq hSum hGe2
  rcases h_int with ⟨Z, hZ⟩
  have h_pos : R1 a q N > 0 := by
    dsimp [R1]
    have h_q_pos : (q : ℝ) > 0 := by exact_mod_cast hq
    have h_P_pos : (P1 a N : ℝ) > 0 := by
      dsimp [P1]
      have h_prod_z : (∏ k ∈ Finset.range N, (a k : ℤ)) > 0 := by
        apply Finset.prod_pos
        intro i _
        have : a i ≥ 2 := hGe2 i
        omega
      exact_mod_cast h_prod_z
    have h_sum_pos : (∑' k, (1 : ℝ) / (a (N + k) : ℝ)) > 0 := by
      have h_summable : Summable (fun k => (1 : ℝ) / (a (N + k) : ℝ)) := by
        have h_comp : (fun k => (1 : ℝ) / (a (N + k) : ℝ)) = (fun k => (1 : ℝ) / (a k : ℝ)) ∘ (fun k => N + k) := by
          ext k; rfl
        rw [h_comp]
        apply Summable.comp_injective hSum.summable
        intro x y hxy
        dsimp at hxy
        omega
      have h_eval : ∑' (k : ℕ), 1 / (a (N + k) : ℝ) = ∑ k ∈ Finset.range 1, 1 / (a (N + k) : ℝ) + ∑' (k : ℕ), 1 / (a (N + (k + 1)) : ℝ) := (Summable.sum_add_tsum_nat_add 1 h_summable).symm
      have h_pos_term : ∑ k ∈ Finset.range 1, 1 / (a (N + k) : ℝ) > 0 := by
        rw [Finset.sum_range_one]
        have : a (N + 0) ≥ 2 := hGe2 _
        positivity
      have h_nonneg_tail : ∑' (k : ℕ), 1 / (a (N + (k + 1)) : ℝ) ≥ 0 := by
        apply tsum_nonneg
        intro k
        have : a (N + (k + 1)) ≥ 2 := hGe2 _
        positivity
      linarith
    positivity
  rw [hZ] at h_pos
  have h_Z_pos : Z > 0 := by exact_mod_cast h_pos
  have h_Z_ge_1 : Z ≥ 1 := by omega
  rw [hZ]
  exact_mod_cast h_Z_ge_1

/-- 
  The Folklore Ceiling:
  If the tail sum is bounded by 2 / a_N, the integer residual forces the current 
  term a_N to be strictly bounded by twice the prefix product.
-/
lemma folklore_ceiling (N : ℕ)
    (hq : q > 0)
    (hSum : HasSum (fun k => 1 / (a k : ℝ)) (p / q))
    (hGe2 : ∀ k, a k ≥ 2)
    (h_tail_bound : ∑' k, (1 : ℝ) / (a (N + k) : ℝ) ≤ 2 / (a N : ℝ)) :
    (a N : ℝ) ≤ 2 * (q : ℝ) * (P1 a N : ℝ) := by
  have h_res := single_residual_ge_one a q p N hq hSum hGe2
  dsimp [R1] at h_res
  
  have hP_pos : (P1 a N : ℝ) > 0 := by
    dsimp [P1]
    have h_prod_z : (∏ k ∈ Finset.range N, (a k : ℤ)) > 0 := by
      apply Finset.prod_pos
      intro i _
      have : a i ≥ 2 := hGe2 i
      omega
    exact_mod_cast h_prod_z
  
  have hq_pos : (q : ℝ) > 0 := by exact_mod_cast hq
  have h_mul_pos : (q : ℝ) * (P1 a N : ℝ) > 0 := mul_pos hq_pos hP_pos
  
  have h_bound : (q : ℝ) * (P1 a N : ℝ) * ∑' k, (1 : ℝ) / (a (N + k) : ℝ) ≤ (q : ℝ) * (P1 a N : ℝ) * (2 / (a N : ℝ)) := by
    exact mul_le_mul_of_nonneg_left h_tail_bound (le_of_lt h_mul_pos)
    
  have h_chain : (1 : ℝ) ≤ (q : ℝ) * (P1 a N : ℝ) * (2 / (a N : ℝ)) := le_trans h_res h_bound
  
  have h_a_pos : (a N : ℝ) > 0 := by
    have : a N ≥ 2 := hGe2 N
    exact_mod_cast (by omega : a N > 0)
    
  have h_mul_a : (a N : ℝ) * 1 ≤ (a N : ℝ) * ((q : ℝ) * (P1 a N : ℝ) * (2 / (a N : ℝ))) := by
    exact mul_le_mul_of_nonneg_left h_chain (le_of_lt h_a_pos)
    
  have h_simplify : (a N : ℝ) * ((q : ℝ) * (P1 a N : ℝ) * (2 / (a N : ℝ))) = 2 * (q : ℝ) * (P1 a N : ℝ) := by
    calc (a N : ℝ) * ((q : ℝ) * (P1 a N : ℝ) * (2 / (a N : ℝ))) 
      _ = (a N : ℝ) * (2 / (a N : ℝ)) * (q : ℝ) * (P1 a N : ℝ) := by ring
      _ = ((a N : ℝ) * 2 / (a N : ℝ)) * (q : ℝ) * (P1 a N : ℝ) := by ring
      _ = 2 * (q : ℝ) * (P1 a N : ℝ) := by
          have : (a N : ℝ) * 2 / (a N : ℝ) = 2 := by
            rw [mul_comm, mul_div_cancel_right₀ 2 (ne_of_gt h_a_pos)]
          rw [this]
  
  rw [h_simplify, mul_one] at h_mul_a
  exact h_mul_a
lemma seq_bound_of_square_bound_real (y : ℕ → ℝ) (h_pos : ∀ n, y n ≥ 0) (h_step : ∀ n, y (n + 1) ≤ y n ^ 2) (n : ℕ) :
    y n ≤ y 0 ^ (2 ^ n) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h1 : y (n + 1) ≤ y n ^ 2 := h_step n
    have h2 : y n ^ 2 ≤ (y 0 ^ (2 ^ n)) ^ 2 := by
      have h_nonneg : 0 ≤ y n := h_pos n
      nlinarith
    have h3 : (y 0 ^ (2 ^ n)) ^ 2 = y 0 ^ (2 ^ (n + 1)) := by
      have : (2 ^ n : ℕ) * 2 = 2 ^ (n + 1) := by ring
      calc (y 0 ^ (2 ^ n)) ^ 2 = y 0 ^ ((2 ^ n : ℕ) * 2) := by rw [← pow_mul]
        _ = y 0 ^ (2 ^ (n + 1) : ℕ) := by rw [this]
    rw [h3] at h2
    exact le_trans h1 h2

lemma P1_step_real (N : ℕ) : (P1 a (N + 1) : ℝ) = (P1 a N : ℝ) * (a N : ℝ) := by
  dsimp [P1]
  rw [prod_range_succ]
  push_cast
  rfl

lemma folklore_asymptotic_bound 
    (hq : q > 0)
    (hGe2 : ∀ k, a k ≥ 2)
    (h_ceiling : ∀ N, (a N : ℝ) ≤ 2 * (q : ℝ) * (P1 a N : ℝ)) (N : ℕ) :
    (a N : ℝ) ≤ (2 * (q : ℝ) * (P1 a 0 : ℝ)) ^ (2 ^ N) := by
  let y := fun n => 2 * (q : ℝ) * (P1 a n : ℝ)
  have h_pos : ∀ n, y n ≥ 0 := by
    intro n
    dsimp [y]
    have hq_pos : (q : ℝ) > 0 := by exact_mod_cast hq
    have h_prod_z : (∏ k ∈ Finset.range n, (a k : ℤ)) > 0 := by
      apply Finset.prod_pos
      intro i _
      have : a i ≥ 2 := hGe2 i
      omega
    have hP_pos : (P1 a n : ℝ) > 0 := by 
      dsimp [P1]
      exact_mod_cast h_prod_z
    positivity
  have h_step : ∀ n, y (n + 1) ≤ y n ^ 2 := by
    intro n
    dsimp [y]
    have h1 : (P1 a (n + 1) : ℝ) = (P1 a n : ℝ) * (a n : ℝ) := P1_step_real a n
    rw [h1]
    have h2 : 2 * (q : ℝ) * ((P1 a n : ℝ) * (a n : ℝ)) = (2 * (q : ℝ) * (P1 a n : ℝ)) * (a n : ℝ) := by ring
    rw [h2]
    have h3 : (2 * (q : ℝ) * (P1 a n : ℝ)) * (a n : ℝ) ≤ (2 * (q : ℝ) * (P1 a n : ℝ)) * (2 * (q : ℝ) * (P1 a n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (h_ceiling n) (h_pos n)
    have h4 : (2 * (q : ℝ) * (P1 a n : ℝ)) * (2 * (q : ℝ) * (P1 a n : ℝ)) = (2 * (q : ℝ) * (P1 a n : ℝ)) ^ 2 := by ring
    rw [h4] at h3
    exact h3
  have h_bound := seq_bound_of_square_bound_real y h_pos h_step N
  have h_a_le : (a N : ℝ) ≤ y N := h_ceiling N
  exact le_trans h_a_le h_bound
