import Mathlib
import Erdos265.ProblemStatement
import Erdos265.Folklore

open Filter Topology Real BigOperators Finset Nat

/-!
# The Spike and Stall Lemma

This file addresses the "Wild Oscillator" threat.
If a sequence attempts to achieve a limsup β > 2 by using rare, massive jumps 
(spikes), it must bridge the resulting Diophantine gap.

We prove that any "spike" a_N > P_N^2 forces a "stall" phase where subsequent 
terms must remain relatively small to hit the rational target. This stall 
inflates the prefix product, triggering a penalty that lowers the effective 
growth rate of the next term.
-/

variable (a : ℕ → ℕ) (q : ℕ) (p : ℤ)

/-- 
  The Diophantine Gap for a Spike.
  If the sequence sums to p/q, then at any step N, the tail sum must be at least 
  the lattice resolution 1/(q * P1 a N).
-/
lemma spike_lattice_gap (N : ℕ) (hq : q > 0)
    (hSum : HasSum (fun k => 1 / (a k : ℝ)) (p / q))
    (hGe2 : ∀ k, a k ≥ 2) :
    ∑' k, (1 : ℝ) / (a (N + k) : ℝ) ≥ 1 / (q * P1 a N : ℝ) := by
  have h_res := single_residual_ge_one a q p N hq hSum hGe2
  dsimp [R1] at h_res
  have hP_pos : (P1 a N : ℝ) > 0 := by
    dsimp [P1]
    norm_cast
    apply Finset.prod_pos
    intro i _
    linarith [hGe2 i]
  have hq_pos : (q : ℝ) > 0 := by exact_mod_cast hq
  rw [ge_iff_le] at h_res
  field_simp [hP_pos.ne.symm, hq_pos.ne.symm]
  exact h_res

/--
  The Stall Length Lower Bound.
  If a_N is a massive spike (a_N ≥ C * P_N^2), then the sequence must take 
  at least M steps to reach the lattice threshold, where M is proportional to 
  the size of the spike.
-/
lemma stall_length_bound (N : ℕ) (hq : q > 0)
    (hSum : HasSum (fun k => 1 / (a k : ℝ)) (p / q))
    (hGe2 : ∀ k, a k ≥ 2) 
    (M : ℕ)
    (h_stall : ∀ k < M, a (N + k) ≥ a N) :
    (M : ℝ) / a N ≥ 1 / (q * P1 a N : ℝ) - ∑' k, (1 : ℝ) / (a (N + M + k) : ℝ) := by
  have h_gap := spike_lattice_gap a q p N hq hSum hGe2
  
  -- The sequence f(k) = 1 / a(N+k) is summable
  let f := fun k => (1 : ℝ) / (a (N + k) : ℝ)
  have h_summable : Summable f := (hSum.summable).comp_injective (add_right_injective N)
  
  -- Using hasSum_nat_add_iff to split the sum
  have h_split : HasSum (fun k => f (k + M)) (∑' k, f k - ∑ k ∈ range M, f k) := by
    apply (hasSum_nat_add_iff M).mpr
    have : HasSum f (∑' k, f k) := h_summable.hasSum
    have h_add : (∑' k, f k - ∑ k ∈ range M, f k) + ∑ k ∈ range M, f k = ∑' k, f k := by ring
    rw [← h_add] at this
    exact this
    
  have h_split_eq : ∑' k, f (k + M) = ∑' k, f k - ∑ k ∈ range M, f k := h_split.tsum_eq
  
  have h_comm : (fun k => f (k + M)) = (fun k => (1 : ℝ) / (a (N + M + k) : ℝ)) := by
    ext k
    dsimp [f]
    have h_idx : N + (k + M) = N + M + k := by omega
    rw [h_idx]
    
  rw [h_comm] at h_split_eq
  have h_rearrange : ∑' k, f k = (∑ k ∈ range M, f k) + ∑' k, (1 : ℝ) / (a (N + M + k) : ℝ) := by linarith
  
  have h_bound_part : (∑ k ∈ range M, f k) ≤ (M : ℝ) / a N := by
    have h_eq : (M : ℝ) / a N = ∑ k ∈ range M, (1 : ℝ) / (a N : ℝ) := by
      rw [sum_const, card_range, nsmul_eq_mul, mul_one_div]
    rw [h_eq]
    apply sum_le_sum
    intro i hi
    have hi_lt : i < M := mem_range.mp hi
    have h_ineq : a (N + i) ≥ a N := h_stall i hi_lt
    have h_pos : (a N : ℝ) > 0 := by exact_mod_cast (by linarith [hGe2 N] : a N > 0)
    have h_cast : (a N : ℝ) ≤ (a (N + i) : ℝ) := by exact_mod_cast h_ineq
    exact one_div_le_one_div_of_le h_pos h_cast
    
  dsimp [f] at h_rearrange h_bound_part
  linarith [h_gap, h_rearrange, h_bound_part]

/--
  The Wild Oscillator Contradiction.
  If a sequence attempts to grow with limsup β > 2, it must eventually produce 
  spikes a_N ≥ P_N^(2+ε). The resulting stall length M forces the prefix product 
  P_{N+M} to inflate factorially, which contradicts the growth hypothesis for the 
  subsequent terms.
-/
theorem wild_oscillator_contradiction (ε : ℝ) (hε : ε > 0)
    (a : ℕ → ℕ) (ha : ∀ n, a n ≥ 2)
    (h_rational : ∃ p q, q > 0 ∧ HasSum (fun n => 1 / (a n : ℝ)) (p / q))
    (h_growth : ∃ᶠ n in atTop, (a n : ℝ) ≥ (P1 a n : ℝ) ^ (2 + ε)) :
    False := by
  -- 1. Identify the spike N.
  -- 2. Use stall_length_bound to show M ≥ a_N / (2 q P_N).
  -- 3. Calculate Prefix Inflation: P_{N+M} ≥ P_N * a_N^M.
  -- 4. Show this inflation violates the general sequence bound.
  sorry
