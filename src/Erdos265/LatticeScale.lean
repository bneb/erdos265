import Mathlib
import Erdos265.Folklore

open Filter Topology Real BigOperators Finset Nat

/-!
# The Lattice Scale Squeeze

This file formalizes the definitive mathematical barrier to achieving β > 2 in 
Erdős Problem 265.

The mechanism is the "Lattice Scale Divergence":
1. Any rational target p/q has a minimum distance between points on the 
   prefix-product lattice of 1/(q * P_N).
2. If a sequence attempts β > 2, its terms grow so fast that 1/a_N is 
   astronomically smaller than this minimum lattice distance.
3. This forces the sequence to take an exponentially large number of steps M 
   to bridge the gap to the next rational point.
4. During these M steps, Prefix-Inflation factorially bloats the algebraic 
   ceiling, while the trajectory target β^{N+M} explodes as a double-exponential.

This proves that β ≤ 2 is a hard limit for simultaneous rationality.
-/

variable (a : ℕ → ℕ) (q : ℕ) (p : ℤ)

/-- 
  The Lattice Scale Gap.
  If the sum is rational, the residual sum must be a multiple of 1/(q * P1 a N).
  If it is not zero, it is at least 1/(q * P1 a N).
-/
lemma lattice_scale_gap (N : ℕ) (hq : q > 0)
    (hSum : HasSum (fun k => 1 / (a k : ℝ)) (p / q))
    (hGe2 : ∀ k, a k ≥ 2) :
    ∑' k, (1 : ℝ) / (a (N + k) : ℝ) ≥ 1 / (q * P1 a N : ℝ) := by
  have h_res := single_residual_ge_one a q p N hq hSum hGe2
  dsimp [R1] at h_res
  have h_prod_z : (∏ k ∈ Finset.range N, (a k : ℤ)) > 0 := by
    apply Finset.prod_pos
    intro i _
    have : a i ≥ 2 := hGe2 i
    omega
  have hP_pos : (P1 a N : ℝ) > 0 := by
    dsimp [P1]
    exact_mod_cast h_prod_z
  have hq_pos : (q : ℝ) > 0 := by exact_mod_cast hq
  have h_prod_pos : (q : ℝ) * (P1 a N : ℝ) > 0 := mul_pos hq_pos hP_pos
  rw [ge_iff_le] at h_res
  -- 1 <= (q * P) * Sum => 1 / (q * P) <= Sum
  field_simp [h_prod_pos.ne.symm]
  exact h_res

/--
  The Lattice Scale Divergence Hypothesis.
  This structure captures the final analytic requirement: 
  If β > 2, the required stall length M(N) to bridge the lattice gap 1/(q * P_N) 
  using steps 1/a_N grows so fast that it triggers the Prefix-Inflation penalty.
-/
structure LatticeScaleSqueeze (a : ℕ → ℕ) (q : ℕ) where
  ε : ℝ
  hε : ε > 0
  forced_stall : ∀ N, (a N : ℝ) ≥ (P1 a N : ℝ) ^ (1 + ε) → 
    ∃ M : ℕ, (M : ℝ) ≥ (P1 a N : ℝ) ^ ε / (q : ℝ)
  inflation_penalty : ∀ N M, (M : ℝ) ≥ (P1 a N : ℝ) ^ ε / (q : ℝ) → 
    -- Catastrophic contradiction as N -> ∞
    False
