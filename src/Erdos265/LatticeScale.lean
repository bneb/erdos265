import Mathlib
import Erdos265.Folklore

open Filter Topology Real BigOperators Finset Nat

/-!
# The Lattice Barrier Theorem

This file formalizes the Diophantine obstruction to achieving β > 2 in 
Erdős Problem 265. 

The core result is that for any rational targets, the sequence terms are 
constrained by a "Lattice Gap" Δ = 1/(q P_N). If a sequence attempts growth 
at β > 2, its steps 1/a_N become smaller than this resolution, necessitating 
a stall length that factorially inflates the prefix product.
-/

variable (a : ℕ → ℕ) (q : ℕ) (p : ℤ)

/-- 
  The Lattice Scale Gap.
  If the sum is rational, the non-zero residual sum is at least 1/(q * P_N).
-/
lemma lattice_scale_gap (N : ℕ) (hq : q > 0)
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
