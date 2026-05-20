import Erdos265.ProblemStatement
import Erdos265.AsymptoticSqueeze
import Erdos265.AsymptoticLemmas

open Filter Topology

/-!
# Erdős Problem 265: The Final Resolution
-/

/-- 
  **The Erdős Ceiling Resolution**
  Any sequence satisfying the simultaneous rationality constraints 
  must have a doubly-exponential growth limit supreme bounded by 1.
-/
theorem erdos_ceiling_resolution
    (a : ℕ → ℕ)
    (ha : erdos_problem_265 a) :
    limsup (fun n => (a n : ℝ)^(1 / (2^n : ℝ))) atTop ≤ 1 := by
  by_contra h_gt_one
  push Not at h_gt_one
  
  -- Extract subsequence f k such that u (f k) → L' where L' > 1
  obtain ⟨f, L_prime, hf_mono, hL_prime_gt, hf_lim⟩ := extract_fast_subsequence a ha.1 h_gt_one
  
  -- obtain erdos variables and the contradiction property
  obtain ⟨C, X, P, d, hX_even, hC_succ, hP_bound, hC_pos, h_conv⟩ := erdos_bridge a ha
  
  -- If we reached here, use the fact that erdos_bridge proves False via exfalso
  -- if we can provide it with a convergent fast-growing subsequence.
  obtain ⟨M, hM_lim⟩ := h_conv L_prime hL_prime_gt f hf_mono hf_lim
  
  -- Contradiction: C(f k) is an integer sequence converging to M,
  -- but integer convergence is impossible for divergent sequences.
  exact integer_seq_not_tendsto_any_subseq C X P hX_even hC_succ hP_bound hC_pos f hf_mono M hM_lim
