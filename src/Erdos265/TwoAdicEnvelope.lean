import Mathlib
import Erdos265.ProblemStatement
import Erdos265.ValuationRatchet

open Filter Topology Real BigOperators

/-- Prefix products -/
def P1 (a : ℕ → ℕ) (N : ℕ) : ℕ := (∏ k ∈ Finset.range N, a k)
def P2 (a : ℕ → ℕ) (N : ℕ) : ℕ := (∏ k ∈ Finset.range N, (a k - 1))

/--
  The β ≤ 3 Algebraic Ceiling Theorem.
  Conditional on the analytic squeeze hypothesis.
-/
theorem algebraic_ceiling_beta_3 (C : ℕ → ℤ) (a : ℕ → ℕ) (h_er : erdos_problem_265 a) 
    (h_ratchet : ∀ N, (2^(N-1) : ℝ) ≤ (C N : ℝ))
    (h_squeeze : ∀ N, (C N : ℝ) ≤ (P1 a N * P2 a N : ℝ) / ((a N : ℝ) - 1)) :
    ∀ N, (a N : ℝ) ≤ (P1 a N * P2 a N : ℝ) / 2^(N-1) + 1 := by
  intro N
  have h1 := h_ratchet N
  have h2 := h_squeeze N

  have h3 : (2^(N-1) : ℝ) ≤ (P1 a N * P2 a N : ℝ) / ((a N : ℝ) - 1) := h1.trans h2
  have ha_gt1 : a N ≥ 2 := h_er.1 N
  have hc : (a N : ℝ) - 1 > 0 := by
    have : (a N : ℝ) ≥ 2 := by exact_mod_cast ha_gt1
    linarith
  have ha : (2^(N-1) : ℝ) > 0 := by positivity
  
  have h_mul : (2^(N-1) : ℝ) * ((a N : ℝ) - 1) ≤ (P1 a N * P2 a N : ℝ) := (le_div_iff₀ hc).mp h3
  have h_div : ((a N : ℝ) - 1) ≤ (P1 a N * P2 a N : ℝ) / (2^(N-1) : ℝ) := (le_div_iff₀ ha).mpr (by linarith)
  linarith
