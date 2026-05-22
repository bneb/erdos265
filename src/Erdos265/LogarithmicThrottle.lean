import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Erdos265.ValuationRatchet

open BigOperators Filter Topology

/-!
# Erdős Problem 265: The Logarithmic Throttle
-/

noncomputable section

def energy_state (X P : ℕ → ℤ) (n : ℕ) : ℝ :=
  Real.log (P n) - Real.log (X n)

theorem linear_difference_eq (X P : ℕ → ℤ) 
    (h_P_succ : ∀ n, P (n + 1) = P n * X n)
    (h_X_pos : ∀ n, X n > 0) (h_P_pos : ∀ n, P n > 0) (n : ℕ) :
    Real.log (X (n + 1)) - 2 * Real.log (X n) = 
    energy_state X P n - energy_state X P (n + 1) := by
  simp [energy_state]
  have h_P_succ_n := h_P_succ n
  have h_P_pos_n := h_P_pos n
  have h_X_pos_n := h_X_pos n
  have h_P_succ_pos : P (n + 1) > 0 := by
    rw [h_P_succ_n]
    exact Int.mul_pos h_P_pos_n h_X_pos_n
  rw [h_P_succ_n]
  push_cast
  have h_log_mul : Real.log (↑(P n) * ↑(X n)) = Real.log (P n) + Real.log (X n) := by
    apply Real.log_mul
    · norm_cast; linarith
    · norm_cast; linarith
  rw [h_log_mul]
  ring

theorem logarithmic_throttle (X P : ℕ → ℤ) 
    (h_P_succ : ∀ n, P (n + 1) = P n * X n)
    (h_X_pos : ∀ n, X n > 0) (h_P_pos : ∀ n, P n > 0) (M : ℕ) (hM : M ≥ 2) :
    (Real.log (X M) / (2^M : ℝ)) = 
    (Real.log (X 1) / 2) + (energy_state X P 1 / 4) 
    - (energy_state X P M / (2^M : ℝ))
    - (∑ n ∈ Finset.Ico 2 M, (energy_state X P n / (2^(n + 1) : ℝ))) := by
  induction' hM with k hk ih
  · have h_lin := linear_difference_eq X P h_P_succ h_X_pos h_P_pos 1
    have h_sum : (∑ n ∈ Finset.Ico 2 2, (energy_state X P n / (2^(n + 1) : ℝ))) = 0 := by simp
    rw [h_sum]
    have h_num : Real.log (X 2) = 2 * Real.log (X 1) + energy_state X P 1 - energy_state X P 2 := by linarith [h_lin]
    rw [h_num]
    ring
  · have h_sum : (∑ n ∈ Finset.Ico 2 (k + 1), (energy_state X P n / (2^(n + 1) : ℝ))) =
                 (∑ n ∈ Finset.Ico 2 k, (energy_state X P n / (2^(n + 1) : ℝ))) + energy_state X P k / (2^(k + 1) : ℝ) := by
      rw [Finset.sum_Ico_succ_top hk]
    rw [h_sum]
    have h_lin := linear_difference_eq X P h_P_succ h_X_pos h_P_pos k
    have h_pow : (2^(k + 1) : ℝ) = 2 * 2^k := by ring
    have h_log_k_1 : Real.log (X (k + 1)) = 2 * Real.log (X k) + energy_state X P k - energy_state X P (k + 1) := by linarith [h_lin]
    rw [h_log_k_1]
    rw [h_pow]
    have h_algebra : (2 * Real.log (X k) + energy_state X P k - energy_state X P (k + 1)) / (2 * 2^k : ℝ) = 
      Real.log (X k) / 2^k + energy_state X P k / (2 * 2^k : ℝ) - energy_state X P (k + 1) / (2 * 2^k : ℝ) := by ring
    rw [h_algebra]
    rw [ih]
    ring

end