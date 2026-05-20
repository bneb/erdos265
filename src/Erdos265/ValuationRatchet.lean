import Mathlib

/-!
# Erdős 265: The 2-Adic Coupling Ratchet

This file proves that because X_N is universally even, the exact coupling 
variable C_N is forced to absorb an exponentially growing 2-adic valuation, 
shattering any hypothesis that the sub-greedy domain permits a bounded coupling.
-/

variable (C X P : ℕ → ℤ)

/-- 
  **The Valuation Ratchet**
  C_N accumulates powers of 2 linearly with N.
-/
theorem exact_coupling_valuation_growth
    (h_X_even : ∀ N, 2 ∣ X N)
    (h_C_succ : ∀ N, C (N + 1) = X N * C N - P N)
    (h_P_bound : ∀ N, (2^N : ℤ) ∣ P N) :
    ∀ N, (2^(N - 1) : ℤ) ∣ C N := by
  intro N
  induction' N with n ih
  · simp
  · cases n with
    | zero =>
      simp
    | succ n =>
      -- Goal: 2^(n + 1) | C (n + 2)
      have h_step : (2 : ℤ) ^ (n + 1) ∣ X (n + 1) * C (n + 1) - P (n + 1) := by
        apply dvd_sub
        · obtain ⟨x, hx⟩ := h_X_even (n + 1)
          rw [hx, mul_assoc]
          have h_cn : (2 : ℤ) ^ n ∣ C (n + 1) := by
            have h_idx : n + 1 - 1 = n := rfl
            rw [← h_idx]
            exact ih
          obtain ⟨c, hc⟩ := h_cn
          rw [hc]
          have : 2 * (x * ((2 : ℤ) ^ n * c)) = (x * c) * ((2 : ℤ) ^ n * 2) := by ring
          rw [this, ← pow_succ]
          apply dvd_mul_left
        · exact h_P_bound (n + 1)
      have h_pow_idx : n + 2 - 1 = n + 1 := rfl
      rw [h_pow_idx, h_C_succ]
      exact h_step





/-- 
  **The Exponential Divergence**
  Because C_N is a strictly positive integer, divisibility forces 
  exponential real-valued divergence.
-/
theorem exact_coupling_exponential_divergence
    (h_X_even : ∀ N, 2 ∣ X N)
    (h_C_succ : ∀ N, C (N + 1) = X N * C N - P N)
    (h_P_bound : ∀ N, (2^N : ℤ) ∣ P N)
    (h_C_pos : ∀ N, C N > 0) :
    ∀ N, (2 : ℤ)^(N - 1) ≤ C N := by
  intro N
  have h_dvd := exact_coupling_valuation_growth C X P h_X_even h_C_succ h_P_bound N
  have h_pos := h_C_pos N
  apply Int.le_of_dvd h_pos h_dvd
