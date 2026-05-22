import Mathlib
import Erdos265.ValuationRatchet
open Filter Topology Set

/-- A convergent sequence of integers is eventually constant. -/
theorem tendsto_int_eventually_constant {f : ℕ → ℤ} {M : ℝ} (h : Tendsto (fun n => (f n : ℝ)) atTop (nhds M)) : ∃ N, ∀ n ≥ N, f n = f N := by
  have h_cau : CauchySeq (fun n => (f n : ℝ)) := h.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp h_cau (1/2) (by norm_num)
  use N; intro n hn
  specialize hN n hn N (le_refl N)
  rw [dist_eq_norm] at hN
  have h_int : ‖(f n : ℝ) - (f N : ℝ)‖ = (|(f n - f N)| : ℝ) := by
    simp [Real.norm_eq_abs]
  rw [h_int] at hN
  have h_abs_lt : (|(f n - f N)| : ℝ) < 1 := by linarith
  norm_cast at h_abs_lt
  have : -1 < f n - f N ∧ f n - f N < 1 := by
    rw [abs_lt] at h_abs_lt
    exact h_abs_lt
  omega

/-- An eventually constant sequence is bounded. -/
theorem bounded_of_eventually_const {u : ℕ → ℤ} {N : ℕ} (h : ∀ n ≥ N, u n = u N) : ∃ B : ℤ, ∀ n, u n ≤ B := by
  classical
  let s := (Finset.range (N + 1)).image u
  have h_s : s.Nonempty := by use u N; apply Finset.mem_image.mpr; use N; simp
  use s.max' h_s
  intro n
  by_cases hn : n ≤ N
  · apply Finset.le_max'; apply Finset.mem_image.mpr; use n; simp [hn]
  · have : u n = u N := h n (by linarith)
    rw [this]
    apply Finset.le_max'; apply Finset.mem_image.mpr; use N; simp

/-- An eventually bounded sequence is bounded. -/
theorem bounded_of_eventually_bounded {u : ℕ → ℝ} {B : ℝ} {N : ℕ} (h : ∀ n ≥ N, u n ≤ B) : ∃ B', ∀ n, u n ≤ B' := by
  classical
  if h_N : N = 0 then
    use B; intro n; apply h; linarith
  else
    let s := (Finset.range N).image u
    have h_s : s.Nonempty := by use u 0; apply Finset.mem_image.mpr; use 0; simp [Nat.pos_of_ne_zero h_N]
    use max (s.max' h_s) B
    intro n
    by_cases hn : n < N
    · apply le_trans _ (le_max_left _ _)
      apply Finset.le_max'; apply Finset.mem_image.mpr; use n; simp [hn]
    · apply le_trans (h n (not_lt.mp hn)) (le_max_right _ _)

/-- Generalization of integer sequence contradiction to any real target, supporting subsequences. -/
theorem integer_seq_not_tendsto_any_subseq
    (C X P : ℕ → ℤ)
    (h_X_even : ∀ n, (2 : ℤ) ∣ X n)
    (h_C_succ : ∀ n, C (n + 1) = X n * C n - P n)
    (h_P_bound : ∀ n, (2 ^ n : ℤ) ∣ P n)
    (h_C_pos : ∀ n, C n > 0)
    (f : ℕ → ℕ) (hf_mono : StrictMono f)
    (l : ℝ) :
    ¬ Tendsto (fun k => (C (f k) : ℝ)) atTop (nhds l) := by
  intro h_tendsto
  obtain ⟨K, hK⟩ := tendsto_int_eventually_constant h_tendsto
  let C_const := C (f K)
  have h_ratchet := exact_coupling_exponential_divergence C X P h_X_even h_C_succ h_P_bound h_C_pos
  -- Contradiction: C(f k) is constant C_const for k >= K, but f k -> inf so C(f k) -> inf.
  have h_unbounded : ∀ B' : ℤ, ∃ k, B' < (2 : ℤ) ^ (f k - 1) := by
    intro B'
    have h_pow : Tendsto (fun n : ℕ => (2 : ℤ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    obtain ⟨n, hn⟩ := (h_pow.eventually (eventually_gt_atTop B')).exists
    obtain ⟨k, hk⟩ := hf_mono.tendsto_atTop.eventually (eventually_ge_atTop (n + 1)) |>.exists
    use k
    have : (2 : ℤ)^n ≤ (2 : ℤ)^(f k - 1) := by
      have h12 : (1 : ℤ) ≤ 2 := by norm_num
      apply pow_le_pow_right₀ h12
      omega
    omega
  obtain ⟨k, hk⟩ := h_unbounded C_const
  let k_idx := max k K
  have h_val := h_ratchet (f k_idx)
  have h_eq : C (f k_idx) = C_const := hK k_idx (le_max_right _ _)
  rw [h_eq] at h_val
  have h_growth : (2 : ℤ)^(f k - 1) ≤ (2 : ℤ)^(f k_idx - 1) := by
    have h12 : (1 : ℤ) ≤ 2 := by norm_num
    apply pow_le_pow_right₀ h12
    apply tsub_le_tsub_right
    exact hf_mono.monotone (le_max_left _ _)
  linarith
