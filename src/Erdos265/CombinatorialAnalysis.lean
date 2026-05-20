import Mathlib
import Erdos265.ProblemStatement
import Erdos265.CombinatorialSqueeze

open Filter Topology Real BigOperators Finset Nat

/-!
# Combinatorial Analysis of the FSM

We have established that `(C_N mod q, P_N mod q)` forms a finite state machine.
By the Pigeonhole Principle, the sequence of states must eventually loop or absorb.
We now analyze the specific structure of the trajectory when `q = q₁`.
-/

variable (a : ℕ → ℕ) (q₁ : ℕ)

lemma local_ascFactorial_eq_prod_range (start q : ℕ) : 
    start.ascFactorial q = ∏ k ∈ range q, (start + k) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.ascFactorial_succ, ih, Finset.prod_range_succ]
    ring

lemma consecutive_prod_dvd_q (start q : ℕ) (hq : q > 0) : q ∣ ∏ k ∈ range q, (start + k) := by
  have h1 : q.factorial ∣ start.ascFactorial q := Nat.factorial_dvd_ascFactorial start q
  have h2 : start.ascFactorial q = ∏ k ∈ range q, (start + k) := local_ascFactorial_eq_prod_range start q
  rw [h2] at h1
  have h3 : q ∣ q.factorial := Nat.dvd_factorial hq le_rfl
  exact Nat.dvd_trans h3 h1

lemma sub_prod_dvd_of_le (start q M : ℕ) (hq : q > 0) (hM : M ≥ q) : 
    q ∣ ∏ k ∈ range M, (start + k) := by
  have h_range : range M = range q ∪ Ico q M := by
    ext x
    rw [mem_range, mem_union, mem_range, mem_Ico]
    omega
  rw [h_range, Finset.prod_union]
  · apply dvd_mul_of_dvd_left
    exact consecutive_prod_dvd_q start q hq
  · rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    rw [mem_range] at hx
    rw [mem_Ico] at hy
    omega

/-- 
  If a sequence enters a slow phase of length M ≥ q₁, the prefix product P_1 
  absorbs M consecutive integers and unconditionally hits the 0 absorbing state mod q₁.
-/
lemma slow_phase_forces_absorption (N M : ℕ) (hq1 : q₁ > 0) (hM : M ≥ q₁)
    (h_slow : ∀ k ∈ Finset.range M, a (N + k + 1) = a (N + k) + 1) :
    (q₁ : ℤ) ∣ (∏ k ∈ Finset.range (N + M), (a k : ℤ)) := by
  have h_split : ∏ k ∈ Finset.range (N + M), (a k : ℤ) = (∏ k ∈ Finset.range N, (a k : ℤ)) * (∏ k ∈ Finset.range M, (a (N + k) : ℤ)) := by
    rw [Finset.prod_range_add]
  rw [h_split]
  apply dvd_mul_of_dvd_right
  have h_a_val : ∀ k, k ≤ M → a (N + k) = a N + k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hk_lt : k < M := by omega
      have h_step : a (N + k + 1) = a (N + k) + 1 := h_slow k (Finset.mem_range.mpr hk_lt)
      have h_ih_val : a (N + k) = a N + k := ih (by omega)
      have h_assoc : N + (k + 1) = N + k + 1 := by omega
      rw [h_assoc, h_step, h_ih_val]
      omega
  have h_prod_eq : ∏ k ∈ Finset.range M, (a (N + k) : ℤ) = ∏ k ∈ Finset.range M, ((a N + k : ℕ) : ℤ) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hk_le : k ≤ M := by
      have : k < M := Finset.mem_range.mp hk
      omega
    rw [h_a_val k hk_le]
  rw [h_prod_eq]
  have h_dvd_nat := sub_prod_dvd_of_le (a N) q₁ M hq1 hM
  exact_mod_cast h_dvd_nat
