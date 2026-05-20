import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Topology.Instances.Rat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open BigOperators Filter Topology

/-!
# Erdős Problem 265: Formal Statement & Witnesses
-/

/-- An Erdős sequence is a sequence of integers all ≥ 2. -/
def is_erdos_seq (a : ℕ → ℕ) : Prop :=
  ∀ n, a n ≥ 2

/-- The sum of the reciprocals of a sequence converges to a rational number. -/
def has_rational_sum (a : ℕ → ℕ) : Prop :=
  ∃ q : ℚ, HasSum (fun n => (1 : ℝ) / (a n)) (q : ℝ)

/-- 
  The Erdős 265 Problem constraints:
  Both ∑ 1/a_n and ∑ 1/(a_n - 1) must be rational.
-/
def erdos_problem_265 (a : ℕ → ℕ) : Prop :=
  is_erdos_seq a ∧ has_rational_sum a ∧ has_rational_sum (fun n => a n - 1)

/-- The Sylvester sequence: a_0 = 2, a_{n+1} = a_n^2 - a_n + 1. -/
def sylvester_seq : ℕ → ℕ
  | 0 => 2
  | n + 1 => (sylvester_seq n)^2 - (sylvester_seq n) + 1

theorem sylvester_ge_two (n : ℕ) : sylvester_seq n ≥ 2 := by
  induction n with
  | zero => exact le_refl 2
  | succ n ih =>
    dsimp [sylvester_seq]
    have h1 : sylvester_seq n * (sylvester_seq n - 1) ≥ 2 * (2 - 1) := Nat.mul_le_mul ih (Nat.sub_le_sub_right ih 1)
    have h2 : sylvester_seq n ^ 2 - sylvester_seq n = sylvester_seq n * (sylvester_seq n - 1) := by
      rw [Nat.pow_two, Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [h2]
    linarith


lemma sylvester_ge_n_plus_two (n : ℕ) : sylvester_seq n ≥ n + 2 := by
  induction n with
  | zero => exact le_refl 2
  | succ n ih =>
    dsimp [sylvester_seq]
    have h2 : sylvester_seq n ^ 2 - sylvester_seq n = sylvester_seq n * (sylvester_seq n - 1) := by
      rw [Nat.pow_two, Nat.mul_sub_left_distrib, Nat.mul_one]
    have h3 : sylvester_seq n * (sylvester_seq n - 1) ≥ sylvester_seq n * 1 := by
      apply Nat.mul_le_mul_left
      have : sylvester_seq n ≥ 2 := sylvester_ge_two n
      omega
    have h4 : sylvester_seq n * 1 = sylvester_seq n := Nat.mul_one _
    rw [h2]
    omega

lemma sylvester_step_real (n : ℕ) : (sylvester_seq (n + 1) : ℝ) - 1 = (sylvester_seq n : ℝ) * ((sylvester_seq n : ℝ) - 1) := by
  have : sylvester_seq (n + 1) = sylvester_seq n ^ 2 - sylvester_seq n + 1 := rfl
  have h2 : sylvester_seq (n + 1) - 1 = sylvester_seq n ^ 2 - sylvester_seq n := by omega
  have h3 : (sylvester_seq n : ℝ) ^ 2 - (sylvester_seq n : ℝ) = (sylvester_seq n : ℝ) * ((sylvester_seq n : ℝ) - 1) := by ring
  have h4 : ((sylvester_seq (n + 1) - 1 : ℕ) : ℝ) = (sylvester_seq (n + 1) : ℝ) - 1 := by
    have : 1 ≤ sylvester_seq (n + 1) := by have h := sylvester_ge_two (n + 1); omega
    rw [Nat.cast_sub this]
    push_cast; rfl
  have h5 : ((sylvester_seq n ^ 2 - sylvester_seq n : ℕ) : ℝ) = (sylvester_seq n : ℝ) ^ 2 - (sylvester_seq n : ℝ) := by
    have : sylvester_seq n ≤ sylvester_seq n ^ 2 := by nlinarith
    rw [Nat.cast_sub this]
    push_cast; rfl
  rw [← h4, h2, h5, h3]

lemma sylvester_inv_diff (n : ℕ) : (1 : ℝ) / (sylvester_seq n : ℝ) = 1 / ((sylvester_seq n : ℝ) - 1) - 1 / ((sylvester_seq (n + 1) : ℝ) - 1) := by
  rw [sylvester_step_real n]
  have h1 : (sylvester_seq n : ℝ) ≥ 2 := by exact_mod_cast sylvester_ge_two n
  have hn_ne : (sylvester_seq n : ℝ) ≠ 0 := by linarith
  have hnm1_ne : (sylvester_seq n : ℝ) - 1 ≠ 0 := by linarith
  field_simp

theorem sylvester_sum_recip : 
    HasSum (fun n => (1 : ℝ) / (sylvester_seq n)) (1 : ℝ) := by
  have h_telescope : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 : ℝ) / (sylvester_seq n) = 1 - 1 / ((sylvester_seq N : ℝ) - 1) := by
    intro N
    induction N with
    | zero => 
      dsimp [sylvester_seq]
      have : (2:ℝ) - 1 = 1 := by norm_num
      rw [this]
      norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, sylvester_inv_diff N]
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have h_tendsto : Tendsto (fun N => 1 - 1 / ((sylvester_seq N : ℝ) - 1)) atTop (nhds (1 - 0)) := by
      apply Tendsto.sub tendsto_const_nhds
      have h_seq_tendsto : Tendsto (fun N => (sylvester_seq N : ℝ) - 1) atTop atTop := by
        apply tendsto_atTop_atTop.mpr
        intro b
        use ⌈b⌉₊
        intro n hn
        have h1 : (sylvester_seq n : ℝ) - 1 ≥ (n + 1 : ℝ) := by
          have ht : sylvester_seq n ≥ n + 2 := sylvester_ge_n_plus_two n
          have htr : (sylvester_seq n : ℝ) ≥ (n + 2 : ℝ) := by exact_mod_cast ht
          linarith
        have h2 : (n + 1 : ℝ) ≥ (⌈b⌉₊ + 1 : ℝ) := by 
          have ht : n ≥ ⌈b⌉₊ := hn
          have htr : (n : ℝ) ≥ (⌈b⌉₊ : ℝ) := by exact_mod_cast ht
          linarith
        have h3 : (⌈b⌉₊ + 1 : ℝ) ≥ b := by 
          have : (⌈b⌉₊ : ℝ) ≥ b := Nat.le_ceil b
          linarith
        linarith
      have : (fun N => 1 / ((sylvester_seq N : ℝ) - 1)) = (fun N => ((sylvester_seq N : ℝ) - 1)⁻¹) := by
        ext N; rw [one_div]
      rw [this]
      exact tendsto_inv_atTop_zero.comp h_seq_tendsto
    have h_eq : 1 - 0 = (1 : ℝ) := by ring
    rw [h_eq] at h_tendsto
    have h_simp : (fun (n : ℕ) => ∑ i ∈ Finset.range n, 1 / (sylvester_seq i : ℝ)) = (fun N => 1 - 1 / ((sylvester_seq N : ℝ) - 1)) := by
      ext N; rw [h_telescope]
    rw [h_simp]
    exact h_tendsto
  · intro n
    have : (sylvester_seq n : ℝ) ≥ 2 := by exact_mod_cast sylvester_ge_two n
    positivity

-- Kovač-Tao (2024) proven via measure theory
structure KovacTaoExists : Prop :=
  (erdos_problem_inhabited : ∃ a, erdos_problem_265 a)
