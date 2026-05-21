import Mathlib
import Erdos265.ProblemStatement

open Filter Topology Real BigOperators

/-- Admissibility condition for dual residuals. -/
def is_stable_state (R1 R2 : ℝ) : Prop :=
  R1 > 0 ∧ R2 > R1 ∧ R1^2 > R2 - R1

/-- Witness Statement: The stable region is non-empty. -/
theorem stable_region_inhabited : ∃ R1 R2 : ℚ, is_stable_state (R1 : ℝ) (R2 : ℝ) := by
  -- Try R1 = 1/2, R2 = 1/2 + 1/8 = 5/8.
  -- R1^2 = 1/4.
  -- R2 - R1 = 1/8.
  -- 1/4 > 1/8. 
  use 1/2, 5/8
  dsimp [is_stable_state]
  norm_num

/-- The Stability Extension Theorem. -/
theorem stability_extension (R1 R2 : ℝ) (h : is_stable_state R1 R2) :
    ∃ a_next : ℕ, 
      (a_next > 1) ∧ 
      (is_stable_state (a_next * R1 - 1) ((a_next - 1) * R2 - 1)) := by
  let t1 := 1 / R1
  let t2 := R2 / (R2 - R1)
  let t3 := (R1 + R2) / R1^2
  let target := max 2 (max t1 (max t2 t3))
  let a_next := ⌈target⌉₊ + 1
  use a_next
  
  have ha_gt_target : (a_next : ℝ) > target := by
    calc (a_next : ℝ) = (⌈target⌉₊ : ℝ) + 1 := by norm_cast
      _ ≥ target + 1 := by linarith [Nat.le_ceil target]
      _ > target := by linarith

  have h_a_ge1 : 1 ≤ a_next := by 
    have : target ≥ 2 := le_max_left 2 _
    linarith

  have h_cast : ((a_next - 1 : ℕ) : ℝ) = (a_next : ℝ) - 1 := by
    rw [Nat.cast_sub h_a_ge1, Nat.cast_one]

  constructor
  · have : target ≥ 2 := le_max_left 2 _
    linarith
  · dsimp [is_stable_state]
    constructor
    · have : target ≥ t1 := (le_max_right 2 _).trans (le_max_left t1 _)
      linarith
    · constructor
      · rw [h_cast]
        have : target ≥ t2 := (le_max_right 2 _).trans ((le_max_right t1 _).trans (le_max_left t2 t3))
        linarith
      · rw [h_cast]
        have : R1^2 > 0 := pow_pos h.1 2
        have : target ≥ t3 := (le_max_right 2 _).trans ((le_max_right t1 _).trans (le_max_right t2 t3))
        nlinarith

/-- Induction bridge: Constructing an infinite sequence of stable states. -/
theorem exists_infinite_stable_sequence (R1 R2 : ℝ) (h : is_stable_state R1 R2) :
    ∃ (a : ℕ → ℕ) (r1 r2 : ℕ → ℝ), 
      (∀ n, a n > 1) ∧ 
      (r1 0 = R1) ∧ (r2 0 = R2) ∧
      (∀ n, is_stable_state (r1 n) (r2 n)) ∧
      (∀ n, r1 (n + 1) = (a n : ℝ) * (r1 n) - 1) ∧
      (∀ n, r2 (n + 1) = ((a n : ℝ) - 1) * (r2 n) - 1) := by
  let f : (Σ' (s : ℝ × ℝ), is_stable_state s.1 s.2) → (Σ' (s : ℝ × ℝ), is_stable_state s.1 s.2) := 
    fun ⟨⟨R1, R2⟩, h⟩ => 
      let a := Classical.choose (stability_extension R1 R2 h)
      let ha := Classical.choose_spec (stability_extension R1 R2 h)
      ⟨⟨(a : ℝ) * R1 - 1, ((a : ℝ) - 1) * R2 - 1⟩, ha.2⟩
  let S : ℕ → (Σ' (s : ℝ × ℝ), is_stable_state s.1 s.2) := 
    fun n => Nat.rec (⟨⟨R1, R2⟩, h⟩) (fun _ prev => f prev) n
  let a := fun n => Classical.choose (stability_extension (S n).1.1 (S n).1.2 (S n).2)
  use a, (fun n => (S n).1.1), (fun n => (S n).1.2)
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro n; exact (Classical.choose_spec (stability_extension (S n).1.1 (S n).1.2 (S n).2)).1
  · intro n; exact (S n).2
  · intro n; show (S (n + 1)).1.1 = (a n : ℝ) * (S n).1.1 - 1; rfl
  · intro n; show (S (n + 1)).1.2 = ((a n : ℝ) - 1) * (S n).1.2 - 1; rfl

