import Mathlib

open Real

def is_stable_state (R1 R2 : ℝ) : Prop :=
  R1 > 0 ∧ R2 > R1 ∧ R1^2 > R2 - R1

theorem stability_extension (R1 R2 : ℝ) (h : is_stable_state R1 R2) :
    ∃ a_next : ℕ, 
      (a_next > 1) ∧ 
      (is_stable_state (a_next * R1 - 1) ((a_next - 1) * R2 - 1)) := by
  let t1 := 1 / R1
  let t2 := R2 / (R2 - R1)
  let t3 := (R1 + R2) / R1^2
  
  let a0 := max 1 (max t1 (max t2 t3))
  let a_next := ⌈a0⌉₊ + 1
  
  use a_next
  
  have h_a0_1 : 1 ≤ a0 := le_max_left 1 _
  have h_a0_t1 : t1 ≤ a0 := (le_max_left t1 _).trans (le_max_right 1 _)
  have h_a0_t2 : t2 ≤ a0 := (le_max_left t2 t3).trans ((le_max_right t1 _).trans (le_max_right 1 _))
  have h_a0_t3 : t3 ≤ a0 := (le_max_right t2 t3).trans ((le_max_right t1 _).trans (le_max_right 1 _))
  
  have ha_gt_a0 : (a_next : ℝ) > a0 := by
    calc (a_next : ℝ) = (⌈a0⌉₊ : ℝ) + 1 := by exact_mod_cast rfl
      _ ≥ a0 + 1 := by linarith [Nat.le_ceil a0]
      _ > a0 := by linarith

  have ha_gt1 : (a_next : ℝ) > 1 := by linarith
  have ha_gt_t1 : (a_next : ℝ) > t1 := by linarith
  have ha_gt_t2 : (a_next : ℝ) > t2 := by linarith
  have ha_gt_t3 : (a_next : ℝ) > t3 := by linarith
  
  have h_next_gt1 : a_next > 1 := by exact_mod_cast ha_gt1
  have h_a_ge1 : 1 ≤ a_next := by omega

  constructor
  · exact h_next_gt1
  · dsimp [is_stable_state]
    have h_cast : ((a_next - 1 : ℕ) : ℝ) = (a_next : ℝ) - 1 := by
      rw [Nat.cast_sub h_a_ge1, Nat.cast_one]
    constructor
    · -- a * R1 - 1 > 0
      have hd1 : R1 > 0 := h.1
      have h_t1 : t1 * R1 = 1 := by dsimp [t1]; exact div_mul_cancel₀ 1 (ne_of_gt hd1)
      nlinarith [ha_gt_t1, hd1, h_t1]
    · constructor
      · -- (a-1) * R2 - 1 > a * R1 - 1
        have hd2 : R2 - R1 > 0 := by linarith [h.2.1]
        have h_t2 : t2 * (R2 - R1) = R2 := by dsimp [t2]; exact div_mul_cancel₀ R2 (ne_of_gt hd2)
        have step1 : (a_next : ℝ) * (R2 - R1) > R2 := by nlinarith [ha_gt_t2, hd2, h_t2]
        have h_eq : ((a_next - 1 : ℕ) : ℝ) * R2 - 1 - ((a_next : ℝ) * R1 - 1) = (a_next : ℝ) * (R2 - R1) - R2 := by 
          rw [h_cast]; ring
        linarith [step1, h_eq]
      · -- Admissibility: R1'^2 > R2' - R1'
        have hc2 : R1^2 > 0 := pow_pos h.1 2
        have h_t3 : t3 * R1^2 = R1 + R2 := by dsimp [t3]; exact div_mul_cancel₀ (R1 + R2) (ne_of_gt hc2)
        have step2 : (a_next : ℝ) * R1^2 - (R1 + R2) > 0 := by nlinarith [ha_gt_t3, hc2, h_t3]
        have h_quad : (a_next : ℝ) * ((a_next : ℝ) * R1^2 - (R1 + R2)) > 0 := by nlinarith [ha_gt1, step2]
        have h_eq : ((a_next : ℝ) * R1 - 1)^2 - (((a_next - 1 : ℕ) : ℝ) * R2 - 1 - ((a_next : ℝ) * R1 - 1)) = (a_next : ℝ) * ((a_next : ℝ) * R1^2 - (R1 + R2)) + 1 + R2 := by
          rw [h_cast]
          ring
        have h_R2_pos : 1 + R2 > 0 := by linarith [h.1, h.2.1]
        linarith [h_quad, h_eq, h_R2_pos]
