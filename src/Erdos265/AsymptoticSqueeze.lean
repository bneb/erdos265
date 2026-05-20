import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import Erdos265.ProblemStatement
import Erdos265.AsymptoticLemmas

open Filter Topology Real BigOperators Finset

noncomputable section

-- ============================================================
-- LEMMA B: X_{n+1}/X_n → ∞
-- ============================================================

lemma seq_tendsto_atTop_of_rpow_tendsto
    {a : ℕ → ℝ} {L : ℝ} (hL : L > 1)
    (h : Tendsto (fun n => a n ^ ((1:ℝ) / 2^n)) atTop (nhds L))
    (ha_pos : ∀ n, 0 < a n) :
    Tendsto a atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  have hM : (L + 1) / 2 > 1 := by linarith
  have h_lb : ∀ᶠ n in atTop, (L + 1) / 2 ≤ a n ^ ((1:ℝ) / 2^n) :=
    h.eventually (Ici_mem_nhds (by linarith))
  have h_pow : ∀ᶠ n in atTop, (b : ℝ) ≤ ((L + 1) / 2) ^ (2^n : ℝ) := by
    have h_pow_tendsto : Tendsto (fun n => (2:ℝ)^n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h_M_tendsto : Tendsto (fun x : ℝ => ((L + 1) / 2) ^ x) atTop atTop := by
      have h_eq : (fun x : ℝ => ((L + 1) / 2) ^ x) = (fun x : ℝ => exp (log ((L + 1) / 2) * x)) := by
        ext x; rw [Real.rpow_def_of_pos (by linarith)]
      rw [h_eq]
      apply tendsto_exp_atTop.comp
      exact (tendsto_const_mul_atTop_iff_pos (tendsto_id (α:=ℝ))).mpr (log_pos hM)
    have h_comp : Tendsto (fun n => ((L + 1) / 2) ^ (2:ℝ)^n) atTop atTop :=
      h_M_tendsto.comp h_pow_tendsto
    exact h_comp.eventually (eventually_ge_atTop b)
  have h_all : ∀ᶠ n in atTop, (((L + 1) / 2) ≤ a n ^ ((1:ℝ) / 2^n)) ∧ ((b : ℝ) ≤ ((L + 1) / 2) ^ (2^n : ℝ)) := h_lb.and h_pow
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_all
  use N
  intro n hn
  have ⟨hn_lb, hn_pow⟩ := hN n hn
  have h2n_pos : (0:ℝ) < 2^n := by positivity
  have h_an : ((L + 1) / 2) ^ (2^n : ℝ) ≤ a n := by
    have h_M_nonneg : 0 ≤ ((L + 1) / 2) := by linarith
    have := Real.rpow_le_rpow h_M_nonneg hn_lb (le_of_lt h2n_pos)
    have hrw : (a n ^ ((1:ℝ) / 2^n)) ^ (2^n : ℝ) = a n := by
      rw [← Real.rpow_mul (le_of_lt (ha_pos n))]
      have h_mul : (1 : ℝ) / 2^n * 2^n = 1 := div_mul_cancel₀ 1 (ne_of_gt h2n_pos)
      rw [h_mul, Real.rpow_one]
    rwa [hrw] at this
  linarith

lemma lower_bound_from_tendsto
    {a : ℕ → ℝ} {L ε : ℝ} (hε : 0 < ε) (hLε : L - ε > 1)
    (h : Tendsto (fun n => a n ^ ((1:ℝ) / 2^n)) atTop (nhds L))
    (ha_pos : ∀ n, 0 < a n) :
    ∀ᶠ n in atTop, (L - ε) ^ (2^n : ℝ) ≤ a n := by
  have h_lb : ∀ᶠ n in atTop, L - ε ≤ a n ^ ((1:ℝ) / 2^n) :=
    h.eventually (Ici_mem_nhds (by linarith : L - ε < L))
  filter_upwards [h_lb] with n hn
  have h2n_pos : (0:ℝ) < 2^n := by positivity
  have h_base_nonneg : 0 ≤ L - ε := by linarith
  have := Real.rpow_le_rpow h_base_nonneg hn (le_of_lt h2n_pos)
  have hrw : (a n ^ ((1:ℝ) / 2^n)) ^ (2^n : ℝ) = a n := by
    rw [← Real.rpow_mul (le_of_lt (ha_pos n))]
    have h_mul : (1 : ℝ) / 2^n * 2^n = 1 := div_mul_cancel₀ 1 (ne_of_gt h2n_pos)
    rw [h_mul, Real.rpow_one]
  rwa [hrw] at this

lemma upper_bound_from_tendsto
    {a : ℕ → ℝ} {L ε : ℝ} (hε : 0 < ε)
    (h : Tendsto (fun n => a n ^ ((1:ℝ) / 2^n)) atTop (nhds L))
    (ha_pos : ∀ n, 0 < a n) :
    ∀ᶠ n in atTop, a n ≤ (L + ε) ^ (2^n : ℝ) := by
  have h_ub : ∀ᶠ n in atTop, a n ^ ((1:ℝ) / 2^n) ≤ L + ε :=
    h.eventually (Iic_mem_nhds (by linarith : L < L + ε))
  filter_upwards [h_ub] with n hn
  have h2n_pos : (0:ℝ) < 2^n := by positivity
  have h_base_nonneg : 0 ≤ a n ^ ((1:ℝ) / 2^n) := Real.rpow_nonneg (le_of_lt (ha_pos n)) _
  have := Real.rpow_le_rpow h_base_nonneg hn (le_of_lt h2n_pos)
  have hrw : (a n ^ ((1:ℝ) / 2^n)) ^ (2^n : ℝ) = a n := by
    rw [← Real.rpow_mul (le_of_lt (ha_pos n))]
    have h_mul : (1 : ℝ) / 2^n * 2^n = 1 := div_mul_cancel₀ 1 (ne_of_gt h2n_pos)
    rw [h_mul, Real.rpow_one]
  rwa [hrw] at this

lemma seq_ratio_tendsto_atTop
    {a : ℕ → ℝ} {L : ℝ} (hL : L > 1)
    (h : Tendsto (fun n => a n ^ ((1:ℝ) / 2^n)) atTop (nhds L))
    (ha_pos : ∀ n, 0 < a n) :
    Tendsto (fun n => a (n + 1) / a n) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  set ε := (L - 1) / 4
  have hε_pos : 0 < ε := by dsimp [ε]; linarith
  have hLmε : L - ε > 1 := by dsimp [ε]; linarith
  set c := (L - ε)^2 / (L + ε)
  have hc_gt1 : c > 1 := by
    have h_pos : 0 < L + ε := by dsimp [ε]; linarith
    rw [gt_iff_lt, lt_div_iff₀ h_pos]
    dsimp [ε, c]; nlinarith [sq_nonneg (L - 1)]
  have h_lb_a  := lower_bound_from_tendsto hε_pos hLmε h ha_pos
  have h_ub_a  := upper_bound_from_tendsto hε_pos h ha_pos
  have h_c_grows : ∀ᶠ n in atTop, b ≤ c ^ (2^n : ℝ) := by
    have h_c_tendsto : Tendsto (fun x : ℝ => c ^ x) atTop atTop := by
      have h_eq : (fun x : ℝ => c ^ x) = (fun x : ℝ => exp (log c * x)) := by
        ext x; rw [Real.rpow_def_of_pos (by positivity : 0 < c)]
      rw [h_eq]
      apply tendsto_exp_atTop.comp
      exact (tendsto_const_mul_atTop_iff_pos (tendsto_id (α:=ℝ))).mpr (log_pos hc_gt1)
    have h_pow_tendsto : Tendsto (fun n => (2:ℝ)^n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h_comp : Tendsto (fun n => c ^ (2:ℝ)^n) atTop atTop :=
      h_c_tendsto.comp h_pow_tendsto
    exact h_comp.eventually (eventually_ge_atTop b)
  have h_an_large := seq_tendsto_atTop_of_rpow_tendsto hL h ha_pos
  have h_an_ge2 : ∀ᶠ n in atTop, 2 ≤ a n :=
    h_an_large.eventually (eventually_ge_atTop 2)
  have h_lb_a1 : ∀ᶠ n in atTop, (L - ε) ^ (2^(n+1) : ℝ) ≤ a (n+1) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp h_lb_a
    exact eventually_atTop.mpr ⟨N, fun n hn => hN (n+1) (by omega)⟩
  have h_all : ∀ᶠ n in atTop, ((L - ε) ^ (2^(n+1) : ℝ) ≤ a (n+1)) ∧ (a n ≤ (L + ε) ^ (2:ℝ) ^ n) ∧ (b ≤ c ^ (2^n : ℝ)) ∧ (2 ≤ a n) := by
    have h_rw : ∀ n, (2:ℝ)^n = (2:ℕ)^n := by intro n; push_cast; rfl
    have h_ub_a_rw : ∀ᶠ n in atTop, a n ≤ (L + ε) ^ (2:ℝ)^n := h_ub_a
    exact h_lb_a1.and (h_ub_a_rw.and (h_c_grows.and h_an_ge2))
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_all
  use N
  intro n hn
  have ⟨hn_lb_a1, hn_ub_a, hn_c, _⟩ := hN n hn
  have h_ratio : c ^ (2^n : ℝ) ≤ a (n + 1) / a n := by
    rw [le_div_iff₀ (ha_pos n)]
    have h_c_mul : c * (L + ε) = (L - ε)^2 := by
      dsimp [c]; exact div_mul_cancel₀ _ (ne_of_gt (by linarith))
    have h_pow_mul : c ^ (2^n : ℝ) * (L + ε) ^ (2^n : ℝ) = (L - ε) ^ (2^(n+1) : ℝ) := by
      calc c ^ (2^n : ℝ) * (L + ε) ^ (2^n : ℝ)
        _ = (c * (L + ε)) ^ (2^n : ℝ) := by rw [← Real.mul_rpow (by positivity) (by positivity)]
        _ = ((L - ε)^2) ^ (2^n : ℝ) := by rw [h_c_mul]
        _ = ((L - ε) ^ (2:ℕ)) ^ (2^n : ℝ) := rfl
        _ = (L - ε) ^ ((2:ℝ) * 2^n) := by
              have h_two : (L - ε) ^ (2:ℕ) = (L - ε) ^ (2:ℝ) := by
                exact (Real.rpow_natCast (L - ε) 2).symm
              rw [h_two, ← Real.rpow_mul (by linarith)]
        _ = (L - ε) ^ (2^(n+1) : ℝ) := by 
              congr 1
              have : (2^(n+1) : ℝ) = (2:ℝ) * 2^n := by push_cast; ring
              rw [this]
    exact calc c ^ (2^n : ℝ) * a n
      _ ≤ c ^ (2^n : ℝ) * (L + ε) ^ (2^n : ℝ) := mul_le_mul_of_nonneg_left hn_ub_a (by positivity)
      _ = (L - ε) ^ (2^(n+1) : ℝ) := h_pow_mul
      _ ≤ a (n + 1) := hn_lb_a1
  exact hn_c.trans h_ratio

lemma X_ratio_tendsto_atTop_v2
    (a : ℕ → ℕ) (ha_ge2 : ∀ n, 2 ≤ a n) {L : ℝ} (hL : L > 1)
    (h_fast : Tendsto (fun n => (a n : ℝ) ^ ((1:ℝ) / 2^n)) atTop (nhds L)) :
    let X := fun n => (a n : ℤ) * ((a n : ℤ) - 1)
    Tendsto (fun n => (X (n+1) : ℝ) / X n) atTop atTop := by
  intro X
  have ha_pos : ∀ n, (0 : ℝ) < a n := by
    intro n; have := ha_ge2 n; exact_mod_cast (by omega : 0 < a n)
  have hX_pos : ∀ n, (0 : ℝ) < X n := by
    intro n; dsimp [X]; push_cast
    have h_r : (2:ℝ) ≤ (a n : ℝ) := by exact_mod_cast (ha_ge2 n)
    have : (0:ℝ) < a n := by linarith
    nlinarith
  have h_a_ratio := seq_ratio_tendsto_atTop hL h_fast ha_pos
  
  have h_comp : Tendsto (fun n => ((a (n+1) : ℝ) / a n)^2 / 4) atTop atTop := by
    have h_sqrt : Tendsto (fun x : ℝ => x^2 / 4) atTop atTop := by
      apply tendsto_atTop_atTop.mpr
      intro b'
      use 2 * Real.sqrt (max b' 0)
      intro x hx
      have h_pos : 0 ≤ 2 * Real.sqrt (max b' 0) := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
      have h_sq := mul_self_le_mul_self h_pos hx
      calc b' ≤ max b' 0 := le_max_left _ _
        _ = (2 * Real.sqrt (max b' 0))^2 / 4 := by
              have h_sqrt2 : (Real.sqrt (max b' 0)) ^ 2 = max b' 0 := Real.sq_sqrt (le_max_right b' 0)
              have : (2 * Real.sqrt (max b' 0))^2 = 4 * max b' 0 := by
                calc (2 * Real.sqrt (max b' 0))^2
                  _ = 2^2 * (Real.sqrt (max b' 0))^2 := by rw [mul_pow]
                  _ = 4 * max b' 0 := by rw [h_sqrt2]; norm_num
              rw [this]
              ring
        _ ≤ x^2 / 4 := by linarith
    exact h_sqrt.comp h_a_ratio

  have h_an_large := seq_tendsto_atTop_of_rpow_tendsto hL h_fast ha_pos
  have h_an_ge2 : ∀ᶠ n in atTop, (2:ℝ) ≤ a n :=
    h_an_large.eventually (eventually_ge_atTop 2)
  
  have h_le : ∀ᶠ n in atTop, ((a (n+1) : ℝ) / a n)^2 / 4 ≤ (X (n+1) : ℝ) / X n := by
    filter_upwards [h_an_ge2] with n hn
    dsimp [X]; push_cast
    have ha : (2:ℝ) ≤ a n := hn
    have ha1 : (2:ℝ) ≤ a (n+1) := by 
      have hn1 := ha_ge2 (n+1)
      exact_mod_cast hn1
    have han : 0 < (a n : ℝ) := by positivity
    have h_denom : 0 < (a n : ℝ) * ((a n : ℝ) - 1) := by nlinarith
    have h_lhs : ((a (n + 1) : ℝ) / a n) ^ 2 / 4 = ((a (n + 1) : ℝ) ^ 2) / (4 * (a n : ℝ) ^ 2) := by 
      field_simp
    
    have h_ineq : ((a (n + 1) : ℝ) ^ 2) * ((a n : ℝ) * ((a n : ℝ) - 1)) ≤ (4 * (a n : ℝ) ^ 2) * ((a (n + 1) : ℝ) * ((a (n + 1) : ℝ) - 1)) := by
      have h1 : (4:ℝ) * ((a (n + 1) : ℝ) * (a n : ℝ) ^ 2) ≤ 3 * ((a (n + 1) : ℝ) ^ 2 * (a n : ℝ) ^ 2) := by
        calc (4:ℝ) * ((a (n + 1) : ℝ) * (a n : ℝ) ^ 2)
          _ = 2 * (2 * ((a (n + 1) : ℝ) * (a n : ℝ) ^ 2)) := by ring
          _ ≤ (a (n + 1) : ℝ) * (2 * ((a (n + 1) : ℝ) * (a n : ℝ) ^ 2)) := by
                apply mul_le_mul_of_nonneg_right
                · exact ha1
                · positivity
          _ = 2 * ((a (n + 1) : ℝ) ^ 2 * (a n : ℝ) ^ 2) := by ring
          _ ≤ 3 * ((a (n + 1) : ℝ) ^ 2 * (a n : ℝ) ^ 2) := by
                have : (0:ℝ) ≤ (a (n + 1) : ℝ) ^ 2 * (a n : ℝ) ^ 2 := by positivity
                linarith
      have h2 : (0:ℝ) ≤ (a (n + 1) : ℝ) ^ 2 * (a n : ℝ) := by positivity
      have h_expand1 : ((a (n + 1) : ℝ) ^ 2) * ((a n : ℝ) * ((a n : ℝ) - 1)) = ((a (n + 1) : ℝ) ^ 2) * ((a n : ℝ) ^ 2) - ((a (n + 1) : ℝ) ^ 2) * (a n : ℝ) := by ring
      have h_expand2 : (4 * (a n : ℝ) ^ 2) * ((a (n + 1) : ℝ) * ((a (n + 1) : ℝ) - 1)) = 4 * (((a (n + 1) : ℝ) ^ 2) * ((a n : ℝ) ^ 2)) - 4 * (((a (n + 1) : ℝ) * ((a n : ℝ) ^ 2))) := by ring
      rw [h_expand1, h_expand2]
      generalize ((a (n + 1) : ℝ) ^ 2) * ((a n : ℝ) ^ 2) = Z at *
      generalize ((a (n + 1) : ℝ) * ((a n : ℝ) ^ 2)) = W at *
      generalize ((a (n + 1) : ℝ) ^ 2) * (a n : ℝ) = Y at *
      linarith

    have h_ineq2 : ((a (n + 1) : ℝ) ^ 2) / (4 * (a n : ℝ) ^ 2) ≤ ((a (n + 1) : ℝ) * ((a (n + 1) : ℝ) - 1)) / ((a n : ℝ) * ((a n : ℝ) - 1)) := by
      have hB : (0:ℝ) < 4 * (a n : ℝ) ^ 2 := by
        have : (0:ℝ) < a n := by
          have h_r : (2:ℝ) ≤ (a n : ℝ) := by exact_mod_cast (ha_ge2 n)
          linarith
        positivity
      rw [le_div_iff₀ h_denom, div_mul_eq_mul_div, div_le_iff₀ hB]
      have h_swap : ((a (n + 1) : ℝ) * ((a (n + 1) : ℝ) - 1)) * (4 * (a n : ℝ) ^ 2) = 4 * ((a n : ℝ) ^ 2) * ((a (n + 1) : ℝ) * ((a (n + 1) : ℝ) - 1)) := by ring
      rw [h_swap]
      exact h_ineq

    rw [h_lhs]
    exact h_ineq2

  exact tendsto_atTop_mono' atTop h_le h_comp


-- ============================================================
-- LEMMA C: Xₙ · S_{n+1} → 0 (tail weight)
-- ============================================================

lemma tail_weight_tendsto_zero_v2
    {X : ℕ → ℤ} (hX_pos : ∀ n, (0:ℝ) < X n)
    (hX_summable : Summable (fun i => 1 / (X i : ℝ)))
    (hX_ratio : Tendsto (fun n => (X (n+1) : ℝ) / X n) atTop atTop) :
    Tendsto (fun n => (X n : ℝ) * ∑' i, 1 / (X (n+1+i) : ℝ)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set r := 2 / ε + 2
  have hr_gt1 : r > 1 := by
    dsimp [r]
    have : (0:ℝ) < 2 / ε := div_pos (by norm_num) hε
    linarith
  have hr_bound : 1 / (r - 1) < ε := by
    have h_eq1 : r - 1 = 2 / ε + 1 := by dsimp [r]; ring
    rw [h_eq1]
    have h_pos : 0 < 2 / ε + 1 := by
      have : (0:ℝ) < 2 / ε := div_pos (by norm_num) hε
      linarith
    rw [div_lt_iff₀ h_pos]
    have h_eq : ε * (2 / ε + 1) = 2 + ε := by
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      field_simp
    rw [h_eq]
    linarith
  obtain ⟨N_r, hN_r⟩ := tendsto_atTop_atTop.mp hX_ratio r
  use N_r
  intro n hn
  rw [Real.dist_eq, sub_zero]
  have h_nonneg : 0 ≤ (X n : ℝ) * ∑' i, 1 / (X (n+1+i) : ℝ) := by
    apply mul_nonneg (le_of_lt (hX_pos n))
    apply tsum_nonneg; intro i
    exact le_of_lt (div_pos (by norm_num) (hX_pos _))
  rw [abs_of_nonneg h_nonneg]

  have h_geom : ∀ k : ℕ, r ^ k * (X (n+1) : ℝ) ≤ X (n + 1 + k) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
        calc r ^ (k+1) * (X (n+1) : ℝ)
            = r * (r ^ k * (X (n+1) : ℝ)) := by ring
          _ ≤ r * (X (n + 1 + k) : ℝ) := mul_le_mul_of_nonneg_left ih (by linarith)
          _ ≤ X (n + 1 + k + 1) := by
              have := hN_r (n + 1 + k) (by omega)
              rw [le_div_iff₀ (hX_pos (n+1+k))] at this
              exact this

  have h_sum_bound : ∑' i, 1 / (X (n+1+i) : ℝ) ≤ ∑' i, (1/r)^i * (1 / X (n+1) : ℝ) := by
    apply Summable.tsum_le_tsum
    · intro i
      have h1 := h_geom i
      have hp1 : 0 < r ^ i * (X (n+1) : ℝ) := mul_pos (by positivity) (hX_pos (n+1))
      have hp2 : 0 < (X (n+1+i) : ℝ) := hX_pos (n+1+i)
      rw [div_le_iff₀ hp2]
      have h_alg : (1 / r) ^ i * (1 / X (n+1) : ℝ) * X (n+1+i) = X (n+1+i) / (r ^ i * X (n+1) : ℝ) := by
        rw [div_pow, one_pow]
        have hr_ne : r ^ i ≠ 0 := by positivity
        have hX : (X (n+1) : ℝ) ≠ 0 := ne_of_gt (hX_pos (n+1))
        field_simp
      rw [h_alg]
      exact (one_le_div₀ hp1).mpr h1
    · have h_sum := (summable_nat_add_iff (n+1)).mpr hX_summable
      have h_eq : (fun i => 1 / (X (i + (n + 1)) : ℝ)) = (fun i => 1 / (X (n + 1 + i) : ℝ)) := by
        ext i; congr 1; ring
      rw [← h_eq]
      exact h_sum
    · exact (summable_geometric_of_lt_one (by positivity) (by
        rw [div_lt_one₀ (by positivity)]; exact hr_gt1)) |>.mul_right _

  calc (X n : ℝ) * ∑' i, 1 / (X (n+1+i) : ℝ)
      ≤ (X n : ℝ) * (∑' i, (1/r)^i * (1 / X (n+1) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_sum_bound (le_of_lt (hX_pos n))
    _ = (X n : ℝ) / X (n+1) * ∑' i, (1/r)^i := by
          rw [tsum_mul_right]
          have h_div : (X n : ℝ) / X (n+1) = (X n : ℝ) * (1 / X (n+1) : ℝ) := by ring
          rw [h_div]
          ring
    _ = (X n : ℝ) / X (n+1) * (1 / (1 - 1/r)) := by
          have h1 : 0 ≤ 1 / r := by positivity
          have h2 : 1 / r < 1 := by rw [div_lt_one₀ (by positivity)]; exact hr_gt1
          rw [tsum_geometric_of_lt_one h1 h2, inv_eq_one_div]
    _ ≤ (1/r) * (r / (r - 1)) := by
          apply mul_le_mul
          · have hr_pos : 0 < r := by linarith
            have h_pos_n : (0:ℝ) < X n := hX_pos n
            have h_pos_n1 : (0:ℝ) < X (n+1) := hX_pos (n+1)
            have h1 := hN_r n hn
            rw [le_div_iff₀ h_pos_n] at h1
            rw [div_le_iff₀ h_pos_n1]
            have h2 : (X n : ℝ) * r ≤ X (n+1) := by linarith
            have h_eq : (1 / r : ℝ) * X (n+1) = X (n+1) / r := by ring
            rw [h_eq, le_div_iff₀ hr_pos]
            exact h2
          · have h_eq : 1 / (1 - 1 / r) = r / (r - 1) := by
              have hr_ne : r ≠ 0 := by linarith
              have hrm1 : r - 1 ≠ 0 := by linarith
              field_simp
            exact le_of_eq h_eq
          · have hr_pos : 0 < r := by linarith
            have h1 : 1 / r < 1 := by rw [div_lt_one₀ hr_pos]; exact hr_gt1
            have : 0 < 1 - 1 / r := by linarith
            positivity
          · have h1 : (0:ℝ) < X n := hX_pos n
            have h2 : (0:ℝ) < X (n+1) := hX_pos (n+1)
            positivity
    _ = 1 / (r - 1) := by 
          have hr_ne : r ≠ 0 := by linarith
          have hrm1 : r - 1 ≠ 0 := by linarith
          field_simp
    _ < ε := hr_bound


-- ============================================================
-- LEMMA D: Yₙ = Xₙ · Sₙ → 1
-- ============================================================

lemma tail_weight_one_v2
    {X : ℕ → ℤ} (hX_pos : ∀ n, (0:ℝ) < X n)
    (hX_summable : Summable (fun i => 1 / (X i : ℝ)))
    (hX_ratio : Tendsto (fun n => (X (n+1) : ℝ) / X n) atTop atTop) :
    Tendsto (fun n => (X n : ℝ) * ∑' i, 1 / (X (n+i) : ℝ)) atTop (nhds 1) := by
  have h_eq : ∀ n, (X n : ℝ) * ∑' i, 1 / (X (n+i) : ℝ) =
      1 + (X n : ℝ) * ∑' i, 1 / (X (n+1+i) : ℝ) := by
    intro n
    have hsumm : Summable (fun i => 1 / (X (n+i) : ℝ)) := by
      have h_sum := (summable_nat_add_iff n).mpr hX_summable
      have h_eq : (fun i => 1 / (X (i + n) : ℝ)) = (fun i => 1 / (X (n + i) : ℝ)) := by
        ext i; congr 1; ring
      rw [← h_eq]
      exact h_sum
    have h_tail : ∑' i, 1 / (X (n + i) : ℝ) =
        1 / X n + ∑' i, 1 / (X (n + 1 + i) : ℝ) := by
      have h_tsum := Summable.tsum_eq_zero_add hsumm
      have h_zero : 1 / (X (n + 0) : ℝ) = 1 / X n := by rw [add_zero]
      rw [h_zero] at h_tsum
      have h_shift : (∑' (i : ℕ), 1 / (X (n + (i + 1)) : ℝ)) = ∑' (i : ℕ), 1 / (X (n + 1 + i) : ℝ) := by
        congr 1; funext i; congr 1; ring
      rw [h_shift] at h_tsum
      exact h_tsum
    rw [h_tail, mul_add]
    have h_cancel : (X n : ℝ) * (1 / X n) = 1 := by
      have h_ne : (X n : ℝ) ≠ 0 := ne_of_gt (hX_pos n)
      field_simp
    rw [h_cancel]
  simp_rw [h_eq]
  have h_tail_zero := tail_weight_tendsto_zero_v2 hX_pos hX_summable hX_ratio
  have h_tendsto := Tendsto.add (tendsto_const_nhds : Tendsto (fun _ => (1 : ℝ)) _ _) h_tail_zero
  rw [add_zero] at h_tendsto
  exact h_tendsto


-- ============================================================
-- SUBSEQUENCE EXTRACTION
-- ============================================================

lemma exists_strictMono_tendsto
    {b : ℕ → ℝ} {L : ℝ}
    (h_freq : ∀ (ε : ℝ), 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ |b n - L| < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => b (φ n)) atTop (nhds L) := by
  have H : ∀ k N : ℕ, ∃ n : ℕ, N < n ∧ |b n - L| < (1 : ℝ) / (k + 1 : ℝ) := by
    intro k N
    have h_pos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    obtain ⟨n, hn1, hn2⟩ := h_freq _ h_pos (N + 1)
    exact ⟨n, by omega, hn2⟩
  choose! next_n h_next using H
  let φ : ℕ → ℕ := fun k => Nat.recOn k (next_n 0 0) (fun n ih => next_n (n + 1) ih)
  have h_mono : StrictMono φ := by
    have h_lt : ∀ n, φ n < φ (n + 1) := fun n => (h_next (n + 1) (φ n)).1
    intro n m hnm
    induction m with
    | zero => exact False.elim (Nat.not_lt_zero n hnm)
    | succ m ih =>
        have h_le : n ≤ m := Nat.le_of_lt_succ hnm
        have h_or : n < m ∨ n = m := Nat.lt_or_eq_of_le h_le
        rcases h_or with h_lt_m | h_eq
        · exact lt_trans (ih h_lt_m) (h_lt m)
        · rw [h_eq]
          exact h_lt m
  use φ
  constructor
  · exact h_mono
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    use K
    intro n hn
    have h1 : (1 : ℝ) / (n + 1 : ℝ) ≤ (1 : ℝ) / (K + 1 : ℝ) := by
      have h_posK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have h_posN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h_le : (K : ℝ) + 1 ≤ (n : ℝ) + 1 := by 
        have hn_k : K + 1 ≤ n + 1 := by omega
        exact_mod_cast hn_k
      exact (one_div_le_one_div h_posN h_posK).mpr h_le
    have h2 : (1 : ℝ) / (K + 1 : ℝ) < ε := by
      have h_bound : 1 / ε < (K + 1 : ℝ) := by linarith
      have h_mul : 1 < (K + 1 : ℝ) * ε := (div_lt_iff₀ (by positivity)).mp h_bound
      have h_mul2 : 1 < ε * (K + 1 : ℝ) := by linarith
      exact (div_lt_iff₀ (by positivity)).mpr h_mul2
    have h_dist : |b (φ n) - L| < (1 : ℝ) / (n + 1 : ℝ) := by
      cases n
      · exact (h_next 0 0).2
      · exact (h_next _ _).2
    rw [Real.dist_eq]
    exact lt_of_lt_of_le h_dist (le_trans h1 (le_of_lt h2))

lemma exists_tendsto_of_limsup_ge
    {a : ℕ → ℝ} {L : ℝ}
    (h_bdd : IsBoundedUnder (· ≤ ·) atTop a)
    (h_bdd_below : IsBoundedUnder (· ≥ ·) atTop a)
    (h_limsup : L ≤ limsup a atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => a (φ n)) atTop (nhds (limsup a atTop)) := by
  set S := limsup a atTop
  set B := {x : ℝ | ∀ᶠ n in atTop, a n ≤ x}
  have h_S_eq : S = sInf B := rfl
  have h_mem_B : ∀ x, x ∈ B ↔ ∀ᶠ n in atTop, a n ≤ x := fun x => Iff.rfl

  have hB_nonempty : B.Nonempty := by
    obtain ⟨M, hM⟩ := h_bdd
    use M
    exact (h_mem_B M).mpr hM
    
  have hB_bdd : BddBelow B := by
    obtain ⟨m, hm⟩ := h_bdd_below
    use m
    intro x hx
    obtain ⟨N1, hN1⟩ := eventually_atTop.mp ((h_mem_B x).mp hx)
    obtain ⟨N2, hN2⟩ := eventually_atTop.mp hm
    let N := max N1 N2
    calc m ≤ a N := hN2 N (le_max_right _ _)
      _ ≤ x := hN1 N (le_max_left _ _)

  have h_freq : ∀ (ε : ℝ), 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ |a n - S| < ε := by
    intro ε hε N
    have h_eventual : ∀ᶠ n in atTop, a n < S + ε := by
      have h_exists : ∃ x ∈ B, x < S + ε := exists_lt_of_csInf_lt hB_nonempty (by linarith)
      obtain ⟨x, hx_B, hx_lt⟩ := h_exists
      have h_ev_x := (h_mem_B x).mp hx_B
      exact h_ev_x.mono (fun n hn => lt_of_le_of_lt hn hx_lt)

    have h_frequent : ∀ M, ∃ n ≥ M, S - ε < a n := by
      intro M
      by_contra h_not
      push Not at h_not
      have h_ev : ∀ᶠ n in atTop, a n ≤ S - ε := eventually_atTop.mpr ⟨M, h_not⟩
      have h_in_B : S - ε ∈ B := (h_mem_B (S - ε)).mpr h_ev
      have h_S_le : S ≤ S - ε := by
        have h_S_le : sInf B ≤ S - ε := csInf_le hB_bdd h_in_B
        exact Eq.symm h_S_eq ▸ h_S_le
      linarith

    obtain ⟨N1, hN1⟩ := eventually_atTop.mp h_eventual
    obtain ⟨n, hn_ge, hn_gt⟩ := h_frequent (max N N1)
    use n
    constructor
    · exact le_trans (le_max_left _ _) hn_ge
    · have hn_lt : a n < S + ε := hN1 n (le_trans (le_max_right _ _) hn_ge)
      have h1 : -ε < a n - S := by linarith
      have h2 : a n - S < ε := by linarith
      exact abs_lt.mpr ⟨h1, h2⟩

  exact exists_strictMono_tendsto h_freq

lemma extract_fast_subsequence
    (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n)
    (h_limsup : 1 < limsup (fun n => (a n : ℝ) ^ ((1:ℝ) / 2^n)) atTop) :
    ∃ (φ : ℕ → ℕ) (L : ℝ), StrictMono φ ∧ L > 1 ∧
      Tendsto (fun n => (a (φ n) : ℝ) ^ ((1:ℝ) / 2^(φ n))) atTop (nhds L) := by
  set b : ℕ → ℝ := fun n => (a n : ℝ) ^ ((1:ℝ) / 2^n)
  
  have hb_bdd_below : IsBoundedUnder (· ≥ ·) atTop b := by
    use (1:ℝ)
    apply eventually_map.mpr
    apply Eventually.of_forall
    intro (n : ℕ)
    have h_an : (1 : ℝ) ≤ a n := by
      have hn_a := ha n
      exact_mod_cast (by omega : 1 ≤ a n)
    exact Real.one_le_rpow h_an (by positivity)

  have hb_bdd : IsBoundedUnder (· ≤ ·) atTop b := by
    by_contra h_unbdd
    have h_eq : {x : ℝ | ∀ᶠ n in atTop, b n ≤ x} = ∅ := by
      ext x
      constructor
      · intro hx
        exact h_unbdd ⟨x, hx⟩
      · intro hx
        exact hx.elim
    have h_limsup_zero : limsup b atTop = 0 := by
      have h_limsup_eq : limsup b atTop = sInf {x : ℝ | ∀ᶠ n in atTop, b n ≤ x} := rfl
      rw [h_limsup_eq, h_eq]
      exact Real.sInf_empty
    linarith

  have h_cluster := exists_tendsto_of_limsup_ge hb_bdd hb_bdd_below (le_refl (limsup b atTop))
  obtain ⟨φ, hφ_mono, hφ_tendsto⟩ := h_cluster
  exact ⟨φ, limsup b atTop, hφ_mono, h_limsup, hφ_tendsto⟩

-- ============================================================
-- LEMMA E: Qₙ = ∏_{i<n} Xᵢ / Xₙ → 1/L²
-- ============================================================

lemma log_Q_eq_of_delta {X : ℕ → ℝ} {L : ℝ} (hX_pos : ∀ n, 0 < X n) (n : ℕ) :
    Real.log ((Finset.prod (Finset.range n) X) / X n) =
    -2 * Real.log L + 2 * (Finset.sum (Finset.range n) (fun k => (2:ℝ)^k * (Real.log (X k) / (2:ℝ)^(k+1) - Real.log L)))
    - (2:ℝ)^(n+1) * (Real.log (X n) / (2:ℝ)^(n+1) - Real.log L) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, Finset.sum_empty, mul_zero, add_zero, zero_add]
    have h1 : Real.log (1 / X 0) = - Real.log (X 0) := by
      rw [Real.log_div (by positivity) (ne_of_gt (hX_pos 0)), Real.log_one, zero_sub]
    rw [h1]
    have hd : (2:ℝ)^(0+1) = 2 := by norm_num
    rw [hd]
    ring
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hP_pos : 0 < Finset.prod (Finset.range n) X := Finset.prod_pos (fun i _ => hX_pos i)
    have hPx_pos : 0 < (Finset.prod (Finset.range n) X) * X n := mul_pos hP_pos (hX_pos n)
    
    have h_log_div_succ : Real.log ((Finset.prod (Finset.range n) X) * X n / X (n+1)) =
        Real.log ((Finset.prod (Finset.range n) X) / X n) + 2 * Real.log (X n) - Real.log (X (n+1)) := by
      rw [Real.log_div (ne_of_gt hPx_pos) (ne_of_gt (hX_pos (n+1)))]
      rw [Real.log_mul (ne_of_gt hP_pos) (ne_of_gt (hX_pos n))]
      rw [Real.log_div (ne_of_gt hP_pos) (ne_of_gt (hX_pos n))]
      ring

    rw [h_log_div_succ, ih]
    
    have hp1 : (2:ℝ)^(n+1) = (2:ℝ)^n * 2 := by rw [pow_add]; norm_num
    have hp2 : (2:ℝ)^(n+1+1) = (2:ℝ)^n * 4 := by
      have h_n2 : n + 1 + 1 = n + 2 := rfl
      rw [h_n2, pow_add]
      have : (2:ℝ)^2 = 4 := by norm_num
      rw [this]

    rw [hp1, hp2]
    have h_pow_pos1 : (0:ℝ) < 2^n * 2 := by positivity
    have h_pow_pos2 : (0:ℝ) < 2^n * 4 := by positivity
    have h_pow_ne1 : (2:ℝ)^n * 2 ≠ 0 := ne_of_gt h_pow_pos1
    have h_pow_ne2 : (2:ℝ)^n * 4 ≠ 0 := ne_of_gt h_pow_pos2
    field_simp
    ring

lemma product_ratio_limit_placeholder
    {X : ℕ → ℤ} (hX_pos : ∀ n, (0:ℝ) < X n)
    {L : ℝ} (hL : L > 1)
    (h_tauber : Tendsto (fun n => 2 * (Finset.sum (Finset.range n) (fun k => (2:ℝ)^k * (Real.log (X k : ℝ) / (2:ℝ)^(k+1) - Real.log L)))
    - (2:ℝ)^(n+1) * (Real.log (X n : ℝ) / (2:ℝ)^(n+1) - Real.log L)) atTop (nhds 0)) :
    Tendsto (fun n => (Finset.prod (Finset.range n) (fun i => (X i : ℝ))) / (X n : ℝ)) atTop (nhds (1 / L^2)) := by
  
  have h_log : Tendsto (fun n => Real.log ((Finset.prod (Finset.range n) (fun i => (X i : ℝ))) / (X n : ℝ))) atTop (nhds (-2 * Real.log L)) := by
    have h_eq : ∀ n, Real.log ((Finset.prod (Finset.range n) (fun i => (X i : ℝ))) / (X n : ℝ)) =
      -2 * Real.log L + (2 * (Finset.sum (Finset.range n) (fun k => (2:ℝ)^k * (Real.log (X k : ℝ) / (2:ℝ)^(k+1) - Real.log L)))
      - (2:ℝ)^(n+1) * (Real.log (X n : ℝ) / (2:ℝ)^(n+1) - Real.log L)) := by
      intro n
      have hX_pos_R : ∀ i, (0:ℝ) < (X i : ℝ) := fun i => by push_cast; exact hX_pos i
      rw [@log_Q_eq_of_delta (fun i => (X i : ℝ)) L hX_pos_R n]
      ring
    simp_rw [h_eq]
    have h_const : Tendsto (fun (_:ℕ) => -2 * Real.log L) atTop (nhds (-2 * Real.log L)) := tendsto_const_nhds
    have h_add := Tendsto.add h_const h_tauber
    have h_zero : nhds (-2 * Real.log L + (0:ℝ)) = nhds (-2 * Real.log L) := by rw [add_zero]
    exact h_zero ▸ h_add
  
  have h_exp_tendsto : Tendsto (fun n => Real.exp (Real.log ((Finset.prod (Finset.range n) (fun i => (X i : ℝ))) / (X n : ℝ)))) atTop (nhds (Real.exp (-2 * Real.log L))) :=
    (Continuous.tendsto Real.continuous_exp (-2 * Real.log L)).comp h_log
  
  have h_exp_eq : ∀ n, Real.exp (Real.log ((Finset.prod (Finset.range n) (fun i => (X i : ℝ))) / (X n : ℝ))) = (Finset.prod (Finset.range n) (fun i => (X i : ℝ))) / (X n : ℝ) := by
    intro n
    apply Real.exp_log
    have hp : (0:ℝ) < Finset.prod (Finset.range n) (fun i => (X i : ℝ)) := Finset.prod_pos (fun i _ => by push_cast; exact hX_pos i)
    exact div_pos hp (by push_cast; exact hX_pos n)
  
  simp_rw [h_exp_eq] at h_exp_tendsto
  
  have h_L_eq : Real.exp (-2 * Real.log L) = 1 / L^2 := by
    have hp : 0 < L := by linarith
    have h1 : -2 * Real.log L = -(Real.log L + Real.log L) := by ring
    have h2 : Real.log L + Real.log L = Real.log (L * L) := by 
      have h_mul : Real.log (L * L) = Real.log L + Real.log L := Real.log_mul (ne_of_gt hp) (ne_of_gt hp)
      rw [h_mul]
    have h3 : L * L = L ^ 2 := by ring
    rw [h1, h2, h3, Real.exp_neg, Real.exp_log (pow_pos hp 2), inv_eq_one_div]
  
  rwa [h_L_eq] at h_exp_tendsto

def construct_X (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  (a n : ℤ) * ((a n : ℤ) - 1)

def construct_P (a : ℕ → ℕ) (d : ℤ) (k : ℕ) : ℤ :=
  d * ∏ i ∈ Finset.range k, construct_X a i

def tail_residual (a : ℕ → ℝ) (d : ℝ) (k : ℕ) : ℝ :=
  d * (∏ i ∈ Finset.range k, a i) * (∑' i, 1 / (a (k + i)))

theorem tail_residual_succ (a : ℕ → ℝ) (d : ℝ) (k : ℕ) 
    (ha_pos : ∀ i, a i ≠ 0) (h_summable : Summable (fun i => 1 / a i)) :
    tail_residual a d (k + 1) = a k * tail_residual a d k - d * (∏ i ∈ Finset.range k, a i) := by
  unfold tail_residual
  have h_summable_k : Summable (fun i => 1 / a (k + i)) := by
    apply h_summable.comp_injective; intro i j h; simp at h; assumption
  have h_split : (∑' i, 1 / a (k + i)) = 1 / a k + (∑' i, 1 / a (k + 1 + i)) := by
    rw [Summable.tsum_eq_zero_add h_summable_k]
    simp; apply tsum_congr; intro i; rw [Nat.add_assoc, Nat.add_comm i 1, ← Nat.add_assoc]
  rw [h_split, Finset.prod_range_succ]
  field_simp [ha_pos k]
  ring

def construct_C_real (a : ℕ → ℕ) (d : ℤ) (k : ℕ) : ℝ :=
  tail_residual (fun i => (construct_X a i : ℝ)) (d : ℝ) k

structure ErdosAnalyticHypotheses (a : ℕ → ℕ) : Prop :=
  (tauberian_bottleneck : ∀ X : ℕ → ℤ, (∀ n, (0:ℝ) < X n) → ∀ L > 1,
    Tendsto (fun n => 2 * (Finset.sum (Finset.range n) (fun k => (2:ℝ)^k * (Real.log (X k : ℝ) / (2:ℝ)^(k+1) - Real.log L)))
      - (2:ℝ)^(n+1) * (Real.log (X n : ℝ) / (2:ℝ)^(n+1) - Real.log L)) atTop (nhds 0))
  (fast_growth_whole_sequence : ∀ L : ℝ, ∀ f : ℕ → ℕ, StrictMono f →
    Tendsto (fun k => (a (f k) : ℝ) ^ ((1 : ℝ) / 2 ^ (f k))) atTop (nhds L) →
    Tendsto (fun n => (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) atTop (nhds L))

theorem analytic_squeeze_from_Q_limit
    (a : ℕ → ℕ) (ha : erdos_problem_265 a)
    (h_analytic : ErdosAnalyticHypotheses a)
    (C X P : ℕ → ℤ) (d : ℤ)
    (hCn_form : ∀ n, (C n : ℝ) = construct_C_real a d n)
    (hX_pos   : ∀ n, (0 : ℝ) < (X n : ℝ))
    (hX_summable : Summable (fun i => 1 / (X i : ℝ)))
    (hX_eq : X = construct_X a)
    (L : ℝ) (hL : L > 1)
    (f : ℕ → ℕ) (hf_mono : StrictMono f)
    (h_fast : Tendsto (fun k => (a (f k) : ℝ) ^ ((1 : ℝ) / 2 ^ (f k))) atTop (nhds L)) :
    Tendsto (fun k => (C (f k) : ℝ)) atTop (nhds ((d : ℝ) / L ^ 2)) := by
  have h_fast_whole : Tendsto (fun n => (a n : ℝ) ^ ((1 : ℝ) / 2 ^ n)) atTop (nhds L) := 
    h_analytic.fast_growth_whole_sequence L f hf_mono (by exact_mod_cast h_fast)

  have h_X_ratio : Tendsto (fun n => (construct_X a (n + 1) : ℝ) / construct_X a n) atTop atTop := 
    X_ratio_tendsto_atTop_v2 a ha.1 hL h_fast_whole

  have h_tail_one := tail_weight_one_v2 (fun n => by 
    dsimp [construct_X]; push_cast
    have h_an_r : (a n : ℝ) ≥ 2 := by exact_mod_cast ha.1 n
    nlinarith)
    (by 
      obtain ⟨q1, hq1⟩ := ha.2.1
      obtain ⟨q2, hq2⟩ := ha.2.2
      apply Summable.congr (Summable.sub hq2.summable hq1.summable)
      intro i; dsimp [construct_X]; push_cast
      have h_ai_r : (a i : ℝ) ≥ 2 := by exact_mod_cast ha.1 i
      have : ((a i - 1 : ℕ) : ℝ) = (a i : ℝ) - 1 := by 
        have : a i ≥ 1 := by
          have : a i ≥ 2 := by exact_mod_cast h_ai_r
          omega
        rw [Nat.cast_sub this]; push_cast; rfl
      rw [this]
      have h1 : (a i : ℝ) ≠ 0 := by linarith
      have h2 : (a i : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring)
    h_X_ratio

  have h_Q_lim : Tendsto (fun n => (∏ i ∈ Finset.range n, (construct_X a i : ℝ)) / (construct_X a n : ℝ)) atTop (nhds (1 / L ^ 2)) :=
    product_ratio_limit_placeholder (fun n => by 
      dsimp [construct_X]; push_cast
      have h_an_r : (a n : ℝ) ≥ 2 := by exact_mod_cast ha.1 n
      have h1 : 0 < (a n : ℝ) := by linarith
      have h2 : 0 < (a n : ℝ) - 1 := by linarith
      positivity) hL (h_analytic.tauberian_bottleneck (fun n => (construct_X a n : ℤ)) (fun n => by 
      dsimp [construct_X]; push_cast
      have h_an_r : (a n : ℝ) ≥ 2 := by exact_mod_cast ha.1 n
      have h1 : 0 < (a n : ℝ) := by linarith
      have h2 : 0 < (a n : ℝ) - 1 := by linarith
      positivity) L hL)

  simp_rw [hCn_form]
  have h_split : ∀ n, construct_C_real a d n = 
    (d : ℝ) * ((∏ i ∈ Finset.range n, (construct_X a i : ℝ)) / (construct_X a n : ℝ)) * 
    ((construct_X a n : ℝ) * ∑' i, 1 / (construct_X a (n + i) : ℝ)) := by
    intro n; dsimp [construct_C_real, tail_residual]
    have hX_pos_i : ∀ i, (construct_X a i : ℝ) ≠ 0 := by
      intro i; dsimp [construct_X]; push_cast
      have h_ai_r : (a i : ℝ) ≥ 2 := by exact_mod_cast ha.1 i
      nlinarith
    have h_ring : ((d : ℝ) * (∏ i ∈ Finset.range n, (construct_X a i : ℝ))) * ∑' (i : ℕ), 1 / (construct_X a (n + i) : ℝ) =
      (d : ℝ) * ((∏ i ∈ Finset.range n, (construct_X a i : ℝ)) / (construct_X a n : ℝ)) * 
      ((construct_X a n : ℝ) * ∑' i, 1 / (construct_X a (n + i) : ℝ)) := by
        field_simp [hX_pos_i]
    exact h_ring

  simp_rw [h_split]
  have h_lim := Tendsto.mul (Tendsto.const_mul (d : ℝ) (h_Q_lim.comp hf_mono.tendsto_atTop)) (h_tail_one.comp hf_mono.tendsto_atTop)
  have h_eq : (fun x ↦
      (d : ℝ) * ((fun n ↦ (∏ i ∈ Finset.range n, (construct_X a i : ℝ)) / (construct_X a n : ℝ)) ∘ f) x *
        ((fun n ↦ (construct_X a n : ℝ) * ∑' (i : ℕ), 1 / (construct_X a (n + i) : ℝ)) ∘ f) x) = 
      (fun k ↦ (d : ℝ) * ((∏ i ∈ Finset.range (f k), (construct_X a i : ℝ)) / (construct_X a (f k) : ℝ)) *
        ((construct_X a (f k) : ℝ) * ∑' (i : ℕ), 1 / (construct_X a (f k + i) : ℝ))) := by ext k; rfl
  rw [h_eq] at h_lim
  have h_target_eq : (d : ℝ) * (1 / L ^ 2) * 1 = (d : ℝ) / L ^ 2 := by field_simp
  rwa [h_target_eq] at h_lim

theorem erdos_bridge (a : ℕ → ℕ) (ha : erdos_problem_265 a) :
    ∃ (C X P : ℕ → ℤ) (d : ℤ), 
      (∀ n, X n = (a n : ℤ) * ((a n : ℤ) - 1)) ∧
      (∀ n, 2 ∣ X n) ∧ 
      (∀ n, P (n + 1) = P n * X n) ∧
      (∀ n, C (n + 1) = X n * C n - P n) ∧ 
      (∀ n, (2^n : ℤ) ∣ P n) ∧
      (∀ n, C n > 0) ∧
      (∀ L > 1, ∀ f : ℕ → ℕ, StrictMono f → 
                Tendsto (fun k => (a (f k) : ℝ)^(1 / (2^(f k) : ℝ))) atTop (nhds L) → 
                ∃ M : ℝ, Tendsto (fun k => (C (f k) : ℝ)) atTop (nhds M)) := by
  let q1 := ha.2.1.choose
  let q2 := ha.2.2.choose
  let q := q2 - q1
  let d_nat := q.den
  let d : ℤ := d_nat
  
  let X := construct_X a
  let P := construct_P a d
  
  have hX_even : ∀ n, 2 ∣ X n := by
    intro n; dsimp [X, construct_X]
    let an := (a n : ℤ)
    match Int.even_or_odd an with
    | Or.inl h => exact Even.two_dvd (Even.mul_right h _)
    | Or.inr h => 
      have h1 : Even (an - 1) := by
        rcases h with ⟨k, hk⟩
        use k; linarith
      exact Even.two_dvd (Even.mul_left h1 an)

  have hX_summable : Summable (fun i => 1 / (X i : ℝ)) := by
    obtain ⟨q1_val, hq1⟩ := ha.2.1
    obtain ⟨q2_val, hq2⟩ := ha.2.2
    apply Summable.congr (Summable.sub hq2.summable hq1.summable)
    intro i; dsimp [X, construct_X]; push_cast
    have h_ai_ge_2 : a i ≥ 2 := ha.1 i
    have : ((a i - 1 : ℕ) : ℝ) = (a i : ℝ) - 1 := by 
      have : 1 ≤ a i := by linarith
      rw [Nat.cast_sub this]; push_cast; rfl
    rw [this]
    have h_ai_r : (a i : ℝ) ≥ 2 := by exact_mod_cast h_ai_ge_2
    have h1 : (a i : ℝ) ≠ 0 := by linarith
    have h2 : (a i : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring

  have hX_sum : (∑' i, 1 / (X i : ℝ)) = (q : ℝ) := by
    obtain ⟨q1_val, hq1⟩ := ha.2.1
    obtain ⟨q2_val, hq2⟩ := ha.2.2
    have h_sub := HasSum.sub hq2 hq1
    have heq : (fun i => 1 / ((a i - 1 : ℕ) : ℝ) - 1 / (a i : ℝ)) = (fun i => 1 / (X i : ℝ)) := by
      ext i; dsimp [X, construct_X]; push_cast
      have h_ai_ge_2 : a i ≥ 2 := ha.1 i
      have : ((a i - 1 : ℕ) : ℝ) = (a i : ℝ) - 1 := by 
        have : 1 ≤ a i := by linarith
        rw [Nat.cast_sub this]; push_cast; rfl
      rw [this]
      have h_ai_r : (a i : ℝ) ≥ 2 := by exact_mod_cast h_ai_ge_2
      have h1 : (a i : ℝ) ≠ 0 := by linarith
      have h2 : (a i : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    rw [heq] at h_sub
    have : (∑' i, 1 / (X i : ℝ)) = (q2_val : ℝ) - (q1_val : ℝ) := h_sub.tsum_eq
    rw [this]
    have h1 : q1_val = (ha.2.1.choose : ℚ) := by
      have : HasSum (fun n => 1 / (a n : ℝ)) (ha.2.1.choose : ℝ) := ha.2.1.choose_spec
      exact hq1.unique this |> Rat.cast_inj.mp
    have h2 : q2_val = (ha.2.2.choose : ℚ) := by
      have : HasSum (fun n => 1 / ((a n - 1 : ℕ) : ℝ)) (ha.2.2.choose : ℝ) := ha.2.2.choose_spec
      exact hq2.unique this |> Rat.cast_inj.mp
    rw [h1, h2]; norm_cast

  have hC_succ_real : ∀ k, construct_C_real a d (k + 1) = (X k : ℝ) * construct_C_real a d k - (P k : ℝ) := by
    intro k; dsimp [construct_C_real, X, P, construct_P]
    have hX_pos : ∀ i, (X i : ℝ) ≠ 0 := by 
      intro i; dsimp [X, construct_X]; push_cast
      have h1 : a i ≥ 2 := ha.1 i
      have h2 : (a i : ℝ) ≥ 2 := by exact_mod_cast h1
      have : (a i : ℝ) * ((a i : ℝ) - 1) > 0 := by nlinarith
      linarith
    have h_rec := tail_residual_succ (fun i => (X i : ℝ)) ((d : ℤ) : ℝ) k hX_pos hX_summable
    rw [h_rec]
    push_cast; rfl

  have hC_int : ∀ k, ∃ c : ℤ, construct_C_real a d k = (c : ℝ) := by
    intro k; dsimp [construct_C_real, tail_residual]
    let Pk_abs := ∏ i ∈ Finset.range k, X i
    have h_tsum : (∑' i, 1 / (X (k + i) : ℝ)) = (∑' i, 1 / (X i : ℝ)) - ∑ i ∈ Finset.range k, 1 / (X i : ℝ) := by
      have h_sum := Summable.sum_add_tsum_nat_add k hX_summable
      have h_shift : (∑' (i : ℕ), 1 / (X (k + i) : ℝ)) = ∑' (i : ℕ), 1 / (X (i + k) : ℝ) := by
        congr 1; ext i; congr 1; ring
      rw [h_shift]
      linarith [h_sum]
    rw [h_tsum, hX_sum]
    let c := q.num * Pk_abs - d * (∑ i ∈ Finset.range k, Pk_abs / X i)
    use c
    have hPk : (Pk_abs : ℝ) = ∏ i ∈ Finset.range k, (X i : ℝ) := by 
      dsimp [Pk_abs, X]; push_cast; rfl
    have h_left : (d : ℝ) * ((Pk_abs : ℝ) * (q : ℝ)) = (q.num : ℝ) * (Pk_abs : ℝ) := by
      have : (d : ℝ) = (q.den : ℝ) := rfl
      rw [this]
      have : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
      rw [this]
      field_simp [show (q.den : ℝ) ≠ 0 by exact_mod_cast q.pos.ne']
    have h_sum_rw : (d : ℝ) * (∏ i ∈ Finset.range k, (X i : ℝ)) * ((q : ℝ) - ∑ i ∈ Finset.range k, 1 / (X i : ℝ)) =
      (d : ℝ) * (∏ i ∈ Finset.range k, (X i : ℝ)) * (q : ℝ) - (d : ℝ) * ∑ i ∈ Finset.range k, (∏ i ∈ Finset.range k, (X i : ℝ)) * (1 / (X i : ℝ)) := by
      rw [mul_sub]
      congr 1
      rw [mul_assoc, Finset.mul_sum]
    rw [h_sum_rw]
    rw [← hPk]
    rw [mul_assoc (d : ℝ), h_left]
    have h_c_cast : (c : ℝ) = (q.num : ℝ) * (Pk_abs : ℝ) - (d : ℝ) * ∑ i ∈ Finset.range k, ((Pk_abs : ℝ) * (1 / (X i : ℝ))) := by
      dsimp [c]
      push_cast
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hdiv : X i ∣ Pk_abs := Finset.dvd_prod_of_mem (fun i => X i) hi
      have hX_i_pos : (X i : ℝ) ≠ 0 := by
        have h_ai_r : (a i : ℝ) ≥ 2 := by exact_mod_cast ha.1 i
        dsimp [X, construct_X]; push_cast; nlinarith
      have h_cast_div := Int.cast_div (α := ℝ) hdiv (by exact_mod_cast hX_i_pos)
      rw [h_cast_div]
      ring
    rw [h_c_cast]
  let C := fun k => (hC_int k).choose
  use C, X, P, d
  
  constructor; · exact fun n => rfl
  constructor; · exact hX_even
  constructor
  · intro n; dsimp [P, X, construct_P]; rw [Finset.prod_range_succ]; ring
  constructor
  · intro k; have hCk := (hC_int k).choose_spec
    have hCkp1 := (hC_int (k+1)).choose_spec
    have h := hC_succ_real k; rw [hCk, hCkp1] at h; norm_cast at h
  constructor
  · intro k; dsimp [P, construct_P]; have : (2^k : ℤ) ∣ (∏ i ∈ Finset.range k, X i) := by
      induction' k with i ih
      · simp
      · rw [Finset.prod_range_succ, pow_succ]; obtain ⟨x, hx⟩ := hX_even i
        rw [hx]; apply mul_dvd_mul ih (dvd_mul_right 2 x)
    apply dvd_mul_of_dvd_right this
  constructor
  · intro k; have hCk := (hC_int k).choose_spec
    have hpos : construct_C_real a d k > 0 := by
      dsimp [construct_C_real, tail_residual]
      have h_d_pos : (d : ℝ) > 0 := by
        have : (d : ℝ) = (q.den : ℝ) := rfl; rw [this]; positivity
      have hX_pos_i : ∀ i, (construct_X a i : ℝ) > 0 := by 
        intro i; dsimp [construct_X]; push_cast; have h_ai : a i ≥ 2 := ha.1 i
        have h_ai_real : (a i : ℝ) ≥ 2 := by exact_mod_cast h_ai
        nlinarith
      have hX_prod_pos : (∏ i ∈ Finset.range k, (X i : ℝ)) > 0 := by
        apply Finset.prod_pos; intro i _; apply hX_pos_i
      have hX_sum_pos : (∑' i, 1 / (construct_X a (k + i) : ℝ)) > 0 := by
        have hf : ∀ i, 0 < 1 / (construct_X a (k + i) : ℝ) := fun i => one_div_pos.mpr (hX_pos_i (k + i))
        have h_summable_k : Summable (fun i => 1 / (construct_X a (k + i) : ℝ)) := hX_summable.comp_injective (fun x y h => by simp at h; assumption)
        exact h_summable_k.tsum_pos (fun n => le_of_lt (hf n)) 0 (hf 0)
      apply mul_pos (mul_pos h_d_pos hX_prod_pos) hX_sum_pos
    rw [hCk] at hpos; exact_mod_cast hpos
  · intro L hL f hf_mono h_fast
    use (d / L^2)
    have hX_pos_real : ∀ n, (0 : ℝ) < (X n : ℝ) := by
      intro i; dsimp [X, construct_X]; push_cast; have h_ai : a i ≥ 2 := ha.1 i
      have h_ai_real : (a i : ℝ) ≥ 2 := by exact_mod_cast h_ai
      nlinarith
    exact analytic_squeeze_from_Q_limit a ha C X P d 
      (by intro n; exact (hC_int n).choose_spec.symm) 
      hX_pos_real hX_summable rfl
      L hL f hf_mono h_fast
