import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Erdos265.AsymptoticLemmas
import Erdos265.ProblemStatement
import Erdos265.AsymptoticSqueeze

open Filter Topology Finset Real

noncomputable section

-- ============================================================
-- 1. TOPOLOGICAL INTEGER SQUEEZE
-- ============================================================

/-- A sequence of integers converging in ℝ must eventually lock into a constant. -/
lemma tendsto_int_eventually_const {f : ℕ → ℤ} {L : ℝ}
    (h : Tendsto (fun n => (f n : ℝ)) atTop (nhds L)) :
    ∃ C : ℤ, ∀ᶠ n in atTop, f n = C := by
  have h1 := Metric.tendsto_atTop.mp h (1/4) (by norm_num)
  rcases h1 with ⟨N, hN⟩
  use f N
  rw [Filter.eventually_atTop]
  use N
  intro n hn
  have h_N := hN N (le_refl N)
  have h_n := hN n hn
  have h_dist : |(f n : ℝ) - (f N : ℝ)| < 1/2 := by
    calc |(f n : ℝ) - (f N : ℝ)| = |((f n : ℝ) - L) - ((f N : ℝ) - L)| := by congr 1; ring
      _ ≤ |(f n : ℝ) - L| + |(f N : ℝ) - L| := abs_sub _ _
      _ < 1/4 + 1/4 := add_lt_add h_n h_N
      _ = 1/2 := by norm_num
  have h_eq : f n = f N := by
    by_contra hc
    have h_abs_ge : 1 ≤ |f n - f N| := by exact Int.add_one_le_iff.mpr (abs_pos.mpr (sub_ne_zero.mpr hc))
    have h_int : (1:ℝ) ≤ |(f n : ℝ) - (f N : ℝ)| := by exact_mod_cast h_abs_ge
    linarith
  exact h_eq

-- ============================================================
-- 2. THE EXACT INTEGER COLLAPSE (NO INTEGER SOLUTIONS)
-- ============================================================

/-- 
  The core arithmetic contradiction: The shifted product X_{N+1} = Y(Y-1) 
  can never equal X_N^2 - X_N + 1 = X(X-1) + 1 for integers X, Y ≥ 2.
  It falls strictly between X(X-1) and X(X+1).
-/
lemma no_integer_collapse (X Y : ℤ) (hX : X ≥ 2) (hY : Y ≥ 2) :
    Y * (Y - 1) ≠ X * (X - 1) + 1 := by
  intro h
  rcases lt_trichotomy Y X with h_lt | h_eq | h_gt
  · have : Y + X - 1 > 0 := by omega
    have : Y - X < 0 := by omega
    have h_bound : Y * (Y - 1) < X * (X - 1) := by nlinarith
    linarith
  · subst h_eq
    nlinarith
  · have : Y - (X + 1) ≥ 0 := by omega
    have : Y + X > 0 := by omega
    have h_bound : Y * (Y - 1) ≥ (X + 1) * X := by nlinarith
    linarith

-- ============================================================
-- 3. CONSTANT COUPLING IMPLIES INTEGER COLLAPSE
-- ============================================================

/-- 
  If the exact coupling variable becomes constant, the sequence X_N = a_N(a_N-1)
  must satisfy X_{N+1} = X_N^2 - X_N + 1. This structurally contradicts `no_integer_collapse`.
-/
theorem constant_coupling_contradiction (a : ℕ → ℕ) (C X P : ℕ → ℤ) (N : ℕ)
    (hGe2 : ∀ k, a k ≥ 2)
    (hX : ∀ n, X n = (a n : ℤ) * ((a n : ℤ) - 1))
    (hRec : ∀ n, C (n + 1) = X n * C n - P n)
    (hP_step : ∀ n, P (n + 1) = P n * X n)
    (hC1 : C (N + 1) = C N)
    (hC2 : C (N + 2) = C (N + 1))
    (hPos : C N > 0) :
    False := by
  set c := C N
  set X_N := X N
  set X_N1 := X (N + 1)
  set P_N := P N
  set P_N1 := P (N + 1)

  have eq1 : c = X_N * c - P_N := by
    calc c = C (N + 1) := hC1.symm
      _ = X N * C N - P N := hRec N
      _ = X_N * c - P_N := rfl

  have eq2 : c = X_N1 * c - P_N1 := by
    calc c = C (N + 1) := hC1.symm
      _ = C (N + 2) := hC2.symm
      _ = X (N + 1) * C (N + 1) - P (N + 1) := hRec (N + 1)
      _ = X_N1 * c - P_N1 := by rw [hC1]

  have hP_eq1 : P_N = c * (X_N - 1) := by linarith [eq1]
  have hP_eq2 : P_N1 = c * (X_N1 - 1) := by linarith [eq2]

  have hP_step_N : P_N1 = P_N * X_N := hP_step N

  have h_alg : c * (X_N1 - 1) = c * ((X_N - 1) * X_N) := by
    calc c * (X_N1 - 1) = P_N1 := hP_eq2.symm
      _ = P_N * X_N := hP_step_N
      _ = c * (X_N - 1) * X_N := by rw [hP_eq1]
      _ = c * ((X_N - 1) * X_N) := by ring

  have hC_ne_zero : c ≠ 0 := ne_of_gt hPos
  have h_X_rec : X_N1 - 1 = (X_N - 1) * X_N := mul_left_cancel₀ hC_ne_zero h_alg
  have h_X_rec2 : X_N1 = X_N * (X_N - 1) + 1 := by linarith [h_X_rec]

  have hX_N_ge2 : X N ≥ 2 := by
    rw [hX N]
    have ha : (a N : ℤ) ≥ 2 := by exact_mod_cast hGe2 N
    nlinarith

  have ha_N1_ge2 : (a (N + 1) : ℤ) ≥ 2 := by exact_mod_cast hGe2 (N + 1)

  have h_collapse := no_integer_collapse (X N) (a (N + 1) : ℤ) hX_N_ge2 ha_N1_ge2
  
  have h_X_N1_def : X (N + 1) = (a (N + 1) : ℤ) * ((a (N + 1) : ℤ) - 1) := hX (N + 1)
  change X (N + 1) = X N * (X N - 1) + 1 at h_X_rec2
  rw [h_X_N1_def] at h_X_rec2
  exact h_collapse h_X_rec2

-- ============================================================
-- 4. THE CEILING CONJECTURE (FINAL CAPSTONE)
-- ============================================================

/--
  **THE ERDŐS 265 CEILING CONJECTURE**
  
  The formal proof that the limit is exactly 1, conditional on the unproved analytic limit steps. 
  If the limit superior were strictly greater than 1, the coupling variable 
  would converge in ℝ. Because it is an integer sequence, it would lock into 
  an exact constant. This constant forces the sequence into a recurrence 
  that has zero integer solutions, yielding a pure contradiction.
-/
