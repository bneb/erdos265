import Mathlib

open Filter Topology Real BigOperators Finset

/-!
# Combinatorial Graph of the Exact Coupling

This file formally defines the transition graph of the exact coupling integer
C_N modulo q. When the sequence enters a slow recovery phase, the prefix product 
absorbs the modulus q, and the recurrence collapses to:
C_{N+1} ≡ (x^2 - x) C_N (mod q)

We prove that the hitting time M required to satisfy the Diophantine gap 
is bounded by the constant q, because the state space is finite.
-/

variable (q : ℕ) [NeZero q]

/-- The set of valid multipliers derived from X_N = a_N(a_N - 1). -/
def valid_multipliers : Set (ZMod q) :=
  { X | ∃ x : ZMod q, X = x * x - x }

/-- 
  The directed relation defining the state transitions.
  There is a path from u to v if a single sequence step can map u to v.
-/
def coupling_rel (u v : ZMod q) : Prop :=
  ∃ X ∈ valid_multipliers q, v = X * u

/-- A path of length M in the graph. -/
def is_path (u v : ZMod q) (M : ℕ) : Prop :=
  ∃ f : ℕ → ZMod q, f 0 = u ∧ f M = v ∧ ∀ k < M, coupling_rel q (f k) (f (k + 1))

/-- 
  Any trajectory of length strictly greater than q must visit a state 
  twice (Pigeonhole Principle).
-/
lemma trajectory_contains_cycle (f : ℕ → ZMod q) (M : ℕ) (hM : M > q) :
    ∃ i j : ℕ, i < j ∧ j ≤ M ∧ f i = f j := by
  let f_fin : Fin (M + 1) → ZMod q := fun x => f x.val
  have h_card : Fintype.card (Fin (M + 1)) > Fintype.card (ZMod q) := by
    rw [Fintype.card_fin, ZMod.card]
    omega
  have h_pigeon := Fintype.exists_ne_map_eq_of_card_lt f_fin h_card
  rcases h_pigeon with ⟨i, j, h_ne, h_eq⟩
  by_cases h_lt : i.val < j.val
  · use i.val, j.val
    exact ⟨h_lt, by omega, h_eq⟩
  · use j.val, i.val
    have h_gt : j.val < i.val := by
      have : i.val ≠ j.val := by
        intro h; apply h_ne; ext; exact h
      omega
    exact ⟨h_gt, by omega, h_eq.symm⟩

/--
  The Combinatorial Shortest Path Bound:
  If a state v is reachable from u, it can be reached in at most q steps.
-/
theorem shortest_path_le_q (u v : ZMod q) :
    (∃ M : ℕ, is_path q u v M) → ∃ M ≤ q, is_path q u v M := by
  classical
  intro h_exists
  let S := { M | is_path q u v M }
  have h_nonempty : ∃ n, n ∈ S := h_exists
  let M_min := Nat.find h_nonempty
  use M_min
  have h_min_is_path : is_path q u v M_min := Nat.find_spec h_nonempty
  constructor
  · -- Proof by contradiction: if M_min > q, we can remove a cycle.
    by_contra h_gt
    push Not at h_gt
    rcases h_min_is_path with ⟨f, h_start, h_end, h_steps⟩
    have h_cycle := trajectory_contains_cycle q f M_min h_gt
    rcases h_cycle with ⟨i, j, h_ij, h_jM, h_eq⟩
    -- Construct a shorter path by skipping the cycle (i -> j)
    let M_short := M_min - (j - i)
    let g : ℕ → ZMod q := fun k => if k < i then f k else f (k + (j - i))
    have h_short_is_path : is_path q u v M_short := by
      use g
      constructor
      · dsimp [g]
        by_cases h_i_zero : 0 < i
        · rw [if_pos h_i_zero]; exact h_start
        · have : i = 0 := by omega
          rw [if_neg (by omega), this, Nat.sub_zero, Nat.zero_add, ← h_eq, this]; exact h_start
      · constructor
        · dsimp [g]
          have h_M_short : ¬ M_short < i := by omega
          rw [if_neg h_M_short]
          have : M_short + (j - i) = M_min := by omega
          rw [this]; exact h_end
        · intro k hk
          dsimp [g]
          by_cases h_ki : k + 1 < i
          · have h_k : k < i := by omega
            rw [if_pos h_k, if_pos h_ki]
            exact h_steps k (by omega)
          · -- k + 1 >= i
            by_cases h_k_i : k < i
            · -- k < i, k + 1 >= i -> k = i - 1
              rw [if_pos h_k_i, if_neg (by omega)]
              have h_eq_i : k + 1 = i := by omega
              have h_eq_j : k + 1 + (j - i) = j := by omega
              rw [h_eq_j, ← h_eq, ← h_eq_i]
              exact h_steps k (by omega)
            · -- k >= i
              rw [if_neg h_k_i, if_neg (by omega)]
              have h_idx1 : k + (j - i) < M_min := by omega
              have h_idx2 : k + (j - i) + 1 = k + 1 + (j - i) := by ring
              rw [← h_idx2]
              exact h_steps (k + (j - i)) h_idx1
    have h_less : M_short < M_min := by
      have : j - i > 0 := by omega
      omega
    have h_not_min := Nat.find_min h_nonempty h_less
    exact h_not_min h_short_is_path
  · exact h_min_is_path
