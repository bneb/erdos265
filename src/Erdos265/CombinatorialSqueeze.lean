import Mathlib
import Erdos265.ProblemStatement

open Filter Topology Real BigOperators Finset Nat

/-!
# The Combinatorial Squeeze

Since the Ergodic Torus approach fails due to the state space crystallizing into 
a finite cyclic group, we pivot to finite combinatorics.

The exact coupling integer `C_N` and the prefix product `P_N` obey the recurrences:
  C_{N+1} = X_N C_N - P_N
  P_{N+1} = X_N P_N

Modulo any integer `q`, this defines a deterministic finite state machine (FSM).
The state at step N is defined by the pair `(C_N mod q, P_N mod q)`.
Because the state space is finite (size q^2), the trajectory of the sequence modulo `q`
is heavily restricted. 

If we can prove that this FSM must eventually force `C_N` into a state that violates
the fractional squeeze `C_N ≤ P_N / (a_N - 1)`, we can mathematically cap the growth
without relying on continuous real-valued dynamics.
-/

variable (a : ℕ → ℕ) (q : ℕ) 

/-- The state of the sequence modulo q. -/
structure ModularState (q : ℕ) where
  c : ZMod q
  p : ZMod q
  deriving DecidableEq

/-- The transition function for the modular state given a new sequence term X = a(a-1). -/
def modular_transition (q : ℕ) (state : ModularState q) (X : ZMod q) : ModularState q :=
  ⟨X * state.c - state.p, X * state.p⟩

/-- 
  Because X_N = a_N(a_N - 1), X_N can only take values in a restricted subset 
  of ZMod q (specifically, elements of the form x^2 - x).
-/
def is_valid_transition (q : ℕ) (X : ZMod q) : Prop :=
  ∃ x : ZMod q, X = x * x - x

/--
  The Pigeonhole Principle guarantees that if the sequence wanders for long enough 
  without absorbing into 0, it must repeat states.
-/
instance modular_state_finite (q : ℕ) [NeZero q] : Fintype (ModularState q) where
  elems := Finset.univ.product Finset.univ |>.map ⟨fun (c, p) => ⟨c, p⟩, by
    intro ⟨c1, p1⟩ ⟨c2, p2⟩ h
    injection h with h_c h_p
    congr
  ⟩
  complete := by
    intro ⟨c, p⟩
    simp

lemma pigeonhole_repetition (q : ℕ) [NeZero q] (f : ℕ → ModularState q) :
    ∃ i j : ℕ, i < j ∧ f i = f j := by
  let f_fin : Fin (Fintype.card (ModularState q) + 1) → ModularState q := fun x => f x.val
  have h_pigeon := Fintype.exists_ne_map_eq_of_card_lt f_fin (by 
    rw [Fintype.card_fin]
    omega
  )
  rcases h_pigeon with ⟨i, j, h_ne, h_eq⟩
  by_cases h_lt : i.val < j.val
  · exact ⟨i.val, j.val, h_lt, h_eq⟩
  · have h_gt : j.val < i.val := by
      have : i.val ≠ j.val := by
        intro h
        apply h_ne
        ext
        exact h
      omega
    exact ⟨j.val, i.val, h_gt, h_eq.symm⟩
