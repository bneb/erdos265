# Formal Verification Framework for Erdős Problem 265

This repository provides a formal verification framework in Lean 4 for analyzing integer sequences $a_n$ that satisfy the **dual-rationality constraint**: both $\sum 1/a_n$ and $\sum 1/(a_n - 1)$ are rational.

The objective is to establish the precise growth limits of such sequences, specifically the supremum of the double-exponential base $\beta = \limsup a_n^{1/2^n}$.

## 1. Verified Results (0 Sorry)

The following components are fully formalized and verified within the Lean 4 kernel:

### Single Rationality Growth Limit (Folklore Theorem)
- **File:** `src/Erdos265/Folklore.lean`
- **Verification:** Proves that for sequences with a uniform growth limit, the growth is strictly bounded by $\mathcal{O}(C^{2^N})$.

### Rational Lattice Spacing and Wild Oscillators
- **File:** `src/Erdos265/WildOscillator.lean` (and `LatticeScale.lean`)
- **Verification:** Proves the **Stall Length Bound**: If a sequence attempts a massive jump (a "wild oscillator" spike), the Diophantine gap between the step size and the rational lattice forces the sequence to stall. This stall phase is rigorously decoupled and bounded using topological series limits.

### Admissibility Stability
- **File:** `src/Erdos265/ExistenceStability.lean`
- **Verification:** Defines a state space for dual residuals and proves that the region $R_1^2 > R_3$ is a stable invariant under a sufficiently large next-step integer term.

---

## 2. Research Frontiers (Formalized Hypotheses)

The repository provides a structural roadmap for resolving the $\beta$ bounds. The following results are formalized within a conditional framework, identifying the remaining links required for an unconditional resolution.

### The $\beta \le 3$ Bound
- **Status:** Conditional on the **Analytic Squeeze** (bounding the tail sum by the prefix product).
- **File:** `src/Erdos265/TwoAdicEnvelope.lean`
- **Mechanism:** Implements a 2-adic valuation ratchet on the coupling integer $C_N$ to establish the ceiling.

### The $\beta \le 2$ Bound
- **Status:** Structural Hypothesis.
- **File:** `src/Erdos265/LatticeScale.lean`
- **Mechanism:** Formalizes the "Lattice Barrier" logic, where growth exceeding base-2 forces a prefix-inflation penalty that contradicts the growth rate.

## 3. Formalization Standards
- **Axioms:** Zero (0).
- **Sorries:** Zero (0) in the primary structural proof path.
- **Witnesses:** Sylvester sequence is established as a valid witness for single-rationality.
