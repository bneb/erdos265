# Formal Verification Framework for Erdős Problem 265

This repository provides a formal verification framework in Lean 4 for analyzing integer sequences $a_n$ that satisfy the **dual-rationality constraint**: both $\sum 1/a_n$ and $\sum 1/(a_n - 1)$ are rational.

The objective is to establish the precise growth limits of such sequences, specifically the supremum of the double-exponential base $\beta = \limsup a_n^{1/2^n}$.

## 1. Verified Results (0 Sorry, 0 Axioms)

The following structural boundaries are fully formalized and verified within the Lean 4 kernel:

### Single Rationality Growth Limit (Folklore Theorem)
- **File:** `src/Erdos265/Folklore.lean`
- **Verification:** Proves that for sequences with a uniform growth limit, the growth is strictly bounded by $\mathcal{O}(C^{2^N})$.

### Rational Lattice Spacing
- **File:** `src/Erdos265/LatticeScale.lean`
- **Verification:** Proves that for any rational target $p/q$, the distance between possible tail sums is at least $1/(q P_N)$, where $P_N$ is the prefix product.

### The Stall Length Bound (Wild Oscillator Defense)
- **File:** `src/Erdos265/WildOscillator.lean`
- **Verification:** Proves that if a sequence attempts a massive jump (a "wild oscillator" spike), the Diophantine gap between the step size and the rational lattice forces the sequence to stall. This stall phase is rigorously decoupled and bounded using topological series limits.

---

## 2. Research Frontiers (Formalized Hypotheses)

The absolute resolution of the problem depends on establishing the link between discrete residuals and continuous growth rates. We formalize these dependencies as structured hypotheses, identifying the exact analytical gaps that remain open.

### The $\beta \le 3$ Algebraic Envelope
- **Status:** Conditional on the **Analytic Squeeze** (bounding the tail sum by the prefix product).
- **File:** `src/Erdos265/TwoAdicEnvelope.lean`
- **Mechanism:** Implements a 2-adic valuation ratchet on the coupling integer $C_N$ to establish the absolute base-3 ceiling.

### The $\beta \le 2$ Supreme Barrier
- **Status:** Structural Hypothesis.
- **File:** `src/Erdos265/WildOscillator.lean`
- **Mechanism:** Formalizes the contradiction logic where growth exceeding base-2 forces a prefix-inflation penalty that contradicts the trajectory.

### The Supremum Existence ($\beta = 2$)
- **Status:** Open Problem.
- **Mechanism:** While empirical data suggests the existence of stable attracting manifolds at the $\beta = 2$ limit, formally proving that the resulting sequences converge to exact rational targets requires advanced asymptotic bounding of the residual ratios ($R_n/P_n \to 0$) which remains unformalized.

## 3. Formalization Standards
- **Axioms:** Zero (0).
- **Sorries:** Zero (0) in the primary structural proof path.
- **Witnesses:** Sylvester sequence is established as a valid witness for single-rationality.
