<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_poly_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Equality of Computed Words

**Claim.** If $f,g:\{0,1\}^*\to\{0,1\}^*$ are polynomial-time computable, then the function mapping $x$ to the one-bit word recording whether $f(x)=g(x)$ is polynomial-time computable.

**Proof.** First compute the encoded pair $(f(x),g(x))$ in polynomial time (Complexity.a3n_poly_pair). On that encoded pair, the equality machine outputs the one-bit answer in time $3|f(x)|+|g(x)|+4$ (Complexity.a3n_eq_computes). Run these machines in sequence: the composition bound (Complexity.a3n_comp_at) is the first computation time plus the intermediate word's length, a fixed overhead, and the equality computation time. The intermediate word length is at most the first machine's running time, since a machine emits at most one output symbol per step (Turing.MultiTapeTM.output_length_le); the computation-time characterization by halting state and output identifies that intermediate output (Turing.FinTM.computesInTime_iff). Because the encoded pair has length $2|f(x)|+2+|g(x)|$, the resulting total time is bounded by a constant multiple of the pair-computation bound plus a constant. The pair-computation bound is polynomial in $|x|$, so this total is polynomial as well. Increasing the time bound preserves the computation (Turing.FinTM.ComputesInTime.mono).

**Key facts.** `Complexity.a3n_poly_pair`, `Complexity.a3n_eq_computes`, `Complexity.a3n_comp_at`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.ComputesInTime.mono`.
