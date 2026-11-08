<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.DTIME_const_mul_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant scaling of deterministic time

**Claim.** For every natural number $C$ and time bound $T$, every language decidable in deterministic time bounded by a constant multiple of $n\mapsto CT(n)$ is decidable in deterministic time bounded by a constant multiple of $T$.

**Proof.** Take a witnessing deterministic machine and constant $c$ for the original time bound. Keep the machine and choose the new constant $cC$. For each input length, the original time bound is $c(CT(n))$, which equals $(cC)T(n)$ by associativity. The machine therefore satisfies the required time bound as well; the general fact that a computation can be viewed as taking more time is supplied by monotonicity (\texttt{Turing.FinTM.ComputesInTime.mono}).

**Key facts.** `Turing.FinTM.ComputesInTime.mono`.
