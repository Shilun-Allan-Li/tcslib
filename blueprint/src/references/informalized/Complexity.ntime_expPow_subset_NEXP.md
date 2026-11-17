<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.ntime_expPow_subset_NEXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Nondeterministic Time Is in NEXP

**Claim.** For every natural number $c$, every language decidable in nondeterministic time $n\mapsto 2^{n^c}$ belongs to $\mathrm{NEXP}$.

**Proof.** Take a language $L$ decided by a nondeterministic machine $N$ within time $a\,2^{n^c}$ for some constant $a$. Use the exponential-time certificate characterization (\texttt{Complexity.e3\_choice\_certificate}): membership in $L$ is equivalent to the existence of a certificate of length $a\,2^{(|x|+1)^c}$ whose concatenation with $x$ is accepted by the associated choice verifier. It remains to show that this verifier is polynomial-time decidable. The timed bit-expansion result (\texttt{Complexity.e3\_exp\_bits\_timed}) computes the binary representation needed by the verifier in time bounded by $B(n+1)^{c+1}$ for some $B$. The split-and-solve result (\texttt{Turing.FinTM.computesFunInTime\_splitSolveWith}) then gives a machine to parse the split certificate and run the verifier's required computation, with a bound involving that polynomial-time expansion and the input length. The verifier construction theorem (\texttt{Complexity.e3\_verifier\_of\_split}) places the resulting choice verifier in $\mathrm P$. For the explicit time bound, write $m=|w|+1$. Since $m\le m^{c+1}$ and $|w|+2\le 2m$, raising the latter inequality to $c+1$ gives $(|w|+2)^{c+1}\le 2^{c+1}m^{c+1}$. These estimates absorb the split computation's overhead into a constant multiple of $m^{c+1}$. The monotonicity of running-time bounds (\texttt{Turing.FinTM.ComputesInTime.mono}) permits enlarging the bound to the stated form. Thus the verifier is in $\mathrm P$, and the certificate characterization supplies the required NEXP representation of $L$.

**Key facts.** `Complexity.e3_choice_certificate`, `Complexity.e3_exp_bits_timed`, `Turing.FinTM.computesFunInTime_splitSolveWith`, `Complexity.e3_verifier_of_split`, `Turing.FinTM.ComputesInTime.mono`.
