<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_pairValid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair-code validity in linear time

**Claim.** There is a finite Boolean-alphabet Turing machine that outputs the one-bit string indicating whether the pair parser succeeds, in time bounded by a constant times the input length plus one.

**Proof.** Use the pair-validity machine itself and take the constant to be $1$. Its computation theorem gives output $[(\operatorname{pairDecode}(x)).\mathrm{isSome}]$ in $|x|+1$ steps, which is the required output and time bound.

**Key facts.** `Turing.FinTM.pairValidTM_computes`.
