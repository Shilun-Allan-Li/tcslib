<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_prepend -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a Fixed Boolean Word

**Claim.** For every fixed Boolean word $w$, there are a finite Boolean Turing machine and a constant $c$ that output $wx$ on every Boolean input $x$ within $c(|x|+1)$ steps.

**Proof.** Use the machine that prepends $w$, which runs in $|w|+|x|+1$ steps. Choose $c=|w|+1$. Since $|w|+|x|+1\le (|w|+1)(|x|+1)$, its running time is within the asserted bound.

**Key facts.** `Turing.FinTM.prependTM_computes`, `Turing.FinTM.ComputesInTime.mono`.
