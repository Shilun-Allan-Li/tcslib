<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.DiagSimulator.diagLang_not_mem_DTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal Language Escapes DTIME

**Claim.** Under the stated growth condition, the language on which the simulator's machine does not compute the one-symbol output $1$ within $g(n)$ steps is not in DTIME$(T)$.

**Proof.** Assume for contradiction that the diagonal language belongs to DTIME$(T)$. By the simulator property, there are constants $A,N_0$ such that for every $n\ge N_0$ some input $x$ of length $n$ makes the simulator compute the diagonal language's indicator within $A\Phi(T(n),n)$ steps. Apply the growth hypothesis with this $A,N_0$ to choose such an $n$ with $A\Phi(T(n),n)\le g(n)$, and then take the corresponding $x$. Monotonicity of computation time (`ComputesInTime.mono`) shows that the simulator computes the indicator of the diagonal language on $x$ within $g(|x|)$ steps. If $x$ belongs to the diagonal language, its indicator is true, so this computation contradicts the definition of the language, which says the simulator does not compute output $[true]$ in that time. If $x$ does not belong, its indicator is false. In that case the definition implies that the simulator does compute $[true]$ within the bound; output uniqueness (`ComputesInTime.output_unique`) then equates $[true]$ with the already computed indicator $[false]$, impossible. Both cases contradict the assumption, proving nonmembership.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.ComputesInTime.output_unique`.
