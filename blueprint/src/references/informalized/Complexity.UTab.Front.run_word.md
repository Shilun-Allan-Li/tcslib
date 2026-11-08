<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.run_word -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Output Word

**Claim.** For every $n\in\mathbb N$, on input consisting of $n$ consecutive $1$ bits, the program starting at its initial label halts after some $t\leq (30+C+5d+14d(C+1))(n+1)^{d+1}$ steps and outputs $1^n0 1^{(C+1)(n+1)^d}0$.

**Proof.** The front-of-program computation theorem (`goes_front`) supplies registers and an input position such that the program, started at $\mathsf{rN}$ with zeroed registers, reaches a halted state within the stated bound and has appended exactly the word $\mathsf{word}(C,d,n)$. Instantiate its arbitrary prior output with the empty string. The initial state is precisely the state with label $\mathsf{rN}$, all registers zero, input position zero, and empty output. Therefore the resulting halted run has output $\mathsf{word}(C,d,n)$, which by definition is $1^n0 1^{(C+1)(n+1)^d}0$.

**Key facts.** `Complexity.UTab.Front.goes_front`.
