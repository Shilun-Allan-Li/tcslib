<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_splitSolve -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Padded Split Search

**Claim.** For every $C,e\in\mathbb{N}$, a finite Boolean Turing machine computes the specified padded split encoding (or the empty word if there is no admissible split) on every input of length $n$ within $c(n+1)^{e+2}$ steps for some $c$.

**Proof.** Apply the closed-machine result for split search with parameters $C,e$. It supplies a finite machine and a constant with exactly the stated output rule and running-time bound.

**Key facts.** `Turing.FinTM.splitSolve_closed`.
