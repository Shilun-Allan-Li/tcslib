<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.nextThird_mod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Modulo Three

**Claim.** Advancing the phase represented by $j$ modulo $3$ gives the phase represented by $j+1$ modulo $3$.

**Proof.** Equality of the two elements of the three-element phase type reduces to equality of their values. The remainder $j\bmod 3$ is one of $0,1,2$. In each case, the phase-advance rule sends it respectively to $1,2,0$, while $(j+1)\bmod 3$ has that same value. Hence the phases agree.
