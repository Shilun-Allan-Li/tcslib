<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loop_orbit_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant Along an Iterated Orbit

**Claim.** If the predicate holds at the initial value and is preserved by each application of the step function, then it holds after every finite number of iterations.

**Proof.** Fix $x$ and argue by induction on the number $i$ of iterations. At $i=0$, the iterate is $s_0(x)$, so the initial hypothesis gives the result. For the successor case, the iterate after $i+1$ steps is obtained by applying $F(x,\cdot)$ to the iterate after $i$ steps. The induction hypothesis gives the invariant at that earlier iterate, and the preservation hypothesis gives it after this final step.
