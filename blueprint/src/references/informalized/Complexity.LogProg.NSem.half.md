<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation Across Halving a Register

**Claim.** If the instruction at a live state halves register $r$ and continues at a new state, and the resulting configuration terminates under the guard and accepts exactly when $P$ holds, then, provided the original configuration satisfies the guard, the original configuration has those same properties.

**Proof.** A halving instruction is a particular deterministic instruction. Its execution sends the machine to the stated new state, replaces register $r$ by $\lfloor v(r)/2\rfloor$, and leaves the other registers unchanged. Apply preservation across a deterministic instruction (\texttt{NSem.det}) to this successor semantics and the assumed guard at the original configuration. The one-step configuration produced by the deterministic transition is exactly the successor specified in the hypothesis, so termination and the acceptance equivalence transfer to the original configuration.

**Key facts.** `Complexity.LogProg.NSem.det`.
