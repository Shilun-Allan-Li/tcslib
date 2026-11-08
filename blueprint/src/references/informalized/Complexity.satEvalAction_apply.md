<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEvalAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Administrative Action on Canonical Configurations

**Claim.** Under the stated head-position hypotheses, applying the administrative action to the canonical evaluation configuration gives the canonical configuration with state $q'$, input position $i'$, certificate-head offset $j'$, and empty output, while preserving the saved machine data and input word.

**Proof.** The action sets the control state to $q'$ and moves the input head exactly to the prescribed position, by the hypothesis on the moved position. It performs no writes, so the saved work tapes and the buffer holding $u$ are unchanged. The first $M.k$ work-tape heads do not move; the additional certificate head moves from $j$ to $j+d=j'$. The action emits no output, leaving the output empty. Thus every component agrees with the specified canonical configuration.
