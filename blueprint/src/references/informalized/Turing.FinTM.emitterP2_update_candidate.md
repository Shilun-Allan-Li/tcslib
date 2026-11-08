<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_update_candidate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate Word Update

**Claim.** Updating the word at position $0$ in the host layout for $(s,u,v)$ with $a$ gives the host layout for $(a,u,v)$.

**Proof.** We prove equality of the two layouts by evaluating them at an arbitrary tape index. At index $0$, the update replaces the stored word $s$ by $a$, which is precisely the first entry of the layout for $(a,u,v)$. Every other index is supplied by the width and suffix banks, which do not depend on the candidate word; hence the two layouts agree there as well. Thus they agree at every index.
