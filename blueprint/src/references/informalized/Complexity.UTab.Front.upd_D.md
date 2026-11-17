<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.upd_D -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register D

**Claim.** Replacing the value at position $4$ of the five-position register function by $v$ gives the function with values $a,b,c,e,v$.

**Proof.** Compare values at all five positions. At position $4$, the update returns $v$. At positions $0,1,2,3$, it preserves the original values $a,b,c,e$, respectively. These are exactly the values of the stated new function, so the functions are equal.
