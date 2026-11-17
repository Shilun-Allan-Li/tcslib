<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.upd_X -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register X

**Claim.** Replacing the value at position $0$ of the five-position register function by $v$ gives the function with values $v,b,c,e,f$.

**Proof.** At position $0$, the update assigns $v$. At positions $1,2,3,4$, it retains the original values $b,c,e,f$. These values coincide with those of the claimed function at every position, so the functions are equal.
