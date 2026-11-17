<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.upd_B -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register B

**Claim.** Replacing the value at position $2$ of the five-position register function by $v$ gives the function with values $a,b,v,e,f$.

**Proof.** Compare the two functions at each of the five positions. At position $2$, the update returns $v$, as does the new register function. At every other position it preserves the old value, giving $a,b,e,f$ at positions $0,1,3,4$. Hence the functions agree at every position.
