<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.upd_A -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register A

**Claim.** Replacing the value at position $1$ of the five-position register function by $v$ gives the function with values $a,v,c,e,f$.

**Proof.** To prove equality of the two register functions, compare their values at each of the five positions. At position $1$, the update returns $v$, which is the value of the new register function there. At each other position, the update leaves the original function unchanged, giving respectively $a,c,e,f$. Thus the functions agree everywhere.
