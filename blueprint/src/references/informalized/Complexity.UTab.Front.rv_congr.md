<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.rv_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Assignment Congruence

**Claim.** If $a=a'$, $b=b'$, $c=c'$, $e=e'$, and $f=f'$, then the register assignments $(a,b,c,e,f)$ and $(a',b',c',e',f')$ are equal.

**Proof.** Replace each of $a,b,c,e,f$ by its equal primed value. The two assignments then have identical defining data, so they are equal.
