<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.splitCharacter_indicator_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign product indicator identity

**Claim.** For signs $a,b,c$, the indicator of $ab=c$ equals $(1+\operatorname{signValue}(a)\operatorname{signValue}(b)\operatorname{signValue}(c))/2$.

**Proof.** Each sign is either $1$ or $-1$, so there are eight possibilities. If $ab=c$, then $abc=1$, and the right side is one; if $ab\ne c$, then $abc=-1$, and the right side is zero. These are exactly the two values of the indicator, proving the identity in every case.
