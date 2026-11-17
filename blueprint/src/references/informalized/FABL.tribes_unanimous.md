<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Examples.lean :: FABL.tribes_unanimous -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes is unanimous

**Claim.** If the block width and number of blocks are positive, tribes takes value $+1$ on the all-$+1$ input and value $-1$ on the all-$-1$ input.

**Proof.** The AND function of positive arity is unanimous: it returns $+1$ on the all-$+1$ input and $-1$ on the all-$-1$ input (`FABL.andFunction_unanimous`). On the all-$+1$ input, every extracted block is all $+1$, so each block AND is $+1$; the unanimous property of OR then makes the tribes output $+1$. On the all-$-1$ input, every block is all $-1$, so every block AND is $-1$; OR's unanimous property makes the tribes output $-1$ (`FABL.orFunction_unanimous`).

**Key facts.** `FABL.andFunction_unanimous`, `FABL.orFunction_unanimous`.
