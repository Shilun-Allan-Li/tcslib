<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentDual.lean :: FABL.IsBent.bentDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bentness of the Dual

**Claim.** For even $n$, if $f$ is bent and sign-valued, then its dual is both sign-valued and bent.

**Proof.** The dual is sign-valued because every bent function has a sign-valued dual (`IsBent.isSignValued_bentDual`). The dual is also bent because the dual of a sign-valued function is bent when $n$ is even (`IsSignValued.isBent_bentDual`). Combining these two conclusions gives both properties.

**Key facts.** `FABL.IsBent.isSignValued_bentDual`, `FABL.IsSignValued.isBent_bentDual`.
