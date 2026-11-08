<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.leadingCoordinateTimes_toReal_fin_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real-valued leading-coordinate product

**Claim.** The real-valued leading-coordinate product at $(b,x)$ equals the real value of $b$ times the real-valued value of $g$ at $x$.

**Proof.** First, the leading-coordinate product at $(b,x)$ is $b g(x)$ by the defining coordinate identity (FABL.leadingCoordinateTimes_fin_cons). Applying the real-valued interpretation means taking the real value of this product. Since the real value map on signs respects multiplication, this is the real value of $b$ multiplied by the real value of $g(x)$, as required.

**Key facts.** `FABL.leadingCoordinateTimes_fin_cons`.
