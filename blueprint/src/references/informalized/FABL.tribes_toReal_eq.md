<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribes_toReal_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real-valued tribes formula

**Claim.** For every $w,s$ and input $x$, the real-valued tribes function equals $2\prod_{i\in\mathrm{Fin}(s)}(1+a_i(x))/2-1$, where $a_i(x)$ is the real value of the AND of block $i$.

**Proof.** By definition, the real-valued tribes output is the real value of the OR applied to the list of block AND values. The real-valued OR formula says that this is twice the product, over all blocks, of one half of one plus that block's real value, minus one (`FABL.signValue_orFunction`). Substituting the AND value of each block gives the claimed expression.

**Key facts.** `FABL.signValue_orFunction`.
