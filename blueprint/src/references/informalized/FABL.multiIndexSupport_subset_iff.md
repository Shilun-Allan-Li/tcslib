<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.multiIndexSupport_subset_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support contained in a set

**Claim.** The support of $a$ is contained in a set $J$ of positions if and only if every position outside $J$ has value $z$.

**Proof.** For the forward implication, take a position $i$ outside $J$. If $a(i)\ne z$, then $i$ belongs to the support, and containment would put $i$ in $J$, a contradiction. Hence $a(i)=z$. Conversely, suppose every position outside $J$ has value $z$. Any position in the support has value different from $z$, so it cannot lie outside $J$; therefore it belongs to $J$, proving support containment.
