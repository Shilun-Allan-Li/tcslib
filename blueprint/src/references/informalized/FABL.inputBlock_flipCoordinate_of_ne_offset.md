<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.inputBlock_flipCoordinate_of_ne_offset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping a coordinate outside a block offset

**Claim.** If offset $o$ differs from the within-block coordinate of $i$, flipping coordinate $i$ leaves unchanged the value of $x$ at offset $o$ in the block containing $i$.

**Proof.** The coordinate in the full vector corresponding to block $(\mathrm{tribesCoord}(w,s,i))_1$ and offset $o$ is different from $i$. Indeed, if the two full coordinates were equal, applying the inverse coordinate identification would show that their block-offset pairs agree, forcing $o=(\mathrm{tribesCoord}(w,s,i))_2$, contrary to the hypothesis. Flipping coordinate $i$ changes a vector only at coordinate $i$; since the selected coordinate is different, its value is unchanged.
