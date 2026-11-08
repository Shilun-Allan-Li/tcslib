<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitCfg_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Configuration Reconstruction

**Claim.** Under the stated agreements of states, input-head positions, outputs, and tape data, embedding $c$ with the supplied contents and head positions and prefixing its output by $p$ yields $d$.

**Proof.** Fix a tape index $j$ among the $k$ tapes. If $j$ is in the image of $\sigma$, write $j=\sigma(i)$. The selected-tape identities show that the embedded contents and head position there are those of $c$ on tape $i$, which by hypothesis agree with $d$ at $j$. If $j$ is outside the image, the unselected-tape identities show that the embedding uses the supplied contents and head position; the outside hypothesis makes these agree with $d$. Thus the two configurations agree on every tape field. Their states and input-head positions agree by assumption, and their outputs agree by the assumed concatenation identity. Equality of all configuration fields gives the result (using `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, and `Turing.embedEmitCfg_unselected`).

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitCfg_unselected`.
