<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleEmbed_updateTape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating an Embedded Tape

**Claim.** Updating tape $i$ of a smaller configuration before embedding gives the same embedded configuration as embedding first and then updating tape $\iota(i)$ to the same contents.

**Proof.** Compare the two configurations component by component. Their states, input-head positions, work-head positions, and outputs agree by the definition of the embedding; it remains to compare tape contents. If a host index is in the image of $\iota$, write it as $\iota(l)$. When $l=i$, both sides use the updated content $f$ on that tape, because embedding preserves selected tape contents (`embedEmitCfg_selected_tape`). When $l\ne i$, injectivity gives $\iota(l)\ne\iota(i)$, so neither update changes that tape and the same selected-tape identity shows agreement. If the host index is outside the image, the update on the embedded side does not affect it. The embedding frame property shows that its contents are the background contents on both sides (`embedEmitTM_frame`). Thus the tape functions, and hence the full configurations, are equal.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitTM_frame`.
