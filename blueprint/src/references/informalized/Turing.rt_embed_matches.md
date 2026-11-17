<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_embed_matches -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of an embedded configuration

**Claim.** Under the stated agreement of states, input positions, embedded tapes and heads, outside tapes and heads, and output, the configuration obtained by embedding $a$ is exactly $d$.

**Proof.** Configurations are equal once their state, input-head position, tape contents, work-tape head positions, and output agree. The first two coordinates agree by the assumed state and input equalities. For any tape index in the image of the injection, write it as $\iota(i)$. The selected-tape and selected-position identities (`embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`) identify the embedded configuration’s tape and head there with those of $a$, which agree with $d$ by hypothesis. For an index outside the image, the embedded configuration uses the chosen surrounding tape and head data; the outside-agreement hypothesis identifies these with $d$. Finally, the embedded output is the prefix followed by $a$’s output, which equals $d$’s output by assumption. Hence all configuration coordinates agree.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`.
