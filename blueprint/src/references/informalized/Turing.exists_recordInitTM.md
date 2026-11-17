<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.exists_recordInitTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initializing a Configuration Record

**Claim.** For every input length and binary representation of a radius, one can build a deterministic machine that writes the joined record of the initial configuration, with the prescribed initial state and tag, in linear time while keeping its heads within a linear distance of their starting positions.

**Proof.** First obtain the scratch-template machine supplied by the existence theorem for writing a scratch template (`rt_exists_scratchTemplateTM`). Embed its work tapes into a larger tape bank: reserve tape $1$ for the radius word, tape $2$ for scratch, tape $0$ for the destination record, and shift the remaining tapes. The embedding preserves the hypotheses needed by the template machine, including the blankness of its scratch and auxiliary tapes. Its run writes a template on the scratch tape; the template fields have the explicit form given by `rt_template_fields`. The template length is $	ext{posWidth}(|x|)+2s+2$ (`joinFields_recordTemplate_length`), which fits within the final record length, so the head movement bound for this first phase can be absorbed into a larger constant.

Next, initialize the destination from the scratch template. The target record fields are identified by `rt_initRecord_fields`: a state field containing $q_0$, the binary input-position field for the initial head position, $k$ blank work-tape fields of width $2s+1$, and the tag field $	au_0$. The binary position word is positive in length, and the scratch source has the two words required by the filling procedure. Apply `rt_initRest_run` to copy and arrange these fields on tape $0`. The record length identity `joinFields_cfgRecord_length` identifies the target interval with the stated length $L$; the hypotheses that this interval is blank and that all other required cells are blank ensure that the procedure writes exactly the target contents and leaves cells outside the interval unchanged. Its run bound and head bound combine with those of the template phase.

Finally, join the two phases with `rt_copy_seam`. This preserves the first phase's avoidance of its exit state before its endpoint, the second phase's avoidance of its own exit before its endpoint, and the head-distance bounds throughout. The chosen constant $2C+64$ absorbs both time bounds into the requested linear bound, including the case $k=0$. The resulting endpoint has the exit state and exactly the specified tape-$0$ record; all other configuration components are unchanged.

**Key facts.** `Turing.rt_exists_scratchTemplateTM`, `Turing.joinFields_recordTemplate_length`, `Turing.rt_template_fields`, `Turing.rt_initRecord_fields`, `Turing.rt_initRest_run`, `Turing.joinFields_cfgRecord_length`, `Turing.rt_copy_seam`.
