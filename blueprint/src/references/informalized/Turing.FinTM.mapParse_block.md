<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapParse_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing One Aligned Bit Pair

**Claim.** Starting at the first bit of an aligned pair in the threaded-map parser, two steps advance the input head past both bits, append the pair to the output exactly when the emitting flag is true, and select the stated successor state according to the pair.

**Proof.** The first step reads $b$ and moves the input head one position right, leaving the controller in the state that remembers $b$; it appends $b$ to the output precisely when the emitting flag is true ($\mathrm{mapParse\_first}$). At the new position, the input-symbol lookup gives $d$, because $x=\mathrm{pre}\,b\,d\,\mathrm{rest}$ and the head now points to the second bit ($\mathrm{mapCfg\_read}$). The parser's transition for the remembered bit $b$ and scanned bit $d$ advances the input head once more. The administrative-action description gives the resulting head position, capture-head displacement, and output update ($\mathrm{mapAction\_apply}$); the input head's right move is exactly to the position after the pair ($\mathrm{moveInputPos\_pos\_of\_ne\_right}$). If the bits agree, the parser continues pair parsing; if $b=1,d=0$, it halts; and if $b=0,d=1$, it enters the post-separator phase. These are the transition cases encoded in the parser, and the two conditional output updates concatenate to append $[b,d]$ exactly when emitting.

**Key facts.** `Turing.FinTM.mapParse_first`, `Turing.FinTM.mapCfg_read`, `Turing.FinTM.mapAction_apply`, `Turing.moveInputPos_pos_of_ne_right`.
