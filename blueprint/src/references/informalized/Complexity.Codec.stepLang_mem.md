<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean :: Complexity.Codec.stepLang_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Logarithmic-Space Membership of the Step Language

**Claim.** For every finite nondeterministic Turing machine with Boolean symbols, the language of pair-encoded tuples describing radius-bounded configuration codes related by one step is decidable in logarithmic space.

**Proof.** The proof constructs a logarithmic-space alternating machine for the language, using the already logarithmic-space codecs. Its correctness is established by analyzing an arbitrary input $y$ and the machine’s parsing and verification runs.

First, parse $y$ as a candidate nested pair encoding. If it has no such shape, the parser halts with rejection. If it does, parsing determines candidates $x,w,w',s$. Pair-encoding injectivity ensures that any other candidate decomposition has exactly these same components. The parser also bounds the encoded space parameter by $2|y|$ (`s_le_of_width`), so the later scans fit within the resource bound `bnd_ge`.

The layout phases inspect the proposed configuration words. The first layout phase either rejects a malformed length or terminal bit, or establishes the required format for $w$; `layout_run` supplies this dichotomy. The input-position field is then decoded. The inequalities `bitsVal_lt_two_pow` and `two_pow_bits_le`, together with `wP_le`, bound this decoded position by a quantity linear in $|x|$. The phase lemma `le_phase` proceeds only when that position is at most $|x|+1$; otherwise it halts and rejects. A second layout phase performs the corresponding checks for $w'$ and provides its length and terminal-bit conditions (`layout2_run`).

Next the machine reads the input symbol at the decoded position (`insym_run`) and scans the first configuration portion. The scan run `vscan_run` produces the verifier state representing the scan of $w$’s configuration cells. The final transition-checking phase is governed by `step_tail`: it halts with the Boolean result of `stepAns`, using the decoded input positions and the two configuration portions.

To identify this result with language membership, apply `stepAns_iff` using the precheck and output-format facts established by the layout phases. Then `stepLang_iff` identifies the step-check predicate with existence of the two bounded configurations and a one-step transition. Thus the final Boolean answer is true exactly when $y$ belongs to the step language. If any parsing or layout branch rejects, the same characterization shows that no valid step-check witness exists, so the language indicator is false. The concatenated machine runs form a valid accepting or rejecting computation by transitivity of reachability (`Reach.trans`, `AReach.halt`); the rejection branch uses `indicator_eq_of_iff`. Finally, `arm_decides_poly` converts this correct alternating-machine procedure, with the polynomial resource bound supplied by `gd_mono` and the logarithmic-space codecs, into membership in LOGSPACE.

**Key facts.** `Complexity.Codec.codecAs_mem`, `Complexity.Codec.gd_mono`, `Complexity.Codec.indicator_eq_of_iff`, `Complexity.Codec.pairEncode_inj`, `Complexity.Codec.parse_run₂`, `Complexity.Codec.shape2_of_code`, `Complexity.Codec.s_le_of_width`, `Complexity.Codec.bnd_ge`, `Complexity.Codec.layout_run`, `Complexity.Codec.bitsVal_lt_two_pow`, `Complexity.Codec.two_pow_bits_le`, `Complexity.Codec.wP_le`, `Complexity.Codec.le_phase`, `Complexity.Codec.layout2_run`, `Complexity.Codec.insym_run`, `Complexity.Codec.vscan_run`, `Complexity.Codec.step_tail`, `Complexity.Codec.stepAns_iff`, `Complexity.Codec.stepLang_iff`, `Complexity.LogProg.AHalt.mono`, `Complexity.LogProg.AReach.halt`, `Complexity.Codec.Reach.trans`, `Complexity.LogProg.arm_decides_poly`.

**Caveat.** The source delegates the detailed symbol-by-symbol behavior and correctness of parsing, layout, scanning, and the final checking phase to substantial upstream machine-run lemmas; their statements establish the phase interfaces, but their internal simulations are not included here.
