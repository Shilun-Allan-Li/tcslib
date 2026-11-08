<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean :: Complexity.LogProg.skipPrefix_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning a Paired-Input Prefix

**Claim.** Under the stated transition assumptions, the machine scans the doubled unary prefix and its separator, reaching state $n_x$ with the input head at position $3+2n$ while preserving the tapes, output, and register-head position; every earlier configuration satisfies the stipulated reachability relation without an oracle call.

**Proof.** Write the input as $1^{2n}01\,\mathrm{rest}$. The repeated scan lemma (`scanR`) handles the first $2n$ positions: at each position the scanned bit is true, so the transition moves right and stays in state $j_K$. At the next position the separator bit is false, so the transition moves right into $j_{K2}$; one further right move enters $n_x$. The one-step conclusions follow from `reaches_right`, with the input-symbol indexing justified by `inSym_succ`. The assumptions that neither scanning state is an oracle-call state ensure each intermediate state meets the reachability requirement. Compose the repeated scan and the two final steps using reflexivity, step extension, and transitivity of reachability (`Reaches.refl`, `Reaches.step`, `Reaches.trans`). The input head has advanced by $2n+2$ positions from its initial position $1$, giving $3+2n$; the actions leave tape contents, output, and the specified register-head position unchanged.

**Key facts.** `Complexity.LogProg.scanR`, `Complexity.LogProg.inSym_succ`, `Complexity.LogProg.reaches_right`, `Complexity.LogProg.Reaches.refl`, `Complexity.LogProg.Reaches.step`, `Complexity.LogProg.Reaches.trans`.
