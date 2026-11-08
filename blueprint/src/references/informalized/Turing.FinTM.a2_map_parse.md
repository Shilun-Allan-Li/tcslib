<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_parse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing a remaining input suffix

**Claim.** For a suffix $r$ following prefix $p$, the non-forward simulator reaches within the stated bound either the virtual configuration corresponding to a successful decoding of $r$, or a halted configuration with empty output when decoding fails.

**Proof.** Induct on the suffix by cases of its initial shape, using two-step list induction. For the empty suffix, one parsing step reads the right boundary and halts without output. For a one-bit suffix, the first parsing step stores that bit as pending; the next step encounters the boundary and halts, again with empty output. For a suffix beginning with two equal bits $b,b$, the two-step pair-parsing result (`a2_map_block`) appends $b$ to the first buffer and returns to parsing. Apply the induction hypothesis to the remaining suffix, extending the already-read prefix by $[b,b]$ and the buffer by $[b]$. The decoding recursion says that decoding succeeds exactly when the remainder decodes successfully, with $b$ prepended to its first component; otherwise it remains undefined. Composing the two steps with the inductive run (`runFrom_add`) gives the asserted endpoint and the bound. If the first two bits differ as $0,1$, pair decoding terminates successfully with the remaining suffix as the second word; the block result enters copyB, and the completion result (`a2_map_finish`) performs the remaining copy, return, and emission phases. Its output and buffer are precisely the virtual configuration for the decoded pair. The other unequal case, $1,0$, halts in the block result with no output, so it supplies the failure case immediately. The empty and one-bit cases, together with these pair cases, exhaust all suffixes; the single-bit reading step is justified by `a2_map_first`.

**Key facts.** `Turing.FinTM.a2_mapCfg_read`, `Turing.FinTM.a2_map_block`, `Turing.FinTM.a2_map_finish`, `Turing.FinTM.a2_map_first`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
