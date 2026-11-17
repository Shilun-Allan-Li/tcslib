<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPair_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying the remaining input suffix

**Claim.** When $x=pr$, the pairing machine in native-copy state, positioned just before the suffix $r$, copies that suffix to the output and halts after $|r|+1$ steps, with the other canonical configuration data preserved.

**Proof.** Induct on the suffix $r$. If $r$ is empty, the input head is at the end of $x$. The input-symbol formula (Complexity.satPairCfg_input) therefore gives no symbol. The machine’s state-7 transition on this end marker halts without moving the capture head or appending output; the single transition is the claimed $|r|+1=1$ step. For the inductive case, write $r=b::r'$. At the current position the scanned input symbol is $b$, again by Complexity.satPairCfg_input and the decomposition $x=p(b::r')$. The state-7 transition appends $b$ and advances the input head one position, yielding the canonical configuration for prefix $p++[b]$ with output $o++[b]$. This transition calculation uses the action-on-canonical-configurations lemma (Complexity.satPairAction_apply) and the one-position movement fact (Turing.moveInputPos_pos_of_ne_right). Apply the induction hypothesis to $r'$ from that new configuration; its remaining $|r'|+1$ transitions complete the copy and halt. The successor-step law for runs (Turing.MultiTapeTM.runFrom_succ_eq_step) relates these transitions to the stated run length, and list associativity identifies the accumulated output as $o++r$.

**Key facts.** `Complexity.satPairCfg_input`, `Complexity.satPairAction_apply`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
