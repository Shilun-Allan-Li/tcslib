<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPair_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replaying a captured suffix

**Claim.** If $u=pr$, replaying from state 4 with the capture head at $|p|$ takes $2|r|+2$ steps, appends the doubled bits of $r$ and separator $01$, leaves the input head and saved configuration unchanged, and enters native-copy state with the capture head at $|u|$.

**Proof.** Induct on $r$. If $r$ is empty, the decomposition gives $u=p$. At the capture head, the buffer tape has no symbol because the head is at the end of $u$. State 4 responds by appending false and entering state 6; state 6 appends true and enters state 7. Both transitions leave the input and capture-head positions unchanged. The action-on-canonical-configurations lemma (Complexity.satPairAction_apply) verifies the configuration updates, and the zero-movement fact (Turing.moveInputPos_zero) keeps the input head fixed. These two steps append precisely the separator. Now suppose $r=b::r'$. The buffer tape at offset $|p|$ contains $b$, by the decomposition and the natural-offset buffer lookup (Turing.FinTM.bufferTape_nat). In state 4 the machine appends $b$ and enters state 5 without moving the capture head; state 5 appends $b$ again, advances the capture head, and returns to state 4. The canonical action lemma (Complexity.satPairAction_apply) gives these updates. Thus two steps append $bb$ and move the head to the start of the remaining suffix. Apply induction to $r'$ with prefix $p++[b]$ and output extended by $bb$. The run successor-step law (Turing.MultiTapeTM.runFrom_succ_eq_step) combines the two initial steps with that run. The resulting output is the doubled suffix followed by $01$, and the final head position is $|u|$.

**Key facts.** `Complexity.satPairCfg_work`, `Turing.FinTM.bufferTape_nat`, `Complexity.satPairAction_apply`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
