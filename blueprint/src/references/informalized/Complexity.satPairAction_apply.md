<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPairAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing action on canonical configurations

**Claim.** Under the stated input-head and tape-head movement equalities, the pairing administrative action transforms the canonical pairing configuration to the one with the updated state and positions, and appends the optional bit to the output.

**Proof.** The action preserves the saved machine state and tape contents. Its input movement carries position $i+1$ to $i'+1$ by the assumed equality, and its administrative state becomes $q'$. On each original tape, it makes no write and no movement, so the saved tape data and head positions remain unchanged. On the added tape, it makes no write and moves the head by $d$, taking position $j$ to $j'$ by the assumed equation. Finally, the action appends the optional bit $b$ to the output, giving $o$ followed by $b$ when present.
