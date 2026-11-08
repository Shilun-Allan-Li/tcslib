<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.tableBitsK_cut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cutting a Transition Table into Read Blocks

**Claim.** The encoded transition table can be decomposed into the complete blocks for the $q$ preceding states, the read entries preceding $(a,w)$ in state $q$, the action at $(q,a,w)$, and a remaining tail, with the stated block and prefix lengths.

**Proof.** Let the ordered states be the finite list from $0$ through $n$, and let the ordered read actions for a fixed state list all input and work-tape read combinations. The table encoding is the concatenation of these state-wise read-action blocks (`tableBitsK_groups`). Split the state list at $q$: its prefix has length $q$, and each state in that prefix contributes one complete read-action block. Each such block has length $3^{k+1}$ (`readActions_length`), since there are three input reads and $3^k$ work-tape read tuples. In the block for state $q$, split the ordered read-action list at the rank $r$ of $(a,w)$. This rank is within the list, and the entry at that index is precisely the action selected by the transition table (`readActions_at`). The preceding list has length $r$; the selected action follows it, and the rest of this state block together with all later state blocks forms the tail. Finally, flattening the state and read blocks concatenates their action encodings, so this decomposition gives the asserted factorization of the bit string.

**Key facts.** `Turing.StepBlock.tableBitsK_groups`, `Turing.StepBlock.readActions_length`, `Turing.StepBlock.readActions_at`.
