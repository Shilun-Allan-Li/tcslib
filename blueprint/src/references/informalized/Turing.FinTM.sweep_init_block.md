<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweep_init_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialization Block Construction

**Claim.** After $k$ initialization steps, the simulator has marked blank cells for all $k$ work tapes, with frontier advanced by $k$, those cells placed before the original left stack in reverse order, and the first $k$ entries removed from the right stack; the input position and output are unchanged.

**Proof.** Let $w$ be the list of the $k$ encoded marked blank cells, one for each work tape. Its length is $k$. At initialization counter $i<k$, the transition writes the cell corresponding to tape $i$, advances the frontier by one, and moves the work head right. The zipper update for a rightward move (`sweepCfg_right_any`) expresses precisely this change: the written cell is pushed onto the left stack and the right stack loses its head. Thus the machine satisfies the step-by-step hypothesis of the general block-generation result (`sweep_generate`) with frontier increment $1$. Applying that result for $k$ steps gives counter $k$, frontier $z+1\cdot k$, the reverse of the written block followed by $l$, and right stack $r$ with its first $k$ entries dropped. Since the block has length $k$, the generated prefix is the whole block. The transition changes neither input position nor output, as recorded in the zipper update.

**Key facts.** `Turing.FinTM.sweepCfg_right_any`, `Turing.FinTM.sweep_generate`.
