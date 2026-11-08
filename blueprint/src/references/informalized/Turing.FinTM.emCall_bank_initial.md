<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_bank_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cleaner Entry Reproduces the Bank Frame

**Claim.** Embedding the cleaner’s entry configuration for tape $i$, initialized with that tape’s data, visited-span marker, origin marker, and head position from the run of $M$, into its three bank slots reproduces the bank frame with the first $i$ banks blank and the cleaner in state $0$ for tape $i$.

**Proof.** Compare tape contents and head positions slot by slot using the layout case theorem (`emCall_layout_cases`). The argument and capture slots are outside the cleaner’s three-slot image, so the embedding preserves their frame values. For each source tape $j$, the triple-layout identity (`emCall_layout_triple`) identifies its three slots. When $j=i$, the cleaner’s initialized data, span marker, origin marker, and head position were taken directly from the run of $M$, so these slots match the corresponding entries in the frame. When $j\ne i$, the embedding leaves the slots unchanged, and the triple-selection facts (`emCall_triple_inverse`, `emCall_triple_other`, and `emCall_triple_pair`) show that they are not among the cleaner’s selected slots. The input position, output, and all unselected tape values are preserved by the embedding; the state is mapped to state $0$ for tape $i$. Thus every field agrees with the bank frame.

**Key facts.** `Turing.FinTM.emCall_layout_cases`, `Turing.FinTM.emCall_triple_inverse`, `Turing.FinTM.emCall_triple_other`, `Turing.FinTM.emCall_triple_pair`, `Turing.FinTM.emCall_layout_triple`.
