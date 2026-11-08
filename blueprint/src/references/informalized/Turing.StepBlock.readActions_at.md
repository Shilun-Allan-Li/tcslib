<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.readActions_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed Transition Actions

**Claim.** The entry at rank $3^k\,\mathrm{rank}(\mathrm{inp})+\mathrm{rank}(w)$ in the list of transition actions at state $q$ is exactly $\mathrm{tr}(q,\mathrm{inp},w)$.

**Proof.** The work-read patterns form a list of length $3^k$, and every pattern occurs in that list (`Turing.StepBlock.length_workReadsK`, `Turing.StepBlock.mem_workReadsK`). Hence the index of $w$ in this list is in range, and retrieving that index after mapping a transition over the list returns the transition for $w$. Each of the three input-read blocks in `readActions` is such a mapped list and has length $3^k$. If the input read is blank, the specified rank is the index within the first block. If it is $0$, the rank shifts past the first block and selects the corresponding entry in the second. If it is $1$, it shifts past both preceding blocks and selects that entry in the third. In each case, the within-block index is the index of $w$, so the selected action is $\mathrm{tr}(q,\mathrm{inp},w)$. The total list length used to justify the outer index is given by `Turing.StepBlock.readActions_length`.

**Key facts.** `Turing.StepBlock.length_workReadsK`, `Turing.StepBlock.mem_workReadsK`, `Turing.StepBlock.readActions_length`.
