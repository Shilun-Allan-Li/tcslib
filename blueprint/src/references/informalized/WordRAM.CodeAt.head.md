<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.CodeAt.head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Instruction at a Code Position

**Claim.** If the list beginning at position $\mathrm{pos}$ has $i$ as its first instruction, then the instruction at that position in $P$ is $i$, with positions beyond the end of $P$ interpreted as reject.

**Proof.** Since $i::l$ is a prefix of $P$ dropped by $\mathrm{pos}$, there is a remainder list whose concatenation with $i::l$ equals that dropped list. Thus the zeroth entry of the dropped list is $i$. The zeroth entry of $P$ dropped by $\mathrm{pos}$ is the entry of $P$ at index $\mathrm{pos}$, when present. Reading that entry with the default value reject therefore returns $i$.
