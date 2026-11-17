<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.agreeOutside_effect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Outside a Write Set

**Claim.** If an instruction satisfies the condition for writing in $s$, then its effect on memory agrees with the original memory at every address outside $s$.

**Proof.** Consider the instruction forms. For a one, addition, subtraction, multiplication, or load instruction, the effect updates its destination address, and the hypothesis says that this address lies in $s$. Updating a memory at an address in $s$ preserves agreement with the original memory on the complement of $s$; this is the update property of agreement outside a set (\(\texttt{WordRAM.AgreeOutside.update}\)), applied to reflexive agreement before the update (\(\texttt{WordRAM.AgreeOutside.refl}\)). For a store instruction, the write condition is false, so there is no case satisfying the hypothesis. For branch and halting instructions, the memory effect leaves the memory unchanged, and reflexive agreement gives the result directly (\(\texttt{WordRAM.AgreeOutside.refl}\)).

**Key facts.** `WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`.
