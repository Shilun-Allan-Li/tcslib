<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.lastOutput_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last output after appending an optional bit

**Claim.** Appending an optional bit to a finite bit list makes the resulting last bit that bit when present; when absent, the last bit remains the list's last bit, with false as the default for an empty list.

**Proof.** Split according to whether the optional bit is absent or present. If absent, appending contributes the empty list, so the last entry and its default are those of $w$. If present, the appended singleton is nonempty and its last entry is the appended bit. These are precisely the two values on the right-hand side.
