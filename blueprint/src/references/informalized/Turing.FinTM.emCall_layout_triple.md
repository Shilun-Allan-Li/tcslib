<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_layout_triple -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values at tracked tape slots

**Claim.** For each source tape and each of its three tracked components, the call layout at that component's physical index has the value assigned to that component of the tape.

**Proof.** Split into the three possible component indices. In the data case, the index lies in the first tracked block, so the layout selects the data value for tape $i$. In the visited-mark case, it lies in the second block and selects that tape's visited-mark value. In the origin-mark case, it lies in the third block and selects its origin-mark value. These are precisely the three branches in the stated component assignment.
