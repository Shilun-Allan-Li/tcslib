<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_triple_inverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triple index and selection are inverse

**Claim.** For each source tape and each component among the data, visited-marker, and origin-marker banks, selection at that component's assigned physical index returns that component.

**Proof.** The component has only three possibilities. The proof checks each one against the three defining index formulas. The source tape index is strictly positive, since it is a member of `Fin M.k`; consequently the three block offsets are distinct and the selected equality is precisely the one for the chosen component. The other selection tests fail, so the result is the chosen component in each case.
