<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.cert_call_cut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cutting a Machine Call

**Claim.** Under the stated hypotheses, one can construct a finite-state machine with a start and finish state that reaches the prescribed final tape words within the same budget and does not visit the finish state earlier.

**Proof.** There are two cases. If the entry and exit states coincide, replace the machine’s states by a disjoint union of a new start state and copies of the old states, using the seam-release construction at the common state. For each parameter, take the positive time supplied by the hypothesis. The first-return property of this construction says that the run reaches the copied exit state at that time with the same final configuration, and does not visit it earlier; the claimed configuration and prefix condition follow from this property. If the entry and exit states differ, keep the original machine and states. Use the supplied time and final configuration. At time zero the new start state differs from the finish state, while at each positive time before the supplied time the hypothesis excludes the exit state. Thus the same time and budget work.

**Key facts.** `Turing.seamReleaseTM_firstReturn`.
