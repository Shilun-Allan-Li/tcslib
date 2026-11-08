<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonStrictInstall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict installation of a computed function

**Claim.** Every finite Boolean Turing machine computing $f$ in time $T$ can be incorporated into a finite Boolean machine with at least one work tape that installs $f(\mathrm{arg})$ on tape $0$ within the stated linear bound and reaches its exit state for the first time at the installation time.

**Proof.** Begin with the installation machine supplied by `exists_installCallTM`. It reaches an exit state with the required tape contents within the stated bound, and its exit is avoided at all positive times before that arrival. The only possible failure of the desired strict first-arrival condition is that its entry and exit states coincide, since time zero begins in the entry state. If they coincide, prepend a release phase using `seamReleaseTM`: start in a new left-summand state and run the original machine, whose first positive return to the anchor is exactly its successful completion. The seam-release first-return result (`seamReleaseTM_firstReturn`) shows that the new right-summand exit is avoided at every earlier time, while preserving the completion time, bound, and tape contents. If entry and exit are distinct, time zero is already safe; every later time before arrival is covered by the original positive-time avoidance property. The work-tape count is unchanged in either case, so it remains positive.

**Key facts.** `Turing.FinTM.exists_installCallTM`, `Turing.seamReleaseTM_firstReturn`.
