<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.satisfyingExtension_compatible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfying extension preserves compatibility

**Claim.** If a coordinate restriction is compatible with a DNF term, then fixing the free literal coordinates to the values prescribed by the satisfying assignment yields another restriction compatible with that term.

**Proof.** Apply the compatibility-preservation fact for fixing the free literal positions (`FABL.DNFTerm.compatible_fix_freeLiteralPositions`). Its hypothesis on the assignment is that the relative bit vanishes at each such position. The satisfying-assignment relative-bit identity supplies exactly this: at every literal position the assigned bit agrees with the required bit, so their sum in $\mathbb{F}_2$ is zero (`FABL.DNFTerm.relativeBit_satisfyingAssignment`). The original compatibility assumption and this identity give the claimed compatibility after the coordinates are fixed.

**Key facts.** `FABL.DNFTerm.compatible_fix_freeLiteralPositions`, `FABL.DNFTerm.relativeBit_satisfyingAssignment`.
