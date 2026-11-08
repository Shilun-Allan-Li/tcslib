<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.blockCode_nonzero_of_not_compatible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero block code from incompatibility

**Claim.** If the original restriction is compatible but becomes incompatible after fixing its free literal coordinates according to $x$, then the block code of those free literal positions has a bit equal to $1$.

**Proof.** Suppose instead that the block code has no position with bit $1$. For any free literal position, its embedded position belongs to the block code's position set, because that position is included in the image of the selected set. The block-code bit there equals the relative bit for that literal (`FABL.DNFTerm.blockCode_bits`). Since no code bit is $1$, this relative bit must be zero; over $[1m\mathbb{F}_2[0m$, the only alternative to $1$ is $0$. Thus every free literal position has relative bit zero. The compatibility-preservation result says that if the original restriction is compatible and all these relative bits vanish, then fixing the corresponding free literal coordinates according to $x$ leaves the term compatible (`FABL.DNFTerm.compatible_fix_freeLiteralPositions`). This contradicts the assumed incompatibility. Therefore the block code must have a position whose bit is $1$.

**Key facts.** `FABL.DNFTerm.compatible_fix_freeLiteralPositions`, `FABL.DNFTerm.blockCode_positions`, `FABL.DNFTerm.blockCode_bits`.
