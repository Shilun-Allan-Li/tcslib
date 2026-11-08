<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.ac0ThresholdParityTarget_activeRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Active Restriction of the Parity Target

**Claim.** For $m\ge7$, placing the sign coordinates of a vector $y$ of length $2m^2$ on the active coordinates of the longer input, and setting every inactive coordinate to $+1$, makes the parity target equal the sign-valued mod-two inner product of the two length-$m^2$ blocks of $y$.

**Proof.** Convert $y$ through the binary/sign cube equivalence to a binary vector $z$, and split $z$ into its first and second blocks, denoted $a,c\in\mathbb F_2^{m^2}$. The block decomposition equivalence says that joining $a$ and $c$ recovers $z$. It is therefore enough to evaluate the target on the sign encoding of this joined vector.

Fix a block index $b\in\{0,\ldots,m-1\}$. Its first group of $m$ queried coordinates has indices $bm+i$ for $0\le i<m$, and its second group has indices $m^2+bm+i$. These are precisely the coordinates in the two blocks indexed by the pair $(b,i)$ under the product reindexing. The active-coordinate bound ensures that these indices lie among the active coordinates; by the active-coordinate combination identity (\(\texttt{FABL.combine\_ac0ActiveCoordinates}\)), the constructed input returns the corresponding coordinate of $y$ there. Thus the entire length-$2m$ sign input for block $b$ is the sign encoding of the two length-$m$ slices of $a$ and $c$ at index $b$.

Consequently, each factor in the target's product over $b$ is the mod-two inner product output for those two slices. The product of these block outputs equals the mod-two inner product output on the full vectors of length $m^2$, by the product decomposition identity (\(\texttt{FABL.prod\_innerProductModTwoBoolean\_blocks}\)). This is the claimed value on $y$.

**Key facts.** `FABL.activeCoordinateCount_le_dimension`, `FABL.blockCoordinateValue_lt_active`, `FABL.combine_ac0ActiveCoordinates`, `FABL.prod_innerProductModTwoBoolean_blocks`.
