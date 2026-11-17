<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.padAuxiliaryAssignment_castLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of auxiliary coordinates

**Claim.** Extending an auxiliary sign assignment on $a$ coordinates to $K$ coordinates by retaining the first $a$ coordinates and filling the rest with $-1$ preserves its value at every original coordinate.

**Proof.** For $i\in\{0,1\}^a$ represented as a finite index, its cast into the first $a$ coordinates of the larger index set has the same underlying index, which is less than $a$. Thus the extension uses the original-assignment branch of its definition, and the value there is exactly $u(i)$.
