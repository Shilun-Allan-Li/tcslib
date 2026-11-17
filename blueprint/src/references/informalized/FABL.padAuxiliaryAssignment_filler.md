<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.padAuxiliaryAssignment_filler -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values at filler coordinates

**Claim.** When $a+3\le K$, padding an auxiliary assignment with $-1$ gives value $-1$ at each of the coordinates $a,a+1,a+2$.

**Proof.** For $j\in\{0,1,2\}$, the selected coordinate has index $a+j$, which is at least $a$. Therefore it is not among the original $a$ coordinates, so the extension takes its filler value, namely $-1$. The gap assumption ensures each of these coordinates lies within the $K$-coordinate assignment.
