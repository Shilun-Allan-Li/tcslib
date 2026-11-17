<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.vScan_cfgWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration scan correctness

**Claim.** Scanning the initial $W(2s+1)$ bits of the encoded configuration word records the configuration's head and output summary, satisfies the scanner's acceptance condition, records each work-tape symbol at its head correctly, and sets its blankness flag exactly when every window cell has the joint-blank property.

**Proof.** The scan over the indicated prefix is equal to folding the cell-update rule over the $2s+1$ cells in the window (`vScan_cfgWord_eq`). Apply the fold characterization (`foldl_vStep`): it says that the recorded head/output pair comes from the first cell, each head-occupancy flag records whether that tape's head occurs in the window, the stored work symbol is taken from the unique cell carrying that head, the acceptance flag checks the correct placement and uniqueness of heads, and the blankness flag is the conjunction of the joint-blank conditions over all scanned cells.

For the first cell, the encoding places the configuration state and output summary there, giving the claimed recorded pair. For any tape head, the in-window bound places its position among the scanned cells: if its coordinate is $z$, then the corresponding cell index is $z+s$, which lies between $0$ and $2s$ and represents coordinate $z$ after subtracting $s$. The head-indicator definition therefore marks that cell, and the uniqueness of the coordinate identifies it as the only marked cell. The fold characterization then shows that the recorded work symbol is exactly the symbol at the actual head position. Finally, its blankness conclusion is exactly the stated equivalence for all cells of the window.

**Key facts.** `Complexity.Codec.vScan_cfgWord_eq`, `Complexity.Codec.foldl_vStep`.
