<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNAND_eq_addressRecursiveNAND -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive NAND on Addressed Inputs

**Claim.** For every depth $d$ and sign assignment $x$ to the $2^d$ coordinates, recursive NAND equals address-recursive NAND on the assignment giving each formula address the value of $x$ at its corresponding index under the canonical bijection.

**Proof.** Proceed by induction on $d$. At depth zero, both definitions return the input at the unique coordinate, which corresponds to the unique depth-zero address. For the successor step, expand recursive NAND at depth $d+1$ (`recursiveNAND_succ`). Its two branches are recursive NAND applied to the two input blocks. The induction hypothesis identifies each branch with address-recursive NAND on the addresses whose first digit is respectively $0$ and $1$. Under the canonical indexing equivalence, these are exactly the two restrictions of the full address assignment. Combining the two branch values by NAND is therefore the defining successor step of address-recursive NAND.

**Key facts.** `FABL.recursiveNAND_succ`.
