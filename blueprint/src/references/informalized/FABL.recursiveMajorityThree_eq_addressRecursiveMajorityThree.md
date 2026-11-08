<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThree_eq_addressRecursiveMajorityThree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Address Representation of Recursive Majority

**Claim.** For every depth $d$ and sign input $x$ indexed by $0,\ldots,3^d-1$, recursive majority on $x$ equals address-based recursive majority on the assignment taking each formula address to the input sign at its corresponding index under the canonical indexing equivalence.

**Proof.** Proceed by induction on $d$. At depth zero, the coordinate set and the address space each have one element, and both recursive definitions return the sign at that unique coordinate. For the successor step, expand recursive majority using its successor equation (`recursiveMajority_succ`): it takes majority of the recursive-majority values on the three input blocks. Apply the induction hypothesis to each block. The canonical indexing equivalence at successor depth identifies an index with a pair consisting of a first ternary coordinate and a lower-depth index; accordingly, the input on block $i$ at a lower-depth index is exactly the address assignment at $(i,a)$. Thus the three inductive expressions are precisely the three address-recursive branches, and the definitions agree.

**Key facts.** `FABL.recursiveMajority_succ`.
