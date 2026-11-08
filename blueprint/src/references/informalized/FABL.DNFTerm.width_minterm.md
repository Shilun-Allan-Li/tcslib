<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.width_minterm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of a minterm

**Claim.** For every input $x\in\{\pm1\}^n$, the minterm specifying $x$ at each coordinate has width $n$.

**Proof.** The minterm lists one literal for each coordinate, using the finite range of the $n$ coordinates. Its width is the length of this list, which is the length of the finite range and therefore equals $n$.
