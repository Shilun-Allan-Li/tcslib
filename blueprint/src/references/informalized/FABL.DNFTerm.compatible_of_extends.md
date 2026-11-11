<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.compatible_of_extends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility under restriction extension

**Claim.** If every coordinate fixed by $$ is fixed to the same state by $$, and a term is compatible with $$, then it is compatible with $$.

**Proof.** Take an assignment $x$ witnessing compatibility with $$. Define a new binary assignment $y$ by encoding, coordinate by coordinate, the sign in the completed vector for $$ and $x$. We show that completing $$ with $y$ reproduces that same sign vector. If a coordinate is free in $$, its completion encodes $y$ back to the sign used to define $y$, by the inverse property of the binary-sign equivalence. If it is fixed at either sign, the extension hypothesis forces $$ to have that same fixed state, so both completions give the identical fixed sign. Therefore the completed vectors coincide, and the witness property for $x$ transfers to $y$.

**Caveat.** The supplied informal statement has lost the symbols naming the two restrictions in several places. The proof uses the standard orientation: $$ is the restriction being extended, $$ is the extension, and compatibility with the extension implies compatibility with the original restriction.
