<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/FiniteFields.lean :: FABL.ncard_rootSet_le_natDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Root count and degree

**Claim.** For a field $K$ and polynomial $p\in K[X]$, the number of distinct roots of $p$ in $K$ is at most its natural degree.

**Proof.** Apply the polynomial root-count bound: over a field, a nonzero polynomial has at most as many distinct roots as its natural degree. The zero polynomial also satisfies the stated inequality, since its root set is all of $K$ and its natural degree is zero only when $K$ is finite of cardinality at most zero—which cannot occur for a field. However, the supplied proof directly invokes `Polynomial.ncard_rootSet_le`; its applicability and handling of the zero polynomial are precisely what establish the claim in the library.

**Caveat.** The proof source delegates entirely to `Polynomial.ncard_rootSet_le`, but its statement is not included among the provided upstream facts. The usual root-count theorem requires a nonzero polynomial, while the formal statement imposes no such hypothesis.
