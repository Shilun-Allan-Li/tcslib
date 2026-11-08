<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.expect_fullParity_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of Full Parity

**Claim.** For a finite nonempty index set, the expected product of independent uniform signs indexed by that set is zero.

**Proof.** Relabel the indices by the equivalent set of indices $\{0,\ldots,|\iota|-1\}$. This bijection also relabels sign assignments and preserves the product, so it preserves the expectation. On the sign cube with these indices, the product is the monomial indexed by the entire coordinate set. The expectation of a monomial is $1$ for the empty index set and $0$ otherwise (the monomial expectation formula, `expect_monomial`). Since the original index set is nonempty, its cardinality is positive, so the full coordinate set is nonempty. The expectation is therefore zero.

**Key facts.** `FABL.expect_monomial`.
