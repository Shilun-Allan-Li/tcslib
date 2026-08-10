<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: fourierCoeff_signEval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The recursion computes the actual Fourier coefficients

**Claim.** For every `T : DecisionTree n` and every `S : Finset (Fin n)`,
`fourierCoeff T.signEval S = T.coeffs S`: the recursively defined
`DecisionTree.coeffs` is literally the Fourier spectrum of the ±1-encoded tree
function.

**Proof.** Three lines.

1. A `have hrepr` promotes the pointwise identity `signEval_eq_sum_coeffs` to an
   equality of functions, `T.signEval = fun x => ∑_S T.coeffs S * chiS S x`, via
   `funext`.
2. `rw [hrepr, fourierCoeff_sum_chiS]` — rewriting along `hrepr` puts the
   function in explicit character form, and uniqueness of the Fourier expansion
   reads off the coefficient.

**Remark.** This is the hinge of the file: everything before it is a statement
about the auxiliary recursion `coeffs`, and everything after it is the same
statement about `fourierCoeff T.signEval`.

**Used in.** All four parts of O'Donnell Proposition 3.16 —
`degree_le_depth`, `spectral_one_norm_le`, `fourierCoeff_granular` and (via the
latter) `sparsity_le` — each of which rewrites with this lemma and then applies
the corresponding `coeffs`-level result.
