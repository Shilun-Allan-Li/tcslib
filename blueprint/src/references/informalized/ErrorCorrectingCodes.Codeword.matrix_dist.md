<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/LinearCodes.lean :: matrix_dist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Distribution of `G · x` for a uniformly random generator matrix

**Definition.** For a fixed message `x : Codeword k α` over a finite field `α`,
`matrix_dist n k x : Codeword n α → ℝ` assigns to each output word `v` the
fraction of `n × k` matrices that send `x` to `v`:

```
matrix_dist n k x v =
  (finite_matrix_dist n k v x).toFinset.card / (Fintype.card α) ^ (n * k)
```

The numerator is the cardinality of `{G | G · x = v}`, made a `Finset` via the
finiteness proof `finite_matrix_dist`; the denominator `|α|^(n·k)` is the total
number of `n × k` matrices over `α`. The declaration is a plain
`noncomputable def` with no proof content.

**Remark.** Nothing here asserts that `matrix_dist` is a probability
distribution; that it is in fact the uniform distribution
`uniform_vector_dist n α` — for every `v` alike — is the content of
`uniformity_lemma`, and only under the hypotheses `x ≠ zero` and `k ≥ 1`.

**Used in.** `uniformity_lemma`, and unfolded in `GilbertVarshamov.lean` where
the uniformity statement is consumed.
