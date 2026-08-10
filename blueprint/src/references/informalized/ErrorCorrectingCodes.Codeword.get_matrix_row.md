<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/LinearCodes.lean :: get_matrix_row -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Extracting a single row of a matrix as a `1 × k` matrix

**Definition.** For `M : Matrix (Fin n) (Fin k) α` and a row index `i : Fin n`,

```
get_matrix_row n k M i : Matrix (Fin 1) (Fin k) α
get_matrix_row n k M i = Matrix.of (fun _ j => M i j)
```

i.e. row `i` of `M`, repackaged as a matrix with a single row. The row index of
the result is discarded (`fun _ j => …`), so the value at either `Fin 1` index
is the same. This is a plain `def` with no proof content.

**Remark.** The reshaping to `Matrix (Fin 1) (Fin k) α` — rather than to a bare
vector `Fin k → α` — is what lets `Matrix.mulVec` be applied uniformly to rows
and to the whole matrix, which is how `uniformity_lemma` reduces
`G · x = v` to the conjunction of per-row conditions
`get_matrix_row n k G i · x = fun _ => v i`. The consequence is that most of the
surrounding proof spends its effort transporting across the `Fin 1` index
(`congrFun … 1`).

**Used in.** Only inside the proof of `uniformity_lemma` (the `h2`, `h3`, `h4`
steps of the row-by-row counting argument); it is a local convenience helper,
not referenced elsewhere in the library.
