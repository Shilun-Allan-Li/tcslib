<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_tight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# One extra unit of slack when both inputs are non-empty

**Claim.** (`private`) For a non-empty literal list `fl :: fls` and a non-empty
path `step :: rest`, writing `p := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ`,

`p.2.2.2.length + 1 + 2 * p.1.length ≤ 2 * (step :: rest).length`.

This is `processClauseLits_bound` (which gives the same inequality without the
`+ 1`) strengthened by one unit, available precisely because a non-empty input
must consume at least one path entry.

**Proof.** Two steps.

1. `simp only [processClauseLits, List.length_cons]` unfolds the recursive
   defining equation, replacing `p` by the call on `fls`/`rest` with
   `Function.update ρ₀ fl.1.var (some step.2)` and
   `Function.update σ fl.1.var (some (!fl.1.neg))`, and rewriting both `length`s
   of the cons lists.
2. Instantiate `processClauseLits_bound fls rest _ _` at those updated
   restrictions and finish with `omega`: the recursive step costs one aux entry
   while the path budget drops by `2`, so a unit of slack is left over. ∎

**Used in.** `encode_go_aux_length_bound` (same file), whose induction needs the
strict decrease to absorb the per-clause termination marker `(w, false)` appended
by `razborovEncode.go`; that bound in turn yields
`razborovEncode_aux_length_le : … ≤ 2 * d`.
