<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: term_length_le_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every term of a DNF is at most as long as the DNF's width

**Claim.** If `t ∈ f` for a DNF `f : DNF n` (a list of terms, each term a list
of literals), then `t.length ≤ f.width`. Here `Term.width t = t.length` and
`DNF.width f = (f.map Term.width).foldr max 0`.

**Proof.** `unfold DNF.width Term.width`, then induction on `f`.

1. `nil`: `t ∈ []` is absurd (`simp at ht`).
2. `cons hd tl`: `simp only [List.map_cons, List.foldr_cons]` presents the width
   as `max hd.length ((tl.map _).foldr max 0)`, and `List.mem_cons.mp ht` splits:
   - `t = hd`: `le_max_left`.
   - `t ∈ tl`: the induction hypothesis bounds `t.length` by the tail's fold,
     then `le_max_right` and `le_trans`.

**Remark.** The fold-based `max` definition of width means this is not a `simp`
one-liner; the induction is what converts "member of the list" into "bounded by
the running maximum".

**Used in.** `Switching.lean:326` and `:549`, and
`Switching/RoundTrip.lean:223` — each time to turn a width hypothesis
`f.width ≤ w` into a length bound on the clause the encoding is currently
processing.
