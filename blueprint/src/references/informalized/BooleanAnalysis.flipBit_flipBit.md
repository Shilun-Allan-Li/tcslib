<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: flipBit_flipBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Flipping a bit twice is the identity

**Claim.** For every `x : BoolCube n` and every coordinate `i`,
`flipBit (flipBit x i) i = x`. Marked `@[simp]`.

**Proof.**

1. `ext j` reduces the equality of hypercube points to an equality of values at
   an arbitrary coordinate `j`.
2. `simp [flipBit, Function.update]` unfolds both updates, leaving a goal that
   branches on whether `j = i`.
3. `split_ifs with h` takes the two branches:
   - on the diagonal, `subst h; simp` closes it — the two nested negations
     cancel by `Bool.not_not`, `!!x i = x i`;
   - off the diagonal, `rfl` — neither update touched `j`, so both sides are
     literally `x j`.

**Remark.** Being an involution makes `x ↦ flipBit x i` a measure-preserving
bijection of the hypercube, which is what licenses the change-of-variables step
in the influence calculations; as a `@[simp]` lemma it is consumed implicitly by
automation rather than at any explicit callsite.

**Used in.** `simp`-normalisation of doubly-flipped points; the companion fact
to `flipBit_ne` in the interface of `flipBit`, and behind the symmetry of
`influence`.
