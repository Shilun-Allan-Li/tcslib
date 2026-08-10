<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: markLast_ne_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# markLast preserves nonemptiness

**Claim.** For a block `block : List (Fin w × Bool)` with `block ≠ []`, the marked
triple list `markLast block` is also nonempty.

**Proof.** Case split on the shape of `block`, using `hne` to rule out `[]`.

1. `match block, hne with` — the `[]` shape is eliminated by the hypothesis, so
   only two patterns remain.
2. Singleton `[hd]`: `markLast [hd] = [(hd.1, hd.2, true)]`, closed by
   `simp [markLast]`.
3. `hd :: hd2 :: rest`: `markLast` produces a cons cell, closed by
   `simp [markLast]`.

**Used in.** `markLast_getLast_true` (to supply the recursive `getLast`
nonemptiness proof) and the encoder's clause-block bookkeeping around line 368,
where `markLast_ne_nil block hblock_ne` feeds `markLast_getLast_true`.
