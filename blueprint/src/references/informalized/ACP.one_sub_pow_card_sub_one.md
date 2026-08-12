<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: one_sub_pow_card_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The zero-indicator over `ZMod p`

**Claim.** For `p` prime (supplied as `Fact (Nat.Prime p)`) and every `a : ZMod p`,

`(1 - a ^ (p - 1) : ZMod p) = if a = 0 then 1 else 0`.

So `1 - a^(p-1)` is the indicator of `a = 0`. This is the single algebraic fact
behind every `MOD p` and OR construction in the file.

**Proof.** `by_cases ha : a = 0`, two branches.

1. `a = 0`: `simp [ha]` rewrites the goal to `1 - 0 ^ (p - 1) = 1`, which needs
   `p - 1 ≠ 0`. That exponent side goal is discharged by `hlt : 1 < p`, obtained
   from `(Fact.out : Nat.Prime p).one_lt`, followed by `omega`.
2. `a ≠ 0`: `rw [ZMod.pow_card_sub_one_eq_one (p := p) ha]` — Fermat's little
   theorem in `ZMod p` — turns the left side into `1 - 1`, and `simp [ha]`
   evaluates both that and the `else` branch to `0`.

**Used in.** `approxOr_failure_iff` (both the "approximator fires" and the
"exact OR fires" computations) and `exactMod_on_bits`; through those, the whole
`approxOr` / `exactMod` correctness chain.
