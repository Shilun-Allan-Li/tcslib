<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counterInc_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment Length and Carry Bounds

**Claim.** For every finite Boolean list $b$, the incremented list has length at most $|b|+1$, and the number of leading true bits of $b$ is at most the length of the incremented list.

**Proof.** Proceed by induction on the list. For the empty list, incrementing produces a one-element list and there are no leading true bits, so both bounds hold. For a nonempty list, split on whether its first entry is false or true. In either case, the recursive definitions express the new length and the leading-true count using the corresponding quantities for the tail, with at most one additional entry. The induction bounds then give both inequalities.
