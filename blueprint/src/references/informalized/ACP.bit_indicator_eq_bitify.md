<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: bit_indicator_eq_bitify -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Fermat indicator recovers the bit on `{0,1}`

**Claim.** For `a : ZMod p` with `a ∈ ({0, 1} : Set (ZMod p))`,

`(1 - (1 - a) ^ (p - 1) : ZMod p) = ((bitify (p := p) a : Fin 2) : ℕ) : ZMod p`.

In words: on Boolean-valued field elements, the degree-`(p-1)` polynomial
`1 - (1 - X) ^ (p - 1)` computes the *identity* — it returns `1` on `1` and `0` on
`0`, which is exactly the bit `bitify a` cast back into `ZMod p`.

**Proof.** `hp1 : 1 < p` from `(Fact.out : Nat.Prime p).one_lt`. Then
`simp [bitify] at ha ⊢` turns the membership hypothesis into the disjunction
`a = 0 ∨ a = 1` and unfolds `bitify a = if a = 1 then 1 else 0`, and
`rcases ha with rfl | rfl` splits on the two values.

- `a = 0`: the left side is `1 - 1 ^ (p - 1) = 0`, and the right side is `0`
  because the test `(0 : ZMod p) = 1` fails — `ZMod p` is nontrivial since `1 < p`.
  `simp` closes it.
- `a = 1`: the left side is `1 - 0 ^ (p - 1) = 1`, and the right side is `1`. Here
  `simp` leaves the side condition `p - 1 ≠ 0` (needed for `0 ^ (p - 1) = 0`),
  discharged by `omega` from `hp1`.

**Remark.** By `one_sub_pow_card_sub_one`, `1 - x ^ (p - 1)` is the indicator of
`x = 0`; substituting `x = 1 - a` makes it the indicator of `a = 1`, which is the
identity on `{0, 1}`. This is the same Fermat-indicator idiom used pointwise in
`approxOr` and, complemented, as the exact AND in `exactAnd_on_bits`.

**Status.** Currently *unused*: no other declaration in the library (and no
`\uses` entry in the blueprint) refers to it. The neighbouring `cast_bitify_eq`,
`one_sub_pow_card_sub_one`, `exactMod_on_bits` and `exactAnd_on_bits` carry the
corresponding work in `exists_poly_for_gate`, so this lemma stands as a
self-contained building block.
