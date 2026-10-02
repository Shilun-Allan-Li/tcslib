<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: SwitchingLemma2.exists_aux_injection -->
<!-- origin: boolean-ch04-dnf-switching-lmn round-7 verdict not_in_text (0.82) -->

# At most (4w)^d auxiliary strings per group

**Claim.** Fix a DNF `f` of width ≤ `w` (`w > 0`), a depth `d`, and a group
key `γ`. There is a map `g` from auxiliary strings to functions
`Fin d → (position < w, direction, marker)` that is injective on the encoder's
image over bad restrictions whose first component is `γ`. The codomain has
`(4w)^d` elements, so at most `(4w)^d` auxiliary strings occur — the counting
step of the switching-lemma bound.

**Proof.** Let `g(aux)` decode `aux` into triples with `parseAux`, read
entries `0 … d−1`, and pad missing entries with the default
`(0, false, false)`.

By `encode_go_wellformed`, every image string renders from a triple list of
length ≤ `d` ending in a `marker = true` entry; with the round-trip
`parseAux (triplesToAux w ts) = ts` (`parseAux_triplesToAux`) this gives, for
every image string `aux`:

1. `triplesToAux w (parseAux aux) = aux`,
2. `|parseAux aux| ≤ d`,
3. the last parsed triple has `marker = true`.

Suppose `g(aux₁) = g(aux₂)`.

- *Equal lengths:* if one parse were shorter, compare entries at the longer
  parse's last index — one side is the padding default (`marker = false`),
  the other a real last triple (`marker = true` by 3): contradiction. The
  final marker is exactly what makes padding distinguishable from data.
- *Equal parses:* equal lengths ≤ `d` plus entrywise equality on `0 … d−1`.
- *Equal strings:* apply `triplesToAux w` and use round-trip (1). ∎
