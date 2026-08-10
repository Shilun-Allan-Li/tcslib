<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/ListDecoding.lean :: list_decodable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# List-decodable code

**Definition.** For `ρ : ℝ` with `0 ≤ ρ ≤ 1`, block length `n`, list size
`L ≥ 1`, and a code `C : Code n α = Finset (Codeword n α)`,

```
list_decodable ρ hρ₁ hρ₂ n L hL C  :=  ∀ y, (hamming_ball ⌊ρ * n⌋₊ y ∩ C).card ≤ L
```

that is: every Hamming ball of radius `⌊ρn⌋`, centred at an arbitrary word
`y : Codeword n α` (not just at a codeword), contains at most `L` elements
of `C`.

**Remark.** The hypotheses `hρ₁ : 0 ≤ ρ`, `hρ₂ : ρ ≤ 1` and `hL : L ≥ 1` are
carried as explicit arguments of the definition even though the body only uses
`ρ` through `⌊ρ * n⌋₊`; they are there to keep the predicate well-behaved as a
radius/list-size pair, and callers must supply them (see the `by linarith`
arguments in the statement of `list_decoding_capacity`). The radius is a
natural number obtained by `Nat.floor`, so `ρ` never appears in the counting
itself.

**Used in.** `exists_listDecodable_code` and `list_decoding_capacity`; the
latter produces a code satisfying this predicate at radius `ρ` for any rate
below `1 - H_q(ρ)`.
