<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean :: cnf_concat_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Concatenating CNFs preserves the width bound

**Claim.** If every `ψ ∈ cnfs` satisfies `CNF.width ψ ≤ l`, then the
concatenation satisfies `CNF.width (listConcat cnfs) ≤ l`.

**Proof.** Induction on `cnfs` (`induction' cnfs with ψ cnfs ih`).

- Empty list: `listConcat [] = []` has width `0`, so `Nat.zero_le _`.
- Cons: `simp_all [listConcat]` reduces to the width of `ψ ++ listConcat cnfs`;
  `unfold CNF.width at *` exposes it as `(·.map Term.width).foldr max 0`, and
  `induction ψ <;> aesop` pushes the `foldr max` through the append, bounding
  each clause length by `l` from the hypothesis and the inductive hypothesis.

**Remark.** Since `CNF.width` is a `foldr max` over clause lengths, no clause is
created or lengthened by concatenation, so the bound is not just preserved but
the width is the max of the two widths. The companion characterisation
`width_le_iff_forall` (`private`, same file) states the underlying fact
`(ts.map Term.width).foldr max 0 ≤ l ↔ ∀ t ∈ ts, t.width ≤ l`.

**Used in.** `compression_and_of_cnfs` (width component) and
`dnf_concat_width_le`, which transports this bound to DNFs through the De Morgan
dual (`cnfToDualDNF_width`).
