<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_sigma_ne_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# processClauseLits never writes the killing direction for a literal

**Claim.** (`private`) Let `l : Literal n` and suppose every `m ∈ lits` with
`m.1.var = l.var` in fact has `m.1 = l` (`hnd`), and that `σ l.var ≠ some l.neg`.
Then the output σ still avoids that value:
`(processClauseLits lits path ρ₀ σ).2.2.1 l.var ≠ some l.neg`. Since
`Literal.killedBy l ρ` is `ρ l.var = some l.neg`, this says σ never comes to kill
`l`.

**Proof.** `induction lits generalizing path ρ₀ σ`.

1. `lits = []`, and `lits = hd :: tl` with `path = []` — output σ is the input σ,
   so `hσ` transfers (`simpa [processClauseLits]`).
2. `lits = hd :: tl`, `path = p :: ps` — unfold one step
   (`simp only [processClauseLits]`) and `apply ih ps _ _`, weakening `hnd` along
   `List.mem_cons_of_mem`. The obligation is that the updated σ,
   `Function.update σ hd.1.var (some (!hd.1.neg))`, avoids `some l.neg` at `l.var`.
3. `by_cases heq : hd.1.var = l.var`. If equal, `hnd hd List.mem_cons_self heq`
   gives `hd.1 = l`, so the written value is `some (!l.neg)`
   (`Function.update_apply`, `if_pos`); `injection` plus `cases hb : l.neg` shows
   `!l.neg ≠ l.neg`.
4. Otherwise the update is inert (`Function.update_apply`, `if_neg`) and `hσ`
   closes it. ∎

**Used in.** `encode_go_not_kills_first_clause` (same file), twice — the encoder
fixes each free literal to its *satisfying* direction `!l.neg`, so the clause it
selected stays un-killed as γ is built.
