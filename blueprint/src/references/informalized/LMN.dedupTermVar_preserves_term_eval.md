<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: dedupTermVar_preserves_term_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# De-duplicating a consistent term preserves its AND value

**Claim.** If `termHasContradiction t = false` then
`Term.eval (dedupTermVar t) x = Term.eval t x` for every `x`. Without the
consistency hypothesis this fails: dropping one of two opposite literals on the
same variable would turn a false conjunction into a satisfiable one.

**Proof.** Induction on `t` (`induction' t with l t ih`); `nil` is `rfl`. In the
`cons` case split on `h : ∃ l' ∈ t, l'.var = l.var`, then unfold
`dedupTermVar`.

1. **Duplicate variable present.** `split_ifs` and `simp_all [Term.eval]`. The
   head `l` is dropped. Consistency (`hnc.1` applied to the witness `l'`)
   forces `l'.neg = l.neg`, hence `Literal.eval l x = Literal.eval l' x`; since
   `l'` is retained, the conjunct `l` is idempotent and the AND is unchanged
   (`grind`).
2. **Fresh variable.** The `if` guard is false, so `l` is kept
   (`rw [if_neg]`) and the goal reduces to `ih hnc` on the tail. Discharging
   the guard uses the auxiliary `h_foldr`: every literal in the `foldr` output
   was already a member of the input list (`induction l <;> aesop`), so a
   surviving literal sharing `l.var` would contradict `h`.

**Used in.** `cleanDNF_eval` (together with `contradiction_term_eval_false`),
which is what lets the switching lemma be applied to `cleanDNF f` instead of
`f`.
