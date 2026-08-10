<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: depth3_compression -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth-3 one-step compression to a single narrow CNF

**Claim.** Let `gates : Fin s₂ → DNF n` each have width `≤ w` with `0 < w`,
terms that are variable-distinct (`hnd`) and `Nodup`, and let `0 < n`,
`0 < p ≤ 1/(40w)`, `p ≤ 1`. Then with `bernoulliRestrProb p`-probability at
least `1 - s₂ · ((1/2)^l + exp(-n·p/3))` the restriction `ρ` admits a *single*
`Ψ : CNF n` with `CNF.width Ψ ≤ l` and
`CNF.eval Ψ x = listAnd (List.ofFn (fun i => restrictFn (gates i).eval ρ)) x`
for all `x` — i.e. the AND of the restricted gates is one width-`l` CNF.

**Proof.**

1. `refine' le_trans (one_step_reduction_with_compression gates w l …) _`: the
   imported theorem already gives the same lower bound for the weaker event
   "*every* gate individually has a width-`l` CNF", leaving only the event
   inclusion.
2. `Finset.sum_le_sum` reduces that inclusion to one restriction `ρ` at a time,
   comparing `bernoulliRestrWeight p ρ`-weighted indicators; `split_ifs <;> norm_num`.
3. Main branch: with `h₁` = all gates have narrow CNFs, `contrapose! h₂` and
   `convert compression_and_of_cnfs (List.ofFn fun i => restrictFn (gates i).eval ρ) l _`
   — concatenating the per-gate clause lists yields the single CNF.
4. Matching the two evaluation statements needs `congr! 3`, `congr! 1`,
   `rw [List.ofFn_eq_map]` and an induction over `List.finRange s₂` to identify
   `List.all` with `listAnd`.
5. The side goal `∀ f ∈ List.ofFn …, ∃ ψ, …` is `h₁` after `simp [List.mem_ofFn]`;
   the leftover indicator branch is `mul_nonneg (pow_nonneg …) (pow_nonneg …)`. ∎

**Note.** Its only dependency `one_step_reduction_with_compression`
(`LMN/CircuitCompression.lean`) still has a `sorry` body (a
`bernoulliRestrProb` complement lemma), so this bound is not yet
sorry-free. The declaration is not used elsewhere in the library.
