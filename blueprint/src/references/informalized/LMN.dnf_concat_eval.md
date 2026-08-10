<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean :: dnf_concat_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Concatenating DNFs computes their disjunction

**Claim.** For any `dnfs : List (DNF n)` and any input `x : Fin n → Bool`,

`DNF.eval (listConcat dnfs) x = dnfs.any (fun φ => DNF.eval φ x)`.

Flattening a family of DNFs into one term list gives a formula that fires exactly
when at least one of the original DNFs fires. This is the OR-of-ORs flattening
identity used to collapse an OR gate sitting above DNF gates.

**Proof.** `DNF.eval φ x` is `φ.any (fun t => t.eval x)`, so this is a statement
about `List.any` over a concatenation. Induction on `dnfs`
(`induction' dnfs with dnfs ih`, followed by `simp_all +decide [DNF.eval]`).

1. Empty list: `listConcat [] = []` and `[].any _ = false`, both sides `false`;
   `tauto` closes it.
2. Cons `φ :: φs`: unfold one step of `listConcat` to `φ ++ listConcat φs`, then
   `List.any_append` splits `(φ ++ listConcat φs).any` into
   `φ.any _ || (listConcat φs).any _`, and the inductive hypothesis (invoked
   anonymously as `‹…›`, since `induction'` bound the tail to `ih`) rewrites the
   second disjunct into `φs.any (fun φ => DNF.eval φ x)`.

**Used in.** `compression_or_of_dnfs` (Step 6, OR case), where it is fed to
`simp_all` together with `dnf_concat_width_le`.
