<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: KKL_trivial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# KKL, trivial form: some coordinate beats the average

**Claim.** For `f : BooleanFunc n` with `0 < n`, there is a coordinate `i` with
`influence i f ≥ totalInfluence f / n`.

**Proof.** One line: `exact max_influence_lower_bound f hn`. The statement is a
verbatim re-export of that lemma from `Basic.lean`, whose own argument is the
averaging/pigeonhole one — if every `Inf_i[f]` were strictly below the mean
`I[f]/n`, summing the `n` strict inequalities would give `I[f] < I[f]`. ∎

**Remark.** Named "trivial" advisedly, and the source comment says so: this is
the `max_i Inf_i[f] ≥ I[f]/n` averaging bound, *not* the KKL theorem. Real KKL
gains the extra `log n` factor (`max_i Inf_i[f] ≥ c · I[f] · log n / n`) and
needs hypercontractivity; that statement is `KKL_balanced` in the same file,
whose hard case is still a `sorry` (line 618). This declaration adds no
mathematical content over `max_influence_lower_bound` — it exists only so the
KKL file states a bound of its own.

**Used in.** Nothing — no other declaration in the repository references it.
Callers that want the averaging bound, including `KKL_balanced` itself
(line 598), call `max_influence_lower_bound` directly instead of going through
this alias.
