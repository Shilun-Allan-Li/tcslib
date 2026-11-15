# Pass–shelat Gate 29 — learning

**Verdict: HOLD.** The proof, frozen statements and supplied seal evidence pass inspection. Two further undisclosed re-proofs remain outside the worker’s overlap table and DL-45. Under the pack’s severity rule, both are majors.

| Blocker | Major | Minor | Note |
|---:|---:|---:|---:|
| 0 | 2 | 0 | 0 |

| Pin | Audited revision |
|---|---|
| PR | [Shilun-Allan-Li/tcslib #313](https://github.com/Shilun-Allan-Li/tcslib/pull/313), draft |
| Lean head | `8befc58966fd39f974a54250849736df194584b9` |
| PR base | `4561c3407f9f015da55255a6a4cbcfc5840fd1f3` |
| Campaign records | `7bd85992f8bd61df48f43092bc5c845d5fac1b27` |
| Exchange | `341f61def10e0481a7c29fa4787a80d6ece7d5df` |

## Findings

All source line numbers below refer to the audited head.

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G29-01 | major | `Randomness/Learning/Random.lean:172–179`, local `hj` in `abs_gameProb_random_sub_half_le` | The remaining collision calculation re-proves the public constant-average lemma inline. | After `uprob_prod` and `uprob_eq_point`, lines 176–179 expand `uexp_def`, sum the constant, prove positive cardinality and cancel the denominator. This is `OneWay.uexp_const`, `OneWayFunctions/Basic.lean:69–73`, already public at the PR base and already called at line 170. Neither the overlap table nor DL-45 discloses this additional re-proof. | Replace the constant-average calculation by `OneWay.uexp_const`; preserve the theorem header. |
| G29-02 | major | `Randomness/Learning/Random.lean:66–69`, `firstBit_of_pos` | This new public theorem independently re-proves the zero-index case of an existing public bit reader. | After `firstBit_eq`, its conclusion is `(List.ofFn y).headD false = y ⟨0, hn⟩`. Public `Authentication.LamportFill.headD_drop_ofFn`, `Authentication/Signatures/Lamport/MachineSpec.lean:195–199`, gives that equation at index `⟨0, hn⟩` after `List.drop_zero`. The reader is present and unchanged at the PR base. This overlap is absent from the worker’s table and DL-45. | Re-derive the theorem through an existing reader, or obtain an explicit disposition for this additional overlap. Importing the cited Lamport helper is acyclic; a shared reader can also avoid that additional import. |

### G29-01: exact remaining overlap

The unreused mathematical step is

```lean
uexp (fun _ : ((Fin m → Fin n → Bool) × ρ) => (1 : ℝ) / 2 ^ n)
  = (1 : ℝ) / 2 ^ n
```

The averaging type is finite and nonempty under the theorem’s existing hypotheses, exactly as required by `OneWay.uexp_const`. The surrounding Fubini step and point-mass specialization remain useful glue. The duplicated part is the subsequent sum-and-cancellation proof.

A replacement proof shape for `hj` is:

```lean
    intro j
    rw [uprob_prod]
    simp only [uprob_eq_point, OneWay.uexp_const]
```

This needs no new import. LE-reuse correctly repairs its two listed overlaps, but leaves this separate occurrence unchanged. DL-45’s coupling-bound disposition does not identify this constant-average re-proof.

### G29-02: exact specialization

The existing reader says

```lean
((List.ofFn y).drop i.val).headD false = y i
```

Specializing `i` to `⟨0, hn⟩` and rewriting `List.drop_zero` gives the new theorem’s entire conclusion after `firstBit_eq`. Its current proof instead splits the positive length and uses `List.ofFn_succ` and `List.headD_cons` to establish that conclusion again.

For example, after importing the cited helper, a replacement proof shape is:

```lean
  rw [firstBit_eq]
  simpa only [List.drop_zero] using
    (TCSlib.Cryptography.Authentication.LamportFill.headD_drop_ofFn y ⟨0, hn⟩)
```

The overlap table’s `firstBit` row explains its relationship to the owned `prfConcept`; it does not disclose this relationship to the existing bit reader. DL-45 records the flip operations and other named overlaps, but not `firstBit_of_pos`. The replacement snippets above were checked by statement matching, not by a new Lean run.

## Proof audit

The delivered proof establishes the frozen prediction statement on inspection, following the first-output-bit concept of [PS10, §8.1, Theorem 179.1, book p. 179](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf#page=191).

1. **Efficient distinguisher.** `exists_learnDist` calls the public `MultiMsg.exists_queryChain_nuppt` with zero message vectors and a polynomial-time learner/verdict machine. Its coin equivalence supplies exactly `m(n) + 1` uniform points and the learner’s coins. The public chain contract gives the stated verdict within budget `m(n) + 1`; it introduces no timeout discrepancy. The disclosed substitution for T1/T4 is valid.
2. **Real-game law.** `iid_uniform`, the product-uniform readers and `snocEquiv` identify the PAC experiment with the distinguisher’s acceptance probability. No conditioning excludes repeated points. Both sides interpret the learner’s prediction as `decide (output = [true])`, including all other output words.
3. **Random-function bound.** For positive `n`, `flipAt` is an involution of function tables. When the test point is absent from the examples, it preserves every example label and negates the test label. Uniform probability is preserved, so success equals its complement and is exactly `1/2`. The public coupling bound and the union bound then give

   \[
   |\operatorname{gameProb}-1/2|
   \le \Pr[\exists j,\ s_j=x]
   \le \sum_{j<m(n)}2^{-n}
   =m(n)/2^n.
   \]

4. **Negligibility.** The owned proof applies the triangle inequality to obtain

   \[
   \operatorname{predictAdv}
   \le \operatorname{prfAdv}+m(n)/2^n
   \qquad(n\ge1).
   \]

   `PRF.negligible_prfAdv` uses precisely the polynomial budget `m + 1`. Polynomial-times-exponential decay, addition and eventual domination finish the argument. The finite exception `n = 0` is handled by the cutoff `1`. With no examples, the empty union gives zero collision probability.

Part (c)’s complete source suffix, including its proof, is byte-identical to the PR base. It combines eventual prediction advantage at most `1/n` with `δ < γ` and the published PAC bridge. The final axiom prints for both (b) and (c) contain exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## Integrity and evidence checks

- **Pack:** all 17 `SHA256SUMS` entries verify. All 14 bundle sections match their pinned repository originals, allowing only the bundle’s framing newlines. Every one of the 138 source-closure files matches the Lean-head git blob.
- **Nested evidence:** `verification.zip` has exactly its 30 manifest paths plus `SHA256SUMS`. The review archive verifies all 488 manifest entries; the reuse archive verifies all 248. Their external and internal manifests agree, with no extra file entries.
- **Freeze:** exactly the five authorized Lean files differ from the PR base. All nine pre-existing declaration headers are byte-identical; there are 47 new public declarations. Part (c) is unchanged. The owned-file changes stay within the permitted imports, module prose, target sketch and target proof.
- **LE-doc:** only doc comments change in its four files. The 17 added formulas agree with their declarations and argument order; no documentation finding was found. The rewritten target sketch describes the delivered proof.
- **LE-reuse:** only `Random.lean` changes: the two disclosed proof bodies, one import and the two permitted docstring insertions. Both cited public lemmas instantiate correctly. `HybridLemmas` adds exactly one module to `Random`’s closure, from 123 to 124, with no cycle and no additional definition. Carrying forward the four unchanged files’ seals is justified.
- **Rule 10:** independently checked the request sets against the supplied catalogs and stored-term references, including matchers and private-name components; removed instrumentation to recover the exact pinned source bytes; and checked installation and EOF records. All 28 seal probes have zero errors: 20 at LE-doc, four for the base owned file, and four for final `Random`. The older base-seal revision `eff2dcd0` has the same 130 source files in the owned file’s closure as the PR base.
- **Controls:** recounted both diagnostic forms directly from raw logs. The canonical review controls have 16 probes and 46 sealed negatives; each negative fails once, reader positives pass, and unsealed controls pass. The strict review controls have 54 correct negative failures plus the disclosed 16 reader-positive failures, confined to `ctlUniformReader` and `ctlCoeReader` in eight sealed probes. Their type mismatches match the projection-coercion attribution. Final reuse controls pass in both variants, with seven sealed negatives per variant. No additional forbidden definition read was found.
- **Builds and axioms:** checked the raw 66-module final build records, their source hashes against the audited git head, their log hashes, and zero error/sorry counts. The supplied census covers 71 stored constants with the standard axiom union. The whole-tree check remains the supplied LE-doc check of 1245 modules; the pack’s separate combined-tree rebuild requirement for the PR merging second remains applicable.
- **Lint and size:** independently reran the final lint: 92 FAIL / 101 WARN, with exactly the same 193 FAIL/WARN lines as the supplied baseline. Files have 220, 275, 137, 174 and 189 lines; every line is at most 100 characters.

**Validation limit:** no Lean toolchain is installed in this audit environment. I independently checked source, manifests, import graphs, instrumentation and raw supplied execution evidence; I did not rerun Lean elaboration or the seals.

**Closure condition:** resolve G29-01 and G29-02 through reader-based proofs or explicit user dispositions, then supply validation for the revised head. No repository change, review submission, dispatch or merge was made by this audit.

**Notation:** `m(n)` means `m.eval n`; `ρ` is the learner’s coin type; `hn` proves `0 < n`; `i` is a bit index; `s_j` is example `j`; `x` is the fresh test point; `Pr` is uniform probability. Other names are the audited Lean declarations.
