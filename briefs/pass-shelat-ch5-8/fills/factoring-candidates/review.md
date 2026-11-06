# Review of the factoring fill brief (`fills/factoring-candidates/brief.md`)

**Verdict: issue after edits.** Do not issue before blocker 1 is fixed in the tree. That needs one
lemma added beside `FactoringAssumption`, in #210 before it merges or in a small PR after it.
Everything else is an edit to the brief.

I checked the brief against PR #210's head `fff0430c7c9db136e60ed14b069e972c2ea56fc8` (worktree
`wt-e1`), with the rulings of 2026-11-06:
- D1 (A): S1–S3 are in #210;
- D2: one Rabin unit, size exception approved, no split;
- D3: still for the maintainer to confirm;
- `BlumDensity` stays a hypothesis.

Logs, probe sources and regenerated inputs are in
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/review/factoring-candidates/`
(below: `$R`).

Counts: 1 blocker, 5 majors, 9 minors, 2 notes.

---

## Findings

### 1. Blocker: rule-10 prerequisite missing for `FactoringAssumption`

`FactoringAssumption` (`Factoring.lean:245`) is
`def FactoringAssumption : Prop := ∀ A : NUPPT, Negligible fun n => factorProb A n`.
It has no published `_iff`/`_eq`; check 8 lists it, and #210 did not add one.

Four targets outside fac read it:
- rsa: `rsa_imp_factoring`, whose goal is `FactoringAssumption`;
- rabin: `blumFactoring_of_factoring`, `rabinCollection_oneWay` and `rabinBlumTrapdoor_oneWay`.
  Each sketch applies `hF A`.

Both readings fail sealed. In `$R/probes/ReviewRSA.lean`, the controls elaborate unsealed. Under
`attribute [local irreducible] FactoringAssumption`:
- `hF A` fails with "Function expected at hF … has type FactoringAssumption"
  (`probe-ReviewRSA.log`, at `Probe/ReviewRSA.lean:348`);
- `intro A` fails with "introN failed" (at `:351`).

There is no way around it, so under zero exclusions these four targets cannot be filled without a
rule-10 exception.

I ran a scan for other cases (`#review_foreign` in the probes) over every foreign TCSlib
definition named in the 39 target statements. Every other one has a published reading:
- `Collection.SampleClose`, `Collection.invProbAt`: P1;
- `TrapdoorCollection.OneWay`: P2;
- `StatClose`: P3;
- `FunFamily.Easy`: P4;
- `factorProb`: P10;
- `primeStr`: `primeStr_eq`;
- `QR`: `mem_QR_iff`;
- `DistinctPrimes.p`/`q`: P6;
- `NUPPT.runAt`, `coinLen`, `inParam`, `inCoins`: `runAt_eq`, `coinLen_eq`, P5;
- `Negligible`: `negligible_iff` and its lemma family;
- `FunFamily.prod`: `invProbAt_prod_eq` and `Easy.prod`;
- the pairing and numeral lemma families.

`FactoringAssumption` is the only gap. Gate 07 should also hear of it, as a consumer read that
R-04-5 (A) missed.

**Fix (tree), in `Factoring.lean` after line 245:**

```lean
/-- The defining property of `FactoringAssumption`: every non-uniform PPT factors with
negligible probability, `FactoringAssumption ↔ ∀ A : NUPPT, Negligible fun n => factorProb A n`. -/
theorem factoringAssumption_iff :
    FactoringAssumption ↔ ∀ A : NUPPT, Negligible fun n => factorProb A n := Iff.rfl
```

**Fix (brief)**, a new row in the prerequisite table:

> | P14 | `factoringAssumption_iff` (`Candidates/Factoring.lean`) | `rsa_imp_factoring`; `blumFactoring_of_factoring`, `rabinCollection_oneWay`, `rabinBlumTrapdoor_oneWay` |

Also add to the rsa and rabin bullets of "Cross-unit statements you may cite": "fac's definition
`FactoringAssumption` (read through `factoringAssumption_iff`, P14)".

### 2. Major: the status block and "Before issue" are stale

Lines 5–19:
- the P-lemmas have landed;
- D1 and D2 are ruled;
- S1–S3 were audited by gate 07, not by a 03f2 delta round;
- `@ANCESTOR@` will certainly be past `5f277163`.

Replace lines 5–19 with:

> - **Statement gates.** Gate 03f2 (`briefs/pass-shelat-ch5-8/gates/03-ch2-4/03f2-pack.md`, findings
>   `findings/gate03f2-findings.md`) closed at 0 blockers, 0 majors and 8 minors. It gave the 36
>   original `sorry`s a verdict each: 13 (a), 23 (b), none (c). Minors F01 and F03–F08 were repaired in the
>   merged batch PR #206 (commit `0701c7cc8a51bdbe7d755f81d15c2cf4d6941ccd`, docstrings and sketches
>   only); F02 was a records fix. The sketches below are the repaired ones; in particular
>   `polyTimeComputable_samplePairRaw` (F08) and `rsaCollection_invProbAt_le` (F05) follow their
>   rewritten sketches. PR #210 added the three shared statements S1–S3 (D1), sorried and with
>   sketches, together with the rule-10 equation lemmas P1–P14; gate 07
>   (`briefs/pass-shelat-ch5-8/gates/07-eqlemmas/`) audited them.
> - **Ruled 2026-11-06:** fill all 39 targets (the 36 and S1–S3). The three units run in parallel,
>   because cross-file dependencies are on statements only. `BlumDensity` stays a hypothesis: use
>   `hD`, never try to prove it.
> - **Before issue (maintainer):**
>   - gate 07 closed and PR #210 merged, with `factoringAssumption_iff` (P14);
>   - D3 confirmed;
>   - the issue commit `@ANCESTOR@`, at or after the merge. Regenerate `inputs/{fac,rsa,rabin}/` there
>     and re-run the pre-ship probes. The record below was re-run at #210's head `fff0430c…`.

### 3. Major: target lists and counts omit S1–S3

The units table (lines 58–59), line 62, "fill all 36" (line 12), the inputs bullet (lines
401–402) and the pre-ship row (line 442) all still give fac 8, rsa 9 and a base of 75.

At #210's head, the owned files have 10, 10 and 19 `sorry`s, and the targets are exactly these:
- `grep -c sorry`: 10, 10, 19;
- `fillinputs.py` at `fff0430c` (`$R/inputs/*/`): order 94 and roots 75, unchanged; base-sorries
  **78 in 15 modules**;
- Factoring: the 8, plus `polyTimeComputable_samplePrimeL` and `statClose_samplePrimeL_pair`;
- RSA: the 9, plus `statClose_sampleUnitL`;
- Rabin: 19, unchanged.

No target statement changed between `5f277163` and `fff0430c`: the five Candidates files have
insertions only. No other restated target exists in these files: decls.tsv's 3 CHANGED rows are
elsewhere.

Replace the fac and rsa rows with:

> | **fac** | `TCSlib/Cryptography/Candidates/Factoring.lean` | `fmult_easy`, `fmult_weakOneWay`, `exists_plantFactorer`, `fmult_prod_strongOneWay`, `polyTimeComputable_samplePrimeL` (S1), `statClose_samplePrimeL_pair` (S2), `polyTimeComputable_samplePairRaw`, `factoringCollection_sampleClose`, `factoringCollection_invProbAt_le`, `factoringCollection_oneWay` (10) |
> | **rsa** | `TCSlib/Cryptography/Candidates/RSA.lean` | `statClose_sampleUnitL` (S3), `polyTimeComputable_rsaGenRaw`, `polyTimeComputable_unitSampleStr`, `rsaSampler_spec`, `rsaCollection_sampleClose`, `rsaCollection_invProbAt_le`, `rsaCollection_oneWay`, `polyTimeComputable_rsaFromFactorRaw`, `factorProb_le_rsaProb`, `rsa_imp_factoring` (10) |

Replace line 62 with: "S1 and S2 (fac) and S3 (rsa) are the shared statements of D1. Each is a
target of its owner and a statement the other units cite."

In the cross-unit bullets, delete both "under D1 (A)".

Replace lines 401–402 with: "`base-sorries.txt` lists 78 sorried declarations in 15 modules.
Your file's entry is exactly your targets (10, 10 or 19)."

In the pre-ship table, set the inputs row to "order 94, roots 75, base 78 sorried in 15 modules;
Factoring 10, RSA 10, Rabin 19, each equal to the unit's targets".

### 4. Major: D1 and D2 contradict the rulings

D1 is written as a proposal, and still offers (B). D2 recommends splitting `Rabin.lean` "as a
landing edit after the fill", which the ruling forbids. Its line ranges (78–633, 634–997) and
"`Rabin.lean` is 999 lines" are stale: at #210's head, Rabin is 1104 lines and RSA 1076.

Replace the heading at line 77 and the D1 and D2 items (lines 77–125) with:

> ## Decisions (D1 and D2 ruled 2026-11-06; D3 for the maintainer to confirm)
>
> - **D1. Shared statements (ruled: (A)).** Three facts are each needed in two units, and a private
>   proof in one unit cannot be cited by the other. PR #210 added them as sorried public statements
>   with proof sketches; gate 07 audited them:
>   - **S1** `polyTimeComputable_samplePrimeL` (… as now …);
>   - **S2** `statClose_samplePrimeL_pair` (… as now …);
>   - **S3** `statClose_sampleUnitL` (… as now …).
> - **D2. Rabin is one unit (ruled).** The 19 Rabin targets are one unit, ordered as below.
>   `RSA.lean` (1076 lines) and `Rabin.lean` (1104 lines) already exceed 1000 lines at the issue
>   tree and grow when filled. The size exception is approved (user, 2026-11-06), and neither file
>   is split, in the fill or at landing.

Keep the S1–S3 sub-bullets as they are; their text matches the statements at #210's head. From D1,
delete "They are drafted and elaborated in `preship/probes/Prereqs.lean`, and adding them needs a
short 03f2 delta round", and delete option (B) with its P11 sentence.

### 5. Major: D3 is not stated precisely

1. **Own unfilled targets are missing from the rsa and rabin lists.** At lines 408–413 only fac's
   list mentions them, although D3's own example (`rsaGen` and `polyTimeComputable_rsaGenRaw`) is
   one.
2. **The definitions carry `_spec` targets, not only polynomial-time ones.** The sorry-source
   probe (`#review_sorry`, `$R/probe-Review*.log`) shows what each target's statement reaches at
   #210's head:
   - `rsaCollection_*`: `polyTimeComputable_rsaGenRaw`, `polyTimeComputable_unitSampleStr` and
     `rsaSampler_spec`;
   - `rabinCollection_*`: `polyTimeComputable_oddGenRaw`, `polyTimeComputable_unitSampleStr` and
     `rabinSampler_spec`;
   - `rabinBlumTrapdoor_*`: also `blumSampler_spec`, `polyTimeComputable_blumInvRaw` and
     `blumInv_spec`;
   - `factoringCollection_*`: `polyTimeComputable_samplePairRaw`.

   Line 196 ("until that file's polynomial-time targets are filled") understates this.
3. **The standard triple is never spelled out.**
4. **The worker has no method to "name the permitted statement behind each `sorryAx` print".**
   `#print axioms` does not say which declaration contributes the `sorry`.
5. **Other `sorry` sources are not addressed.** The base list includes eight machine-layer
   modules' sorried declarations, in `base-sorries.txt`. None is reached by these definitions
   (probe), but the brief should say that reaching one fails the criterion.

Replace D3 (lines 126–132) with:

> - **D3. Axiom criterion (maintainer to confirm).** `#print axioms` of a filled target passes when it
>   is `[propext, Classical.choice, Quot.sound]`, or that triple plus `sorryAx` where every
>   declaration that contains `sorry` itself and that the target reaches is in your unit's permitted
>   set:
>   - **fac:** fac's own unfilled targets;
>   - **rsa:** rsa's own unfilled targets; `statClose_rejectBlocksL` (dl-a, `Candidates/Concrete.lean`);
>     fac's `polyTimeComputable_samplePrimeL` (S1) and `statClose_samplePrimeL_pair` (S2);
>   - **rabin:** rabin's own unfilled targets; `statClose_rejectBlocksL`; rsa's
>     `polyTimeComputable_unitSampleStr` and `statClose_sampleUnitL` (S3).
>
>   Own targets are reached through the statements themselves. The collections carry their
>   generators' and samplers' polynomial-time proofs and their `_spec` theorems as fields
>   (`rsaSampler_spec`, `rabinSampler_spec`, `blumSampler_spec`, `blumInv_spec`). So a filled
>   `…_sampleClose` prints `sorryAx` until those are filled. Find the sources with the sorry-source
>   probe (`preship/probes/SorrySources.lean`): for a declaration, it lists the TCSlib declarations
>   containing `sorry` that it reaches. Any other source fails the criterion and is reported, for
>   example a machine-layer declaration of `base-sorries.txt`. The integration replay re-prints
>   after all units land.

The maintainer should commit `$R/sorry-sources.lean.part` (the `#review_sorry` command) as
`preship/probes/SorrySources.lean`, with an import line and a usage example.

Then replace the axiom bullet in "Final checks" (lines 408–415) with "**Axiom prints for every
filled target**, passing D3. In `REPORT.md`, give each print and the sorry-source probe's list
for it." Replace line 196's "polynomial-time targets" with "polynomial-time and `_spec` targets".

### 6. Major: the lint criterion is false at the issue tree

Line 417 says `style_lint.py` "reports 0 findings (it reports 0 at the issue tree)". At #210's
head (`$R/style-lint-head.log`), it reports 0 findings for `Factoring.lean`, and 1 each for
`RSA.lean` ("1077 lines (> 1000, must split)") and `Rabin.lean` ("1105 lines …"). A worker would
fail this check without having done anything wrong.

Replace lines 417–418 with:

> - **Lint:** `python3 -I scripts/style_lint.py <owned file>` reports no finding for `Factoring.lean`,
>   and exactly one for `RSA.lean` and for `Rabin.lean`: the line count above 1000, which is the
>   approved size exception (D2; do not split). Any other finding fails.
>   `python3 -I scripts/campaign_style_lint.py --check8b TCSlib/Cryptography/Candidates` shows no
>   FAIL row for your owned file (rabin: the seven short sketches, once expanded, clear its seven
>   FAILs) and no public `def` that the issue tree's run does not list.

Change ground rule 7 to: "**No split.** Do not split or move files (D2). `RSA.lean` and
`Rabin.lean` are over 1000 lines; record the size findings in `REPORT.md` as the approved
exception."

### 7. Minor: line numbers of the seven short Rabin sketches are stale

Lines 329–330 cite lines 145, 347, 532, 805, 892, 927 and 951. At #210's head the campaign lint
(`$R/campaign-lint-head.log`) gives 145, 347, 578, 851, 997, 1032 and 1056. They are the same
seven theorems, checked against the old tree.

Replace with names: "Seven Rabin targets have a short sketch with no 'Proof sketch' paragraph
(the campaign lint's seven FAIL rows): `blumFactoring_of_factoring`,
`polyTimeComputable_blumGenRaw`, `rabinCollection_sampleClose`, `polyTimeComputable_blumInvRaw`,
`rabinBlumTrapdoor_sampleClose`, `rabinBlumTrapdoor_oneWay` and `polyTimeComputable_rabinRootRaw`."

### 8. Minor: the prerequisite table, now that #210 has landed

Every P-lemma P1–P10 and P12 exists at #210's head, in the file the table names, with the cited
meaning (probe results below). P11 (`samplePrimeL_eq`) is absent; it was needed only under D1 (B).

Edits:
- Heading (line 134): "## Rule-10 prerequisites (published by #210)".
- Intro (lines 136–140): "The sketches read these foreign definitions. PR #210 published each
  lemma beside its definition (`briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence/decls.tsv`);
  `preship/seal-control.log` shows that, without them, sealed readings fail. Use them by these
  names. A reading of a foreign definition that none of them covers is a reported rule-10
  exception."
- Delete row P11. Add row P14 (finding 1).
- P5: add `NUPPT.runAtL_eq`, `NUPPT.coinLen_eq`, `NUPPT.layout_eq` (also published by #210).
- P9: add `sizeStr_eq` and `natToList_eq`. `polyTimeComputable_unitSampleStr` and `_rsaGenRaw`
  read `sizeStr` through `H.size`.
- "Already published" (lines 158–165): add the domain equivalences and their field equations:
  - `factoringCollection_domEquiv`, `rsaCollection_domEquiv`, `rsaTrapdoor_domEquiv`,
    `rabinCollection_domEquiv`, `rabinBlumTrapdoor_domEquiv`;
  - `TrapdoorCollection.toCollection_domEquiv`;
  - their `_uprob`, `_f`, `_encD`, `_decD`, `_gen`, `_sample`, `_eval` (and `_perm`, `_inv`).

  These are the published interface to each collection's domain. They live in the collection's
  own file, so unfolding there stays allowed, but they are the shortest route for every
  `_sampleClose`/`_invProbAt_le` target.
- Ground rule 2 (line 374): "those listed above, and P1–P12 once they land" becomes "those listed
  above (P1–P10, P12–P14)".

### 9. Minor: gate references for S1–S3

Ground rule 5 (lines 385–386), "Gate 03f2 screened all 36, so a report is a finding against that
gate", becomes "Gate 03f2 screened the 36 original targets and gate 07 the shared statements
S1–S3, so a report is a finding against that gate". Line 451 ("S1–S3 are only stated, not proved;
their truth rests on the routes above") becomes "S1–S3 are only stated, not proved; gate 07
audited their statements."

### 10. Minor: attachment language

Line 393 says "the environment addendum v1 (`fills/fill-environment-addendum.md`), attached at
dispatch". EXCHANGE.md puts the addendum in the fill's outbox folder, with no attachments.
Replace with: "the environment addendum v1, in `outbox/fills/factoring-candidates/` on the
exchange branch beside this brief (the same text as
`briefs/pass-shelat-ch5-8/fills/fill-environment-addendum.md` at `@ANCESTOR@`)". There is no other
zip or attachment language.

### 11. Minor: docstring sketches that the brief's routes replace

Several sketches still describe the route that S1/S3 or a brief correction replaces:
- `polyTimeComputable_samplePairRaw` and `polyTimeComputable_rsaGenRaw` re-derive the
  `iterateFind` loop of `exists_samplePrime_nuppt`; the brief says to use S1;
- `polyTimeComputable_unitSampleStr` uses `pairEq` with `[true]`;
- `polyTimeComputable_rabinFactorRaw` uses `pairTakePoly`;
- `rabinCollection_invProbAt_le` (and the Blum analogues) say "`statClose_rejectBlocksL`, as in
  `rsaCollection_sampleClose`" for the unit; the brief says S3.

Under ground rule 1, a worker who follows the brief leaves a sketch that does not describe the
proof (policy §3). Proposed for the maintainer: add to ground rule 1, "and the **Proof sketch**
paragraph of a target whose route this brief replaces or corrects (marked **Route** or
**Correction**, or 'from S1'/'S3'), rewritten to the proof you wrote; statements stay
byte-identical".

### 12. Minor: reuse of the rejection loop

- **rsa step 5:** `rsaGenParams` takes its exponent as
  `(sampleUnitL Φ (Nat.size Φ) B(m) T(m) (r.drop 2L)).getD 1`. That is `unitSampleStr` of the
  `2m`-bit numeral of `Φ`, at parameter `m = max n 2`, on `r.drop 2L`: the fallback `1 % Φ = 1`
  because `Φ ≥ 2`, and the output width `2m` is the index width. Add: "Get `e` from
  `polyTimeComputable_unitSampleStr` on a re-laid-out input (`NUPPT.polyTimeComputable_layout`,
  with the numeral of `Φ` as the argument and `r.drop 2L` as the coins), not from a second
  rejection loop."
- **rabin step 5:** change "Write one private generic helper for both generators, under your
  prefix" to "… under your prefix, and request it in `REPORT.md` as a shared lemma
  (`polyTimeComputable_rejectBlocksL` for a polynomial-time test). rsa's
  `polyTimeComputable_unitSampleStr` and dl-a's `polyTimeComputable_expSampleRaw` build the same
  loop."

  No public polynomial-time lemma for `rejectBlocksL` exists (grep). This turns three silent
  copies into one disclosed debt.

### 13. Minor: source sections

Line 44–46: S1 cites Algorithm 50.16 and Lemma 51.17. Gate 07's pack lists §2.6–2.7 for them.
Change "§2.7 (Theorem 51.1)" to "§2.6–§2.7 (Algorithm 50.16, Lemma 51.17, Theorem 51.1)".

### 14. Minor: paths and checkpoints

- After the source bullet, add: "Paths `inputs/…` and `preship/…` are relative to
  `briefs/pass-shelat-ch5-8/fills/factoring-candidates/`, and `gates/…` and `fills/…` to
  `briefs/pass-shelat-ch5-8/`, in the campaign tree at `@ANCESTOR@`."
- "Checkpoint" is never defined. Add: "Push a checkpoint after each filled target, and at least
  after each numbered step of your unit's order."

### 15. Note: routes, Mathlib and parallel safety (no change needed)

**Routes.** Every route names published lemmas only. Every Mathlib name the brief or the overlap
advice gives for these units resolves in the owning unit's closure:
- `ZMod.unitOfCoprime`, `ZMod.val_lt`, `ZMod.unitsEquivCoprime`, `ZMod.finEquiv`,
  `ZMod.val_coe_unit_coprime`, `ZMod.coe_unitOfCoprime`, `ZMod.isUnit_iff_coprime`;
- `ZMod.coe_mul_inv_eq_one`, `ZMod.chineseRemainder`, `ZMod.neg_one_ne_one`;
- `Nat.odd_iff`, `Nat.Prime.eq_two_or_odd'`, `Units.sq_eq_sq_iff_eq_or_eq_neg`;
- `Nat.lt_size_self`, `Nat.size_le`, `Nat.lt_size`.

**S3 at the rsa and rabin call sites.** S3's hypotheses hold where the units need it:
- `rsaGenParams`'s exponent sampler uses `rsaBlock`/`rsaTrials` at `max m 2`. That is `n` for the
  `n ≥ 2` of `rsaCollection_invProbAt_le`, and `Nat.size Φ ≤ 2n ≤ 2(n+2)`;
- the fallback is `1 % Φ = 1`;
- `unitSampleStr` instantiates S3's function verbatim.

**Parallel safety.**
- The units own disjoint files on the chain Factoring → RSA → Rabin.
- The sorry-source probe confirms that no statement in one unit reaches another unit's unfilled
  proof, except rabin's statements reaching rsa's `polyTimeComputable_unitSampleStr` through
  `rabinSampler`/`blumSampler`. That one is listed.
- No import is authorized, so there are no cycles.

### 16. Note: `BlumDensity`

The brief keeps it as the hypothesis `hD` throughout: rabin step 8, and the overlap advice "keep
`hD`". Finding 2 adds the explicit sentence.

---

## Probe results (at `fff0430c`, olean tree `e1-oleans`, `scripts/lean_check_tree.sh`, one Lean process at a time)

| Probe | `#check`s | Errors | Of which |
|---|---|---|---|
| `Probe/ReviewFac` (imports `Candidates.Factoring`) | 263 | 10 | All expected, and identical to the pre-ship `import-probe-fac.log`: the 5 QR names and 3 Euler names, which are in rabin's closure only by design; `uexp_prod` (→ `HardcoreBit.uexp_prod`); `ofFn_padFin_of_le` (→ `Collection.ofFn_padFin_of_le`, not cited by the brief) |
| `Probe/ReviewRSA` (imports `Candidates.RSA`) | 278 | 12 | The same 10 expected, plus the 2 sealed `FactoringAssumption` readings (finding 1), which fail as intended; their unsealed controls elaborate |
| `Probe/ReviewRabin` (imports `Candidates.Rabin`) | 350 | 3 | Expected and identical to pre-ship: `uexp_prod`, `uprob_eq_one_div_card` (→ `OneWay.uprob_eq_one_div_card`), `ofFn_padFin_of_le` |

**Each pre-ship import probe is re-run at #210's head.** The extra checks resolve with the cited
meanings. Signatures were checked in the logs for P1, P3, P4, P7, P8, S1–S3,
`statClose_rejectBlocksL` and `rejectBlocksL_eq`. The extras were:
- P1–P10 and P12;
- S1–S3;
- the domain-equivalence families;
- `factoringSampler_runAt`, `Turing.FinTM.computesFunInTime_unaryMul`, `mulStr_natToList`,
  `one_sub_one_div_pow_le_exp_neg`;
- the 13 pre-ship `BriefNames`;
- `HardcoreBit.uexp_prod`, `OneWay.uprob_eq_one_div_card`, `DistinctPrimes.one_lt_totient`,
  `NumberTheory.le_totient_mul_log_succ`, `rsaFromFactorStep_correct`;
- the QR/CRT names: `pow_div_four_succ_mem_QR`, `mem_QR_mul_iff`, `sq_pow_div_four_succ`,
  `sq_crtUnits_symm`, `eq_blumSqrt_of_sq_eq`, `crtUnits_fst`/`_snd`, `pushesUniform_sqTo`,
  `statClose_of_pushesUniform`, `sq_mem_QR`;
- `two_pow_le_two_mul_card_primes`, `rabin_symmetry`, `gcd_sub_eq_prime_of_sq_eq_sq`,
  `rabinFactorer_runAt`, `rabinBlumInverter_runAt`, `Complexity.polyTimeComputable_iterateFind`;
- the Mathlib names of finding 15.

**Sorry sources (`#review_sorry`)** are listed for the 39 targets and the key definitions (finding
5). No definition or statement reaches a machine-layer `sorry`. Outside each unit's own targets,
the only foreign sorried target reached is rsa's `polyTimeComputable_unitSampleStr`, from rabin.

**Foreign definitions in statements (`#review_foreign`).**
- fac: 17;
- rsa: 13, including `FactoringAssumption`;
- rabin: 12, including `FactoringAssumption` and `TrapdoorCollection.OneWay`.

All have a published reading except `FactoringAssumption` (finding 1).

**Inputs** (`fillinputs.py` at `fff0430c`, `$R/inputs/{fac,rsa,rabin}/`):
- order 94 and roots 75: byte-identical to the brief's `inputs/`, and identical across the units;
- base-sorries: 78 in 15 modules, against the brief's 75. The Factoring and RSA rows changed
  (finding 3).

**Lint at `fff0430c`:**
- `style_lint.py`: Factoring 0; RSA 1 and Rabin 1, the size findings (finding 6);
- campaign lint: the 7 Rabin FAILs at new lines (finding 7); check-8 WARNs as before; size WARNs
  for RSA and Rabin.

Probe files: `Probe/ReviewFac.lean`, `Probe/ReviewRSA.lean`, `Probe/ReviewRabin.lean` in
`wt-e1`, untracked. Copies are in `$R/probes/`. No TCSlib source was edited.
