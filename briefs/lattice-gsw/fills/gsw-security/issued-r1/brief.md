# Claude fill · column leftover hashing and IND-CPA of public-key GSW (`gsw-security`)

**Issue base** `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, the head of draft PR #333 (branch `stmt/gsw`; Gate 41
CLOSED by disposition). It contains #332's commit `94eae71b779c4ca0f76c138d699f4d737dbd6cee` as an ancestor
(`486f44f8~3`). **Unit** `gsw-security`: fill units F5 and F6 of `briefs/lattice-gsw/plan-section.md` §G7 (lattice
campaign, phase 5). **Worker** Claude, a **single agent** (Seyoon's ruling, 2026-11-16). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the 6 admitted, frozen statements of `TCSlib/Cryptography/Hashing/SIS/Columns.lean` and
`TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean`. They passed the phase-5 statement phase
and Gate 41, which accepted every target as true with the hypotheses it displays. Each docstring holds the
maintainer's proof sketch.

## Feasibility and size (maintainer's assessment)

Feasible. The six statements mirror the audited Regev PKE hybrids
(`Encryption/PublicKey/Regev/Experiments.lean`), with one new ingredient: a column-by-column hybrid over the
existing single-column leftover-hash bound. Gate 41 checked the hybrid and the final bound (two DLWE advantages
plus `2Nε`) by hand.

**Estimated size: about 270 lines** of proof (plan §G6): Columns about 130, Security about 140. The files are 89
and 217 lines now.

## Checkout and delivery

- Fetch `stmt/gsw` (or the commit itself). Start a local branch `fill/gsw-security` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/gsw-security/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, the
    committer's name, email and date, and its **signing** (`none`, or the signature format), so that `git am` at
    the base reproduces every hash. Commit with `git -c commit.gpgsign=false`; if a commit is signed anyway, say
    so in its row and in `REPORT.md`. Before you push, check the reproduction in a scratch clone and say so in
    `REPORT.md`;
  - `src/`: the changed and new files under their repository paths;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/gsw-security/` except itself. The
    delivered paths must **equal** the manifest's paths exactly: nothing missing, nothing extra, and no leading
    `./`. Check this before each push.
- Commit on the exchange as `fill gsw-security: checkpoint N` and `fill gsw-security: final`.
- Pull with rebase before pushing. Push only your delivery path, never force-push, and never touch another path
  (other fills, gates, the `arora-barak-ch3-4/` and `lwe-sis-constructions/` folders). If a push is refused,
  keep the commit and say so. Campaign changes land by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#332 (F0) and #333 are not merged.** #333 is stacked on #332; your base contains both. Neither F0 reader is
  needed here. #332 merges first, then #333, then the fills, rebased by the maintainer. If either changes or
  merges during the fill, **stay on the issue base**.
- **`gsw-core` runs in parallel** from the same base. It owns `GSW/{Gadget,Noise,Scheme,Symmetric,Eval}.lean`,
  which are in your order and which you never edit. **Proved-modulo:** you may cite their targets as frozen
  statements, exactly as stated. The expected route needs none of them (it uses only the `rfl` readers
  `encrypt_eq`, `view_eq`, … and the Regev, SIS and Foundations layers); if your proof does cite a `gsw-core`
  target, name it in the dependency trace.
- **F6 depends on F5 inside this job.** Prove F5 first (checkpoint 1); F6 may cite F5's statements meanwhile.

## Targets (frozen; quoted from the issue base)

6 declarations, each a `theorem` whose body is `sorry` (`base-sorries.txt`). Lines are at the issue base.

| Unit | File (lines at base) | Targets (declaration line) |
|---|---|---|
| F5 | `Hashing/SIS/Columns.lean` (89) | `hashColumns_eq_mul` (60), `distAdv_hashColumns_uniform_le` (78) |
| F6 | `AdvancedEncryption/Homomorphic/GSW/Security.lean` (217) | `real_uniformKey_advantage` (153), `uniformKey_uniform_advantage_le` (172), `distAdv_encrypt_le` (189), `distAdv_encrypt_le_of_width` (205) |

Counts: F5 2, F6 4; they equal plan §G7. The statements, with their docstrings and sketches, are in the files.
The column hybrid, for orientation:

```lean
theorem distAdv_hashColumns_uniform_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (N : ℕ)
    (D : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.columns) (Fin N) Bool => (r.1, hashColumns P N r.1 r.2))
      (id : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → _) D ≤
      N * ((1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns)) := by
  sorry
```

`P` here is `TCSlib.Cryptography.SIS.Parameters` (note `P.columns` is the SIS column count, not GSW's `N`).

## Published interfaces (reuse first)

Read other files' definitions **only** through these readers (Rule 10). The list is a start, not a limit: search
for more before writing any lemma.

| Interface | Provider (path under `TCSlib/`, line at base) |
|---|---|
| `hashColumns_apply` (own file, F5) | `Cryptography/Hashing/SIS/Columns.lean` |
| `view_eq`, `realView_eq`, `uniformKeyView_eq`, `reduction_eq`, the `simps` readers of `view`, `realView`, `uniformKeyView` and `columnHashParameters` (own file, F6) | `…/GSW/Security.lean` |
| `Hashing.SIS.hash_eq` (49) | `Cryptography/Hashing/SIS/Basic.lean` |
| **`Hashing.SIS.distAdv_hash_uniform_le`** (166): the strong single-column LHL, valid for a test with independent coins | `Cryptography/Hashing/SIS/Universality.lean` |
| `encrypt_eq`, `gadget_apply`, `lift_apply`, `Parameters.columns_eq` | `…/GSW/Scheme.lean`, `…/GSW/Gadget.lean` (frozen, `gsw-core`'s) |
| `LWE.decisionAdvantage_eq` (53); `LWE.sample_fst`/`_snd` (`LWE/Basic.lean` 109, 116) | `Cryptography/LWE/Experiments.lean` |
| **`Regev.real_uniformKey_advantage`** (128), **`uniformKey_uniform_advantage_le`** (244), **`distAdv_encrypt_le`** (301): the pattern; `augmented_eq` (173), `augmented_bijective` (182), `encrypt_augmented` (199), `extractionError_eq` (232), `two_extractionError_le` (334); `hashParameters` (154, the Q11 twin) | `Cryptography/Encryption/PublicKey/Regev/Experiments.lean` |
| `acceptProb_def` (98), `distAdv_def` (102), `acceptProb_comp_equiv` (107), `distAdv_le_statDist` (173) | `Cryptography/Foundations/Experiments.lean` |
| `uprob_comp_equiv` (165), `uprob_prod` (153), `uprob_fst` (175), `abs_sub_le_sum_hybrids` (218), `exists_hybrid_gap` (230) | `Cryptography/Foundations/Probability.lean` |
| `acceptProb_fst`/`_snd` (73, 83), `acceptProb_bind` (91), `acceptProb_update` (103), `distAdv_comp` (141); `multicopyHybrid`, `multicopyRed` and `acceptProb_multicopyRed_left`/`_right` (the independent-copies relative of the column hybrid) | `Cryptography/Pseudorandom/Indistinguishability.lean` (an allowed extra import) |
| `columnHybrid`, `columnTest`, `column_gap` (82, 106, 138): a column hybrid under one public matrix, with DLWE gaps | `Cryptography/TrapdoorFunctions/Lossy/Experiments.lean` (pattern only) |
| `Matrix.mul_apply`, `Matrix.mulVec`, `dotProduct`, `Equiv.prodAssoc`, `Equiv.prodCongr`, `Equiv.addRight`, `Equiv.ofBijective`, `Real.sqrt_le_sqrt`, `Real.sqrt_mul_self` | Mathlib (search for the exact names at the pin) |

## Proof routes and checkpoints

The docstrings' sketches are the route; Gate 41 validated them.

**F5 · Columns** (2 targets).
- `hashColumns_eq_mul`: entrywise, `hashColumns_apply`, `hash_eq`, `Matrix.mul_apply` and `Matrix.of_apply`; both
  sides are the same binary-weighted sum. (Statement ruling QS1: the right side is `A * Matrix.of …`.)
- **`distAdv_hashColumns_uniform_le`.** Hybrid `H_j`: the first `j` columns of the second component are
  independent uniform columns and the rest are hashes of independent binary columns under the **same** public
  matrix; `H_0` is the real sampler and `H_N` the ideal one after relabelling seeds (`uprob_comp_equiv`,
  `acceptProb_comp_equiv`). `abs_sub_le_sum_hybrids` bounds the end-to-end gap by the sum of the `N` neighbouring
  gaps. Each gap is the advantage, between `(A, hash A r)` and `(A, u)`, of the test that plants its challenge
  column at `j`, samples the other columns itself with coins carried in its own randomness (a product of finite
  nonempty types), and runs `D`; `distAdv_hash_uniform_le` bounds it. Gate 41: the existing **strong** LHL applies
  despite the shared matrix, because the test receives `A`. At `N = 0` both samplers give the same distribution
  and the gap is 0. This is **not** a matrix leftover-hash lemma: make no universality claim for the whole-matrix
  family `R ↦ AR`.

**F6 · Security** (4 targets). Write `ε = Regev.extractionError P.lwe = ½·√(q^{n+1}/2^m)`.
- `real_uniformKey_advantage`: exact equality, as `Regev.real_uniformKey_advantage`. Reassociate the independent
  key, coin-matrix and distinguisher seeds (`uprob_comp_equiv` with `Equiv.prodAssoc`) on both sides, then
  `LWE.decisionAdvantage_eq` and `distAdv_def`. The reduction's coins are exactly the binary matrix coins paired with
  `D`'s coins.
- `uniformKey_uniform_advantage_le`: as `Regev.uniformKey_uniform_advantage_le`. Relabel the key by
  `Equiv.ofBijective _ (Regev.augmented_bijective _)`; the augmentation bijection retains the **entire** public key.
  The ciphertext is `hashColumns (columnHashParameters P) N Ā R + μG` (`encrypt_eq`, `hashColumns_eq_mul`,
  `lift_apply`); translation by `μG` is a bijection of the ciphertext space, so after relabelling both samplers the
  gap is that of `(Ā, ĀR)` versus `(Ā, U)`. Apply `distAdv_hashColumns_uniform_le` and rewrite its bound with the
  `columnHashParameters` readers and `extractionError_eq`. `columnHashParameters` is this file's own definition and
  may be read directly here; it is the disclosed Q11 twin of `Regev.hashParameters`, which you must not unfold.
- `distAdv_encrypt_le`: insert both uniform-key views and the common uniform view; the triangle inequality gives
  `|a_{μ₀} − a_{μ₁}| ≤ Adv(red_{μ₀}) + Adv(red_{μ₁}) + 2Nε` (two exact DLWE terms, two statistical terms), as
  `Regev.distAdv_encrypt_le`.
- `distAdv_encrypt_le_of_width`: `distAdv_encrypt_le` and `Regev.two_extractionError_le`, multiplied by `N ≥ 0`:
  `2Nε = N·√(q^{n+1}/2^m) ≤ N·2^{−κ}` when `q ≤ 2^w` and `(n+1)·w + 2κ ≤ m`.
- These are the concrete, fixed-bit, function-level statements of ruling Q8. Prove nothing about efficiency or the
  asymptotic `NUPPT` bridge, and assume no SIS hardness.

**Checkpoints** (each delivers whole proved declarations; at least one mid-way checkpoint is required):
1. **Checkpoint 1 · F5**: both Columns targets proved, with the module's checks, axiom prints and seals. Send it.
2. **Final · F6** and every target proved; the full checks below.

If a sketch is wrong, or a target is false as stated, stop that line of work and escalate with the exact
obligation: a checkpoint with the counterexample or the missing fact. **Do not weaken any statement**, add a
hypothesis or change a definition. A partial final is allowed only with each unproved target named and its exact
remaining obligation stated.

## Scope

**Owned files.** `Hashing/SIS/Columns.lean` and `AdvancedEncryption/Homomorphic/GSW/Security.lean`. In them you
may:
1. replace each target's `sorry` body;
2. rewrite each target's `**Proof sketch.**` paragraph to describe the delivered proof (the statement prose before
   it stays byte-identical);
3. add auxiliary declarations (lemmas, `private` or public) before their first use, each public one with a
   formula docstring, and list new public results under `## Main results`. Hybrid samplers or column tests, if you
   make them public definitions, land with `_eq` readers; prefer local `let`s or `private` definitions;
4. add precise `import` lines for Mathlib modules and for `TCSlib.Cryptography.Pseudorandom.Indistinguishability`
   (in `order.txt`). Fetch the cache for any new Mathlib root as the addendum says. Any other import needs a scope
   request. `Columns.lean` must not import anything under `AdvancedEncryption/`.

**The frozen-statement rule (binding; checked).** Every declaration present at the issue base in an owned file
stays in the same file and order, with its header byte-identical: attributes and modifiers (the `simps`
attributes included), keyword, name, binders and type, up to the `:=`, `by`, `where` or first `|` that begins the
proof. Every `def` (`hashColumns`, `view`, `realView`, `uniformKeyView`, `reduction`, `columnHashParameters`)
stays byte-identical, body included, and so do the readers and the `attribute [simps …]` line. Delete nothing. Keep
every `open`, `set_option` and the module title. Write a `python3 -I` script that extracts every declaration of the
owned files at base and at final, compares headers (and whole definitions) byte for byte, checks the order, and
prints the full diff; deliver it and its output under `evidence/headers/`, with zero unexpected differences. Add
two controls: one header altered by one character must report exactly one difference, and a deleted reader must
report exactly one removal.

**Helper modules.** Not expected. If one is needed, it goes under `Hashing/SIS/Columns/` or `GSW/Security/`, is
imported by that owned file only, and states its lemmas generically. The facades `Hashing/SIS.lean`,
`Hashing.lean`, `GSW.lean`, `Homomorphic.lean`, `AdvancedEncryption.lean` and `TCSlib.lean` are frozen.

**Frozen files.** Everything else, including `gsw-core`'s five GSW files, the SIS, LWE, Regev and Foundations files
and all facades.
- **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
  import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff and
  the reason, and go ahead only on his approval. Record the request and his answer verbatim under
  `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. Seyoon prefers a route with no frozen-file edit.
- A lemma that belongs in an existing file goes in your owned file, with a promotion request. The generic column
  hybrid is meant for the shared hash layer, which is why it lives in `Columns.lean`; state any helper there
  generically.

## Sources and citations (DW-6, DW-7)

- The sources are [GSW13] (author version of 8 June 2013), [Pei16] (author version of 17 February 2016), [BV14]
  (ePrint 2013/541) and [Vad12, Theorem 6.18]. **GSW13 and BV14 are not ingested** (DW-7, Seyoon 2026-11-16:
  Markdown transcriptions of the passages used are added later by the maintainer), and the scoped Pei16 Markdown
  does not yet cover §6.1.3 (DW-7 also extends it later).
- You may rely on: the frozen docstrings' tags; the Gate 41 excerpts on the exchange,
  `outbox/gates/41-gsw-statements-gate/source-excerpts/{GSW13,BV14,Pei16}-excerpts.md` (SHA-256
  `b1241a90e4068e3f95a0bd80a2b4b497753d644e12c03fcd859be27cb70a4311`,
  `d83ffb1914e2e88956ce03d62e5a7f6a87b4c14af1ce25221da43c94ae139166`,
  `2b86ff971644029c715d748ac9425bcbed4c7a5ac3c2f4418a610d3c0ff11199`); and the committed raw extraction
  `blueprint/src/references/peikert2016-lattice-survey.raw.md` (§5.2.1 is also in the scoped `.md`).
- **Never fabricate a source excerpt, quotation or location.** A new declaration either is glue (no tag) or carries
  a tag whose passage is in those materials. Do not add reference files, edit `blueprint/` or run
  `scripts/sources.py`.
- **Small-secret LWE (A3, DW-6) is not used.** The DLWE instance has the GSW key's `m` rows and one common uniform
  secret. Introduce no normal-form assumption.

## Proof discipline

- **Size and width.** Every line has at most 100 characters (Python `len`), every file at most 1000 lines (policy
  target 150–600 per math file). Check both with a short `python3 -I` script before each push and put its output in
  `evidence/`.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key names.
    Reuse published lemmas by importing them. The table above is a start; search further.
  - **Probability, advantage and hybrid lemmas first.** The undisclosed re-proofs that recent reviews and gates
    found were mostly of this kind (prf-mac F-01 `prfAdv_eq_expect`; learning `OneWay.uprob_eq_one_div_card`;
    G29-01 `OneWay.uexp_const`; G32-01 the `getD`/`headD`-of-`List.ofFn` family). Before writing any advantage,
    triangle, hybrid-sum, relabelling, push-forward, coin-planting or uniform-coordinate lemma, search for
    `uprob_*`, `uexp_*`, `acceptProb_*`, `distAdv_*`, `abs_sub_le_sum_hybrids`, `exists_hybrid_gap` and the
    multicopy family.
  - **Undisclosed copies of public lemmas are majors** (Gates 23, 24, 29, 32, 34).
  - **Nearest relatives here:** the Regev PKE hybrids (F6 restates them for GSW's ciphertext space, which Gate 41
    accepted as not duplicate); `Lossy.column_gap` and the multicopy hybrid (F5's hybrid); and
    `Regev.hashParameters`, of which `columnHashParameters` is the disclosed Q11 copy.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published readers,
    keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    (and every inline `have` re-proof) that restates, specializes or re-proves existing material (public or
    private, TCSlib or Mathlib), give its nearest relative (`path:line`), the relation, and why it is not reused.
    List the searches you ran.
- **Docstrings and sketches.** Do these yourself:
  - every new public declaration has a docstring that states its formula, with its arguments in the Lean order, and
    a source tag only as *Sources and citations* allows;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3); each target's sketch describes the delivered proof;
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8);
  - add no `@[simp]`, and no global attribute.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections (the
    table above). Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step but are never passed to
    `simp`, `rw` or `unfold`; use their equation lemmas.
  - Each owned file may read **its own** definitions directly. `Columns.lean` and `Security.lean` are foreign to each
    other (Security reads `hashColumns` only through `hashColumns_apply`/`hashColumns_eq_mul`), and both are
    foreign to `gsw-core`'s files (`encrypt` through `encrypt_eq`, `gadget` through `gadget_apply`).
  - **Type-level Rule 10 (plan §G8).** Matrix index types must never be reached by unfolding another file's
    definition: never unfold `Regev.hashParameters`, `Regev.augmented`, `LWE.sample` or `distAdv`/`acceptProb` at
    the type level. The seal must cover `Regev.augmented`, `LWE.sample` and the SIS `hash`.
  - **Notation, never sealed:** reducible abbreviations (here GSW's `Parameters.columns` and `Ciphertext`),
    `PolyExpr.eval`, and projection coercions (a `CoeFun`/`Coe` whose body is a structure projection; Seyoon,
    2026-11-14).
  - Identifiers use the Greek `μ` (U+03BC); never the micro sign `µ` (U+00B5).

## Checks and report

- **Bootstrap.** From `order.txt` (147 modules) and the narrow `roots.txt` (84), following the addendum. The order
  is the upstream closure of the modules downstream of your two owned files (they include the `Hashing` and
  `AdvancedEncryption` facades; root `TCSlib` excluded) and of `Pseudorandom/Indistinguishability`. Check one
  module per `scripts/lean_check_tree.sh` call, one Lean process at a time on the host. **Never run `lake build`**
  or an unfiltered `lake exe cache get`. Run Python as `python3 -I`. Insert any helper module before its consumer.
- **Per-module native check and sweep.** Check each owned module after each change. Before each delivery,
  recheck both owned modules and sweep the whole order with 0 errors.
- **Admissions.** Compare the `sorry` warnings with `base-sorries.txt` (53 declarations in 15 modules: the 35 GSW
  targets and 18 complexity-layer admissions). At the final the only change is the removal of your 6 targets (47
  in 13 modules). A checkpoint lists exactly which targets it removed.
- **Axioms.** Print the axioms of every target and of every stored constant of the changed files. At the final
  expect only `propext`, `Classical.choice` and `Quot.sound`. Run a **dependency trace** (a probe that walks the
  constant closure and lists every sorried constant reached); it should reach none, and any `gsw-core` target it
  reaches must be named.
- **Headers.** The frozen-statement check with its controls.
- **Rule 10 evidence.**
  - Whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and final,
    with **`-DmaxErrors=0`**.
  - Both the **strict** and the **coe** variant; **the coe-variant seal A is canonical**. Report every failing
    declaration in each and attribute every difference by reading its raw log.
  - Paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - The explicit-unfold scan.
  - **Error counts (G26-N1), both forms.** Count both `error:` and `error(…)`, for example with
    `^\S+\.lean:\d+:\d+: error[:(]`, in every seal, control, sweep and probe log. Keep every raw log.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  The maintainer's baseline at the issue base is **92 FAIL / 101 WARN over 364 files**; the two owned files have no
  FAIL or WARN line. Diff the line sets, not only the counts: no new FAIL line, and no new WARN line except one you
  disclose and justify.
- **Name-clash scan.** No new name (public or private, namespaces resolved) may already be declared in `TCSlib/`
  at the issue base. Deliver the script and its output under `evidence/clash/`.
- **Report.** `REPORT.md` gives the base and the status of each target; the changed files with lines at base and
  final, and the sketch edits; the new declarations; **Overlap and reuse**; **Scope requests** (none, or each with
  Seyoon's answer); promotion requests; the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered: seal and control sources, manifests and request
  records; the header check, its output and controls; the clash scan; the dependency trace; every raw log and
  `results.jsonl`; the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's (top level and `evidence/`), with no
  leading `./`.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing, after #332
and #333 merge.

**Ready to dispatch**
