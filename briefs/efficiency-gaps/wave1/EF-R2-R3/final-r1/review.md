# EF-R2/R3 `ef-r23-regev` · final r1 · maintainer review (phase 1 static, phase 2 Lean)

**Verdict: ACCEPT WITH LANDING EDITS; landing held.** There is no blocker and one **major**, EFR23-F01: an
undisclosed inline re-derivation of `EnsembleLemmas.coinsEquiv` and `ofFn_coinsEquiv` inside the proof of
`exists_reductionMachine`. The fix is a proof-only landing edit (LE-coins, 5 lines). Phase 2 compiled it,
checked its axioms and sealed it. Under the standing rule (no landing with a major) **no landing branch was
pushed and no PR was opened**; question EF-R23-R1 asks Seyoon to rule.

The mathematics is right. Both reductions are proved `NUPPT` machines built with
`NUPPT.exists_realizesOn_of_preTarget_id` (the PKE one followed by the registered `NUPPT.exists_split`), their
parameters and messages are advice only, and the four target theorems are stated **exactly as in the brief**,
with equalities. The security theorems reach `DLWEAssumption` through those machines with no efficiency
hypothesis and no smuggled assumption. The general-modulus toolkit is new, uniform (`PolyTimeComputable`)
and built only on registered hosts.

**Findings:** major F01; minors F02 to F04; information I1 to I6.

Phase 2 (`phase2.md`) replayed the delivery on the merge of `iO/phase-a-base` with the records tip, on a
`cp -al` copy of snapshot #11:
- 26/26 modules rc 0, 0 errors in either form, 0 `sorry`, including root `TCSlib` and both `audits/*/Checks`;
- 80 stored constants of the three owners, standard axioms;
- canonical coe-A seal of the three owners: 0 errors; the delivered paired controls ALL_OK;
- lint unchanged; snapshot #11 rehashes 0/0/0.

## What was reviewed

- **Delivery.** `inbox/fills/ef-r23-regev/` on `exchange/pass-shelat-ch5-8` at
  `4b6d3db5a54342de48cb067c50b11ec6b75c2cc0` ("fill ef-r23-regev: final"; parent `cad5c7c8`, checkpoint 1).
  - Unsigned (0 `gpgsig`); 8 paths changed, all under the unit's folder. The path is unchanged at the exchange
    tip `0e18bf6d` at review time.
  - Extracted with `git archive`: 677 files (`REPORT.md` 238 lines, 3 patches with `COMMITS.tsv`, `src/` 6 files,
    `evidence/`). Top-level `SHA256SUMS` `00800e7c…`, `evidence/SHA256SUMS` `95d9bef8…`.
- **Contract.** `briefs/efficiency-gaps/wave1/EF-R2-R3/brief.md`, `COMMON.md`, `rulings.md` (Q-R-1 A,
  Q-R-2 A) and `README.md` at the records pin `54dcb302`. Between the pin and the tip the brief, `COMMON.md`
  and `rulings.md` are unchanged; `README.md` and the dispatch prompt changed only in pin and EF-D4 lines.
  Handoff §2 rules 15 and 16.
- **Base.** `iO/phase-a-base` = `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, tree `91559030…` (#374, #378, #384,
  #380; all open).
- **Method.** The EF-D1 review (`../../EF-D1/final-r1/review.md`, `phase2.md`), scaled.

## Checks

| Check | Result |
|---|---|
| **Integrity** | **PASS with a gap (F02).** Both manifests verify every *present* file, list no file twice, have no leading `./` and do not list themselves. But **43 listed paths are not in the delivered tree** (in neither manifest's tree, nor in checkpoint 1's): `evidence/probes/ToolkitProbe.lean.txt`, `evidence/probes/toolkit-probe.log` (the R-P1/R-P2 evidence) and 41 sub-agent dry-run probe sources under `evidence/subagents/tools-agent/dryrun/probes/`. No file is extra. |
| **Patches (C13)** | **PASS, 3/3.** `git am` at the base in a sparse scratch worktree, signing off, committer data per `COMMITS.tsv`: `c7b23617`, `daaf5e65`, `324c5de20c4b5fe1e0ee95a07612d3fa2ffd4b1a` (= REPORT's head). 0 `gpgsig`. `src/` equals the head, 6/6 files byte for byte. **Against checkpoint 1:** commits 1–2 are checkpoint 1's (`daaf5e65` was its head); their four sources are byte-identical and the patches differ only in `[PATCH n/2]` → `n/3`. Commit 3 (series 3) is new. |
| **Scope** | **PASS.** `git diff --stat 5ed465f6 324c5de2` lists exactly the brief's six files: `Encoding/ModularArithmetic.lean` +730, `Encryption/Symmetric/Regev/Asymptotic.lean` +310, `Encryption/PublicKey/Regev/Asymptotic.lean` +423 (new), and the three facades +3 each (one `import`, one two-line `## Contents` bullet; C7 frozen check PASS). 1,463 new lines, inside the brief's 1,100–1,900. `TCSlib.lean` unchanged. |
| **decls2 (C3)** | **PASS.** Pinned `decls2.py` (`fa81981a`) on the reproduced head: **62 ADDED, 0 CHANGED, 0 REMOVED**; byte-identical to the delivered `statements/decls2.txt`. |
| **Clashes (C10)** | **PASS.** The 18 most distinctive new names grepped on all **285 remote heads** (4 moved heads fetched): **0 hits**. Positive control (`coinsEquiv`, `listToNat_modulusWord`): 128 heads, including `iO/phase-a-base`. The three short names shared with #377's `GSW.encodeView*` are in another namespace; no module opens either Regev namespace and nothing outside `GSW/Asymptotic.lean` uses `encodeView` unqualified. The merged-tree root build (phase 2), which imports both, is clean. |
| **Admissions (C4)** | **PASS.** 0 `sorry`/`admit`/`native_decide`/`axiom`/`opaque`, 0 `@[simp]`, no new `attribute`, no `private`. Every base lemma used (`distAdv_encrypt_le`, `two_extractionError_le`, `Realization.lean`, `LWE/*`) is itself admission-free. |
| **Hygiene** | **PASS.** Widths ≤ 100 characters, files 730/310/423 lines. Mathlib-style headers, repository copyright, `relaxedAutoImplicit false`, `autoImplicit false`. Every public declaration has a docstring with its formula; every proof of about 15 lines or more has a `**Proof sketch.**` (the one long declaration without one, `encryptPre_eq`, is an `rfl` reader). Every definition has its `_eq` reader. |
| **Citations** | [Pei16] §5.2.1 and Def. 4.2.3, [Wu24] Def. 20.5 and Lecture 21 (the "compilation last updated 30 April 2024" wording is the ingested file's), [Vad12] Thm 6.18, [PS10] Defs 26.8 and 91.1 (ingested `pass-shelat-2010-ch2/ch3`), [AB09] §7.2 for the toolkit: all are the brief's list. Glue declarations say "Glue". |

## Statements versus the brief

Every target maps to a declaration (REPORT *Target map*), checked against the source.

| Brief target | Delivered | Form |
|---|---|---|
| `exists_shiftMachine` | `Symmetric/Regev/Asymptotic.lean:228` | the brief's statement verbatim, **`=`** |
| `singleMessageSecure_of_dlweAssumption` | `:284` | verbatim (ε before the messages) |
| `encodeView`, `encodeView_eq`, `_length` | `PublicKey/Regev/Asymptotic.lean:73–93` | key via `encodeChallenge`, then `encodeVector`, then the residue numeral |
| `exists_reductionMachine` | `:298` | verbatim, **`=`** |
| `singleBitSecure_of_dlweAssumption` | `:397` | verbatim; `hm` is #377 A1's width condition |
| toolkit `addModPoly`, `vecAddModPoly(_encodeVector)`, `subsetSumModPoly(_encode)` and their polynomial-time theorems | `addMod`, `vecAddModWords(_encodeVector)`, `subsetSumModWords(_encodeMatrix)`, `polyTimeComputable_*` | renamed, sizes read from words (change 1) |

The disclosed statement changes, each checked:

1. **`…Words` instead of `…Poly`; sizes read from input words.** Justified: under Q-R-2 A the modulus,
   counts and width are the reduction's advice, not `PolyExpr`s of the input length, so the dyadic `Poly`
   signature cannot carry them. The correspondence lemmas are the brief's (`… = encodeVector |c| (u + v)`,
   `… = encodeVector |c| (Aᵀ *ᵥ r)`) with canonical-context forms at width `w`. Question EF-R23-W2.
2. **Subset bits `ofFn r ++ extra`.** A strengthening; it lets the PKE machine draw `S(κ) ≥ m` coins.
3. **The scalar `⟨b, r⟩ mod q` is the one-column subset sum.** No second loop; correct.
4. **`modContext w q = ⟨0^w, natToList (w+1) q⟩`**, public with readers, shared by series 2 and 3. Its
   modulus numeral is #384's `modulusWord` convention; see F03.
5. **Public pre-processing ingredients** (`shiftAdvice`, `shiftPre`, `shiftAdviceBound`, `encryptAdvice`,
   `encryptPre`, `encryptAdviceBound`) with readers, lengths, correctness and polynomial-time theorems.
6. **Two must-reuse items unused**, with reasons that hold: `acceptProb_distinguisherL_congr` needs agreement
   on every coin string, which `RealizesOn` gives only at the layout length; the symmetric coin transport uses
   `RealizesOn.distinguisherL_eq`, `NUPPT.coinsCongr`/`runAt_coinsCongr` and `acceptProb_coins_equiv`
   instead of `runAt_coinsEquivPoly_symm`.

**No target was weakened**, and there is no new hypothesis.

## Rule 15 and the security conclusions (the heart of the review)

**The reductions are the stated machines.**
- **Symmetric.** `exists_realizesOn_of_preTarget_id D` with `f = shiftPre` (`polyTimeComputable_shiftPre`),
  advice `shiftAdvice P_κ w_κ (μ κ)` bounded by `shiftAdviceBound F`, and the target
  `shiftPre ⟨shiftAdvice μ, enc x⟩ = enc (shift μ x)` (`shiftPre_shiftAdvice`, at `F.modulus_le_pow`). The
  resulting `B` *realises* `fun κ x r => D.runAtL κ (enc (shift (μ κ) x)) (r.take …)` on the DLWE challenge
  encoding with `D`'s coins; `hverdict` turns this into `D`'s verdict on the shifted challenge, and
  `acceptProb_coins_equiv` transports both acceptance probabilities. `D' = B`.
- **PKE.** The realiser `B` reads `⟨enc pk, s⟩` with `s ∈ {0,1}^{S(κ)}` and runs `D` on
  `encodeView (view μ pk (Fin.take m s))` (`encryptPre_encryptAdvice`: subset sums modulo `q` with the
  toolkit, plus the codepoint, all from advice). `NUPPT.exists_split B S` (Closure.lean:390) gives
  `D' = B₂` with coins `S + D.coins`, whose first `S(κ)` coins become `s`. The coin relabelling
  `((t, v), u) ↦ t ++ u ++ v` and `acceptProb_coins_fst` (the `S − m` unread bits) identify `D'`'s DLWE
  advantage with `decisionAdvantage (reduction P μ D_κ)`, the function-level reduction's coin type being
  `(Fin m → Bool) × D.Coins κ` (`reduction_eq`).
- **Both `D'` are `NUPPT` values**, a structure that carries its own time bound and halting proof
  (`Randomized/PPT.lean:137`), produced by the registered constructors `exists_reparam_pre_post` (through
  `exists_realizesOn_of_preTarget_id`) and `exists_split`. Nothing is assumed.
- **Advice only.** `shiftPre` and `encryptPre` are single uniform `PolyTimeComputable` maps; `n`, `m`
  (unary), `q` (numeral), the width (`0^w`), the codepoint(s) and, for the symmetric scheme, the message
  are advice. The worst message of `singleMessageSecure_of_dlweAssumption` is chosen by
  `Finset.exists_max_image` per `κ` and enters only as advice; the machine's efficiency is proved for every
  advice value, so `Classical.choice` picks data, not a machine (the `FromPRG` pattern, cited).
- **REPORT's advice and coin table** matches the source: advice lengths `2mnw + mw + 2m + 12w + 20` and
  `2mnw + 4n + 2m + 13w + 24` with `PolyExpr` bounds `shiftAdviceBound`/`encryptAdviceBound`; coins `D.coins`
  and `S + D.coins`.

**The security theorems.** `singleMessageSecure_of_dlweAssumption` instantiates `distAdv_encrypt_le` at the
distinguisher `fun c r => D.distinguisherL κ (encodeChallenge c) r`, bounds each term by the worst message's,
and rewrites it with `exists_shiftMachine` into `F.advantageAt D' κ`; `ε = 2·advantageAt D'` is negligible by
`dlweAssumption_iff`. `singleBitSecure_of_dlweAssumption` instantiates the PKE `distAdv_encrypt_le` at exactly
the `D_κ` of `exists_reductionMachine`, rewrites both reduction terms (`h₀`, `h₁`), bounds
`2·extractionError` by `2^{-κ}` (`two_extractionError_le` with `F.modulus_le_pow` and `hm`), and closes with
`Negligible.add`/`mono`. **There is no gap between the machines and the bounds, and no hypothesis beyond
`DLWEAssumption F` and (PKE) the brief's width condition.** No final theorem has an efficiency hypothesis; the
honest algorithms are untouched (EF-H5/H6). Audit rows R43/R44 become class **M**.

## Duplication sweep (binding)

**Searches** (base `5ed465f6`, records tip with #377 merged, all 285 remote heads for the new names, the
EF-H11 delivery on the exchange, Mathlib by name): modular add/mod compositions (`BinArith.mod (pairEncode …`),
`addMod`/`modAdd`/`addS`/`addModW`, subset sums, `mulVec`, `modulusWord`, `listToNat_natToList`, iterate-length
lemmas, coin-splitting equivalences (`appendEquiv`, `coinsEquiv`, `splitCoins`, `seedEquiv*`), zero-numeral
identities, `coinsCongr` lemmas, GSW `Asymptotic.lean` declarations.

**Result.**
- **No general-modulus vector arithmetic existed.** The toolkit is genuinely new: the dyadic layers reduce mod
  `2^W`; `DetMod`'s `entryModW`/`rowModW` and `Words.zipWithW` work on the self-delimiting `encWords` layout,
  not the fixed-width `encodeVector` layout the brief mandates; BB1's `addS` is built on `Candidates.addStr`/
  `divModStr` (excluded by the brief, EF-H1's) and a group order.
- **One undisclosed inline re-derivation: F01 (major).**
- **Undisclosed near-relatives, not re-proofs: F03.**
- **Disclosed and accurate:** the dyadic analogues, `subsetSumStep_iterate_length_le` (a quadratic-growth
  variant of `length_iterate_le_of_ctx`, which only covers linear growth in the context: genuinely needed,
  I2), the GSW `encodeView` analogue, `ReductionEfficient` as the proved Regev analogue, the bounds vs
  `inputBitsBound`, `acceptProb_coins_equiv` (and the pre-existing duplicate in `ReductionSupport.lean:221`).
- **Hosts.** `BinArith.forLoop` (with `forLoop_bound_of_ctx` and a cubic envelope), `polyTimeComputable_ite`,
  `pairTakePoly`/`pairDropPoly`, `BinArith.add`/`mod`/`mulU`, `toLE`/`fromLEPoly`: all registered. No new host.
- **#384 contract and #377 GSW:** nothing re-proved; see F03 for `modulusWord`.

## Recount of the worker's evidence

From the raw files, bound to the reproduced sources. Tool: `tools/recount_r10.py` (in the evidence zip).

- **Build (C1).** `build/summary.txt`: 8 modules rc 0, 0/0 errors, 0 `sorry`; the logs are empty, as
  `lean_check_tree.sh` leaves them on a clean compile; each source SHA-256 equals the reproduced head's.
- **Seals (C6).** 24 raw seal logs (6 owners/facades × A/B × strict/coe): **0 `error:`, 0 `error(`, 0 `sorry`**;
  exactly one `G06-SEAL-END` each with `requested = verified` (coe-A: 1011/1121/1131/1134/1145/1149, as
  REPORT); every log SHA-256 equals its `results.jsonl` record with rc 0; every sealed source embeds the head
  source verbatim (24/24). Unlike EF-D1's delivery, the raw logs are included.
- **Paired controls.** `ctlcheck-{strict,coe}`: 12 probes each, `all_ok` true. Per control (theorem span):
  13 definitions (`addMod`, `vecAddStep`, `vecAddModWords`, `subsetSumStep`, `subsetSumModWords`,
  `modContext`, `shiftAdvice`, `shiftPre`, `shiftAdviceBound`, `encodeView`, `encryptAdvice`, `encryptPre`,
  `encryptAdviceBound`); each negative fails exactly once sealed, each reader control passes, unsealed 0
  errors. The toolkit's six pairs are repeated in the two scheme hosts (hence 6/9/10 errors per sealed host).
- **Explicit-unfold scan.** 363 items (206 toolkit, 55 symmetric, 102 PKE), **0 foreign**.
- **Axioms (C5).** 62 constants, all within the three standard axioms; recomputed in phase 2 (80 stored
  constants).
- **Lint (C8), sizes (C9), frozen (C7), clash (C10), admissions (C4).** Re-derived independently above and in
  phase 2; all agree.
- **R-P1/R-P2 (C12).** Not recountable: the files are missing (F02). Phase 2 wrote and ran its own probes:
  0 mismatches (see `phase2.md`).
- **C2.** The worker could not build the root (PFR oleans), F04; phase 2 closes it.

## Findings

**Blockers: none. Majors: one.**

- **EFR23-F01 (major; undisclosed inline re-derivation).** In `exists_reductionMachine`
  (`PublicKey/Regev/Asymptotic.lean:334–343`) the coin relabelling ends with
  `(Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool))`, which is the body of
  `EnsembleLemmas.coinsEquiv hlen.symm` (`Asymptotic/EnsemblesLemmas.lean:141`), and `hφ` re-proves
  `EnsembleLemmas.ofFn_coinsEquiv` (`:145`) twice inline (`List.ofFn_congr`, `List.ofFn_fin_append`, its own
  proof). Both are public, in a module the file imports directly, and are the house pattern (used throughout
  `Asymptotic/`). REPORT lists `Fin.appendEquiv` and `finCongr` as reuse but not the TCSlib helper.
  - **Grade.** COMMON §4.4: "no inline re-derivation of a TCSlib or Mathlib fact"; an undisclosed re-proof is
    a major (precedents G48-01 and DL-61, regraded major at Gate 50: "an inline re-derivation of a library
    lemma is a re-proof").
  - **Fix (LE-coins, proof-only, 6+/5−).** Replace the two `Fin.appendEquiv` steps by
    `EnsembleLemmas.coinsEquiv rfl` and `EnsembleLemmas.coinsEquiv hlen.symm`, and prove `hφ` by
    `change … ; rw [EnsembleLemmas.ofFn_coinsEquiv, EnsembleLemmas.ofFn_coinsEquiv]`; one docstring word.
    **Phase 2 demonstrated it** on a scratch commit (`90123822`): compiles with 0 errors, both PKE theorems
    keep axioms `[propext, Classical.choice, Quot.sound]`, and its own coe-A seal has 0 errors. Statements
    unchanged. The diff is `phase2.md` §P2-6 and `le-coins.patch` in the evidence zip.
- **EFR23-F02 (minor; integrity).** 43 paths listed in both manifests are not in the delivered tree (above),
  including the brief's R-P1/R-P2 evidence (`probes/ToolkitProbe.lean.txt`, `toolkit-probe.log`). The same
  gap was in checkpoint 1. Likely an ignore rule in the worker's environment; nothing else is affected.
  **Closed for the review** by the maintainer's own R-P1/R-P2 probes (phase 2, 0 mismatches). Fix: none for
  landing; noted for the delivery checklist ("`git ls-tree` the delivered path against the manifest").
- **EFR23-F03 (minor; disclosure).** Near-relatives missing from REPORT *Overlap and reuse*, none a re-proof:
  - `listToNat_modulusNumeral` (`listToNat (natToList (w+1) q) = q` for `q ≤ 2^w`) and the numeral half of
    `modContext` vs #384's `CoinSampling.modulusWord`/`listToNat_modulusWord`
    (`CoinSampling/Contract.lean:313`, `:322`): the same numeral and read-back. The toolkit's form is the more
    general one (plain `w`, `q`, `q = 0` allowed); the contract's cannot produce it. Both are one-line
    applications of `Candidates.listToNat_natToList`.
  - `addMod` vs BB1's `addS` (`BonehBoyenMachine/Words.lean:154`) and `DetMod.entryModW`/`rowModW`
    (`ClassP/BinaryArith/DetMod.lean:322`, `:325`), and `vecAddModWords` vs `Words.zipWithW`: other layouts or
    excluded primitives.
  - **Fix.** Disclosure only; ledger note (question EF-R23-R2).
- **EFR23-F04 (minor; closed in phase 2).** C2: the worker could not build root `TCSlib` (PFR oleans).
  Phase 2 rebuilt the root and both `audits/*/Checks` on the merged tree: rc 0. Answers EF-R23-W1.
- **EFR23-I1 (information; cross-job).** EF-H11's delivery (exchange, under review in parallel) has its own
  scalar modular leaves `addModW`/`subModW`/`mulModW` (`SecretSharing/Efficient.lean:386`ff, little-endian
  `Nat.bits` words cut to `|p|`), siblings of `addMod` (MSB fixed-width numerals). Neither is on a base yet.
  Relayed for the EF-H11 review and the ledger (EF-R23-R2).
- **EFR23-I2 (information).** `subsetSumStep_iterate_length_le` is a disclosed, justified variant of the
  registered `length_iterate_le_of_ctx` for quadratic growth. A future generalization of the registered lemma
  (growth any function of the context) would absorb it.
- **EFR23-I3 (information).** `encodeView` injectivity is not stated (the brief: "if used"); it is not used.
- **EFR23-I4 (information).** The PKE facade keeps the base sentence "All nontrivial new statements are
  admitted for the combined statement audit", now above a bullet for fully proved results. Base text the
  worker could not change; a later facade cleanup.
- **EFR23-I5 (information; EF-R1).** The toolkit (series 1) is what EF-R1 (GSW reductions) needs; its base is
  "the #377 merge plus the accepted EF-R2-R3 head". F01 touches only series 3's proof, so series 1–2 are
  unaffected by the landing edit.
- **EFR23-I6 (information).** The worker's commits carry the worker's own `Claude-Session` trailer
  (`session_01PqpVTk66VZE4WBTyevEPhu`); cherry-picks keep messages verbatim, as in earlier landings.

## Landing (held)

- **Not done:** no `land/ef-r23-regev` branch, no push, no PR. The standing instruction lands only with no
  blocker or major; F01 is a major.
- **Ready to do on EF-R23-R1 (A):** branch `land/ef-r23-regev` from `iO/phase-a-base` with `git cherry-pick -S`
  of the three worker commits (they apply cleanly: the scratch check head reproduces
  `git merge-tree --write-tree 324c5de2 bff0567b`), then one maintainer-signed commit LE-coins (the demonstrated
  diff), a re-run of the PKE owner's compile, axioms and coe-A seal on the landing head, and a **draft** PR on
  base `iO/phase-a-base`. The PR body should say that the delivery supplies EF-R1's toolkit and that a Codex
  gate is to be staged.
- Stacking: like #387, the PR lands after #374, #378, #384 and #380.

## Questions for Seyoon

- **EF-R23-R1 (F01, the inline `coinsEquiv`).**
  - **(A, recommended)** Maintainer landing edit LE-coins (demonstrated in phase 2: compiles, axioms
    standard, coe-A seal 0 errors), then land as a draft PR stacked on `iO/phase-a-base`.
    *Why:* proof-only, five lines, no statement change; it repays the duplicate before it lands.
  - (B) Return to the worker for a fix round (a new final), then re-review.
  - (C) Land as delivered and record F01 as debt in the duplication ledger (fix in Stage 3).
- **EF-R23-R2 (F03 and I1, modular-arithmetic consolidation).**
  - **(A, recommended)** Record a ledger entry now: `ModularArithmetic` is the general-modulus home; at the
    next shared-file window derive `listToNat_modulusWord` from `listToNat_modulusNumeral`, and decide at
    EF-H11's landing whether its scalar leaves re-point to `addMod` (layouts differ, so no forced change now).
  - (B) Require EF-H11 to re-point its scalar leaves to `ModularArithmetic.addMod` before it lands.
  - (C) No action.
- **EF-R23-W1 (the worker's: the root build of C2).**
  - **(A, recommended)** Accept: phase 2 built root `TCSlib` and both `Checks` on the merged tree, rc 0 (F04).
  - (B) Authorize a PFR package build for the worker.
- **EF-R23-W2 (the worker's: toolkit names).**
  - **(A, recommended)** Keep `vecAddModWords`/`subsetSumModWords`: their sizes come from input words, not
    `PolyExpr` schedules, so `…Poly` would mislead.
  - (B) Rename to the brief's `…Poly` names in a landing edit.

**Not yet clear to land: F01 (major) awaits EF-R23-R1; stacked on `iO/phase-a-base` (#374, #378, #384, #380
unmerged); Codex gate to be staged.**
