# Gate 46 · the GSW 6b gate: O2 (#376) and the 6b statements (#377) · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).
- This is **Gate 46** of the phase-6 rulings (P6-Q1: the cryptography-layer statement gate of GSW phase 6, "6b").
- Its scope is the one plan section r3 §H7 gives it ("Gate 46 audits (6b and O2)").
- Two stacked draft PRs are audited. The checks named below are in `verification.zip` (`checks/`).

## Pins

- **PR #376 (O2):** draft [PR #376](https://github.com/Shilun-Allan-Li/tcslib/pull/376), branch `land/gsw-6b-o2`, head
  **`04ba2446f541c39dd02aefaa97a9eb31dbbda748`** (tree `8b615e060f72d72749f67abd39f820d117e0a806`), base
  `cryptography/pass-shelat-ch2-4`.
  - Its parent is the records tip it was cut on, `38123ccbebef878cd25dd2d2761de1b40ba7e421`.
  - It is one SSH-signed commit: the maintainer's `git cherry-pick -S` of the worker's
    `5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd`, with author and message kept.
    - Range-diff: 1/1 `=`.
    - Its tree equals `git merge-tree --write-tree 38123ccb 5bd5ada5`.
    - `LWE/BitEncoding.lean` is byte-equal to the worker's (`checks/series.txt`).
  - It changes 1 file, +58/−0.
  - GitHub's REST `base.sha` is `1a9a32959cc58d7a882d0f6a7e2b0003b52f82ae`, a records-only descendant of `38123ccb`.
- **PR #377 (statements):** draft [PR #377](https://github.com/Shilun-Allan-Li/tcslib/pull/377), branch
  `land/gsw-6b-statements`, head **`7563734a8badba842223e0687c719b3b4692e9d2`** (tree
  `c56db4c403ccab179a994143c5f989d4f3718910`). It is **stacked on #376**: base `land/gsw-6b-o2` at `04ba2446`.
  - **Re-pinned after LE-g46.** This pack was first staged at `680be9fa` (tree `956fc086`). The pre-dispatch sweep's S1
    was ruled fix-now, so LE-g46 (section *LE-g46* below) moved the head before dispatch.
  - It has seven SSH-signed commits:
    - five maintainer picks `47aae69d`, `c10e0d3e`, `80366e7f`, `52f52dc7`, `75c683b2` of the worker's
      `7a814546..8f92fe7d53967bc488a4075fb38210e7d40b9031` (range-diff 5/5 `=`; the tree of `~1`, `22349e8e`, is
      `git merge-tree 38123ccb 8f92fe7d`; every file is byte-equal to the worker's);
    - the maintainer's landing-edit commit **`680be9fa`** (LE-6b1, LE-6b2, LE-6b3);
    - the maintainer's landing-edit commit **`7563734a`** (LE-g46: S1 fixed, and the [Gen09] citations).
  - It changes 11 files, +2144/−1.
- **Records pin: `<RECORDS>`.** This is the commit that files this directory, `briefs/lattice-gsw/gates/46-gsw-6b/`.
  - The records tip at re-staging is `9ae6b909305f868f51f5cc05787c66e4d336bf74`; the pin's parent is that tip or a
    records-only descendant. The pin files this directory as re-staged (with `le-g46.md`, `le-g46.diff.txt` and
    `le-g46-evidence.zip`) and ledger row DL-61 as repaid.
  - The first staging's tip was `dab31951abb5c892dc6279c229e49497ec95de10`. Every record this pack cites at `dab31951`
    (`verification.zip` `records/`, `sources.zip` `context/` and `references/`) reads the same at `9ae6b909`, except the
    decision log and the ledger, whose extracts are re-cut at `9ae6b909`.
  - `9ae6b909` is `38123ccb` plus 31 records-only commits (0 Lean paths; `checks/lean-equality.txt`).
- **Delivery (exchange):** `inbox/fills/gsw-6b-statements/` at `3b340824dde77433b2135a3c8d20c7ed194cf18c` ("stmt gsw-6b:
  final", unsigned). The worker's six commits reproduce hash for hash by `git am` on the issued base
  `3e51b5f28900db6190f1eb2e6d207d27ee15d541` (phase 1).
  - The issued package was staged at exchange `32e54c43` (records pin `e913abe5`).
  - This pack's own exchange commit is named in the dispatch prompt.
- **Lean base.** `38123ccb`'s Lean equals `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62`, the #368 merge, which is **olean
  snapshot #10** (map `84d88738…`). #366 (all 98 6a targets proved) and #368 are merged. The records tip's Lean is the
  same (`checks/lean-equality.txt`). Mathlib is `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`. `GSW/` is
`AdvancedEncryption/Homomorphic/GSW/`. Line numbers are at the heads.

## Scope

- **#376 (O2)** is audited **as a proof**: `decodeLo`, `decodeHi`, their `rfl` readers and the proved interval reader
  `decode_iff_mem_Ico` in `LWE/BitEncoding.lean` (P6-Q7, r3 §H5.8). The file changes by insertions only.
- **#377** gets a **statement-fidelity audit of all 24 admitted targets**. They are the 23 `target` rows of
  `issued-6b-r1/targets.txt`, plus G17 split into a pure lemma and a leveled one, which `targets.txt` allows.
  - The audit is against the sources, cited exactly as the issued brief pins them (next section), and against plan
    section r3 with the rulings.
  - Also in scope: the two proved citations (G11, L1), the two reader-only rows (G14, A2), every definition with its
    readers (the audited surface, `workflow.md` §2), the citations, the deviation notes and the sketches.
- **The landing edits** LE-6b1, LE-6b2 and LE-6b3 (ruled Q-6B-F1 A): their identity with the proposed diff, and that
  they are docstrings-only apart from LE-6b3's proof.
- **LE-g46** (ruled 2026-11-18): S1's proof-only fix, and the [Gen09] citations that replace the stale "not ingested"
  disclosure (docs only).
- **The disclosures:** phase 2's new infos **G6B-F10, G6B-F11, G6B-F12**, phase 1's G6B-F01 to F09, and this gate's
  pre-dispatch sweep item **S1** (question H).
- **Out of scope** (mention only if something in scope depends on it):
  - 6a: #358, #359, #360 and #366 (Gates 45 and 50, merged). Their statements are the frozen base that 6b cites.
  - #368 (Gate 50, merged): `decrypt_eq_decode_dotProduct` and `hybridPlant_eq`, which G6 and L4 consume.
  - The 6b fills U12–U19.
  - The merge order and snapshot adoption (*Merge interaction*), which are maintainer merge conditions.

### Sources, as the issued brief pins them

The ingests at the base, under `blueprint/src/references/`, with the SHA-256 of the issued brief. All six are unchanged
at `dab31951`, which I re-hashed at staging.

| Tag | File | SHA-256 |
|---|---|---|
| [BV14] | `brakerski-vaikuntanathan-2014-fhe.md` | `3da79813fa63acfea4a83229c46f2f8947a7a754657fac8f4d6bf1e7891e9392` |
| [BV11] | `brakerski-vaikuntanathan-2011-fhe.md` | `f415fdbd4488316e2044e0a8e767c75b69964ff48fb6294617b35ae125177eba` |
| [AP14] | `alperin-sheriff-peikert-2014-bootstrapping.md` (Alperin-Sheriff–Peikert, bootstrapping) | `d2605ae062162641ee40701c7592f29d69c342a64c3b4575df547f21153df868` |
| [GSW13] | `gentry-sahai-waters-2013-fhe.md` | `df0d793d8a5a952662502a6c80cb2e3dc41a7372d4ae8e26c7aa49b6219ca540` |
| [Pei16] | `peikert2016-lattice-survey.md` | `fb5c997ea6c0efc2340217c1beff8fc146f08f5d71e892b58d694907466e5955` |
| [Bar89] | `barrington-1989-bounded-width-bp.md` | `0e14d97efe06b4c9f0e2f7672d744885b4e53fa2a3777c3694a664322620c71a` |

The brief's record point is that BV14's "[BV11, Lemma 4.1]" (Prop 3.4) is **Lemma 4.5** in the BV11 version held, so
it is cited as [BV11, Lemma 4.5] with BV14's numbering noted. `sources.zip` carries all six (`.md` and `.raw.md`), and the
[Gen09] ingest as well: `gentry-2009-fhe-thesis.md`, SHA-256
`078db24941b2d00f6f307747ecff87a15d96878fdaab6a008b6c0de14a781d0d` (DW-8, records `bdcadd85`, 2026-11-16; tag `Gen09` in
`sources.json`). The brief did not pin it; LE-g46 cites it on Seyoon's ruling (question C3).

## What changed

**#376** (base `38123ccb`): `LWE/BitEncoding.lean` 142 → 200 lines.
- Two module-docstring entries and five declarations after `decode_eq`:
  - `decodeLo P = P.modulus / 2 / 2 + 1`;
  - `decodeHi P = (P.modulus + P.modulus / 2 + 1) / 2`;
  - their `rfl` readers;
  - `decode_iff_mem_Ico : decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P`, proved.
- decls2: **5/0/0**.
- No `sorry`. The axioms are standard: `decode_iff_mem_Ico` uses `propext`, `Classical.choice` and `Quot.sound`; the
  other four use none.

**#377** (base `04ba2446`):

| File | Status | Targets | Lines |
|---|---|---:|---:|
| `GSW/Branching.lean` | new: `select`, `homEvalPBP`, `homEvalFormula` | 3 (G1–G3) | 179 |
| `GSW/DecryptFormula.lean` | new: `neZero_columns`, `keyBits`, `decConstants`, `decryptFormula`, `nandFormula`, `decDepth` | 6 (G5–G8) | 216 |
| `GSW/Bootstrap.lean` | new: `PublicKey`, `Secret`, `Coins`, `KeySeed`, `bootNoise`, `bootNAND`, `bootGate`, `fheEval`, `fheEvalCircuit`, `evalKey`; G11 proved | 5 (G9, G10, G12, G13, G18) | 349 |
| `GSW/Circular.lean` | new: `FheView`, `Seeds`, `fheView`, `WeakCircularSecure` (G14 reader-only) | 1 (G15) | 146 |
| `GSW/Leveled.lean` | new: `LevelCoins`, `levelKey`, `literalCts`, `levelGate`, `leveledEval`, `leveledEvalCircuit`; L1 proved | 2 (L2, L3) | 291 |
| `GSW/LeveledSecurity.lean` | new: `LeveledSeeds`, `LeveledView`, `leveledView`, `levelHybrid`, `levelMsgs`, `levelAssemble`, `levelReduction`, `levelTerm`, `challengeDist`, `challengeTerm` | 2 (L4, L5) | 362 |
| `GSW/PolyRatio.lean` | new: `Parameters.ofFamily`, `pBoot` | 3 (G16, G17 ×2) | 179 |
| `GSW/Asymptotic.lean` | new: the four encodings, `WeakCircularSecureFamily` (A2 reader-only), `ReductionEfficient`, `LeveledReductionEfficient` | 2 (A1, A3) | 338 |
| `LWE/Ratio.lean` | new: `Family.RatioBounded` | 0 | 59 |
| `GSW.lean`, `LWE.lean` | facades: imports, contents entries, and the GSW title and opening line (brief, *Changed files*) | 0 | 35 → 57, 38 → 40 |

- **decls2, tip → #377 head: 136 ADDED, 0 CHANGED, 0 REMOVED** (phase 2). That is #376's 5 plus #377's 131; `simps`
  adds 4 more names. There are **no `private` declarations**.
- **24 targets, 24 `sorry`** (`checks/targets.txt`, a comment-stripped scan):
  - one per target, in 8 files;
  - each has a formula docstring, a `[TAG, locator, anchor]` tag (G13 `bootNoise_le` says "Glue" instead) and a
    `**Proof sketch.**`;
  - the admitted names equal `targets.txt`'s 23 target rows plus `decrypt_leveledEval_of_ratio`.
- **Everything else is proved:** the definitions' readers (`_eq` by `rfl`, `_iff` by `Iff.rfl`, the case readers of
  `bootGate` and `levelGate`, `literalCts_castAdd`/`_natAdd`, the four `_length` readers, non-simp `simps`), the
  instance `Parameters.neZero_columns`, and the citations G11 `encrypts_evalKey` and L1 `encrypts_levelKey`.
- **LE-6b1..3** (`680be9fa`, 5 files, +17/−21). They are byte-identical to the records'
  `final-6b-r1/landing-edits-proposed.diff` applied to the worker's files (`checks/le-identity.txt`, 5/5 IDENTICAL).
  The comment-stripped code changes only in `Parameters.neZero_columns` (LE-6b3).
  - **LE-6b1** (G6B-F01, F09) rewrites four passages made stale by #366/#368: G6's "**MISSING**"
    `decrypt_eq_decode_dotProduct`; the `fheEvalCircuit` and `leveledEvalCircuit` "while N2 (N12, N13) is admitted"
    sentences; and L4's `hybridPlant_eq`.
  - **LE-6b2** (G6B-F02, F03): PolyRatio's constant is exactly `2^70`; `Leveled` names its extra citations; and
    `LeveledSecurity` adds [BV14, §2.5].
  - **LE-6b3** (G6B-F04): `neZero_columns` uses core's `Nat.one_lt_two_pow_iff`.
- **LE-g46** (`7563734a`, 4 files, +63/−27): see the section *LE-g46* below.
- **Scope:** `TIP..#377` touches exactly the brief's 12 paths. No 6a (`TCSlib/Complexity/`) file, phase-5 GSW file,
  `TCSlib.lean`, `ComputationalModels.lean`, `machine-library-design.md`, `blueprint/` or `audits/` path changes
  (`checks/lean-equality.txt`).
- **Sizes and style:** at most 362 lines and 99 characters wide; 0 tabs; 0 trailing spaces (`checks/sizes.tsv`).

## LE-g46 (S1 fixed; [Gen09] citations)

Seyoon's rulings of 2026-11-18 on this gate's pre-dispatch sweep (`LatticeCryptographyPlan.md`, decision-log row "Gate 46
staged"): S1 is **fixed now** (Q-G46-S1 A, proof-only; ledger DL-61 → "Repaid by LE-g46"), and the stale [Gen09]
disclosure is fixed in the same commit (docs only). Record: `le-g46.md`; diff: `le-g46.diff.txt`; evidence:
`le-g46-evidence.zip`.
- **Commit `7563734a8badba842223e0687c719b3b4692e9d2`** (tree `c56db4c4`), on `680be9fa`, SSH-signed, pushed
  fast-forward. 4 files, +63/−27. No statement, declaration header or `_length` docstring changes.
- **S1:** `encodeFheView_length` and `encodeLeveledView_length` (`GSW/Asymptotic.lean:127`, `:158` at the head) apply
  `TCSlib.Cryptography.length_flatten_map_const` after `List.ofFn_eq_map` and `List.length_finRange`; the inline
  `List.length_flatten`/`List.ofFn_comp'`/`List.ofFn_const`/`List.sum_replicate_nat` chains are gone (the probe's direct
  constants confirm it).
- **[Gen09]:** the stale sentences in `Leveled` (module and `levelKey`), `LeveledSecurity`, `PolyRatio` and `Asymptotic`
  are replaced by citations to §4.1 (p056-b002, p056-b003, p057-b001), Thm 4.2.1 (p059-b001) and Thm 4.2.3 with its proof
  (p060-b001, p061-b001), the index correspondence and the remaining deviations (question C3).
- **Evidence:** the recheck R2-g46 (section *The replays*); comment-strip identity of the three docs-only files with
  controls; the stripped diff of `Asymptotic.lean` is the two proofs.

## Rulings and records in force

1. **Phase-6 rulings P6-Q1..Q19**, with the Q19 refinement and the location ruling (`records/phase6/rulings.md`).
   - **Q7:** O2 lands owner-side.
   - **Q8:** the evaluation key is public-key encryptions under the user's own `pk` of the `N` bits of `G⁻¹(t)`,
     `t = (−s, 1)`.
   - **Q9/Q16:** bootstrapping is NAND-only over 6a's NAND form, with fan-in 1 padded to `(a, a)` and fan-in 0 to
     `(G, G)`.
   - **Q10/Q15 A:** the concrete `WeakCircularSecure` is per distinguisher; the asymptotic family is the headline.
   - **Q11/Q14 B:** the full leveled scheme with a consecutive key chain over layered NAND circuits on `2k` literals.
   - **Q12:** explicit `decDepth`/`bootNoise`, `RatioBounded` in `LWE/Ratio.lean`, and an explicit `PolyExpr` `pBoot`.
   - **Q13:** `fheEval` is computable.
   - **Q19 B, refined:** no `[Gen09]` in the statement job, plus a reconstruction disclosure; the [Gen09] citation is a
     docstring-only follow-up after the ingest, done by LE-g46 (question C3).
2. **Plan section r3** (`records/phase6/plan-section.md`, SHA-256
   `06824b3db875e7388771b6f7a5e78d62bf7d77fa35571fc3a9deeebc329214fd`):
   - §H5.8 (O2) and §H5.9–H5.16 (G1–G18, L1–L5, A1–A3);
   - §H6 (the noise ledger);
   - **§H7, "Gate 46 audits (6b and O2)"**, the checklist this pack's questions cover;
   - §H8.
3. **The issued brief** `records/phase6/issued-6b-r1/` (brief, `targets.txt`, `census.txt`, `pins.txt`, the addendum),
   with **Q-6B-1 A**: G14 and A2 are reader-only.
4. **Checkpoint 1** (`records/phase6/checkpoint1-6b-review.md`):
   - G6B-C1-F01: O2's `habs` re-proved `ZMod.valMinAbs_natAbs_eq_min`; it is fixed in the final;
   - F02 and F03;
   - **Q-C1**: `decrypt_eq_decode_dotProduct` is owner-side in `GSW/Scheme.lean`, landed by #368.
5. **The 6b statement rulings** (Seyoon, 2026-11-18; decision-log row "6b statements rulings"; `final-6b-r1/review.md`
   § *Questions*), all as recommended:
   - **Q-6B-W1 A:** G16 has **factor 8**, so `pBoot`'s constant is exactly `2^70` (`8·4^33·2`), because r3's factor 4
     fails G17 at `q = 4y + 1`.
   - **Q-6B-W2 A:** `LeveledReductionEfficient` also dominates the two challenge reductions.
   - **Q-6B-W3 A:** `levelTerm` depends on μ, and L5's bound is the two-chain one.
   - **Q-6B-F1 A:** apply LE-6b1, LE-6b2 and LE-6b3 (LE-6b3 compiles and is kept).
   - **Q-6B-F2 A:** **`decDepth_le` stays an admitted target.**
6. **Duplication** (policy §1):
   - **G45-01:** an admitted statement that restates a public lemma is a major, even behind a definition wrapper.
   - **G44-01:** disclosure is not acceptance. An accepted duplicate needs a recorded acceptance and a ledger row with
     its repayment.
   - **G48-01, GF-F01, GF-F03 (regraded major at Gate 50):** an inline re-derivation of a library lemma is a re-proof.
   - **G50-05:** dispositions are recorded when found, and name and body scans are not statement-shape review.
   - Ledger rows DL-54 and DL-61 (`records/extracts/duplication-ledger-DL54-DL61.md`).
7. **Rule 10** (policy §1): readers only across files; coe-A is canonical; reducible abbreviations, projection
   coercions and `PolyExpr.eval` are notation. A file may read its own definitions.
8. **Frozen files** (brief, *Scope*): everything except the 9 new files, the two facades (imports and contents) and O2's
   insertions in `BitEncoding.lean`. This includes every 6a file, every phase-5 GSW file and the other `LWE/` files.
9. **Signing** (BS-F08): the account's Claude sessions share one SSH signing key. A signature attests a session on the
   account, not the maintainer. Provenance rests on the pinned hashes and the cherry-picks.

## Standing rule 15 (efficiency) and this gate (Seyoon, 2026-11-18)

After this pack was first staged, Seyoon made efficiency mandatory (standing rule 15,
`briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2): honest algorithms must be proved efficient in
uniform form, every security reduction must be a proved non-uniform PPT machine, and efficiency is
part of every primitive's definition. #377's A1/A3 take the reduction's efficiency as hypotheses
(`ReductionEfficient`, `LeveledReductionEfficient`), and GSW's honest algorithms are not proved
efficient (`Asymptotic.lean` says so). **Seyoon's ruling for this gate:** Gate 46 audits statement
fidelity now; these efficiency hypotheses are **known, tracked holes** under rule 15, to be closed by
one lattice-wide remediation plan (from the efficiency audit `briefs/efficiency-gaps/audit-r1.md`, in
progress), so as not to restate the 6b statements twice. **#377 does not merge until that plan
exists.** Report the hypotheses as a single known item (not as new majors); do report any *other*
efficiency hole you find, and any place where a hypothesis is stronger than "this specific
reduction is efficient" (e.g. one that would make a statement vacuous or smuggle in security).

## Questions for the audit

**A. #376 (O2), as a proof**
1. Is `decode_iff_mem_Ico` true for every `q ≥ 2` and every `v`? Does the proof establish it?
   - Check the `hsub` case split and `hcast`.
   - Check that both distances go through `ZMod.valMinAbs_natAbs_eq_min` (the checkpoint fix).
   - The delivery's kernel `decide` probe covers `q ≤ 63`; the issued `o2check.py` covers `2 ≤ q ≤ 2000`, with 0
     mismatches.
2. Do `decodeLo`/`decodeHi` match r3 §H5.8, and is `decodeLo ≤ decodeHi ≤ q` for every `q ≥ 2`? G6 needs this:
   `modSumInterval_eval` (F9) requires `lo ≤ hi ≤ q`.
3. Insertions only (decls2 5/0/0)? Are the "Glue" notes, the formula docstrings and the sketch accurate?

**B. #377: fidelity of the 24 targets** (statement by statement; `checks/targets.txt` gives file:line)

For each target: is it **true** as stated? Does it say what the cited source says, or what r3 states with the deviation
disclosed? Are its hypotheses satisfiable and **not vacuous or contradictory**? Is it **strong enough** for its U12–U19
fill and its consumers? Are the **edge cases** right (`N`, `k`, `L`, `B`, `β` equal to 0, empty circuits, fan-in 0 and 1)?
1. **Branching, G1–G3**, against BV14 §3.3 Eq. (5)–(6), Lemma 3.6, Thm 3.5; AP14 Eq. (4.1), Lemma 4.1; and Pei16 §6.1.3.
   - G1 `Encrypts.select`:
     - the fresh selector sits on the left (Gate 41);
     - the noise is `βV + 2·(N·β)`, additive through the exact `|x₁|·β₂` term;
     - `b ∈ {0,1}`.
   - G2: stated under `IsPermutation`, from the one-hot start `Pi.single s₀ G`, with noise `length·2Nβ`, in worst case.
   - G3:
     - `4^depth·2Nβ` and `maxFanin ≤ 2`;
     - `[NeZero k]`;
     - the fixed five-cycle `sigma1`;
     - the output coordinate **`σ 0`** (6a's C16 and G6A-F11; coordinate 0 would encode the complement).
2. **DecryptFormula, G5–G8**, against AP14 §5.1, Pei16 §5.4.3, BV14 Prop 3.4 / BV11 Lemma 4.5, BV14 Def 2.13 / BV11
   Def 3.7, and BV14 Lemma 4.4.
   - Are `keyBits` (= `decomposeVec (secretVector s)`) and `decConstants` (= `vecMul (decryptColumn C) (gadget P)`, i.e.
     `Gᵀc`) the right orientation for G5?
   - `decryptFormula` runs F9 with O2's interval.
   - G7 uses **one key block**.
   - G8: depth `≤ decDepth + 1` and fan-in 2.
   - `decDepth_le`'s settled constants are `(9, 2, 21)`, with no term linear in `ℓ` (G6B-F05; ruled Q-6B-F2 A). Is it
     a weakening of F10 rather than a restatement?
3. **Bootstrap, G9–G13, G18**, against BV14 Thm 2.14, Lemma 4.4, Def 2.13 and BV11 Thm 3.1, 3.2, Defs 3.5, 3.8.
   - G9 is in the key-switching form: `evk` under `t'`, decryptions under `s`, no hypothesis on `C₁, C₂`. Is it true
     with no noise hypothesis on the inputs?
   - The padding: fan-in 1 goes to `(a, a)` and fan-in 0 to `(G, G)`. Does `bootGate` compute `DAGGate.eval` of an
     `IsNAND` gate with 0, 1 and 2 arguments?
   - `bootNoise = 4^(decDepth+1)·2Nβ`.
   - G10/G12 cover every depth.
   - G12's `hsep` is the only separation hypothesis. Is the input separation implied, as it is not stated? L3 states
     both `hsep` and `hin`; is that redundant or needed?
   - G13 `bootNoise_le` gives `4^33·N^19·(ℓ+⌈log₂N⌉+3)^4·2β`: re-derive it.
   - G18 goes through N3–N4.
   - Compactness is shown by typing only (docstrings).
4. **Circular, G14–G15**, against GSW13 §3.2, AP14 §5.3, BV14 §2.5 and BV11 Defs 3.1, 3.8.
   - Is `WeakCircularSecure` per distinguisher (P6-Q15 A) non-trivial, and its docstring's reason accurate?
   - Is `fheView`'s evaluation key the circular one: bits of `s` under its own `pk`?
   - G15 is stated over the evk-dropped projection of `fheView`. Is it the transport of `distAdv_encrypt_le` and **not
     a restatement** (sweep N6)?
5. **Leveled, L1–L3**, against BV11 Thm 3.1 / Def 3.6 and BV14 Thm 2.14 (first part) / Thm 3.7.
   - The consecutive chain: `levelKey d` encrypts the bits of `s_d` (`d.castSucc`) under `pk_{d+1}`, `N·L` ciphertexts.
   - `literalCts` follows `litInput`'s order.
   - `levelGate` uses `levelKey (δ − 1)` at `depthAt δ`, and `0` off the chain.
   - L2: the output is under `s_{depth}`, with noise `max βin (bootNoise βk)`.
   - L3's public output level is `(Cc.toNANDForm hC).depth`, through N10's exact `layerNAND_depth`.
   - The P6-Q19 B paragraph, now with the [Gen09] citations (LE-g46; question C3).
6. **LeveledSecurity, L4–L5**, against AP14 §5.3, GSW13 §3.2 Lemma 1, BV14 Thm 2.14 / Thm 3.7 / §2.5 and BV11 Thm 3.1.
   - `levelHybrid h` zeroes the levels `≥ h`.
   - L4 compares `h = e+1` with `h = e` over `N` positions, through `hybridPlant`/`distAdv_multi_le_sum`.
   - Is it sound to plant `pk_{e+1}`? Phase 1's argument: `s_{e+1}` occurs only in level key `e+1`, which is already
     replaced.
   - L5's two-chain bound plus `challengeTerm` (W3).
   - `levelMsgs`' `Fin (N − 1 + 1)` cast is meaning-preserving.
7. **Ratio and PolyRatio, G16–G17**, against BV14 Thm 3.7 (worst-case analogue) and §3.4.
   - `RatioBounded`, and `ofFamily` with type-level Rule 10.
   - `pBoot` is explicit, with constant `2^70` (W1).
   - G16's factor 8, and G17's `pBoot·B < q` ⇒ `2·(ℓ·bootNoise) < ⌊q/2⌋` (re-derive, including `bootNoise = 0`).
   - Does `pBoot` really dominate through the `Family` bounds (`dimension_le`, `samples_le`, `residueBits`)?
8. **Asymptotic, A1–A3**, against GSW13 §3.2, BV11 Def 3.1, BV14 Thm 2.14 / Thm 3.7 and r3 §H5.16.
   - The quantifier structure of `ReductionEfficient`/`LeveledReductionEfficient`: domination, not construction, and the
     advice remark.
   - Is either hypothesis unsatisfiable, which would make A1/A3 vacuous?
   - W2's challenge reductions.
   - A1's width hypothesis `(n+1)ℓ + 2κ ≤ m`.
   - A1/A3 come from the unchanged `DLWEAssumption`.
   - The encodings and their `_length` readers.
   - A2 is reader-only.
9. **Definitions.** Every definition has a body; none contains `sorry`. Only `levelTerm` and `challengeTerm` are
   `noncomputable`, and `fheEval`/`leveledEval` are computable.
   - Phase 2's probe: **`sorryAx` is in exactly the 24 targets**, each tracing only itself.
   - `fheEvalCircuit`, `leveledEvalCircuit` and their `_eq` readers are standard now that 6a is proved.
   - Does any definition compute the wrong object?
10. **Readers** (`policy.md` §1): every public definition has a reader. Are the `rfl`/`Iff.rfl` readers exact? Is
    `neZero_columns` a sound instance with no diamond?
11. **The consumers.** Is each sketch a viable plan for its U12–U19 fill, naming the 6a/phase-5 lemmas and hosts H18
    (`evalWith`) and H19 (`runWith`) it uses? r3 §H7: "6b imports the 6a modules and restates none of them."

**C. Sources, citations, docstrings**
1. **The 140 anchors** (`checks/anchors.txt`): every `pNNN-bNNN` resolves in the ingest of its tag, 140/140. That is
   phase 1's 123 plus the 17 [Gen09] anchors of LE-g46 (20 `[Gen09` occurrences in all).
   - Does each anchor point at the passage that supports the claim?
   - Do the locators name the right results (G44-02)?
   - Is BV11 Lemma 4.5 cited as the brief's record point says?
2. **G6B-F03 and LE-6b2:** are the extra citations ([BV14, Def 2.12, §3.3], [Bar89, Thm 1], [GSW13, §3.2, Lemma 1],
   [BV11, Def 3.1], [BV14, §2.5]) attached to sub-facts only, and are the module sentences now accurate?
3. **The [Gen09] citations (LE-g46).** Check that they are correct. At staging the leveled docstrings still said "no
   ingested passage gives them … will be cited here once it is ingested", although the [Gen09] thesis passages were
   ingested on 2026-11-16 (DW-8, records `bdcadd85`, an ancestor of the 6b issue base). Seyoon ruled a docs-only fix,
   folded into LE-g46. The citations are now in `GSW/Leveled.lean` (module docstring, *Sources and reconstruction*, and
   `levelKey`), `LeveledSecurity.lean`, `PolyRatio.lean` and `Asymptotic.lean`, each with a [Gen09] entry under
   `## References` (`sources.zip` `references/gentry-2009-fhe-thesis.md`):
   - the key chain, [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003];
   - the reverse order, [Gen09, §4.1, p. 46, p056-b002]: Gentry encrypts `sk_i` under `pk_{i−1}` and evaluates down the
     index, so his level `i` is level `L − i` here and his `Enc(pk_{i−1}, sk_i)` is `levelKey (L − i)`;
   - the layered circuits, [Gen09, §4.1, p. 47, p057-b001];
   - correctness, [Gen09, Thm 4.2.1, p. 49, p059-b001] (statement only ingested; PolyRatio);
   - the hybrid, [Gen09, Thm 4.2.3 and its proof, pp. 50–51, p060-b001, p061-b001]: Game `k` is `H_{L−k}`, and the step
     `k → k + 1` plants `pk_k` (`pk_{e+1}` with `e = L − k − 1`), whose secret occurs only in encryptions already
     replaced, which is L4/L5's top-down order;
   - the deviations stated in `LeveledSecurity`: zeros instead of an unrelated fresh key's bits; a hybrid over the `N`
     positions instead of one challenge of Gentry's `ℓ`-fold scheme; steps reduced to DLWE (phase 5), not to the base
     scheme's semantic security; and phase 5's challenge step instead of Gentry's Game `d + 1`.

   Do the anchors point at the passages cited? Are the index correspondence, the game correspondence and the stated
   deviations right? Is anything still claimed "reconstructed" that Gen09 gives, or attributed to Gen09 that it does not
   give? The declaration-level "Reconstruction disclosed (module docstring)" pointers are kept, and no target docstring
   carries a [Gen09] tag: is that adequate under policy §2? This is a docstring-only change (comment-strip identity in
   `le-g46.md`), not a statement change.
4. **Sketches** (policy §3): does each target's `**Proof sketch.**` name its obligations, and does any rely on an unfold
   that Rule 10 forbids? Does G6's sketch now name `decrypt_eq_decode_dotProduct` and L4's `hybridPlant_eq` (LE-6b1)?

**D. The rulings.** Are W1, W2, W3, F1, F2, Q-6B-1 and Q-C1 applied as ruled? Is any of them unsound?
- W1: check `8·4^33·2 = 2^70` and r3's `q = 4y + 1` counterexample.
- W2: is the dominated challenge reduction the one L5's last step uses?

**E. Frozen files.**
- Only the 12 brief paths change.
- The facades change only by imports, contents and the GSW title and opening line.
- `BitEncoding.lean` changes by insertions only.
- No 6a or phase-5 file is touched, and no registry row or model is added.
- Was any frozen statement weakened through a new instance? `Parameters.neZero_columns` is a global instance on
  phase-5 `Parameters`.

**F. Landing-edit identity.**
- Is `680be9fa` exactly LE-6b1..3 as proposed (`checks/le-identity.txt`)?
- Is LE-6b1's new prose true at the head? Phase 2's scan says no other stale passage remains.
- Is LE-6b3 proof-only? decls2 against `75c683b2` is 0/0/0.
- **LE-g46** (`le-g46.diff.txt`, `le-g46.md`): is it exactly S1's proof change in `Asymptotic.lean` plus docstrings? The
  comment-stripped diff of `Asymptotic.lean` is the two `_length` proofs; `Leveled`, `LeveledSecurity` and `PolyRatio` are
  comment-strip identical to `680be9fa` with mutation controls caught; decls2 `680be9fa` → `7563734a` is 0/0/0.

**G. Seals, controls, admissions and axioms: recount from phase 2's evidence** (`evidence/`; `final-6b-r1/phase2.md`)
1. **Admissions** are 192 at the tip, 192 at R1 and **216** at R2. The difference is exactly 8 module lines and 24
   targets, **EXACT** (`admissions/`).
2. **Axioms:**
   - 175 constants: 153 DECL and 22 AUX. The 153 are the 136 new declarations, 4 `simps` lemmas, `bootGate.match_1` and
     BitEncoding's 12 pre-existing declarations, reconciled at staging.
   - `sorryAx` is in exactly the 24 targets.
   - **G6B-F10:** LE-6b3 removes `neZero_columns._proof_1` and drops `Quot.sound` from three constants.
3. **Seals:** strict A/B and coe A/B on 12 owners, 48 probes, **0 errors**, with requests per owner as in phase 2's table.
   Do the request-set differences from the delivery (+17, −4) come only from closure drift since `3e51b5f2`?
4. **Controls:**
   - `mkctl_g6b`: 10 rows, 70 + 70 sealed negatives each failing exactly once, ALL_OK.
   - **G6B-F11:** the delivery's 50 control files give 34 OK; the other 16 pass after 4 stale `IterateFind` names are
     pruned. Is the pruning confined to those names?
5. **Unfold scan:** 101 items, 0 foreign.
6. **G6B-F12:** root coe-A was not re-run (the root is unchanged and declares nothing, and both facades were sealed).
   Is that sufficient, or is it necessary evidence?
7. **Binding:** do R1, R2 and R2-g46 bind to `04ba2446`, `680be9fa` and `7563734a`? Tree `8b615e06` is merge-tree(tip,
   `5bd5ada5`); `~2` is `22349e8e`; `680be9fa` is `956fc086`; the head is `c56db4c4` = merge-tree(tip, `7563734a`).
   Exports match blob for blob (1599, 1608 and 1608 files).
8. **LE-g46's recheck** (`le-g46.md`, `le-g46-evidence.zip`): 8 modules rebuilt on R2, rc 0; the `sorry` warnings are
   exactly the 24 targets (EXACT); admissions 216; the two lemmas keep `[propext, Quot.sound]`; coe-A on the 4 edited
   owners 0 errors with request sets equal to R2's. Is it sufficient?

**H. Duplication** (policy §1; question 6's standard)
1. **The pre-dispatch sweep** (`dup-sweep.md`; `checks/dup-sweep.txt`) found one item, **S1**.
   - `encodeFheView_length` and `encodeLeveledView_length` (`GSW/Asymptotic.lean:123`, `:152`) rebuild inline the length
     of a flatten of constant-length blocks.
   - The public `TCSlib.Cryptography.length_flatten_map_const` (`Foundations/BitLists.lean:175`) is in their import
     closure. The `List.ofFn` form `Authentication.length_flatten_ofFn` (`Lamport.lean:123`) is not.
   - It was undisclosed and missed by phase 1.
   - **Its disposition (ledger row DL-61): fixed by LE-g46.** Seyoon ruled fix-now (Q-G46-S1 A); the fix is landing edit
     LE-g46 (`7563734a`), and this pack is re-pinned to that head. DL-61 reads "Repaid by LE-g46".
   - Grade S1 and its fix: do both proofs now go through `length_flatten_map_const` (with `List.ofFn_eq_map` and
     `List.length_finRange`), and is no other inline flatten-length derivation left in #377?
2. The notes N1–N11 of the sweep: `decDepth_le` vs F10, O2's `hsub`, `neZero_columns` (repaid by LE-6b3), the proved
   citations G11/L1, the reader-only G14/A2, G15's transport, the compositions, the thin wrappers, the case readers, the
   relatives from the brief's list, and the pre-existing flatten-length family. Do you agree that none of them is a
   duplicate needing a ruling?
3. Anything else: any declaration, or any inline step, of #376/#377 that is an undisclosed or unaccepted re-proof of a
   public TCSlib or Mathlib lemma.

**I. Disclosures to grade.** In a separate table, grade **G6B-F01 to G6B-F12** (`final-6b-r1/review.md`, phases 1 and
2) and sweep item **S1**: agree, or regrade with the reason. In particular grade F01 (closed by LE-6b1), F03, F04 (LE-6b3),
F05 (ruled), F06 (probe coverage), F10, F11 and F12.

## The replays (maintainer, 2026-11-18, on snapshot #10)

| | #376 (R1 = tip × O2) | #377 (R2 = R1 × statements, with LE-6b1..3; at `680be9fa`) |
|---|---|---|
| Range-diff | 1/1 `=` | 5/5 `=` + the LE commit |
| Tree | `8b615e06` | `~1` `22349e8e`, head `956fc086` |
| Rebuilt / reused | 19 / 1428 | 14 / 1442 |
| Rebuilt modules | rc 0, 0 `error:`/`error(`, 0 `sorry` | rc 0, 0 errors; the `sorry` warnings are exactly the 24 targets |
| State check | 1447/1447 OK | 1456/1456 OK |
| Admissions | 192 (+0) | **216** (+24 EXACT) |
| decls2 vs the tip | 5/0/0 | 136/0/0; the LE commit 0/0/0 |
| Axioms | 24 constants, standard | 175; `sorryAx` in exactly the 24 targets |
| Seals (strict A/B, coe A/B) | BitEncoding 9/9/9/9, 0 errors | 12 owners, 48 probes, 0 errors |
| Controls | the delivery's 5: ALL_OK | `mkctl_g6b` ALL_OK; the delivery's 50: 34 + 16 after pruning (F11) |
| Unfold scan | 54 items, 0 foreign | 101 items, 0 foreign |
| Lint | FAIL/WARN = the tip's (92/103) | the same; `style_lint` 0 |
| Snapshot #10 rehash | 0/0/0 | 0/0/0 (before, after R1, after R2, end) |

**R2-g46 (LE-g46 recheck at `7563734a`, `le-g46.md`):** a `cp -al` copy of R2; 8 modules rebuilt (the 4 edited files,
`GSW`, `Homomorphic`, `AdvancedEncryption`, the root), 1448 reused; rc 0, 0 errors; `sorry` warnings exactly the 24
targets (EXACT); state 1456/1456 OK; link count 1; only the 4 edited oleans differ from R2; admissions 216 (equal per
module); decls2 `680be9fa` → head 0/0/0; axioms of the two `_length` lemmas unchanged (`[propext, Quot.sound]`; closures
913/914 → 1009), census 174 constants (the auxiliary `encodeLeveledView_length._simp_1_1` is gone), `sorryAx` in exactly
the 24 targets; coe-A on the 4 edited owners 0 errors with request sets equal to R2's; lint unchanged; snapshot #10 and R2
rehash 0/0/0. Output map `65ca0263…`.

- **Recipe:** no `lake build` and no cache get. Modules ran through `scripts/lean_check_tree.sh`, and probes through
  `lean -DmaxErrors=0` without `-o`. Python ran as `python3 -I`, with one Lean process of this job at a time.
- **Integrity at staging:**
  - `evidence-SHA256SUMS` gives 2/2 OK.
  - The phase-1 ZIP's inner `SHA256SUMS` verifies 25/25, and the phase-2 ZIP's 598/598, from fresh extracts.
  - `owner-prereqs-6b/evidence-SHA256SUMS` gives 3/3.

## Known dispositions and slips (not findings)

- **"5 + 136".** The phase-1 decls2 line ("136 ADDED, five of them in `BitEncoding.lean`") counts O2 inside the 136, so
  #377 alone adds 131.
- **Phase-1 locator.** `review.md` (*O2*) puts `Fin.coe_sub_iff_lt` at `Mathlib/Data/Fin/Basic.lean:306`. It is core's
  (`Init/Data/Fin/Lemmas.lean:1089`), and Mathlib's line 306 is `Fin.intCast_val_sub_eq_sub_add_ite`. The disposition is
  unchanged (sweep N2).
- **Phase-1 line counts** are at `8f92fe7d`. After LE-6b1..3: Bootstrap 349, DecryptFormula 216, Leveled 284,
  PolyRatio 175. After LE-g46: Leveled 291, LeveledSecurity 362, PolyRatio 179, Asymptotic 338.
- **Phase-1 "inline proofs".** "The `_length` proofs use only library lemmas" is superseded by sweep S1 (fixed by
  LE-g46).
- **#376's REST `base.sha`** is `1a9a3295`, a records-only descendant of the cut tip `38123ccb` (Lean-equal).
- **#377's description** ended with "_Generated by [Claude Code](…)_" at staging. **Fixed** with the LE-g46 update: it
  now ends with the standard two attribution lines. Its "+2202/−1, counting O2" is right (58 + 2144).
- **The descriptions** (`pr376-description.md`, `pr377-description.md`) are the REST `.body` values at re-staging (#376
  updated 2026-11-18T06:41:38Z, unchanged; #377 07:36:30Z, with LE-g46).
- **The [Gen09] disclosure** was stale against the DW-8 ingest. Found at staging; **fixed by LE-g46** (docs only, on
  Seyoon's ruling). Question C3 now checks the citations.
- **Authorship:** the five picked worker commits are an external Claude worker's (a lead with sub-agents `seal` and `probe`,
  G6B-F08), delivered as patches and cherry-picked and signed by the maintainer. LE-6b1..3 and LE-g46 are the maintainer's.
- **No Lean, no `lake`, no seal or control was run for this staging.** `checks/` holds git-object reads and hashes; the
  rest is the recorded evidence. The only Lean runs behind this re-staging are LE-g46's recheck (`le-g46.md`).

## Merge interaction (maintainer merge conditions, not audit items)

`checks/lean-equality.txt`, `git merge-tree --write-tree`, git 2.43.0:
- **#376 × the records tip `9ae6b909`:** clean, Lean-equal to `8b615e06` (0 Lean paths differ). **#377 × the tip:** clean,
  Lean-equal to `c56db4c4`.
- **Order:** #376 first. On merge, adopt `olean-replay-6b-o2` (map `e1d210bf…`) as snapshot #11 if the merge's Lean
  equals `8b615e06`. Then #377, retargeted to `cryptography/pass-shelat-ch2-4`; adopt `olean-replay-6b-stmt-g46` (map
  `65ca0263…`, LE-g46) if the merge's Lean equals `c56db4c4`, and otherwise re-replay (`phase2.md` § *Merge and
  adoption*; `le-g46.md`). `olean-replay-6b-stmt` (`956fc086`) is superseded for #377.
- **Merge condition:** Gate 46 closed, with zero blockers and zero majors. S1 is fixed by LE-g46, so the adoption tree
  for #377 is the new head's (`olean-replay-6b-stmt-g46`, already re-replayed).

## Evidence files

- **`pack.md`** (this file), **`dispatch.md`** (the Codex prompt; records only) and **`dup-sweep.md`** (the pre-dispatch
  sweep).
- **`pr376.diff.txt`:** `git diff 38123ccb 04ba2446` (1 file, +58/−0).
- **`pr377.diff.txt`:** `git diff 04ba2446 7563734a` (11 files, +2144/−1).
- **`pr377-le.diff.txt`:** `git diff 75c683b2 680be9fa`, the LE-6b1..3 commit.
- **`le-g46.md`**, **`le-g46.diff.txt`** (`git diff 680be9fa 7563734a`) and **`le-g46-evidence.zip`** (inner
  `SHA256SUMS`): LE-g46 and its recheck.
- **`pr376-description.md`**, **`pr377-description.md`:** the PR bodies at re-staging.
- **`source-head.json`:** the pins; every commit of both PRs (parents, tree, author, committer, signature, files); and
  for each changed file its status, blob, SHA-256, line counts at base and head, maximum width, over-width, tabs and
  trailing spaces.
- **`sources.zip`:**
  - `head-7563734a/`: the 12 files at the re-pinned head;
  - `base-38123ccb/`: the 3 changed files at the base;
  - `context/`: the phase-5 GSW files, `LWE/`, Regev, `EnsembleSecurity` and `Encoding/` files and the 6a files the
    statements consume, at the records tip, plus the S1 relatives (`BitLists`, `Lamport`);
  - `references/`: the six ingests and Gen09 (`.md`, `.raw.md`).

  Its `README.md` gives every entry's SHA-256 and origin.
- **`verification.zip`:** `MANIFEST.md`, `POINTERS.md` and `SHA256SUMS`, which covers every other entry.
  - `checks/`: `series.txt`, `lean-equality.txt`, `le-identity.txt`, `targets.txt`, `anchors.txt`, `sizes.tsv`,
    `dup-sweep.txt` and `evidence-verify.txt`;
  - `tools/`: the staging scripts;
  - `evidence/`: the phase-1 and phase-2 evidence ZIPs, nested unchanged, `landing-edits-proposed.diff`,
    `evidence-SHA256SUMS`, and `le-g46/` (LE-g46's record, diff and evidence ZIP);
  - `records/`:
    - `review.md`, `phase2.md` and `checkpoint1-6b-review.md`;
    - the issued package (`README.md`, `brief.md`, `dispatch.md`, the addendum, `targets.txt`, `census.txt`,
      `pins.txt`, `SHA256SUMS`);
    - plan section r3, `rulings.md` and `policy.md`;
    - the Gate 45 findings (r1, r2) and the Gate 50 findings;
    - extracts of the decision log (from the 6b staging ruling on) and of the ledger (header, DL-54, DL-61);
  - `pr/`: the two PRs' REST fields.
- **`SHA256SUMS`:** the files of this directory other than `dispatch.md` and itself.

## Findings delivery

Return `gate46-gsw-6b-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP. The user
dispatches and merges.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Number the findings **G46-01, G46-02, …**. Grade G6B-F01 to G6B-F12 and S1 in a separate table. Report the audited
heads, the records pin, the counts by severity per PR, and one verdict per PR and overall:
- **CLEAR:** zero blockers and zero majors.
- **HOLD:** otherwise.

The gate closes at zero blockers and zero majors.

**Severities** (`workflow.md` §3)
- **blocker:** a later phase (the 6b fills) would build on a wrong statement. That means:
  - a false, vacuous or unusable target or definition;
  - a target too weak for its fill or its consumer;
  - a proof in #376 that does not establish its statement;
  - a scope violation.
- **major:** fixable but materially misleading:
  - a mis-stated source correspondence, or a fabricated tag or locator;
  - an undisclosed or unaccepted restatement or re-derivation of a public lemma;
  - a changed frozen file outside the brief's scope;
  - a definition that depends on an admitted target beyond a proof field;
  - necessary evidence that cannot be verified or does not bind to the audited commit.
- **minor:** documentation or API defects: an inaccurate formula docstring, deviation note, disclosure, sketch, citation
  or PR description, or a missing reader.
- **note:** anything else.
