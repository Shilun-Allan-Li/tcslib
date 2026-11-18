## ===== pack.md (this pack) =====

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
- **Records pin: `1404eff9d9d9f55f7e4687a87395dec70dbb791e`.** This is the commit that files this directory, `briefs/lattice-gsw/gates/46-gsw-6b/`.
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

## ===== dup-sweep.md (this pack) =====

# Gate 46 · pre-dispatch duplication sweep (GSW 6b: #376 O2 and #377 statements)

Run 2026-11-18 at staging, before dispatch (binding practice since Gate 50, lesson G50-05). Static only: no Lean, no
`lake`; git objects, `python3 -I` and grep. The raw output is `checks/dup-sweep.txt` in `verification.zip`
(`tools/dupsweep46.sh`); the import closures are from `tools/closure.py`.

**Result: one finding needs a ruling (S1). Everything else is a note with a disposition already on record.**

**Update at re-staging (2026-11-18): S1 is ruled and fixed.** Seyoon ruled option A (fix now). Landing edit LE-g46
(`7563734a8badba842223e0687c719b3b4692e9d2` on #377; `le-g46.md`) makes both proofs apply `length_flatten_map_const`
after `List.ofFn_eq_map` and `List.length_finRange`; DL-61 reads "Repaid by LE-g46". The sweep's greps were re-run at
the new head (`verification.zip` `checks/dup-sweep.txt`); apart from line numbers they differ only in the two proofs.
The text below is the sweep as written at staging, at `680be9fa` (line numbers there).

| Item | Kind | Disposition |
|---|---|---|
| **S1** | undisclosed inline re-derivation of a public TCSlib lemma (two proved readers in #377) | **ruling pending (Seyoon), question Q-G46-S1**; recorded today as ledger row **DL-61** (status open) |
| N1–N11 | notes: no duplicate, or a duplicate-shaped item already ruled or by design | none needed; listed for the auditor |

## Pins

- #376 `04ba2446f541c39dd02aefaa97a9eb31dbbda748` (O2); #377 `680be9fa45a9cf5deeb7a59820e8e86aaaa4f068`.
- Records tip at staging `dab31951abb5c892dc6279c229e49497ec95de10`. Its Lean equals the PR cut tip
  `38123ccbebef878cd25dd2d2761de1b40ba7e421` and snapshot #10's T `cf6a2266`.
- `main` `acea851c1dbafae140d481d91827dcf72ba31c74`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, Batteries `39260e31b7b3f7f05643da95242463b462dc05f1`, core
  Lean 4.25.0.

## What was swept

- **Inventory.** decls2, tip → #377 head (phase 2, `decls2/tip-vs-stmt.tsv`): **136 ADDED, 0 CHANGED, 0 REMOVED**.
  Of these, 5 are #376's (`decodeLo`, `decodeHi`, `decodeLo_eq`, `decodeHi_eq`, `decode_iff_mem_Ico`) and **131** are
  #377's. ("5 + 136" in the staging request counts O2 twice: the 136 already contain it.)
  - An independent count of added keyword lines gives the same 136: 9 `abbrev`, 41 `def`, 1 `instance`, 85 `theorem`.
  - There are **0 `private`** declarations.
  - `simps` adds 4 more names, `Parameters.ofFamily_lwe`/`_width` and `fheView_fst`/`_snd`.
- **By name.** All 135 short names were checked as declarations in `TCSlib/` and `audits/` at the records tip and at
  `main`, and in Mathlib and Batteries. The only hits are the unrelated namespaces phase 1 lists: `Coins` (PPT,
  `SecureComputation.Hybrid`, `ZeroKnowledge.Interaction`), `PublicKey` (RSA) and `select` (`Turing.Cfg.select`,
  `Randomness.Rejection.select`). Mathlib and Batteries give 0 hits.
- **By definition body.** Each new definition's body shape was grepped across TCSlib: `decomposeVec P (secretVector …)`,
  `vecMul (decryptColumn …) (gadget …)`, `mul P (gadget P - …)`, `evalWith (select …)`, `modSumInterval (fun …)`,
  `Fin.append cts …homNot`, `encodeMatrix P.width`, `encodeChallenge P.lwe P.width`, and the names `RatioBounded`,
  `ofFamily`, `ReductionEfficient`, `WeakCircular`, `hybridPlant (encrypt …)`. Nothing is found outside the new files.
  The new definitions reuse `encodeMatrix`, `encodeChallenge`, `homNot`, `hybridPlant`, phase-5 `reduction`/`encrypt`,
  6a `modSumInterval`, `evalWith`, `barrington`, `runWith`, `toNANDForm` and `layerNAND` as terms. They copy none of them.
- **By statement shape.** I read every target and reader statement against its nearest relatives: phase-5 GSW,
  `LWE/`, Regev, `EnsembleSecurity`, the 6a `Complexity/` layer and the brief's list of near-relatives.
- **Inline proofs.** I read every proof body at the head that is not `rfl`, `Iff.rfl` or `sorry` (section 3 of
  `dup-sweep.txt`): O2's `decode_iff_mem_Ico`; `neZero_columns` (after LE-6b3); the case readers of `bootGate` and
  `levelGate`; `literalCts_castAdd`/`_natAdd`; G11 and L1; and the four `_length` readers. Each one-step use of a library
  lemma is listed there.

The name scan and the body scan are kept separate from the statement-shape reading, as G50-05 asks. S1 was found by the
shape reading, not by either scan.

## S1 · ruling needed

**What.** Two readers in #377 rebuild "a flatten of constant-length blocks has length count × block" inline, and the
docstrings do not say so:
- `GSW.encodeFheView_length` (`AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean:123`);
- `GSW.encodeLeveledView_length` (`:152`).

Both proofs run `List.length_flatten`, `← List.ofFn_comp'`, `List.ofFn_const` and `List.sum_replicate_nat` for each
`(List.ofFn fun i => encodeCiphertext P (…)).flatten` block (`:128–130`, `:157–160`).

**The public lemmas.**
- **`TCSlib.Cryptography.length_flatten_map_const`** (`Cryptography/Foundations/BitLists.lean:175`):
  `(l.map g).flatten.length = l.length * k` when every `g x` has length `k`.
  - It is proved by the same chain, `List.length_flatten`, `map_const'`, `sum_replicate_nat`.
  - `Foundations.BitLists` **is in the import closure** of `GSW/Asymptotic` (134 modules).
  - It applies after Mathlib's `List.ofFn_eq_map` (`Mathlib/Data/List/FinRange.lean:87`) and core's
    `List.length_finRange`.
- **`TCSlib.Cryptography.Authentication.length_flatten_ofFn`** (`Authentication/Signatures/Lamport.lean:123`): the exact
  `List.ofFn` form for `List Bool` blocks, `(List.ofFn g).flatten.length = q * B`. It is **not** in the closure.
- `TCSlib.Cryptography.length_flatten_ofFn` (`Encryption/PublicKey/HybridMachine.lean:105`, in the closure) and
  `CommitmentLemmas.length_flatten_ofFn` (`ZeroKnowledge/CommitmentLemmas.lean:211`) state only the
  `List.ofFn (f i)`-block case, so they do not apply to `encodeCiphertext` blocks.
- Core, Mathlib and Batteries have no `flatten`-of-`ofFn` length lemma (section 4a).

**Grade.** Under the dispatched standard, an inline re-derivation of a public lemma is a re-proof:
- Gate 50 regraded GF-F03 to **major** for rebuilding `Finset.sum_le_card_nsmul` from `sum_le_sum` and `sum_const`;
- see also G48-01 and GF-F01.

These two proofs rebuild a public lemma of the closure from the same core steps, and it is not disclosed. Unless
Seyoon rules it accepted, Codex would grade it like GF-F03.

Phase 1 (`final-6b-r1/review.md`, *Inline proofs*) read these proofs and wrote "The `_length` proofs use only library
lemmas". That is the G50-05 pattern: the review looked at names and bodies, not at the statement shape.

**Question Q-G46-S1 (Seyoon). Not decided here.** *(Ruled 2026-11-18: A, fix now; done by LE-g46.)*
- **A. Fix now** with a proof-only landing edit **LE-g46** on #377. This follows the Gate 50 sweep ruling (fix now,
  LE-g50) and G48-01 (repaid before round 2).
  - It touches `GSW/Asymptotic.lean` only and changes both proofs to go through `length_flatten_map_const` (with
    `List.ofFn_eq_map`, `List.length_finRange`). The docstrings name the lemma.
  - Checks: comment-strip identity outside the two proofs; a re-replay of `GSW.Asymptotic`, `GSW`, `Homomorphic`,
    `AdvancedEncryption` and `TCSlib` on R2; the coe-A seal of `GSW/Asymptotic`; decls2 0/0/0.
  - It needs one Lean slot. #377's head changes, so the pack is re-pinned to the new head before dispatch.
- **B. Accept as debt.** Ledger row DL-61 becomes Accepted, and the pack discloses it as accepted debt (G44-01: a
  recorded acceptance plus a ledger row with its repayment).
  - Repayment: the U19 fill, or Cleanup Stage 2 together with the pre-existing family in N11.
  - No Lean is needed now.

**Recorded today:** `briefs/pass-shelat-ch5-8/duplication-ledger.md` row **DL-61**, status *Open: ruling pending*
(now *Repaid by LE-g46*). The
lattice rows (DL-50, DL-54) live in that ledger, and there is no separate lattice ledger. The row is updated with the
ruling.

## Notes (no ruling needed)

- **N1 · `decDepth_le` (G8) against F10 `modSumDepth_le`** (`FormulaArith/ModSum.lean:365`). F10 bounds
  `modSumDepth M q` by `9⌈log₂ M⌉ + 2⌈log₂(⌈log₂ q⌉ + ⌈log₂ M⌉ + 3)⌉ + 21`, and G8 bounds `decDepth P` (= `modSumDepth N q`,
  `decDepth_eq`) with `ℓ` in place of `⌈log₂ q⌉`.
  - It is a weakening with a different right-hand side, not a restatement.
  - Disclosed (G6B-F05) and **ruled** Q-6B-F2 A (it stays an admitted target; the U13 fill is about 3 lines).
- **N2 · O2's `hsub`** (`LWE/BitEncoding.lean:157–166`), the two-case value of `(v − ⌊q/2⌋).val`.
  - The first case uses Mathlib's `ZMod.val_sub`.
  - The second case is the `ZMod` analogue of core's `Fin.coe_sub_iff_lt` (`Init/Data/Fin/Lemmas.lean:1089`), stated for
    `Fin`. Mathlib's `Fin.intCast_val_sub_eq_sub_add_ite` (`Mathlib/Data/Fin/Basic.lean:306`) is its ℤ-cast form.
  - There is no `ZMod` lemma for an abstract modulus (`Mathlib/Data/ZMod/`). Using the `Fin` one would need a case split
    `q = n + 1` through `ZMod`'s definition.
  - The phase-1 disposition (no lemma, info) stands. Phase 1 put `Fin.coe_sub_iff_lt` at `Mathlib/Data/Fin/Basic.lean:306`;
    it is in core, and Mathlib's line 306 is `intCast_val_sub_eq_sub_add_ite` (pack, known slips).
  - O2's other step goes through `ZMod.valMinAbs_natAbs_eq_min`, the checkpoint-1 fix of G6B-C1-F01.
- **N3 · `Parameters.neZero_columns`** (`GSW/DecryptFormula.lean:65`). The old case contradiction re-derived core
  `Nat.one_lt_two_pow_iff` (G6B-F04). **Repaid** by LE-6b3 (ruled Q-6B-F1 A), which compiles. No `NeZero P.columns` or
  `width_pos` lemma exists elsewhere (section 4c).
- **N4 · G11 `encrypts_evalKey` and L1 `encrypts_levelKey`.** These are proved citations of phase-5 `encrypts_encrypt`
  (`Scheme.lean:182`) and `encrypts_keygen_encrypt` (`:207`) through the file's own `evalKey_eq`/`levelKey_eq`. The brief
  allows this (the LE-g45 `const_eval` precedent); they are never admitted, and they are disclosed in REPORT §4.
- **N5 · G14 and A2** are reader-only: `weakCircularSecure_iff` and `weakCircularSecureFamily_iff`, ruled Q-6B-1 A.
  No `distAdv_fheView_le` or `fheView_negligible` exists.
- **N6 · G15 `distAdv_fheView_noEvk_le`** has the right-hand side of phase-5 `distAdv_encrypt_le` (`Security.lean:248`).
  - Its left-hand side is a view over `Seeds P χ`, which has an extra evaluation-key coin component, so it is the
    transport of that theorem along the coin regrouping (`acceptProb_comp_equiv`, `acceptProb_fst`/`uprob_fst`), not a
    restatement.
  - This is the brief's design: over `realView` it would restate the theorem (G45-01).
- **N7 · Compositions.**
  - G18 is G10 through N3–N4;
  - G17 (split) is G12/L3 with G16;
  - G3 is C14/C16 with G2;
  - G6 is `decrypt_eq_decode_dotProduct` (#368), F9 and O2.

  Each is a theorem to be proved from public lemmas, not a restatement of one.
- **N8 · Thin wrappers.** `encodeCiphertext` (= `encodeMatrix P.width`), `keyBits`, `decConstants`, `homEvalPBP`,
  `literalCts` and the seven type abbreviations are definitions over existing terms, each with its reader. No existing
  declaration has the same body (section 4d).
- **N9 · Case readers.** `bootGate_of_args_eq_*` and `levelGate_of_lt`/`_of_le` unfold the file's own definitions.
  `literalCts_castAdd`/`_natAdd` are readers through core `Fin.append_left`/`_right`.
- **N10 · Other relatives** from the brief's list are confirmed different: `eval_encrypts`/`decrypt_keygen_eval`
  (phase-5 leveled `eval`), `homGate`, `Encrypts.nand`, `vecMul_secretVector_augmented`, `gadget_mulVec_decomposeVec`,
  `decode_codepoint_add`. The three `negligible_polyExpr_mul` copies are cited in sketches; no fourth is added.
- **N11 · A pre-existing family of flatten-length lemmas** (not 6b's; context for S1 option B). The same fact is stated
  at least six times in TCSlib:
  - `length_flatten_ofFn` in Lamport, HybridMachine and CommitmentLemmas;
  - BitLists' `length_flatten_map_const`/`_map_range`;
  - `Programs/Util/List.lean`'s `length_flatMap_finRange`/`length_flatMap_range`;
  - `PSubsetPPolyTableau.length_flatMap_const`;
  - EnsemblesLemmas' `length_flatMap_range`.

  None is in the ledger. Whether to consolidate them is a Cleanup Stage 2 question for Seyoon, not a 6b one.

## Not swept

- 6a and #368 content: audited at Gates 45 and 50, merged.
- Proof sketches as plans: they name the lemmas a fill will use and prove nothing.
- Duplication inside the delivery's evidence tools.

## ===== briefs/lattice-gsw/phase6/final-6b-r1/review.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

# gsw-6b-statements · final r1 · phase-1 (static) maintainer review

**Interim verdict: ACCEPT WITH LANDING EDITS, pending phase 2 and the rulings below.** There is no blocker and no
major. There are three minors, all docstring-only and closed by the proposed landing edits LE-6b1 and LE-6b2, and seven
infos. Three questions come from the worker's own r3 deviations (G6B-W1–W3); I recommend accepting all three.

The delivery does what the brief and the checkpoint-1 feedback ask:
- **Checkpoint fixes.** All four are done. O2 now rewrites with Mathlib's `ZMod.valMinAbs_natAbs_eq_min` and has no
  `habs`. G15's sketch names `uprob_fst`. The census lists `decrypt_eq_decode_dotProduct` as MISSING beside
  `hybridPlant`. The admissions comparison now covers all 1,452 modules, including the new ones.
- **Reproduction and integrity.** Both series reproduce hash for hash on the issued base, and `src/` and `src-o2/` are
  byte-equal to the heads. Both manifests verify, with exact path sets.
- **Statements.** decls2 gives 136 ADDED / 0 / 0, five of them in `BitEncoding.lean` (O2).
  - There are exactly 24 admitted targets (23 r3 rows, with G17 split), each with a formula docstring, a source tag and
    a `**Proof sketch.**`.
  - G11 and L1 are proved citations. G14 and A2 are reader-only. G15 is stated over `fheView`'s projection.
- **Admissions.** 313 = 289 + 24 in 63 = 55 + 8 modules, name for name, recounted from the bound build logs.
- **Duplication.** No new declaration restates or re-derives a public lemma by name or by shape. I checked against
  `TCSlib/` at the base, the records tip, #366 and #368, and Mathlib. There are no private declarations at all.

I ran no Lean. Phase 2 replays the landing branches on the olean snapshot current at landing.

## What was reviewed

- **Delivery.** `inbox/fills/gsw-6b-statements/` on `exchange/pass-shelat-ch5-8`.
  - Final: `3b340824dde77433b2135a3c8d20c7ed194cf18c` ("stmt gsw-6b: final", 2026-11-17 23:48 UTC). Its parent is
    `f01fae49fe6c987696b310395052e2f7a637302d` (another job's commit).
  - Checkpoint 1 was `1e0647b99de8ee4d11722b5bad862fe40837a2ce`.
  - The final commit is unsigned (`gpgsig` 0) and touches only that path. No later exchange commit touches it (the
    exchange tip at review is `c05e1cb9fdb85f4e9d9b90339d00eeb562639a0c`).
  - I extracted the folder with `git archive` into an empty scratch directory. It holds 2,688 files: `REPORT.md`
    (462 lines), `patches/o2/` (1 patch), `patches/stmt/` (5 patches), each with `COMMITS.tsv`, `src/` (12 files),
    `src-o2/` (1 file), and `evidence/` (2,664 files plus its manifest).
- **Heads (REPORT §0).**
  - O2 `owner/o2-decode`: `5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd`.
  - Statements `stmt/gsw-6b`: `7a8145468202f908f6a1e41638fc793c2313b850` (Branching, DecryptFormula),
    `dd9f00f484a7e89390ce8a68b19cac773fb6f9b1` (Bootstrap, Circular), `1378740f5f516f8047fd9cf83e56414091dde8af`
    (Leveled, LeveledSecurity), `5c8f81cdd83aca13d737cea3fd0d03fb37d9f9b8` (Ratio, PolyRatio, Asymptotic) and
    **`8f92fe7d53967bc488a4075fb38210e7d40b9031`** (facades).
  - Base `3e51b5f28900db6190f1eb2e6d207d27ee15d541`, unchanged.
- **Contract.** `issued-6b-r1/` (brief, addendum, `targets.txt`, `census.txt`, `pins.txt`, `base-sorries.txt`,
  `closures.txt`, `order.txt`, `tools/`), plan section r3, `rulings.md` (P6-Q1..Q19 and the Q19 refinement), Q-6B-1 A,
  `checkpoint1-6b-review.md` and the feedback relayed on 2026-11-17 (decision log).
- **Moved since the base.**
  - The records tip is `5ed4ca865597d56e59e079eb7ae90c21b9b0617b`; #347 and #355 have merged into it.
  - #366 (`land/gsw-6a-fills` `597fb736e545706a058cc212243a13f6dadfeceb`) and #368 (`land/gsw-6b-owner-prereqs`
    `1953898b18a33ab2cd533820c5754a1aacffeb44`) are open drafts. Gate 50 closed CLEAR on both.

## Checks

| Check | Result |
|---|---|
| **Integrity** | Top `SHA256SUMS`: 2,687/2,687 OK. `evidence/SHA256SUMS`: 2,664/2,664 OK. Both path sets equal their manifests exactly: no missing or extra file, and no `./`. The diff of the final commit touches only `inbox/fills/gsw-6b-statements/`. |
| **Base** | `issued-6b-r1/tools/mkbase.sh`, run in a scratch repository whose object store points at the records clone, prints `STEP1 04947bcf… tree 8eca9617…` and `BASE 3e51b5f28900db6190f1eb2e6d207d27ee15d541 tree b69a66a385ca3439d56af1d6b9791b5847984fde`. |
| **Reproduction** | Sparse worktree, detached at the base. `git am` per patch, with each row's committer name, email and date from `COMMITS.tsv` and `commit.gpgsign=false`. All six hashes reproduce in order (`5bd5ada5…`, `7a814546…`, `dd9f00f4…`, `1378740f…`, `5c8f81cd…`, `8f92fe7d…`), none signed. `src/` is 12/12 byte-equal to `8f92fe7d`, and `src-o2/` is byte-equal to `5bd5ada5`. `git diff --stat` base..head lists exactly the 9 new files and the 3 changed ones (+2,170/−1; the −1 is the GSW facade's title line). |
| **Checkpoint fixes** | **F01:** `decode_iff_mem_Ico` rewrites both distances with `ZMod.valMinAbs_natAbs_eq_min`, and `habs` is gone. The sketch names the lemma. **F02:** G15's sketch (`Circular.lean:131–136`) names `acceptProb_def`, `acceptProb_comp_equiv` and `uprob_fst`. **F03:** G6's sketch (`DecryptFormula.lean:158–162`) points at the owner-side `decrypt_eq_decode_dotProduct`, and the census lists it as MISSING beside `hybridPlant` (`census/reader-census.md:121–160`). `Scheme.lean` is untouched. **F04:** the admissions comparison covers all 1,452 modules (see *Admissions*). Against checkpoint 1's `src/`, the four checkpoint files differ only in the two sketch paragraphs. |
| **O2** | The diff base → `5bd5ada5` is insertions only: two docstring entries, plus `decodeLo`, `decodeHi`, `decodeLo_eq`, `decodeHi_eq` (`rfl`) and `decode_iff_mem_Ico` (`BitEncoding.lean:118–172`), proved, with no `sorry`. decls2 at the O2 head: exactly 5 ADDED. The headers match r3 §H5.8 and the brief, every declaration says "Glue", and the theorem has a sketch. The issued `o2check.py` (re-run): moduli 2..2000, 0 mismatches. The remaining inline step `hsub` (the two-case value of `v − ⌊q/2⌋`) has no `ZMod` lemma in Mathlib. My grep of `Mathlib/Data/ZMod/` finds only `ZMod.val_sub` for the first case; the two-case facts exist only for `Fin` (`Fin.coe_sub_iff_lt`, `Mathlib/Data/Fin/Basic.lean:306`). Nothing else in the file changes. |
| **decls2** (pinned `fa81981a…`) | Base → `8f92fe7d` over the 12 files: **136 ADDED, 0 CHANGED, 0 REMOVED**. This is line-identical to the delivered `decls2-final-r2.txt`. The `simps` projections `fheView_fst`/`_snd` and `Parameters.ofFamily_lwe`/`_width` bring the new names to 140. |
| **Targets** | My comment-stripped scan finds 24 `sorry`, exactly one in each target: Branching 3, DecryptFormula 6, Bootstrap 5, Circular 1, Leveled 2, LeveledSecurity 2, PolyRatio 3, Asymptotic 2. There are none in `Ratio.lean`, `BitEncoding.lean` or the facades. Each of the 24 has a docstring with the formula, a `[TAG, loc, anchor]` tag and a `**Proof sketch.**`, checked by script. The row map (REPORT §4) is complete: **G11** `encrypts_evalKey` and **L1** `encrypts_levelKey` are proved citations (`rw [evalKey_eq]`/`rw [levelKey_eq, evalKey_eq]`, then `encrypts_encrypt`/`encrypts_keygen_encrypt`). **G14** and **A2** are reader-only (`weakCircularSecure_iff`, `weakCircularSecureFamily_iff`, `Iff.rfl`), and no `distAdv_fheView_le` or `fheView_negligible` exists. **G15** is stated over `fun r => ((fheView P χ μ r).1, (fheView P χ μ r).2.2)`. |
| **Definitions and readers** | Every `def`/`abbrev` has its reader, by script: `_eq` (rfl), `_iff` (Iff.rfl), the case readers of `bootGate` (3) and `levelGate` (2), `literalCts_castAdd`/`_natAdd`, `_length` for the four encodings, and non-simp `simps` for `fheView` and `Parameters.ofFamily`. The computable definitions are not `noncomputable`. Only `levelTerm` and `challengeTerm` (real-valued) are. |
| **Statement fidelity** | I read all nine files against r3 §H5.9–§H5.16 and the brief. REPORT §5 lists 22 deviations, all of them disclosed. Beyond checkpoint 1 (which covered G1–G15, G18): **L1–L3** match r3 §H5.13. `levelKey` encrypts `keyBits (ss d.castSucc)` under `pks d.succ`, and L3's output level `(Cc.toNANDForm hC).depth` is right because `layerNAND_depth` (N10) preserves depth exactly. **L4** is true as stated. With `hybridPlant`'s order (positions `< j` encrypt `0`, `j` planted, `> j` key bits), the gap at `j` is `adv(b = true) + adv(b = false) + 2·N·ε_LHL`. The reduction may plant `pk_{e+1}` because `s_{e+1}` occurs only in the level key `e + 1`, which `H_{e+1}` has already replaced; level keys below `e` use `pk_{e'+1}` with `e' + 1 ≤ e`. **L5:** the two-chain bound is right. `H_0(μ)` is `challengeDist` on phase 5's `realView`, so `challengeTerm` is exactly `distAdv_encrypt_le`'s right-hand side. **G16/G17:** `8·4^33·2 = 2^70` checks. With `8y ≤ pBoot·B < q`, `q ≥ 8y + 1 ≥ 4y + 2` for `y ≥ 1`, which gives `2y < ⌊q/2⌋`. With r3's `4` it fails at `q = 4y + 1` (G6B-W1). **A1/A3** match r3 §H5.16, with the challenge reductions added to (A4) (G6B-W2). |
| **Sources** | No `[Gen09]`. The P6-Q19 B disclosure is in the module docstrings of Leveled, LeveledSecurity, PolyRatio and Asymptotic, and each leveled declaration refers to it. Every `pNNN-bNNN` anchor in the 9 new files exists in its tag's ingest at the base: 123 checked, 0 missing (script `anchors.py`). But see G6B-F03. |
| **Hygiene** | No `native_decide`, `admit`, `axiom`, `@[simp]`, `attribute`, `show`, `change` or `delta`. The only `@[simps …]` carry `isSimp := false`. There is no `private` declaration. The only `unfold`s are of the file's own `bootGate` (×3) and `levelGate` (×2), in their case readers. Every name passed to `rw`/`simp only` is a lemma or the file's own reader. No micro sign, tab or trailing space. |
| **Widths and sizes** | Maximum width 99. Lines: Branching 179, DecryptFormula 220, Bootstrap 351, Circular 146, Leveled 283, LeveledSecurity 351, PolyRatio 174, Asymptotic 324, Ratio 59, BitEncoding 200, facades 57 and 40. With r3 §H7's upper fill estimates the largest files reach Bootstrap 791, LeveledSecurity 721 and Asymptotic 604. All stay under 1,000; these three are over the 600 target (G6B-F07). |
| **Lint** | `style_lint` (base blob) on the 12 files: 0 findings. `campaign_style_lint TCSlib/Cryptography --check8b` on sparse base and head checkouts: **92 FAIL / 104 WARN** over 529 and 538 files, with identical FAIL/WARN line sets. |
| **Clash** | The 135 new short names, grepped as declarations in `TCSlib/` and `audits/` at the base, the tip, #366 and #368, hit only unrelated namespaces: `Coins` (`PPT`, `SecureComputation.Hybrid`, `ZeroKnowledge.Interaction`), `PublicKey` (`RSA`) and `select` (`Turing.Cfg.select`, `Randomness.Rejection.select`). Since the base, the tip and #366/#368 add 87 declarations and change or remove none (decls2 base → tip×#366×#368). Their short names meet a 6b token only once, the intended `decrypt_eq_decode_dotProduct` in G6's docstring. All 129 backticked TCSlib names of the 6b docstrings that are declared at the base are still declared at that merge. |

## Evidence recount (from the raw logs)

- **Build binding.** Every module of `root-final/summary.txt` has its log at the stated run, with rc 0 and 0 errors in
  both forms, and its recorded source SHA-256 equals the blob at `8f92fe7d`: 1,452/1,452. The runs are the bootstrap at
  the base (270 modules), the root at the pre-review head `a855e111` (1,154) and `sweep-final-r2` at `8f92fe7d` (28).
  - **Staleness check** (`stale.py`). 12 modules have a source that differs between their earlier build and the
    final head: the 9 new modules, `BitEncoding` and the two facades.
  - No module bound to an earlier run has any of them in its import closure at the final head.
  - The rebuild set that requires is exactly the 28 of `sweep-final-r2`.
  - `a855e111` itself is not delivered. The check therefore uses the root run's recorded source hashes, and the base
    blobs for prefix modules.
- **Admissions** (`admit.py`). I took the `sorry` warnings of the 1,452 bound logs, mapped each to the declaration name
  at its position in the final source, and compared against `base-sorries.txt` plus the 24 targets: **313 in 63, 0
  differing modules.** At the O2 head: 289 in 55 (worker's graph scan; O2 adds no `sorry`).
- **Axioms** (`AxiomProbe-r2.log`). 176 constants (153 declarations and 23 auxiliaries). `sorryAx` reaches exactly
  28 of them:
  - the 24 targets;
  - `fheEvalCircuit` and `fheEvalCircuit_eq`, through N2 `nandGadget_correct` only;
  - `leveledEvalCircuit` and `leveledEvalCircuit_eq`, through N2, N12 `layerGates_acyclic` and N13 `layerOutput_lt`
    only.

  This is exactly the brief's prediction. There are no other axioms, and O2's constants are standard. At a landing
  that contains #366 all 6a targets are proved, so phase 2 expects `sorryAx` in the 24 targets only.
- **Seals** (`seals.py` over `rule10/r2/*/seal/run-*/mods/*.log`). At the final head, over 11 owners (the 9 new
  modules and the 2 facades), every variant has 0 errors in both forms, one `SEAL-END` per log and
  `requested = verified` at install and EOF:
  - A: 10,069 requests;
  - B: 10,075;
  - coe-A: 10,059;
  - coe-B: 10,065.

  `BitEncoding` has 9/9/9/9 requests at both the O2 head and the final head, also with 0 errors. The seal source hashes
  equal the heads' blobs, and the per-owner counts equal REPORT §9.
- **Controls.** Final: 45 rows, 9 owners × (unsealed negative + strict and coe negative and positive). `BitEncoding`:
  5 rows at each head. `ALL_OK` holds. In the raw logs every sealed negative control has exactly 1 error and every
  other control has 0.
- **Probes** (P1–P8). No `native_decide`.
  - P3 (O2): 62 kernel `decide` theorems for `2 ≤ q ≤ 63` with standard axioms, plus `#eval` to 2,000. The negative
    control is refuted.
  - P7: the constants hold (1,746 and 6,984 grid checks, 0 violations; `decDepth` grows by about 7–11 per doubling
    of `ℓ`).
  - P8: elaborates.
  - Partial runs are disclosed (G6B-F06).

## Duplication (policy §1; G44-01, G45-01, G48-01, GF-F01–F03, BS-F02, Gate 50 U1–U3)

I searched by name (all 135 short names, see *Clash*) and by shape, at four revisions: the base, the records tip,
#366 and #368, and in Mathlib `029db123` and core.

**Definitions.**
- **Type abbreviations** (`PublicKey`, `Secret`, `Coins`, `KeySeed`, `FheView`, `Seeds`, `LevelCoins`, `LeveledSeeds`,
  `LeveledView`). Phase 5 and Regev name none of these types: Regev's `keygen` spells its seed type inline, and
  `Regev/Experiments.lean:136` has only a local `let`. LWE has no challenge-type abbreviation.
- **`Family.RatioBounded`.** No ratio predicate exists. The only `modulus ≤ …eval…` is the `Family` field
  `modulus_le_pow`.
- **`Parameters.ofFamily`.** Nothing maps a family to GSW parameters.
- **Encodings.** They are thin wrappers over `Encoding.Modular.encodeMatrix` and `LWE.encodeChallenge`, and there is
  no GSW encoding.
- **`WeakCircularSecure`/`Family`.** There is no circular-security predicate anywhere.
- **`ReductionEfficient`/`Leveled…`.** No GSW asymptotic statement exists. `DLWEAssumption` is used only in
  `LWE/Assumption`, `SampleSchedules`, `Pseudorandom/Generators/LWE/Basic` and `Lossy/Experiments`.
- **The hybrid layer** (`levelHybrid`, `levelMsgs`, `levelAssemble`, `levelReduction`, `levelTerm`, `challengeDist`,
  `challengeTerm`). It is built from the public `hybridPlant`, phase-5 `reduction` and `encrypt` as terms, with no
  local hybrid lemma.
- **`levelGate`** is a `dite` over `bootGate`, and **`literalCts`** is `Fin.append` with phase-5 `homNot`, which is
  reused, not copied.

**Targets.** None is an exact restatement.
- **A1** has no phase-5 counterpart: phase 5 is concrete only (`distAdv_encrypt_le_of_width`).
- **G17** composes G12/L3 with G16 under different hypotheses.
- **G18** is G10 composed with N3–N4.
- **`decDepth_le`** is a *weakening* of F10's `modSumDepth_le`: `ℓ` replaces `⌈log₂ q⌉` behind `decDepth`.
  `targets.txt` makes it a target, and the worker discloses it (G6B-F05, info).
- The near-relatives in the brief's list are confirmed different: `eval_encrypts`/`decrypt_keygen_eval`, `homGate`,
  `Encrypts.nand`, `vecMul_secretVector_augmented`, `gadget_mulVec_decomposeVec`, `decode_codepoint_add`. The three
  `polyExpr_mul` copies are cited, not a fourth added.

**Inline proofs.**
- **O2.** `hsub` has no `ZMod` lemma (see *O2*); `hcast` is a cast identity; `hh : q/2 < q` is one `omega`.
- **`Parameters.neZero_columns`** derives `P.width ≠ 0` from `2 ≤ q ≤ 2^ℓ` by `rw [h, pow_zero] at hle; omega`. This
  is core's `Nat.one_lt_two_pow_iff` (`1 < 2 ^ n ↔ n ≠ 0`, `Init/Data/Nat/Lemmas.lean:1123`), used backwards. It is a
  two-line case contradiction and was present at checkpoint 1. I grade it info, borderline like Gate 50's U3, with an
  optional proof-only LE-6b3 (G6B-F04).
- The `_length` proofs use only library lemmas (`encodeMatrix_length`, `encodeChallenge_length`,
  `List.length_flatten`, `List.ofFn_const`, `List.sum_replicate_nat`).

**Cross-file copies.** There are none: no `private` declaration exists in any of the 12 files.

## Merge interaction and landing shape

- **`git merge-tree --write-tree`** is clean (rc 0) for each pair:

  | With | O2 head | stmt head |
  |---|---|---|
  | tip `5ed4ca86` | tree `293fd00a` | tree `1d9fd4d5` |
  | #366 `597fb736` | tree `ceca9f2e` | tree `7c66ca47` |
  | #368 `1953898b` | tree `97c0f35b` | tree `40aa06d2` |

  The chain tip × #366 × #368 × O2 × stmt is also clean (scratch commits; final tree `35574eb6`).
- **Shared paths.** None. Against their merge base `036d8239`, #366, #368 and the tip touch none of the 12 delivery
  paths.
- **Semantic interaction.**
  - #368 adds `decrypt_eq_decode_dotProduct`, character-equal to the census proposal, and the `hybridPlant` reader,
    named `hybridPlant_eq` where the census proposed `hybridPlant_apply`. Both fill prerequisites are therefore met
    once #368 merges.
  - #366 proves N2, N12 and N13, so `fheEvalCircuit` and `leveledEvalCircuit` lose `sorryAx`. Three 6b docstrings
    then become stale (G6B-F01; LE-6b1).
  - Admissions expected at landing: 192 (tip × #366 × #368) + 24 = **216**.
- **Proposed landing.** It waits for #366 and #368 to merge (base on that tip).
  1. **PR O2** `land/gsw-6b-o2`: the O2 commit replayed on the tip. It touches `BitEncoding.lean` only (+58/−0).
  2. **Statement PR** `land/gsw-6b-statements`, stacked on PR O2: the five statement commits, then one landing-edit
     commit with LE-6b1 and LE-6b2 (and LE-6b3 if ruled and if it compiles).
  - Phase 2 then replays both on the snapshot current at landing:
    - the 18 `DOWN` modules, the 9 new modules, the facades and the root, all rc 0;
    - admissions +0 at O2 and +24 at the statements;
    - axioms: `sorryAx` only in the 24 targets;
    - seals and controls with no new failures;
    - decls2 136/0/0 plus LE-6b3's no-op on headers;
    - lint unchanged.
  - Gate 46 then audits both PRs.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| G6B-F01 | minor (stale prose at landing; the G50-01/G50-02 pattern) | Once #366 and #368 merge, which the landing requires, three docstring passages become stale. (a) G6's sketch (`DecryptFormula.lean:158–162`) calls `decrypt_eq_decode_dotProduct` "**MISSING** at the base", but #368 adds it with the identical statement. (b) The `fheEvalCircuit` and `leveledEvalCircuit` docstrings (`Bootstrap.lean:193–194`, `Leveled.lean:174–175`) say "While 6a's N2 (N12, N13) is admitted, `sorryAx` reaches this definition…", but #366 proves them. (c) L4's sketch (`LeveledSecurity.lean:311`) says "`hybridPlant`'s planted position", where #368 now provides the reader `hybridPlant_eq`. | **LE-6b1** (docstrings, −10/+6; landing after #366/#368). |
| G6B-F02 | minor (docstring accuracy) | `PolyRatio.lean:48` and REPORT §6 describe the settled constant as "(r3 §H6: `c < 2^70`)". The constant is exactly `2^70` (`8·4^33·2`). r3's draft bound `c < 2^70` held only with r3's factor `4` (`2^69`), which the worker replaced by `8` (G6B-W1). | **LE-6b2** (the sentence says "constant `2^70`; r3 §H6 drafted `c < 2^70` with the factor `4`"). |
| G6B-F03 | minor (brief deviation, partly disclosed) | The brief (from the P6-Q19 refinement) says the leveled docstrings cite only [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3]. `Leveled.lean` also cites [BV14, Def 2.12] (compactness), [BV14, §3.3] and [Bar89, Thm 1] (literal inputs), yet its module docstring says the statements cite the three sources "only". `LeveledSecurity.lean` also cites [GSW13, §3.2, Lemma 1] and [BV11, Def 3.1], which it discloses, and [BV14, §2.5], which it does not. All of these are ingested, their anchors exist, and they attach to sub-facts (one-key steps, the view, literals, compactness), never to the key chain or the hybrid order. That is within the ruling's text ("citing only ingested sources"). | **Q-6B-F1**. Recommended: accept the citations and make the two sentences accurate (**LE-6b2**). |
| G6B-F04 | info (borderline re-derivation) | `Parameters.neZero_columns` (`DecryptFormula.lean:65–70`) proves `P.width ≠ 0` by the case contradiction `rw [h, pow_zero] at hle; omega` instead of core `Nat.one_lt_two_pow_iff`. It was present at checkpoint 1, which I did not flag. | Optional **LE-6b3** (proof only; dropped if it fails to compile, as LE-gf4). Seyoon's call in Q-6B-F1. |
| G6B-F05 | info (specialization, disclosed) | `decDepth_le` (G8) is F10's `modSumDepth_le` at `M = N` behind `decDepth`, weakened by `⌈log₂ q⌉ ≤ ℓ`. It is an admitted target by `targets.txt`, and the worker discloses it in *Overlap and reuse*. Once #366 lands, F10 is proved and the U13 fill is about 3 lines (its sketch names `modSumDepth_le`, `Nat.clog_le_iff_le_pow` and `Nat.clog_mono_right`). Not a restatement: the right-hand side differs. | Keep as delivered (**Q-6B-F2** A). Gate 46 may ask; the disclosure answers it. |
| G6B-F06 | info (probe coverage, disclosed) | **P2c** (G3 numeric noise) was stopped for time; only the noise-free part ran (7 formulas × 4 inputs). **P5b** (`fheEval` on the padded XOR circuit) completed 1 of 4 inputs before a container restart. One input takes over an hour; P5a covers `bootNAND` on all 4 pairs. **P6** ran the depth-2 parity twin `NAND(x₀, NAND(x₁))`, which has a level gap, on 4/4 inputs, instead of 6a's P9 XOR and odd-gap circuits (cost). **P4**'s kernel attempt on G6/G7 got stuck; `#eval` covers them. No statement was found false. | Record. The fills prove these statements; probes are evidence only. |
| G6B-F07 | info (size) | The surface is about 2,090 lines in the 9 new files, above the brief's 1,300–1,800 estimate (mostly docstrings and the reader layer). Fill projections: Bootstrap ≤ 791, LeveledSecurity ≤ 721, Asymptotic ≤ 604, all under 1,000 and over the 600 target. | Watch at the U14/U17/U19 fills. |
| G6B-F08 | info (process) | (a) The lead again stopped a stray `git clone` with `pkill -f` instead of by PID (handoff rule 4), and disclosed it. (b) A probe was OOM-killed at 13.2 GB, and the pool shrank from 3 to 2 slots. (c) The root build was resumed after the 2-hour tool limit. (d) The probe sub-agent stopped on a usage limit, and the lead re-ran its last runs. (e) The split differs from the suggested one: the lead wrote every statement, and the sub-agents `seal` and `probe` only verified. Every item is recorded in REPORT §3 and §14. | Record. |
| G6B-F09 | info (census naming) | The census proposes `hybridPlant_apply`; #368 landed the reader as `hybridPlant_eq` (Gate 50 CLEAR). | LE-6b1 names `hybridPlant_eq`; no census edit (it is evidence). |

## Questions for Seyoon (recommended option first)

- **Q-6B-W1 (G16's factor; worker's question).**
  - **A (rec.)** Accept G16 as `8·(ℓ·bootNoise) ≤ pBoot·B` with `pBoot`'s constant `2^70`, and keep G17's r3 hypothesis
    `pBoot·B < q`. With r3's `4`, G17 would need `4y + 2 ≤ q` but get only `4y + 1 ≤ q` (counterexample `q = 4y + 1`);
    I checked this.
  - **B** Keep `4` in G16, and state G17's hypothesis as `pBoot·B + 2 ≤ q`.
- **Q-6B-W2 (`LeveledReductionEfficient`; worker's question).**
  - **A (rec.)** Accept the delivered form: one `D'` also dominates the two challenge reductions
    `reduction P_κ μ' (challengeDist …)` that L5's last step needs. Without them A3 would not follow, and building an
    NUPPT for `challengeDist ∘ D` is the out-of-scope machine construction.
  - **B** A separate hypothesis for the challenge step.
- **Q-6B-W3 (L4/L5 shape; worker's question).**
  - **A (rec.)** Accept `levelTerm … μ e j D` and L5's bound `∑ₑ ∑ⱼ (levelTerm μ₀ + levelTerm μ₁) + challengeTerm μ₀
    μ₁`. The level reduction must simulate `Enc_{pk₀}(μ)`, so r3's μ-free `levelTerm` with `2·∑` was inconsistent with
    r3's own `levelReduction (… μ …)`.
  - **B** `2·∑ max_μ levelTerm`.
- **Q-6B-F1 (landing edits).**
  - **A (rec.)** Apply LE-6b1 and LE-6b2 (docstrings only) in one landing-edit commit on the statement PR, with the
    landing on the tip after #366 and #368. Also apply LE-6b3 (proof only), dropped if it fails to compile.
  - **B** LE-6b1 and LE-6b2 only.
  - **C** LE-6b2 only, leaving G6's and L4's sketches to the U13/U17 fills. Not recommended: Gate 50 graded the same
    staleness minor.
- **Q-6B-F2 (`decDepth_le`).**
  - **A (rec.)** Keep it an admitted target, as `targets.txt` makes it. The U13 fill proves it from F10.
  - **B** Prove it at landing as a citation (admissions 24 → 23; a new proof in a statement PR).

## Proposed landing edits

`landing-edits-proposed.diff` (141 lines; uncompiled; it applies in order to `8f92fe7d`, which I checked with
`git apply`, and to the landing merge, since no path is shared). Widths stay ≤ 100.
- **LE-6b1** (G6B-F01, F09; only for a landing on a tip that contains #366 and #368), 4 files, docstrings:
  - G6's sketch says `decrypt_eq_decode_dotProduct` is in `GSW/Scheme.lean` (owner-side, ruling Q-C1).
  - `fheEvalCircuit` and `leveledEvalCircuit` drop the "while … is admitted" sentence.
  - L4's sketch names `hybridPlant_eq`.
- **LE-6b2** (G6B-F02, F03), 3 files, docstrings:
  - PolyRatio's deviation sentence gives the constant `2^70`.
  - `Leveled` says its extra citations are for compactness and the literal inputs.
  - `LeveledSecurity` adds [BV14, §2.5] to its disclosed list.
- **LE-6b3** (G6B-F04, optional), `DecryptFormula.lean` proof only:
  `⟨Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.one_lt_two_pow_iff.mp (Nat.lt_of_lt_of_le P.lwe.modulus_ge_two
  P.modulus_le))⟩`.

No edit changes a declaration header; decls2 stays 136/0/0.

## For the worker

No action is needed: the delivery is complete. If Seyoon rules otherwise on Q-6B-W1–W3, the maintainer re-issues with
the change.

## Evidence

`gsw-6b-final-r1-phase1-evidence.zip` (SHA-256 in `evidence-SHA256SUMS`). It contains `PROVENANCE.txt`, an internal
`SHA256SUMS`, `scripts/` (`repro.sh`, `decls.py`, `sorries.py`, `bind.py`, `stale.py`, `admit.py`, `seals.py`,
`anchors.py`) and `out/`:
- integrity and `mkbase.sh` output;
- reproduction;
- decls2 (final, and base → tip × #366 × #368);
- the new-declaration and sorry scans;
- binding staleness and admissions;
- the seal recount;
- anchors;
- campaign-lint line sets;
- merge-tree.

## Phase 2 (2026-11-18): landing and Lean replays on snapshot #10

**Final verdict: ACCEPT WITH LANDING EDITS, applied. PASS. Both PRs are open as drafts for Gate 46 (Codex).** The full
record is in `phase2.md`, with evidence in `gsw-6b-final-r1-phase2-evidence.zip` (`60cfe326…`, in `evidence-SHA256SUMS`).

**Rulings applied (2026-11-18):** W1–W3 accepted as delivered; F1 A, so LE-6b1, LE-6b2 and LE-6b3 are all applied (LE-6b3
compiles, so nothing is dropped); F2 A, so `decDepth_le` stays admitted.

**The PRs**
- **PR O2 #376**: `land/gsw-6b-o2` = `04ba2446f541c39dd02aefaa97a9eb31dbbda748`, a signed pick of `5bd5ada5` onto the
  records tip `38123ccb`. The tip is Lean-equal to snapshot #10's T. Range-diff 1/1 `=`. Only `BitEncoding.lean` changes.
- **Statement PR #377**: `land/gsw-6b-statements` = `680be9fa45a9cf5deeb7a59820e8e86aaaa4f068`, stacked on O2.
  - It holds five signed picks (range-diff 5/5 `=`) and one signed landing-edit commit.
  - The edits are byte-identical to `landing-edits-proposed.diff`.
  - LE-6b1 corrects the four stale passages: G6's "MISSING" `decrypt_eq_decode_dotProduct`, the
    `fheEvalCircuit`/`leveledEvalCircuit` "while N2/N12/N13 are admitted" sentences, and L4's `hybridPlant_eq`. No other
    stale passage remains.

**Replays**
- **R1** (tip × O2): 19 modules rebuilt; rc 0, 0 errors, 0 `sorry`; state 1447/1447 OK; admissions 192 (+0); decls2
  5/0/0; standard axioms.
- **R2** (R1 × statements): 14 modules rebuilt; rc 0, 0 errors; the `sorry` warnings are exactly the 24 targets; state
  1456/1456 OK; admissions **216**, EXACT against `targets.txt` with G17 split.
  - decls2 136/0/0, and the landing-edit commit gives 0/0/0.
  - `sorryAx` is in exactly the 24 targets. **`fheEvalCircuit`, `leveledEvalCircuit` and their `_eq` lemmas are now
    standard.**
- **Rule 10:** strict and coe A/B seals of the 12 owners give 0 errors.
  - The paired controls (the delivery's 10 rows) are ALL_OK in both harnesses.
  - The delivery's own 50 controls give 34 OK unchanged, and 16 OK after pruning 4 names absent at the tip.
  - 0 foreign unfolds.
- **Lint and snapshot:** lint FAIL/WARN is identical to the tip's. Snapshot #10 rehashed 0/0/0 throughout.

**New infos:** G6B-F10 (LE-6b3's axiom-log effect), G6B-F11 (the delivery's baked control payloads are stale at the tip)
and G6B-F12 (root coe-A not re-run). There are no new blockers, majors or minors.

## ===== briefs/lattice-gsw/phase6/final-6b-r1/phase2.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

# gsw-6b-statements · final r1 · phase 2: landing and merged-tree Lean replays on snapshot #10

**Verdict: PASS for both landing branches. Both are pushed, with draft PRs open.**

- **PR O2** [#376](https://github.com/Shilun-Allan-Li/tcslib/pull/376), branch `land/gsw-6b-o2`, head
  `04ba2446f541c39dd02aefaa97a9eb31dbbda748`. Base: `cryptography/pass-shelat-ch2-4`.
- **Statement PR** [#377](https://github.com/Shilun-Allan-Li/tcslib/pull/377), branch `land/gsw-6b-statements`, head
  `680be9fa45a9cf5deeb7a59820e8e86aaaa4f068`. Base: `land/gsw-6b-o2`.
- Phase 2 found no blocker, major or minor. It adds three infos (G6B-F10 to F12, below).
- The ruled landing edits LE-6b1, LE-6b2 and LE-6b3 are applied in one signed commit. **LE-6b3 compiles and is kept.**

| Check | R1 = tip × O2 | R2 = R1 × statements (with LE-6b1..3) |
|---|---|---|
| Range-diff against the delivered series | 1/1 `=` | 5/5 `=`, plus the landing-edit commit |
| Tree | `8b615e06` = merge-tree(tip, `5bd5ada5`) | `~1` `22349e8e` = merge-tree(tip, `8f92fe7d`); head `956fc086` |
| Rebuilt / reused | 19 / 1428 | 14 / 1442 |
| Every rebuilt module | rc 0, 0 `error:`/`error(`, 0 `sorry` | rc 0, 0 `error:`/`error(`; `sorry` warnings exactly the 24 targets |
| State check | 1447/1447 OK | 1456/1456 OK |
| Link count of rebuilt oleans | 1 (19/19) | 1 (14/14) |
| Admissions | 192 (tip 192, +0) | **216** (+24, EXACT against the targets) |
| decls2 against the tip | 5 ADDED / 0 / 0 | 136 ADDED / 0 / 0; landing-edit commit 0/0/0 |
| Axioms | 24 BitEncoding constants, standard | 175 constants; `sorryAx` in exactly the 24 targets; `fheEvalCircuit`/`leveledEvalCircuit` and `_eq` standard |
| Seals (strict A/B, coe A/B) | BitEncoding 9/9/9/9, 0 errors | 12 owners, 48 probes, 0 errors |
| Controls | the delivery's 5 BitEncoding controls: ALL_OK | `mkctl_g6b` ALL_OK in strict and coe (70 + 70 sealed negatives); the delivery's 50: 34 unchanged + 16 after pruning stale names, all OK |
| Explicit-unfold scan | 54 items, 0 foreign | 101 items, 0 foreign |
| Lint | FAIL/WARN = tip (92/103) | FAIL/WARN = tip (92/103); `style_lint` 0 |
| Snapshot #10 rehash | 0/0/0 | 0/0/0 (before, after R1, after R2, end) |

Run on 2026-11-18, 04:20–06:45 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
The evidence is `gsw-6b-final-r1-phase2-evidence.zip`, under `gsw-6b-final-r1-phase2/`. Its SHA-256 is in
`evidence-SHA256SUMS`.

**Builds**
- No `lake build` and no cache get.
- Modules ran through the recipe's `runner.py` (`scripts/lean_check_tree.sh`). Probes ran through `runner_full.py`, which
  is `lean -DmaxErrors=0` without `-o`, so it writes nothing to a tree.
- Each call went through a slot gate, `pgrep -c -x lean`, which waits while 3 or more `lean` processes run.
- This job ran one Lean process at a time. Another job's single `lean` was running for part of the time, so the
  machine had at most 2.
- No process was signalled.

**Disk:** 7747 MB free at the start and 5976 MB at the end. The 1.5 GB guard never fired.

## P2-0 Tip and snapshot
- The records tip is `38123ccbebef878cd25dd2d2761de1b40ba7e421`.
- `git diff --name-only cf6a2266 38123ccb -- '*.lean' lean-toolchain lake-manifest.json lakefile.lean scripts audits` is
  empty, so the tip is Lean-equal to snapshot #10's T.
- #366 and #368 are merged into the tip, and every 6a target is proved.
- **Snapshot #10** (`$SP/olean-snapshot`) was verified with `snapmap.py verify` against `olean-snapshot.map-cf6a2266.tsv`
  (`84d88738…`). It gave **1478 files, 0 extra / 0 changed / 0 missing** at the start, after R1, after R2 and at the
  end. It was read only as the source of `cp -al`.

## P2-1 Reproduction and landing branches
- **Reproduction:**
  - delivery: `git archive 3b340824 inbox/fills/gsw-6b-statements`, with the top `SHA256SUMS` OK;
  - worktree: sparse, detached at the issued base `3e51b5f2`;
  - `git am` per patch, with the `COMMITS.tsv` committer data and `commit.gpgsign=false`;
  - result: all six hashes reproduce, `5bd5ada5`, `7a814546`, `dd9f00f4`, `1378740f`, `5c8f81cd` and `8f92fe7d`
    (`landing/reproduction.txt`).
- **`land/gsw-6b-o2`** = `04ba2446`:
  - built as `git cherry-pick -S 5bd5ada5` onto the tip;
  - tree `8b615e06` = `git merge-tree --write-tree 38123ccb 5bd5ada5`;
  - diff: `LWE/BitEncoding.lean` only, +58/−0;
  - range-diff `3e51b5f2..5bd5ada5` against `38123ccb..land/gsw-6b-o2`: **1/1 `=`**.
- **`land/gsw-6b-statements`**, stacked on O2:
  - five `-S` picks, `47aae69d`, `c10e0d3e`, `80366e7f`, `52f52dc7` and `75c683b2`;
  - range-diff `5bd5ada5..8f92fe7d` against `land/gsw-6b-o2..~1`: **5/5 `=`**;
  - the tree of `~1` is `22349e8e` = merge-tree(tip, `8f92fe7d`);
  - the picks keep the worker's messages and trailers.
- **Landing-edit commit `680be9fa`** (signed, with this session's two trailers, explicit paths):
  - It applies LE-6b1, LE-6b2 and LE-6b3 from `landing-edits-proposed.diff`, split per edit and applied in order with
    `git apply`.
  - Each of the 5 files is byte-equal to the proposal applied to `8f92fe7d` (`landing/le-vs-proposal.txt`).
  - Diff +17/−21. Line widths stay ≤ 99.
- **Signatures:** all 7 landing commits carry an SSHSIG with key `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`,
  the records tip's key. The worker's `5bd5ada5` and `8f92fe7d` are unsigned. This checks key identity only.
- **Exports:** `git archive` of each head (`TCSlib`, `TCSlib.lean`, `audits`, manifests, `lakefile.lean`, `scripts`)
  matches blob for blob: 1599 files (R1) and 1608 files (R2), 0/0/0.

### Prose that called the prerequisites missing or admitted (task item: "list each")
At this base #368 provides `decrypt_eq_decode_dotProduct` and `hybridPlant_eq`, and #366 proves N2, N12 and N13. The
landing-edit commit corrects every such passage in the series:
1. `GSW/DecryptFormula.lean`, G6 `decryptFormula_eval` sketch. The text "It is **MISSING** at the base (the step exists
   only inside the private `decrypt_eq_decode_errorSum`), listed in the reader census, and lands owner-side before this
   fill" becomes "in `GSW/Scheme.lean` (owner-side, ruling Q-C1)" (LE-6b1).
2. `GSW/Bootstrap.lean`, `fheEvalCircuit` docstring. "While 6a's N2 (`nandGadget_correct`) is admitted, `sorryAx` reaches
   this definition through `toNANDForm` only" is removed (LE-6b1).
3. `GSW/Leveled.lean`, `leveledEvalCircuit` docstring. "While 6a's N2, N12 and N13 are admitted, `sorryAx` reaches this
   definition through `toNANDForm` and `layerNAND` only" is removed (LE-6b1).
4. `GSW/LeveledSecurity.lean`, L4 `distAdv_levelHybrid_le` sketch. "`hybridPlant`'s planted position" becomes
   "`hybridPlant_eq` (the planted position)" (LE-6b1).

A scan of the 12 series files after the commit found no other passage that calls either prerequisite missing, calls a
6a declaration admitted, or names `hybridPlant_apply` (`landing/stale-prose-scan.txt`). The remaining "admitted" phrases
refer to 6b's own targets, and "will be cited once ingested" is the P6-Q19 B disclosure.

Outside the series, `GSW/Scheme.lean` and `EnsembleSecurity.lean` already carry LE-g50e's corrections. The census itself
(`issued-6b-r1/census.txt`, the delivery's `census/reader-census.md`) is evidence and is left unchanged, as G6B-F09 rules.
Its rows for `decrypt_eq_decode_dotProduct` and the `hybridPlant` reader (landed as `hybridPlant_eq`) are now satisfied
at the tip.

### Comment-strip identity (`commentstrip/`)
- `commentstrip50.py` (LE-g50d's tool, unchanged), `75c683b2` against `680be9fa`:
  - Bootstrap, Leveled, LeveledSecurity and PolyRatio give **RESULT EQUAL**;
  - every M1, M2 and M3 mutation is caught;
  - every N1 docstring control stays EQUAL;
  - overall **RESULT OK**, with 16 controls.
- DecryptFormula's comment-stripped diff (`stripdiff.py`) is exactly the `neZero_columns` proof: 5 lines out, 2 in.

## R1: the O2 head (`r1/`)
- **Recipe:**
  - copy: `cp -al $SP/olean-snapshot $SP/olean-replay-6b-o2`;
  - overlay: `mloverlay.sh` (3346 symlinks) and `mathlibextra.sh` NthRootLemmas `c0a9cff0…` (lean rc 0);
  - state: `stateplan init` at `cf6a2266` (1447 modules);
  - `downorder.py`: changed 1, down 19;
  - `fullorder.py`: 1447;
  - `stateplan plan`: **19 to build, 1428 reused**. The queue equals `down.txt`.
- **Build** (04:26:38–04:27:13, maximum RSS 4.4 GB): **19/19 rc 0**, `error:` 0, `error(` 0, substring "error" 0,
  `sorry` 0, and no log/record mismatch (`permod.py`).
  - The 3 warnings (Regev `simps` ×2, one unused section variable) are pre-existing.
  - All 18 modules with a reference log are SAME as the delivery's `sweep-o2-r2` logs; the root has no reference.
- **Accept:**
  - `stateplan update` took 19 modules;
  - `check` gives **1447/1447 RESULT OK**, and again at the end;
  - the rebuilt oleans have link count 1 (19/19), and the 1428 reused ones are snapshot #10's inodes;
  - there are no `.ilean` files and no stray symlinks.
- **Output map** (Mathlib excluded): `olean-replay-6b-o2.map-04ba2446.noMathlib.tsv`, 1478 entries, `e1d210bf…`.
  Against #10 only `LWE/BitEncoding` differs; the 18 rebuilt downstream oleans are byte-equal to the snapshot's.
- **Admissions:** `sorryscan.py` over the full order gives **192 in 44 modules** at the tip and at R1, byte-equal per
  module.
- **decls2** (pinned `fa81981a…`, tip against the O2 head): **5 ADDED**, 0 CHANGED, 0 REMOVED, empty `.err`.
- **Axioms** (the delivery's `AxiomProbe.lean` restricted to `BitEncoding` and the `LWE` facade): 24 constants, 17 DECL
  and 7 AUX, **all standard**.
  - `decodeLo`, `decodeHi`, `decodeLo_eq` and `decodeHi_eq` use none.
  - `decode_iff_mem_Ico` uses `propext`, `Classical.choice` and `Quot.sound`.
  - No `sorryAx`.
- **Rule 10** (`rule10/o2/`; owner `LWE.BitEncoding`; `touched.json` against the tip):
  - seals: strict A/B and coe A/B, **9/9/9/9 requests, 0 errors**, install and EOF records;
  - the maintainer harness's covering controls have no BitEncoding row at R1, since no downstream owner is sealed;
  - the delivery's 5 BitEncoding controls (`r2/o2/controls/src`, unchanged) give **5/5 OK**. The unsealed body read has
    0 errors. Sealed strict and coe, the negative has exactly 1 error, in the example, and the reader 0. Install and EOF
    records are present, with 14 requests;
  - explicit-unfold scan: 54 items (52 THEOREM, 2 LOCAL), **0 foreign**.

## R2: the statement head with LE-6b1..3 (`r2/`)
- **Recipe:**
  - copy: `cp -al $SP/olean-replay-6b-o2 $SP/olean-replay-6b-stmt`, with the overlay carried along;
  - state: R1's checked state;
  - `downorder.py` against the O2 head: changed 11, down 14;
  - `fullorder.py`: 1456;
  - `stateplan plan`: **14 to build, 1442 reused**. The queue equals `down.txt`.
- **The 14 rebuilt modules:** `LWE/Ratio`, `LWE`, the 8 new `GSW/*` modules, `GSW`, `Homomorphic`,
  `AdvancedEncryption` and `TCSlib`.
- **Build** (04:28:41–04:29:07, maximum RSS 4.4 GB): **14/14 rc 0**, `error:` 0, `error(` 0. There are 24 warnings, all
  `declaration uses 'sorry'`, and no log/record mismatch.
  - The warnings are SAME as the delivery's `sweep-final-r2` in 10 modules. They are SAME-TEXT, with only line numbers
    shifted, in the 4 files whose line count the landing edits change: DecryptFormula, Bootstrap, Leveled and PolyRatio.
  - **LE-6b3 compiles**: DecryptFormula has rc 0 and 0 errors.
- **Accept:**
  - `stateplan update` took 14 modules;
  - `check` gives **1456/1456 RESULT OK**, and again at the end;
  - the rebuilt oleans have link count 1 (14/14);
  - R1 stayed consistent: its check is still 1447/1447 OK at the end, and its output map is unchanged. Its 5 oleans that
    R2 did not rebuild are shared with R2 by `cp -al`.
- **Output map** (Mathlib excluded): `olean-replay-6b-stmt.map-680be9fa.noMathlib.tsv`, 1487 entries, `52ed7825…`.
  - Against R1: 9 modules added; `LWE`, `GSW` and `Homomorphic` changed; `AdvancedEncryption` and the root are
    byte-equal.
  - Recomputed at the end, the map is equal.

### Admissions (`admissions/`)
- `sorryscan.py` over the full order: **216 in 52 modules** at R2, against 192 in 44 at the tip.
- The diff is exactly 8 new module lines:
  - Branching 3, DecryptFormula 6, Bootstrap 5, Circular 1, Leveled 2, LeveledSecurity 2, PolyRatio 3 and
    Asymptotic 2;
  - no other module changes.
- `admmap6b.py` maps each `declaration uses 'sorry'` warning of the R2 logs to its enclosing declaration in the export:
  - 24 targets, 24 admitted, 24 matched;
  - none outside the targets, none twice, none missing: **EXACT**.
- The 24 are the 23 `target` rows of `issued-6b-r1/targets.txt`, plus `decrypt_leveledEval_of_ratio`, which is G17's
  split. `targets.txt` provides for it ("24 if G17 is split").
- Per the ruling Q-6B-F2, `decDepth_le` is among them.

### decls2 (`decls2/`)
- **Tip against the head:** **136 ADDED, 0 CHANGED, 0 REMOVED**, empty `.err`. Ignoring line numbers, it is identical
  row for row to phase 1's `decls2-final.tsv`. 50 rows carry shifted line numbers, all in the files the landing edits
  change.
- **`~1` against the head** (the landing-edit commit): **0/0/0**. LE-6b3 does not change the instance header.

### Axioms (`axioms/`)
- **Probe:** the delivery's `AxiomProbe.lean` (`evidence/stmt/probe/`), unchanged, on R2. It reports 175 constants: 153
  DECL and 22 AUX.
- **Non-standard axioms other than `sorryAx`:** none.
- **`sorryAx`** is in **exactly the 24 targets**. Each TRACE names only the target itself.
- **`fheEvalCircuit`, `fheEvalCircuit_eq`, `leveledEvalCircuit` and `leveledEvalCircuit_eq` are standard**
  (`propext`, `Classical.choice`, `Quot.sound`). This confirms that with 6a fully proved, the four N2/N12/N13
  dependents of the delivery's log no longer reach `sorryAx`.
- **Against the delivery's `AxiomProbe-r2.log`:** 192 lines are equal, 7 appear only here and 12 only there.
  - The 4 dependents above lose `sorryAx`, and their 4 TRACE lines go.
  - **LE-6b3** changes three things:
    - `Parameters.neZero_columns` goes from `[Quot.sound, propext]` to `[propext]`;
    - its auxiliary `neZero_columns._proof_1` disappears, which leaves 22 AUX instead of 23;
    - `levelMsgs._proof_1` and `levelAssemble._proof_1`, which use `NeZero.ne P.columns`, go from
      `[Quot.sound, propext]` to `[propext]`.

  There is no other difference (G6B-F10).
- **O2's five declarations:** standard, as at R1.

### Rule 10 (`rule10/stmt/`, `scan/stmt/`)
- **Driver:** `rule10_g6b.sh`, which is `rule10_g6a.sh` re-pointed.
  - Owners: the 9 new modules, the facades `GSW` and `LWE`, and `BitEncoding`.
  - `touched.json` is taken against the tip.
  - `SEAL_CHUNK=1000`.
  - Every probe goes through the slot gate.
- **Seals:** 48 probes, **all rc 0 with 0 errors**. Each has one install and one EOF record, with
  `requested = verified`.

  | Owner | A | B | coe-A | coe-B |
  |---|---|---|---|---|
  | `LWE/BitEncoding` | 9 | 9 | 9 | 9 |
  | `LWE/Ratio` | 947 | 948 | 946 | 947 |
  | `GSW/Branching` | 200 | 200 | 200 | 200 |
  | `GSW/DecryptFormula` | 381 | 381 | 380 | 380 |
  | `GSW/Bootstrap` | 445 | 445 | 444 | 444 |
  | `GSW/Circular` | 465 | 465 | 464 | 464 |
  | `GSW/Leveled` | 480 | 480 | 479 | 479 |
  | `GSW/LeveledSecurity` | 1,562 | 1,563 | 1,561 | 1,562 |
  | `GSW/PolyRatio` | 1,395 | 1,396 | 1,394 | 1,395 |
  | `GSW/Asymptotic` | 1,654 | 1,655 | 1,653 | 1,654 |
  | `GSW.lean` (facade) | 1,663 | 1,664 | 1,662 | 1,663 |
  | `LWE.lean` (facade) | 966 | 967 | 965 | 966 |

- **Against the delivery's strict seal records** (`rule10/stmt-requests-vs-delivery.txt`): the sets differ only by
  closure drift since the issued base.
  - **17 names are added**, all from modules the tip changed since `3e51b5f2`: 6a's fills in `CarrySave` (6),
    `NANDLayering` (5), `Compare` (1) and `Barrington` (1), plus `BitLists` (3) and `IterateFind` (1).
  - **4 names are gone:** `IterateFind`'s `polyTimeComputable_find.match_1`, `match_1_1` and their two private
    `splitter`s, which no longer exist at the tip.
  - BitEncoding is identical.
- **Paired controls** (`mkctl_g6b.py`: `mkctl_g6a.py` with the harness unchanged, and rows B replaced by the delivery's
  10 rows):
  - The rows are `RatioBounded`, `select`, `decDepth`, `bootNoise`, `WeakCircularSecure`, `levelKey`,
    `challengeDist`, `pBoot`, `encodeCiphertext` and `decodeLo`. Their statements are verbatim, stated inside the
    delivery's namespace with its opens.
  - Covering subset: 14 seal records, giving 28 probes per harness.
  - **Strict and coe each:**
    - 70 sealed negatives, each failing exactly once: `decodeLo` 14, `select` 10, `decDepth` 10, `RatioBounded` 8,
      `bootNoise` 8, `levelKey` 6, `WeakCircularSecure` 4, `challengeDist` 4, `pBoot` 4, `encodeCiphertext` 2;
    - 70 positives with 0 failures, and 140 unsealed controls with 0 errors;
    - **ALL_OK** (`ctlcheck2.py`).
  - Every row is exercised.
- **The delivery's own control files** (`evidence/rule10/r2/{final,final-bitenc}/controls/src`, 50 files, run
  byte-unchanged; `rule10/delivered-stmt/`):
  - **34/50 OK.**
  - The 16 sealed files of `Ratio`, `PolyRatio`, `LeveledSecurity` and `Asymptotic` (strict and coe, negative and
    positive) stop at harness install. The reason is `absent/ambiguous imported name
    Complexity.IterateFind.polyTimeComputable_find.match_1`, followed by the EOF consequence. Their request sets were
    baked at the issued base and name the 4 names that are now gone.
  - `dctlprune.py` removes exactly those 4 entries from each `payload` and `componentPayload` literal, and lowers
    `expectedRequests` by 4. Nothing else changes, as the file diff confirms. The pruned files give **16/16 OK**:
    - each negative fails exactly once, in the example;
    - each positive gives 0 errors;
    - install and EOF records are present (Ratio 944/943, PolyRatio 1380/1379, LeveledSecurity 1553/1552,
      Asymptotic 1644/1643) (`rule10/delivered-stmt-pruned/`; G6B-F11).
- **Explicit-unfold scan** (the 12 changed files): 101 items, **0 foreign**.
  - THEOREM 91.
  - OWNED_DEFINITION 5: the file's own `unfold bootGate` ×3 and `unfold levelGate` ×2, in their case readers.
  - LOCAL_OR_UNRESOLVED 5.
- **Root coe-A was not re-run.** The root file is unchanged by both PRs and owns no declaration. Both changed facades
  were sealed in all four variants (G6B-F12).

### Lint and sizes (`lint/`)
- **`campaign_style_lint.py TCSlib/Cryptography --check8b`**, each run from its own export:
  - tip: 92 FAIL / 103 WARN over 531 files;
  - R1: 92/103 over 531;
  - R2: 92/103 over 540.
  - The FAIL and WARN line sets are **identical** to the tip's (0 diff lines). Phase 1's 104 WARN at the base dropped to
    103 at the tip, because #368 gave `hybridPlant` its reader.
- **`style_lint.py`:** 0 findings in the 12 changed files at R2.
- **Sizes:** at most 351 lines (LeveledSecurity) and at most 99 characters wide (`landing/sizes.tsv`).

## Infos added by phase 2
| # | Severity | Finding | Disposition |
|---|---|---|---|
| G6B-F10 | info | LE-6b3 removes `neZero_columns._proof_1` and drops `Quot.sound` from `neZero_columns`, `levelMsgs._proof_1` and `levelAssemble._proof_1`. It is the only axiom-log difference besides the four N2/N12/N13 dependents, which are now standard. | Record; expected from LE-6b3. |
| G6B-F11 | info (tooling) | The delivery's 16 sealed controls for the IterateFind-dependent owners bake request sets from the issued base, and 4 of their names no longer exist at the tip, so they fail at install. Pruning only those entries makes all 16 pass. The maintainer harness, built with the current request sets and the same 10 rows, is ALL_OK. | Record. Not a module finding. |
| G6B-F12 | info (scope) | The root coe-A was not re-run: the root is unchanged and declares nothing. | Record. Gate 46 may ask for it. |

## Merge and adoption (for the maintainer; nothing is merged here)
1. **#376 (O2) first.** On merge, run `git diff --name-only <merge> 8b615e060f72d72749f67abd39f820d117e0a806 -- '*.lean'
   lean-toolchain lake-manifest.json lakefile.lean`. If it is empty, adopt `$SP/olean-replay-6b-o2` (map `e1d210bf…`,
   after removing `Mathlib/`) as snapshot #11.
2. **Then #377**, retargeted to `cryptography/pass-shelat-ch2-4`. If the tip is otherwise unchanged, run the step-3 diff
   against `956fc086044551e8f04298ab70dd5aa451069c16`. If it is empty, adopt `$SP/olean-replay-6b-stmt`, which already
   contains R1. Otherwise re-replay its 14 modules.
3. Gate 46 (Codex) audits both PRs before merge.

## Not done or left
- The records files are uncommitted: this file, the zip, `evidence-SHA256SUMS` and the `review.md` append.
- The two replay trees are kept for adoption. They have 0 `.ilean` files, and their `Mathlib/` overlay is still in place.
- The landing worktree `$SP/g6b-p2/land` and the reproduction worktree `$SP/g6b-p2/repro` stay registered and were not
  pruned.

## ===== briefs/lattice-gsw/phase6/checkpoint1-6b-review.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

# gsw-6b-statements · checkpoint 1 review (maintainer, static)

**Verdict: PROCEED WITH NOTES.** 0 blockers, 1 major (G6B-C1-F01, in O2, can be fixed before the final),
2 minors (F02, F03), 6 infos. The checkpoint is a full payload for its claim (lesson G6A-C1-F01 applied): both
series reproduce bit for bit, `src/` and `src-o2/` match the reproduced heads, and the build logs bind every
claimed source. O2 is correct and matches r3's interval form, but one step re-derives a Mathlib lemma (F01). The
four statement files match r3 §H5.9–§H5.12 and the brief, and I found no restatement of an existing lemma. One
fill prerequisite needs a ruling from Seyoon (F03, Q-C1).

## Delivery
- Exchange `1e0647b99de8ee4d11722b5bad862fe40837a2ce` ("stmt gsw-6b: checkpoint 1", 2026-11-17 18:37 UTC, unsigned),
  parent `8b901411b9ff723aeca422319d2f35b106aad88e`; 602 files, all under `inbox/fills/gsw-6b-statements/`
  (no other path is touched). Extracted with `git archive` into an empty scratch directory.
- Heads named in `REPORT.md`: O2 `dd84941f747bca798c2a5a792616f5ead21cfa0b`; stmt `6e01df6c7d5a4f36e92000040d8c83322cb7fef7`
  (Branching, DecryptFormula), `57815173072bf8c145a4bb774797989061fe96f4` (Bootstrap, Circular); base
  `3e51b5f28900db6190f1eb2e6d207d27ee15d541` (tree `b69a66a3…`).
- Contents: `REPORT.md`, `patches/o2/` (1 commit), `patches/stmt/` (2 commits), `src/` (5 files), `src-o2/` (1 file),
  `evidence/` (588 files), `SHA256SUMS`.

## Checks
- **Integrity.** The top-level `SHA256SUMS` (601 entries) and `evidence/SHA256SUMS` (588 entries) verify with rc 0. The
  delivered path sets equal the manifests exactly (nothing missing, nothing extra, no `./`). The issued pack's
  `SHA256SUMS` verifies 25/25.
- **Reproduction.** In a shared scratch clone, the issued `tools/mkbase.sh` prints `STEP1 04947bcf… tree 8eca9617…`
  and `BASE 3e51b5f2… tree b69a66a3…`, the same as the worker's `mkbase.log`. With a sparse checkout at the base
  (`LWE/`, `AdvancedEncryption/Homomorphic/`), `git am` with `COMMITS.tsv`'s committer data and no signing gives
  `dd84941f…`, `6e01df6c…` and `57815173…`. `src-o2/` and all five `src/` files are byte-equal to the heads. The diff
  base..head covers exactly the 4 new GSW files and `BitEncoding.lean` (957 insertions, 0 deletions). The head is
  unsigned (`gpgsig` 0) and every signing column reads `none`.
- **O2.** My own diff against the base shows insertions only: one entry in each of the module docstring's
  *Main definitions* and *Main results*, and the block after `decode_eq` (`:118–178`): `decodeLo` and `decodeHi` with
  `rfl` readers `decodeLo_eq` and `decodeHi_eq`, and `decode_iff_mem_Ico`, proved with no `sorry`. The headers equal
  r3 §H5.8 and the brief character for character, and each declaration has a formula docstring that says "Glue"; the
  theorem also has a proof sketch. `decode_codepoint_add` is not re-proved. Issued `o2check.py`: 0 mismatches for
  `2 ≤ q ≤ 600`. Worker evidence I checked: decls2 5 ADDED / 0 / 0; frozen check 0 violations, with controls; sweep
  18/18 rc 0 with source SHA-256 `ac627bf2…` = delivered; seals A/B/coe-A/coe-B 9 requests each, all PASS; the
  `decodeLo` controls fail sealed exactly once (`:117`, inside the example) and pass positive and unsealed; the axioms
  are standard, with no `sorryAx` in 31 constants. **But see F01.**
- **Statements (4 files).** Headers match r3 §H5.9–§H5.12 (G1–G3, G5–G8, G9–G13, G18, G15), with r3's elided
  hypotheses filled in and the *(fix)* constants settled: `decDepth_le` is `9⌈log₂N⌉ + 2⌈log₂(ℓ+⌈log₂N⌉+3)⌉ + 21`
  (no term linear in ℓ), and `bootNoise_le` is `4^33·N^19·X^4·(2β)`. I checked the derivation of both by hand: they
  follow from F10's `modSumDepth_le` and `4^⌈log₂y⌉ ≤ 4y²`. There are exactly 15 `sorry`, one at each target
  (Branching 3, DecryptFormula 6, Bootstrap 5, Circular 1). The sweep logs show the same counts as `sorry` warnings,
  0 errors in both forms, and source hashes equal to the delivered files. **G11** `encrypts_evalKey` is proved as
  `rw [evalKey_eq]; exact encrypts_encrypt …`, the LE-g45 pattern. **G14** is reader-only (`weakCircularSecure_iff`,
  `Iff.rfl`), and no `distAdv_fheView_le` exists (Q-6B-1 A). **G15** is stated over the evk-dropped projection of
  `fheView`, not over `realView`, as the brief requires. Every definition has its body and an `rfl` reader; `bootGate`
  has three case readers covering every argument list; `fheView` has non-simp `simps`. `Parameters.neZero_columns`
  is proved. The statements check out on paper (G1's `|1−b|+|b| = 1`, G2's step noise, G12's `m·B ≤ bootNoise`
  from `N ≥ 1`, G6's `decodeLo ≤ decodeHi ≤ q`). Every target docstring gives the formula, an `[TAG, loc, anchor]`
  or "Glue", its deviations and a `**Proof sketch.**`. The sketches cite 39 TCSlib and Mathlib names; all exist at
  the base or the Mathlib pin (`args_lt` and `output_lt` are structure fields).
- **Sources.** No `[Gen09]`. Every `pNNN-bNNN` anchor in the four files exists in the ingest of its tag at the base
  (script check over BV14, BV11, AP14, GSW13, Pei16 and Bar89).
- **Duplication.** I searched by name and by conclusion shape in `TCSlib/` at the base and at both tips (main
  `b986b862`, records `bfa1f5a4`) and in the Mathlib pin. No new declaration restates a public lemma. The near
  relatives are a citation (G11 ← `encrypts_encrypt`), a specialization (`decDepth_le` ← admitted F10
  `modSumDepth_le`, `ModSum.lean:179`, with ⌈log₂q⌉ widened to ℓ, so its right side is weaker) and different
  constructions (`fheEval` vs phase-5 `eval` with `homGate`; G12 vs `decrypt_keygen_eval`; `select` vs `Encrypts.nand`).
  There are no private helpers and no cross-file copies. New full names do not clash; the short names `Coins`,
  `PublicKey` and `select` exist only in unrelated namespaces (PPT, Hybrid, Interaction, RSA, Extraction). Two
  issues: one inline re-derivation in O2 (F01) and two fill-time risks in sketches (F02, F03).
- **Hygiene.** No `native_decide`, `admit`, `axiom`, `@[simp]`, `show`, `change` or `delta`. The only `unfold` is of
  the file's own `bootGate` in its three case readers. The `Nat.mul_ne_zero` step reads `Parameters.columns`, a
  reducible abbreviation (notation). Maximum line width is 99. Sizes: Branching 179, DecryptFormula 217, Bootstrap
  351, Circular 146, BitEncoding 206. No micro sign.
- **Evidence recount.** The bootstrap built 288/288 rc 0 with 99 `sorry` in 17 modules, as expected. Admissions at
  the O2 head are 289 in 55 and byte-equal to `base-sorries.txt`. Build logs: the 22 sweep modules at `57815173` are
  rc 0. Seal summary as above.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| G6B-C1-F01 | **major** (re-derivation; GF-F01, G48-01) | `decode_iff_mem_Ico` (`src-o2/…/BitEncoding.lean:156–162`) proves the inline helper `habs : y.valMinAbs.natAbs = if y.val ≤ q/2 then y.val else q − y.val` by `rw [ZMod.valMinAbs_def_pos]; split_ifs <;> omega`. This is Mathlib's `ZMod.valMinAbs_natAbs_eq_min` (`Mathlib/Data/ZMod/ValMinAbs.lean:160`, `a.valMinAbs.natAbs = min a.val (n − a.val)`, proved by `rw [valMinAbs_def_pos]; omega`), written in `if` form. The brief's *No re-derivation* rule grades it a major. REPORT §3's lemma list and the worker's duplication search miss it. | **Worker fixes before the final.** Delete `habs` and rewrite both distances with `ZMod.valMinAbs_natAbs_eq_min` (`omega` handles `min`); update the sketch. Rerun O2's checks (decls2, frozen, sweep, seals, controls, axioms) and rebase the stmt series on the new O2 head. |
| G6B-C1-F02 | minor (sketch; fill-time GF-F01 risk) | G15's sketch (`Circular.lean:133–135`) describes the marginalization step without naming a lemma: "a sampler that ignores an independent uniform coordinate has the same acceptance probability (`acceptProb_def`, `uprob` over a product with a constant factor)". That fact is public as `uprob_fst` (`Foundations/Probability.lean:175`) and `uprob_snd` (`Pseudorandom/Functions/LazySampling.lean:70`). | **Worker:** name `uprob_fst` (after `acceptProb_def` and `acceptProb_comp_equiv`, `Foundations/Experiments.lean:107`) in the sketch and list it in *Overlap and reuse*. |
| G6B-C1-F03 | minor (fill prerequisite; GF-F02 pattern) | G6's sketch (`DecryptFormula.lean:158–160`) needs `c_last − ⟨s, c_init⟩ = ⟨t, decryptColumn P C⟩` for `t = (−s, 1)`. At the base this is only step 1 (`hsplit`) of the **private** `decrypt_eq_decode_errorSum` (`GSW/Scheme.lean:213–231`). Rebuilding it in the U13 fill would copy private material across files, which Codex flagged as GF-F02. It is not a public lemma, so the statement surface is fine as delivered. | **Seyoon: Q-C1.** Under A, the worker lists it in the reader census as MISSING, with the proposed public lemma, beside `hybridPlant`. |
| G6B-C1-F04 | info | The checkpoint's admission scan (`admissions/graph/cp1`) reports 289, the same as the base, because the four new modules are not reached from the root until the facades import them (38 unreached modules against 34). The 15 new admissions show up only in the sweep logs and my grep. | Final: the check-4 comparison must cover the new modules (root reach through the facades, or the sweep plus the syntactic scan), with 23–26 names in the 8 GSW files. |
| G6B-C1-F05 | info (size watch) | `Bootstrap.lean` has 351 statement lines. With r3 §H7's U14 estimate (280–440 fill lines) it would fill to about 630–790: under the 1,000 cap, over the 600 target. The other three files project to 330–550. | Check in the final review. |
| G6B-C1-F06 | info (process) | (a) The lead stopped its own stray `git clone` with `pkill -f` instead of by its recorded PID (handoff rule 4), and disclosed it. (b) The split differs from the suggested one: the lead wrote every statement, and the sub-agents (`seal`, `probe`) only verify; this is recorded as the brief allows. (c) `axioms-summary.txt` and the lint lines describe the undelivered final-head files (24 targets traced, so G17 is presumably split), and I cannot verify them here. | Record only; (c) is verified at the final. |
| G6B-C1-F07 | info (freshness) | The records tip has moved to `bfa1f5a4` (#347 and #355 merged; 23 Lean files, none on a 6b path; `Asymptotic/Adversary.lean` gains declarations). `git merge-tree` of the tip with `57815173` is clean, and none of the 68 new names is declared at the tip. | Stay on the base (brief); the maintainer replays at landing. |
| G6B-C1-F08 | info (nit) | The type-level readers `PublicKey_eq`, `Secret_eq`, `Coins_eq`, `KeySeed_eq`, `FheView_eq` and `Seeds_eq` follow phase 5's `Ciphertext_eq` precedent. However, `FheView_eq` (type) and `fheView_eq` (sampler) differ only in case. | Optional: keep, or mention the pair in the docstrings; no action needed. |
| G6B-C1-F09 | info | REPORT defers the row map, *Statement changes against r3*, *Overlap and reuse*, the census and the probes to the final, which the checkpoint definition allows. No questions or scope requests from the worker. | Final. |

## For the worker (maintainer relays)

> Checkpoint 1 reviewed: PROCEED WITH NOTES. Reproduction, integrity, the build bindings and the four statement
> files are in order. Please fix three points before the final:
> 1. **O2 (major, G6B-C1-F01).** In `decode_iff_mem_Ico`, `habs` re-proves Mathlib's `ZMod.valMinAbs_natAbs_eq_min`
>    (`Mathlib/Data/ZMod/ValMinAbs.lean:160`, `a.valMinAbs.natAbs = min a.val (n - a.val)`) in `if` form. Delete
>    `habs`, rewrite with `ZMod.valMinAbs_natAbs_eq_min` (`omega` handles `min`), and update the proof sketch. Rerun
>    O2's evidence (decls2, frozen check, sweep, seals and controls, axioms), rebase `stmt/gsw-6b` on the new O2 head,
>    and list the lemma in *Overlap and reuse*.
> 2. **G15 sketch (G6B-C1-F02).** Name the marginalization lemma, `uprob_fst` (`Foundations/Probability.lean:175`),
>    after `acceptProb_def`/`acceptProb_comp_equiv`, instead of "`uprob` over a product with a constant factor".
> 3. **G6 prerequisite (G6B-C1-F03).** The step `c_last − ⟨s, c_init⟩ = ⟨secretVector P s, decryptColumn P C⟩` exists
>    only inside the private `decrypt_eq_decode_errorSum` (`GSW/Scheme.lean:213`). Do not restate it in a 6b file.
>    In the reader census, list it as MISSING with a proposed one-line public lemma in `Scheme.lean` (for example
>    `decrypt_eq_decode_dotProduct : decrypt P s C = decode P.lwe (secretVector P s ⬝ᵥ decryptColumn P C)`), beside
>    `hybridPlant`, and point G6's sketch at it. (Pending Seyoon's Q-C1; if he rules otherwise, I will tell you.)
> Also at the final: the admissions comparison must reach the new modules (G6B-C1-F04).

## Questions for Seyoon
- **Q-C1 (G6B-C1-F03): the decryption-residual step behind G6.**
  - **A (rec.)** Treat it as a fill prerequisite, like `hybridPlant`'s reader: an owner-side one-line public lemma in
    `GSW/Scheme.lean` (`decrypt_eq_decode_dotProduct`, promoted from step 1 of the private
    `decrypt_eq_decode_errorSum`, which then uses it), landed with the other owner-side readers before the U13 fill.
    The 6b statements stay unchanged.
  - **B** Let the U13 fill re-derive the step inline in `decryptFormula_eval` (about 7 lines) and disclose it in
    *Overlap and reuse*. This risks a GF-F02 or G48-01 finding at the fills gate.
  - **C** Approve a scope request now, so that this job adds the public lemma to `Scheme.lean` (a frozen-file edit)
    in the statement series.

## ===== briefs/lattice-gsw/phase6/rulings.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

# GSW phase 6 · rulings P6-Q1 to P6-Q13 and the location ruling (Seyoon, 2026-11-16)

Seyoon answered the thirteen questions in [questions.md](questions.md): eight as recommended and five changed (Q3, Q4,
Q9, Q10, Q11). He then added a location ruling. `plan-section.md` is revised to match before the statement phase.

| # | Ruling | |
|---|---|---|
| P6-Q1 | **One phase 6** on the BV14 route to pure FHE at a polynomial ratio; it merges the roadmap's phases 6 and 7. **Two statement gates:** **Gate 45** covers the complexity layer (6a: branching programs, Barrington, formula arithmetic, NAND conversion), and **Gate 46** covers the cryptography (6b). The quasi-polynomial instantiation is dropped. Gates 42–44 are taken, so 45 and 46 replace the plan's provisional 42 and 43. | as recommended |
| P6-Q2 | Barrington's input model is **`BoolCircuit.TreeCircuit n`**, AND/OR formulas over literals with polarity, which is Bar89's model. `DAGCircuit` is reached through the depth-preserving `DAGCircuit.toTree`. | as recommended |
| P6-Q3 | **Both directions now: BWBP = NC¹.** This covers Bar89 Thm 1 with Lemmas 1–3, the `DAGCircuit` corollary (length ≤ `4^depth`), NC¹ ⊆ polynomial-length width-5 PBPs, **and** Thm 2 (BWBP ⊆ NC¹) with its composition-tree circuit. The plan's estimate is about +300–500 lines; FHE does not use Thm 2. | **changed** (was: Thm 1 and NC¹ ⊆ PBP only) |
| P6-Q4 | **The general branching-program model of Bar89 §1**, with instructions mapping `[w] → [w]`, plus an **`IsPermutation`** predicate. It is otherwise as proposed: instructions `⟨var, f0, f1⟩` in BV14's order (`f0` when the bit is `0`), with Bar89's order disclosed; `yield` in program order; and the public host `evalWith`, generic in the selector and value type, with the step-indexed relational lemma `evalWith_rel`. It is registered in `ComputationalModels.lean` and `machine-library-design.md` §14. Boolean semantics and GSW are its consumers. | **changed** (was: permutation programs only) |
| P6-Q5 | The decryption formula is built in a **new shared formula-arithmetic layer** over `TreeCircuit`: De Morgan negation, substitution, `xor3`/`maj3`, the carry-save (3:2) reduction, carry-out comparison with constants, and the modular interval sum. | as recommended |
| P6-Q6 | The layer goes in **`Complexity/CircuitComplexity/FormulaArith/{Combinators,CarrySave,Compare,ModSum}.lean`**, as the first rows of a circuit/formula gadget registry. A small owner-side PR promotes the private `TreeNCAC.combine` to public. `Parity.lean`'s private dual-rail XOR is re-pointed later, on the dedup queue. At statement prep, check `Complexity/FormulaKit/Gate.lean` (CNF truth-table gates) for reuse; it is a different formula model. | as recommended |
| P6-Q7 | **`decode_iff_mem_Ico`**, with explicit `lo` and `hi`, is a published reader in the owner file `LWE/BitEncoding.lean`, added by a small owner-side PR. | as recommended |
| P6-Q8 | The evaluation key is **public-key GSW encryptions, under the user's own `pk`, of the `N` bits of `G⁻¹(t)` with `t = (−s, 1)`**. This is BV11 Def 3.8. There is one `GSW.Parameters` record, the evaluation-key noise is `m·B`, and decryption becomes a binary subset sum with public constants `Gᵀc`. | as recommended |
| P6-Q9 | **Bootstrapping is NAND only**, literally BV14 Def 2.13. Circuits are first converted to NAND form by a **new conversion with its own lemmas** (semantics, size and depth). | **changed** (was: every `DAGCircuit` gate) |
| P6-Q10 | **The concrete statements, and now also the asymptotic forms:** an asymptotic `WeakCircularSecure` family predicate and an asymptotic IND-CPA theorem, conditional on an explicit reduction-efficiency hypothesis. Concrete as in phase 5: `WeakCircularSecure P χ ε` bounds every distinguisher's advantage on `(pk, evk, Enc(μ))`, and the `evk`-free view inherits phase 5's DLWE bound. Compactness holds by typing and is stated in the docstring. | **changed** (was: concrete only, asymptotic later) |
| P6-Q11 | **The full leveled scheme now:** `L+1` keys, correctness, and IND-CPA by a hybrid over the keys from DLWE (BV14 Thm 2.14 first part; BV11 Thm 3.1). The plan's estimate is about +400–700 lines. It is the FHE statement that needs no circular-security assumption. The key-switching form of the bootstrapping lemma remains its basis. | **changed** (was: key-switching lemma only) |
| P6-Q12 | **Explicit `decDepth P` and `bootNoise P β`** in the correctness theorems, with closed-form bounds proved separately. The ruled `RatioBounded F B p` goes in a new `LWE/Ratio.lean`, with a family theorem carrying an explicit `PolyExpr` `pBoot`. | as recommended |
| P6-Q13 | **`barrington` is computable**: Lemma 1's conjugator is explicit (`θ(σᵏ 0) = τᵏ 0` for five-cycles), so `fheEval` is computable. | as recommended |

## Location ruling (Seyoon, 2026-11-16, after Q1–Q13)

**Branching programs, Barrington and the NAND conversion go in `Complexity/`.** In Seyoon's words, these are general
facts about models of computation and will be usable elsewhere. The 6b (GSW) modules only consume them.

The maintainer proposes these homes; the revised plan section confirms them:
- **Branching programs.** The facade is `Complexity/BranchingPrograms.lean`, with:
  - `Complexity/BranchingPrograms/Defs.lean`: the general model, `IsPermutation` and `yield`;
  - `Complexity/BranchingPrograms/Eval.lean`: the host `evalWith` and `evalWith_rel`;
  - `Complexity/BranchingPrograms/Barrington.lean`: Thm 1, Lemmas 1–3 and the NC¹ corollary;
  - `Complexity/BranchingPrograms/BarringtonConverse.lean`: Thm 2.

  The model is registered in `ComputationalModels.lean`.
- **NAND conversion:** `Complexity/CircuitComplexity/NANDForm.lean`, beside `DAGTransform.lean`.
- **Formula arithmetic:** `Complexity/CircuitComplexity/FormulaArith/`, per P6-Q6.

## Effect on scope
The changed rulings enlarge the phase:
- Thm 2 adds about 300–500 lines (P6-Q3), and the leveled scheme about 400–700 (P6-Q11), per the plan's estimates.
- The general BP model (P6-Q4), the NAND conversion (P6-Q9) and the asymptotic forms (P6-Q10) are new items. The revised
  plan section estimates them.
- Gate 45 (6a) now covers the BP model, Barrington in both directions, formula arithmetic and the NAND conversion.

## Rulings P6-Q14 to P6-Q19 (Seyoon, 2026-11-16, on plan section r2)

| # | Ruling | |
|---|---|---|
| P6-Q14 | **Consecutive keys plus a layering conversion.** Each `evk_d` encrypts the bits of `s_{d−1}`, giving `N·L` ciphertexts (the textbook chain). Circuits are made **layered** by a new generic conversion under `Complexity/`, which pads uneven paths with double-NAND identity chains, with care for odd gaps. It is part of 6a and Gate 45; estimated +150–250 lines. | **changed** (was: keys by depth, evk to every lower key) |
| P6-Q15 | **Per-distinguisher concrete form:** `WeakCircularSecure P χ D ε := distAdv (fheView … false) (fheView … true) D ≤ ε`. The asymptotic `WeakCircularSecureFamily` (NUPPT, negligible) is the headline hypothesis, faithful to BV11 Def 3.8. This corrects P6-Q10's concrete form, which, quantified over every function, holds only for `ε` near 1. | as recommended |
| P6-Q16 | **NAND form is a predicate on `DAGCircuit`:** every gate is a `¬` gate (negated conjunction) of fan-in ≤ 2. The conversion is an instance of `DAGCircuit.rewrite`, within its budget, with depth factor 2. Bootstrapping pads fan-in 1 to `(a, a)` and fan-in 0 to `(G, G)`. Disclosed: NAND-form circuits are not `IsWellFormed`. | as recommended |
| P6-Q17 | **Registry rows:** `BranchingProgram.evalWith` as H18; `runWith`/`runWith_rel` recorded as H19 and `DAGCircuit.rewrite` as H20. Gate 45 audits their contracts. Records only. | as recommended |
| P6-Q18 | **Thm 2's circuit is a `TreeCircuit` formula** with fan-in 2, mirroring Bar89's three sections. It reaches `DAGCircuit` and `Language.InNC 1` through `Language.InTreeNC.inNC`; its size `l^{O(log w)}` is polynomial for fixed `w`. | as recommended |
| P6-Q19 | **Ingest Gen09:** the leveled-bootstrapping passage of Gentry's thesis or his STOC 2009 paper (the key chain and its security hybrid), which is cited for the leveled scheme. **Needs the PDF from Seyoon.** Until then the 6b leveled-scheme statements wait; 6a is unaffected. | **changed** (was: no new ingest) |

Effect: 6a gains the layering conversion (P6-Q14). 6b's leveled scheme uses the consecutive chain over layered circuits and cites
Gen09 once ingested. The plan section is updated to r3 accordingly.

**P6-Q19, refinement (Seyoon, 2026-11-16, same day):** Gen09 must not be a bottleneck. Seyoon sends the PDF later today, and
it affects only docstrings. Nothing waits for it.
- The 6b leveled statements proceed now, citing only ingested sources ([BV11, Thm 3.1, Def 3.6]; [BV14, Thm 2.14 first
  part, Thm 3.7]; [AP14, §5.3]) and disclosing that the key-chain construction and hybrid order are reconstructed.
- After the ingest, a docstring-only follow-up adds the [Gen09] citation. No Lean docstring cites [Gen09] before then.

## ===== briefs/lattice-gsw/phase6/issued-6b-r1/brief.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

# Claude statement job · GSW phase 6b: bootstrapping, pure and leveled FHE, security, ratio (and owner PR O2)

**Base** `3e51b5f28900db6190f1eb2e6d207d27ee15d541` (tree `b69a66a385ca3439d56af1d6b9791b5847984fde`): a
deterministic, unsigned, two-step local merge.
- **Step 1** `04947bcf35e08ed5f3a4902b2637a77482fd32d2` (tree `8eca961769fef59d5a22fd1b46dc821a614daf06`): #360's head
  `cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25` (the 6a owner-side readers with the `TreeDAG` addendum, branch
  `land/gsw-6a-readers`) merged into #359's head `d154c8830fc8ffc52671b41992e7dbef61e30959` (the 6a statements with the
  Gate 45 landing edits LE-g45 and LE-g45b, branch `land/gsw-6a-statements`, stacked on #358's head
  `a616adcac0760ab56b1b0a2a4869f4763843f9ab`, O1).
- **Step 2**, the base: step 1 merged into the records tip at staging, `036d823933c8248bd8894c7963e15dd0f1837075`
  (`cryptography/pass-shelat-ch2-4`), whose Lean is snapshot #6 (#357's merge `8060f6b7`).
  The records branch has moved since (Gate 45 round 2 filed at `5ac18f4e`, then this package), by records files only;
  its Lean is unchanged.
- Both merges are clean (`git merge-tree --write-tree`, rc 0). The base's Lean is the records tip's plus exactly the
  23 Lean files of #358, #359 and #360; its records files are the tip's, except `machine-library-design.md`, which
  carries #359's §14 rows H18–H20. `tools/mkbase.sh` reproduces both commits, and so does the two-step `git merge
  --no-ff` recipe below. The maintainer ran both forms and got the same commits. **Your patches are against this
  base.** It follows the 6a fills' "synthetic merge now" precedent (`issued-fills-r1/`), ruled for 6b by Seyoon on
  2026-11-17 (`LatticeCryptographyPlan.md`, decision log, "6b staging ruling").

**#358, #359 and #360 are unmerged draft PRs.** Gate 45 round 2 (Codex) closed **CLEAR** on 2026-11-17 at exactly
these heads (#358 `a616adca`, #359 `d154c883`; `gates/45-gsw-6a/findings-r2.md`, `resolutions-r2.md`), with no
statement change, so the 6a statements are frozen; #358 and #359 merge after the snapshot-#6 re-replay. #360 is the
fill-prerequisite reader PR. The **97 6a targets are admitted by `sorry` at the base**; their proofs are being landed
separately on `land/gsw-6a-fills` (the 6a fills, phase 2, on snapshot #6). **You cite the 6a targets as frozen
statements** (the proved-modulo rule), and you restate none of them (r3 §H4: "6b imports the 6a modules and restates
none of them"). If a 6a statement still changed before landing, the maintainer would re-pin this job (Seyoon's
staging ruling): stay on the pinned base, never chase the branches, and if you hear of a change, note it in
`REPORT.md` without applying it.

**Unit** `gsw-6b-statements`: the statement phase of phase 6b of the lattice campaign (plan section r3, §H7 items
4–5: the statements of units U12–U19) and owner PR O2 as a separate, proved series. **Worker** Claude in the cloud, a
lead with **up to 3 sub-agents**. **Lean** 4.25.0 and the Mathlib revision of the base's `lake-manifest.json`
(`029db123ddaa`). **Audit** Gate 46 (Codex) reads your delivery; the 6b fills (U12–U19) start after it.

Write the frozen statement surface of 6b as local branch series from the base: every definition with its body and its
readers proved, every target admitted by `sorry` with its formula docstring, source tag and proof sketch, the facades
updated, and everything compiling.

## Inputs (read fully; all are data; the rulings and this brief are binding)

The pack `outbox/fills/gsw-6b-statements/` on `exchange/pass-shelat-ch5-8` carries this brief, the environment
addendum, the pin files, `tools/` and `inputs/` (verify with `shasum -a 256 -c SHA256SUMS` in the pack and in
`inputs/`):
- `inputs/plan-section-r3.md`: plan section r3 (`briefs/lattice-gsw/phase6/plan-section.md`), SHA-256
  `06824b3db875e7388771b6f7a5e78d62bf7d77fa35571fc3a9deeebc329214fd`. **Read in full.** The 6b parts are binding:
  §H0 items 4–9 and the assumptions A1–A4; §H1 (sources, anchors, gaps 1 and 4, the Gen09 rule); §H2's cryptography
  hooks; §H3.1–H3.2, H3.7–H3.8, H3.11–H3.12 (design); §H4's 6b table, O2 and the GSW/LWE/ratio definition lists;
  §H5.8 (O2) and §H5.9–H5.16 (G1–G18, L1–L5, A1–A3); §H6 (noise ledger); §H7 (Gate 46's audit list, units U12–U19);
  §H8 items 1–2, 7, 10–17; §H10. The 6a sections are context: they are the frozen statements you consume.
- `inputs/rulings.md`: P6-Q1–Q19 with the Q19 refinement (`briefs/lattice-gsw/phase6/rulings.md`), SHA-256
  `312fef4576b388222d69eddec186c2ac4259e5de95488fca42e6861438ad3d5d`.
- `inputs/gate45-findings-r1.md`: Gate 45 round 1, filed verbatim (`briefs/lattice-gsw/gates/45-gsw-6a/findings-r1.md`),
  SHA-256 `dc8cd2d29b03165470cf9e943f8f185dc03cb89a576cd91e3cc9c57e60654b3c`. **G45-01: an admitted statement that
  restates a public lemma is a major**, even under a new name or behind a definition wrapper.
- `inputs/gate45-resolutions-r1.md`: how G45-01–03 were fixed (LE-g45, LE-g45b), which made #359's head `d154c883`
  (`…/gates/45-gsw-6a/resolutions-r1.md`), SHA-256 `4de570d238c38732329eee4008e496b70fdbb7a40673564f9741a48be97c92ab`.
  LE-g45 is the **proved-citation** precedent: `const_eval` stayed, proved from the public `eval_node_nil`.
- `inputs/gate45-findings-r2.md`: Gate 45 round 2, CLEAR, filed verbatim (`…/gates/45-gsw-6a/findings-r2.md`), SHA-256
  `0a7ed19136085dfe2e9b9e47ef219bde31141e5e8086dfc12b165aee35813540`: Codex accepted the move of `eval_node_nil` and the
  proved citation.
- `inputs/final-6a-r1-review.md`: the maintainer's review of the 6a statement delivery, with G6A-F01 (an undisclosed
  duplicate of `reidx`) and G6A-F03 (the reader census) and Seyoon's rulings 6a Q1–Q4
  (`…/phase6/final-6a-r1/review.md`), SHA-256 `dde685375cdb8571e2e43fe864a65a8c8b1225fffdadb88aa1cae4886513b17f`.
- `inputs/checkpoint1-6a-review.md`: the 6a statement job's checkpoint review, lesson G6A-C1-F01 (a checkpoint carries
  `src/` and its head hash) (`…/phase6/checkpoint1-6a-review.md`), SHA-256
  `5968e98ac305cdbfd92dc79812745c8d89a1d414d4c12be30da5d4cf0d7cb232`.
- `inputs/fills-final-r1-review.md`: the 6a fills' phase-1 review, with GF-F01 (an inline re-derivation of Mathlib's
  `Nat.pow_log_le_add_one`) and GF-F02 (private helpers copied across files) (`…/phase6/fills-final-r1/review.md`),
  SHA-256 `f1672720d381c5df3d5dfe1b9f8140130d98f1860cdc455e32fe9319b43c3f0e`.

On the records branch `cryptography/pass-shelat-ch2-4` at the records pin named in the dispatch prompt (all equal at the
base tip `036d8239`), with their SHA-256:
- `policy.md` (`6599b12230e3879bc0e1fb22c0376ea6201bca8b7edd79dfc55da43986f991d4`): §1 (layout, facades, *Definitions
  land with their lemmas*, *Duplication*, Rule 10), §2 (attribution), §3 (proof sketches);
- `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2, the standing rules
  (`ec3789a127a648862e7ee4b714339200a0fc8adde9538aebae254b9df4271f58`);
- `briefs/pass-shelat-ch5-8/duplication-ledger.md` (`d500c17e11005f36b65d5e414724a8fabff82c589c71c777352178b99b250cf1`),
  rows DL-54–DL-58;
- the duplication precedents: `briefs/pairings/gates/48-bb1-sim-fill/findings-r1.md`
  (`9e44113b3be5e0a3c29e402294c4fee57fe6edcff2e4599612fbf042d5f4efe4`) and `findings-r2.md`
  (`05c78ae9ea8842762fc866b61d8aa188d21636bfdf3aa4359d7756f71ceef888`);
  `briefs/pairings/gates/44-pairing-fills/findings-r1.md`
  (`48f6b28cbd04ed247a85c7315b403003bf784ec64bc434882721392bd0621180`) and `findings-r2.md`
  (`bebe099a36b8c6c144d6149404124f3b601376cd6160c647ff6d653e8f47b4af`);
- `briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py` (`fa81981add5de30d3a98b7e1614e73b17f149723e8be79558ac1a29b6fe67fbc`).

`workflow.md` on `main` at `b986b8620fc6117034462212df7070c80a79ff65` (fetch `main` by name, read with `git show`;
SHA-256 `6f986529280a265b72040576603ac3430841ececbf0ff19b685df868bd8155f9`): §2 (statement phases: sketches name their
hosts), §4.1 (*Lean parallelism*; the delivery payload).

At the base, the ingests you may cite (`blueprint/src/references/`, anchors per r3 §H1):
`brakerski-vaikuntanathan-2014-fhe.md` (`3da79813fa63acfea4a83229c46f2f8947a7a754657fac8f4d6bf1e7891e9392`),
`brakerski-vaikuntanathan-2011-fhe.md` (`f415fdbd4488316e2044e0a8e767c75b69964ff48fb6294617b35ae125177eba`),
`alperin-sheriff-peikert-2014-bootstrapping.md` (`d2605ae062162641ee40701c7592f29d69c342a64c3b4575df547f21153df868`),
`gentry-sahai-waters-2013-fhe.md` (`df0d793d8a5a952662502a6c80cb2e3dc41a7372d4ae8e26c7aa49b6219ca540`),
`peikert2016-lattice-survey.md` (`fb5c997ea6c0efc2340217c1beff8fc146f08f5d71e892b58d694907466e5955`) and
`barrington-1989-bounded-width-bp.md` (`0e14d97efe06b4c9f0e2f7672d744885b4e53fa2a3777c3694a664322620c71a`).

On `exchange/pass-shelat-ch5-8`, your starting tools: the 6a statement delivery `inbox/fills/gsw-6a-statements/`
(final `d7a9adb5b70c70c1b6fb8dc3d0aa5a60d720c1ef`; `evidence/tools/`: the seal tools `xr/` and `frozen_check.py`,
`clash_scan.py`, `scan_unfold.py`, `admissions.py`, `rowmap.py`, `sizes.py`, `sweep.py`, `controls.py`; its
`evidence/probes/` and `P0_Axioms`) and the 6a fills delivery `inbox/fills/gsw-6a-fills/` (final
`607034428468ffd88adec313eb293e3e60520f59`; `evidence/tools/lead/`: the Lean pool `poollib.py`, `pool_run.py`,
`pbuild.py`, and `dup_inventory.py`, `trace_check.py`). The GSW phase-5 statement phase's `probe/StmtDump.lean` and
`AxiomProbe.lean` (`briefs/lattice-gsw/statement-phase/evidence/stmt-gsw.zip` on the records branch) are the models
for the statement dump and the axiom probe. Copy what you use into `evidence/tools/`, adapt host paths, and record
each change in the tool's header.

**Pack contents beyond the brief** (all from git objects at the base, by `tools/`; see `README.md`): `order.txt`,
`prefix.txt`, `roots.txt`, `prefix-roots.txt`, `closures.txt`, `SOURCE-SHA256SUMS`, `base-sorries.txt`, `targets.txt`,
`pins.txt` (where every TCSlib name the r3 6b sketches cite is declared at the base; r3's own line numbers are at the 6a
issue base `f6f295a6` and many have moved) and `census.txt` (a static reader census of the foreign definitions the 6b
sketches read).

## Binding rulings (Seyoon; full text in `inputs/rulings.md` and the review inputs)

- **P6-Q1.** One phase 6; Gate 46 audits 6b and O2.
- **P6-Q7.** `decode_iff_mem_Ico`, with explicit `decodeLo`/`decodeHi`, is a published reader in the owner file
  `LWE/BitEncoding.lean`, added by owner PR O2. **It does not exist at the base** (checked across every branch), so O2
  is in this job, as O1 was in the 6a job.
- **P6-Q8.** The evaluation key: public-key GSW encryptions under the user's own `pk` of the `N` bits of `G⁻¹(t)`,
  `t = (−s, 1)` (BV11 Def 3.8); one `GSW.Parameters` record; noise `m·B`.
- **P6-Q9, P6-Q16 A.** Bootstrapping is NAND only (BV14 Def 2.13), over the 6a NAND form (`DAGGate.IsNAND`,
  `DAGCircuit.IsNANDForm`, `toNANDForm`); fan-in 1 padded to `(a, a)`, fan-in 0 to `(G, G)` (disclosed).
- **P6-Q10, P6-Q15 A.** Concrete and asymptotic forms. The concrete `WeakCircularSecure P χ D ε` is **per
  distinguisher**; the asymptotic `WeakCircularSecureFamily F` is the headline hypothesis; asymptotic IND-CPA under the
  explicit reduction-efficiency hypotheses (A4); compactness by typing, in docstrings only.
- **P6-Q11, P6-Q14 B.** The full leveled scheme: `L+1` keys in a **consecutive chain** (`evk_d` encrypts the bits of
  `s_{d−1}` under `pk_d`, `N·L` ciphertexts) over **layered** NAND circuits on the `2k` literals (6a's `layerNAND`,
  `litInput`), correctness, and IND-CPA by a top-down key hybrid from DLWE.
- **P6-Q12.** Explicit `decDepth P` and `bootNoise P β` in the correctness theorems with closed-form bounds proved
  separately; `RatioBounded F B p` in a new `LWE/Ratio.lean`; a family theorem with an explicit `PolyExpr` `pBoot`.
- **P6-Q13.** `barrington` is computable, so `fheEval` is.
- **P6-Q19 B with Seyoon's refinement.** Gen09 blocks nothing. **No docstring cites `[Gen09]`.** The leveled-scheme
  docstrings (`Leveled`, `LeveledSecurity`, A3) cite only [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part,
  Thm 3.7] and [AP14, §5.3], and carry r3 §H5.13's disclosure: "The key-chain construction and the hybrid order are
  reconstructed: no ingested passage gives them. BV11 and BV14 attribute leveled bootstrapping to Gentry's work; that
  passage will be cited here once it is ingested."
- **6a Q1 A (LE-ren).** No `TreeCircuit.rename`; reindex with the public `TreeCircuit.reidx`.
- **6b staging ruling (2026-11-17).** This base; the 6a targets as frozen statements; a re-pin if Gate 45 round 2
  changes anything (it closed CLEAR with no change).
- **Gate 45 G45-01 and the duplication standard** (G44-01, G48-01, GF-F01, GF-F02): see *Duplication* below.

## Ruling Q-6B-1 (staging question; the brief implements the recommended option)

r3's **G14** (`distAdv_fheView_le (h : WeakCircularSecure P χ D ε) : distAdv (fheView P χ false) (fheView P χ true) D ≤
ε`) is, word for word, the forward direction of `WeakCircularSecure`'s own `_iff` reader, and **A2**
(`fheView_negligible (h : WeakCircularSecureFamily F) (D) : Negligible …`) is the same for
`WeakCircularSecureFamily`. Under G45-01 neither may be an admitted target. The maintainer asked Seyoon:
- **A (recommended; implemented here).** No theorem: the readers `weakCircularSecure_iff` and
  `weakCircularSecureFamily_iff` are the statements, and the predicates' docstrings say that they are the security
  half of [BV11, Thm 3.2] and [BV14, Thm 2.14 second part]. `targets.txt` marks G14 and A2 *reader-only*.
- **B.** Keep both names as **proved citations** (`:= (weakCircularSecure_iff …).1 h`), never admitted, disclosed in
  *Overlap and reuse*, as LE-g45 kept `const_eval`.
- **C.** Keep them as r3 sketches them (admitted targets). Not recommended: G45-01 grades it a major.

A and B leave the admissions unchanged. If the dispatch prompt names a ruling other than A, follow it.

## Feasibility and size (maintainer's assessment)

Feasible as one job. Everything is statements and definitions; the only proofs are the readers (mostly `rfl` or
`Iff.rfl`), the definitions' own obligations (structure fields, `NeZero` instances, termination), the citations of
`targets.txt` and O2 (r3: 60–90 proved lines). Estimated surface: about **1,300–1,800 statement lines** in 9 new files
(8 under `GSW/`, `LWE/Ratio.lean`), O2 (about 60–90 lines in `BitEncoding.lean`) and the two facades. The heavy items
are the definitions with bodies: `select`, `homEvalPBP`, `homEvalFormula`, `decConstants`, `decryptFormula`,
`nandFormula`, `bootGate`, `fheEval` (computable through `runWith`), the leveled `levelKey`/`literalCts`/`leveledEval`
with their seed and view types, the hybrid `levelReduction`/`levelTerm`, the encodings and the A4 hypotheses. r3 §H7
projects 1,390–2,310 fill lines for U12–U19 later; every file must stay under 1,000 lines filled, so state compactly.

**Targets** (`targets.txt`, 25 r3 rows): **23 admitted targets** (24 if G17 is split into a pure and a leveled lemma),
**2 citations** (G11, L1: proved now if one step from `encrypts_encrypt`/`encrypts_keygen_encrypt`, else admitted),
**2 reader-only rows** (G14, A2; Q-6B-1), and O2's `decode_iff_mem_Ico` **proved**. Per unit: U12 3, U13 6, U14 5 + 1
citation, U15 1 (+ G14 reader-only), U16 2 + 1 citation, U17 2, U18 2 (or 3), U19 2 (+ A2 reader-only).

## Branches, series and delivery

- **Checkout.** In your own clone, fetch by name `cryptography/pass-shelat-ch2-4`, `land/gsw-6a-statements` and
  `land/gsw-6a-readers`. If a `land/` branch has moved past its pinned head, fetch `refs/pull/359/head` and
  `refs/pull/360/head`, or the pinned commits by hash; if you cannot get all three pinned commits (`d154c883…`,
  `cc05f76c…`, `036d8239…`), stop with **E-BASE**.
- **The base.** Run `bash <pack>/tools/mkbase.sh` in the clone: it must print
  `STEP1 04947bcf35e08ed5f3a4902b2637a77482fd32d2 tree 8eca961769fef59d5a22fd1b46dc821a614daf06` and
  `BASE 3e51b5f28900db6190f1eb2e6d207d27ee15d541 tree b69a66a385ca3439d56af1d6b9791b5847984fde`. Equivalently, with a
  work tree:

  ```sh
  export GIT_AUTHOR_NAME='TCSlib gsw-6b-statements staging' GIT_AUTHOR_EMAIL='staging@tcslib.invalid'
  export GIT_COMMITTER_NAME='TCSlib gsw-6b-statements staging' GIT_COMMITTER_EMAIL='staging@tcslib.invalid'
  export GIT_AUTHOR_DATE='2026-11-17T18:00:00+00:00' GIT_COMMITTER_DATE='2026-11-17T18:00:00+00:00'
  git checkout -b gsw-6b-step1 d154c8830fc8ffc52671b41992e7dbef61e30959
  git -c commit.gpgsign=false -c merge.log=false merge --no-ff --no-edit \
    -m 'gsw-6b statements base, step 1: merge #360 head cc05f76c (6a readers) into #359 head d154c883 (6a statements)' \
    cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25
  git checkout -b gsw-6b-base 036d823933c8248bd8894c7963e15dd0f1837075
  git -c commit.gpgsign=false -c merge.log=false merge --no-ff --no-edit \
    -m 'gsw-6b statements base, step 2: merge the 6a drafts (step 1) into records tip 036d8239 (snapshot #6 Lean)' \
    gsw-6b-step1
  git rev-parse HEAD HEAD^{tree} HEAD^2   # 3e51b5f2…, b69a66a3…, 04947bcf…
  ```

  If a tree or a commit differs, stop with **E-BASE**. Record the output in `REPORT.md`. The base is not delivered as a
  patch.
- **Series 1, O2** (`owner/o2-decode`, from the base): only O2 (*O2* below). Proved; no `sorry`.
- **Series 2, statements** (`stmt/gsw-6b`, from series 1's head): every 6b file and the facades. Suggested commits,
  each compiling: (1) `GSW/Branching`, `GSW/DecryptFormula`; (2) `GSW/Bootstrap`, `GSW/Circular`; (3) `GSW/Leveled`,
  `GSW/LeveledSecurity`; (4) `LWE/Ratio`, `GSW/PolyRatio`, `GSW/Asymptotic`; (5) the facades `GSW.lean` and
  `LWE.lean`.
- Keep both branches local. Commit them with `git -c commit.gpgsign=false`: the series must be **unsigned**, so that
  `git am` reproduces every hash. The maintainer opens O2 and the statement PR (stacked on O2) after review; Seyoon
  approves and merges.
- **Deliver** every checkpoint and the final only under `inbox/fills/gsw-6b-statements/` on
  `exchange/pass-shelat-ch5-8`, in the standard payload (`workflow.md` §4.1):
  - `REPORT.md` (*Report*), naming the **full hashes of both branch heads it describes**;
  - `patches/o2/` (`git format-patch <base>..owner/o2-decode`) and `patches/stmt/`
    (`git format-patch owner/o2-decode..stmt/gsw-6b`), each with a `COMMITS.tsv`: one row per commit with its hash, the
    author's name, email and date, the committer's name, email and date, and its **signing** (`none`, or the format).
    Check in a scratch clone that `git am` at the base reproduces every hash of both series, and say so;
  - `src/`: every new or changed file at the `stmt/gsw-6b` head, under its repository path; `src-o2/`:
    `TCSlib/Cryptography/LWE/BitEncoding.lean` at the `owner/o2-decode` head;
  - `evidence/`, with its manifest `evidence/SHA256SUMS` (*Evidence completeness*);
  - a top-level `SHA256SUMS` of every delivered file except itself. The delivered paths must **equal** the manifests'
    paths: nothing missing, nothing extra, no leading `./`. Check this before each push.
- **Every checkpoint is a full payload for what it claims** (lesson G6A-C1-F01): its `REPORT.md` names the head hashes,
  its `patches/` run to those heads, and its `src/` holds every file it claims compiles, with the build logs that bind
  those sources to that head. A claim without `src/` and patches is not a claim.
- **Exchange commits.** Commit on the exchange as `stmt gsw-6b: checkpoint N` and `stmt gsw-6b: final`, with
  `git -c commit.gpgsign=false`. Pull with `git -c commit.gpgsign=false pull --rebase` (BSF-F01). After the rebase and
  before the push, `git cat-file -p HEAD | grep -c gpgsig` must print `0`. **The maintainer expects unsigned commits
  throughout**; if the platform signs one anyway, disclose it in the next commit, never rewrite or force-push.
- Push only your path; never force-push; never touch another path (other fills, gates, `outbox/`, `arora-barak-ch3-4/`,
  `lwe-sis-constructions/`). **Never push a campaign branch.** If a push is refused, keep the commit and say so.

## Base and parallel work

- **Open PRs at staging** (2026-11-17): #358, #359, #360 (in your base); #355 (cleanup Stage 1 promotions, stacked on
  #347): it adds declarations to `Cryptography/Asymptotic/Adversary.lean`, which 6b imports but does not edit, and none
  of its new names collides with a 6b name of r3; #347 (DW-5) and #362 (Arora–Barak blueprint) touch no 6b path.
- **Not at the base, reserved:** the GF-W1 promotions that land with the 6a fills (`TreeCircuit.maxDepth_le_of_forall`,
  `maxFaninL_le_of_forall` in `Basic.lean`; `prefixVal_eq_of_false`, `prefixVal_testBit` in `Adder.lean`; CarrySave's
  `depth_getD_le`, `maxFanin_getD_le` made public). Declare none of these names; if 6b needs such a fact, it is a scope
  request, never a restatement.
- If any PR merges during the job, **stay on the base**; the maintainer replays at landing (`workflow.md` §6.1). At
  delivery, record `git merge-tree --write-tree` of your head with the then records tip (information only).

## Scope

**New files** (namespace `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW`, except `LWE/Ratio.lean` in
`TCSlib.Cryptography.LWE`; r3 §H4):
- `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/{Branching,DecryptFormula,Bootstrap,Circular,Leveled,
  LeveledSecurity,PolyRatio,Asymptotic}.lean`;
- `TCSlib/Cryptography/LWE/Ratio.lean`.

**Changed files:**
- `TCSlib/Cryptography/LWE/BitEncoding.lean`: O2 only (series 1).
- `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean` (facade): the eight new imports and their `## Contents`
  entries; its title and opening line may say that the folder now also covers bootstrapping and pure and leveled FHE.
- `TCSlib/Cryptography/LWE.lean` (facade): `import TCSlib.Cryptography.LWE.Ratio` and its `## Contents` entry.

`TCSlib.lean` already imports both facades' parents; it is **not** changed. No model or conversion is registered (6b
adds none), and `machine-library-design.md` is not changed: 6b consumes the registered hosts H18 (`evalWith`, in
`homEvalPBP`) and H19 (`runWith`, in `fheEval` and `leveledEval`), which name these consumers already. Each new
sketch names the host it uses (`workflow.md` §2).

**Frozen:** everything else, including every phase-5 GSW file (`Gadget`, `Noise`, `Scheme`, `Eval`, `Security`,
`Symmetric`), every other `LWE/` file, `Encoding/`, `Asymptotic/`, `Foundations/`, `Encryption/`, every 6a file and
everything #358, #359 and #360 touch, `ComputationalModels.lean`, `TCSlib.lean`, `machine-library-design.md`,
`blueprint/` and `audits/`.
- **Scope requests.** If a definition or statement needs a change to a frozen file (a reader, a promotion, an import
  that would create a cycle, a new module because a file would pass 1,000 lines), stop that line of work and ask
  Seyoon in your session, giving the file, the diff and the reason; proceed only on his approval. Record the request
  and his answer verbatim under `evidence/scope-request/` and in `REPORT.md`. Seyoon prefers routes with no frozen-file
  edit. A missing reader is never worked around by unfolding.
- **Known reader gap** (`census.txt`): `hybridPlant` (`Encryption/PublicKey/EnsembleSecurity.lean:110`) has no
  `_eq`/`_apply` reader. Your statements need not unfold it (define `levelReduction`/`levelTerm` through
  `hybridPlant` and phase-5 `reduction` as terms, as r3 §H5.14 says); list the gap in the census with the proposed
  one-line reader. It is the 6b analogue of 6a's `GadgetCorrect` gap, for an owner-side reader before the L4 fill.

## What to write

**For every new file:** the policy header (copyright block, precise imports, the three `set_option` lines, a module
docstring with `# Title`, `## Main definitions`, `## Main results`, `## References` with full citations of every tag
used: [BV14], [BV11], [AP14], [GSW13], [Pei16], [Bar89] as cited). Lines of at most 100 characters (Python `len`); every
file under 1,000 lines, target 150–600 filled (r3 §H7's estimates). No `@[simp]`, no global attribute. Identifiers
use the Greek `μ` (U+03BC), never the micro sign.

**Definitions.** Every r3 §H4 definition gets its body now, total and, where r3 says so, computable (`select`,
`homEvalPBP`, `homEvalFormula`, `bootNAND`, `bootGate`, `fheEval`, `leveledEval`; `fheEvalCircuit` and
`leveledEvalCircuit` are computable bodies around `toNANDForm`/`layerNAND`). Each new public `def` lands with its
readers, **proved**: `_eq` by `rfl` where that holds, case lemmas covering every input, `_iff` for predicates
(`Iff.rfl`), non-simp `simps` for structures and pairs (phase-5 `Security.lean` is the model:
`@[simps! (config := { isSimp := false }) fst snd]`). Each reader's docstring states its formula. Types that r3 names
loosely (`PublicKey P`, `Secret P`, `Seeds P χ`, `FheView P`, `LevelCoins P L`, `LeveledSeeds P χ L`,
`LeveledView P L`) are reducible abbreviations or definitions with readers, built from phase 5's types
(`Security.lean`'s view and seed types, `Regev.keygen`'s seed). Where a definition must carry a proof (an instance
such as `NeZero P.columns`, a structure field), prove it now; if you cannot, state it as a **target** lemma that the
definition cites, and list every such definition in the axiom report. Termination proofs are never admitted.

**Expected `sorryAx` dependents** (not targets): `fheEvalCircuit` reaches `sorryAx` through 6a's N2
(`nandGadget_correct`, via `toNANDForm`), and `leveledEvalCircuit` through N2 and N12–N13 (`layerGates_acyclic`,
`layerOutput_lt`, via `layerNAND`): Gate 45 r1 lists exactly `toNANDForm`, `toNANDForm_eq`, `layerNAND`,
`layerNAND_gates`, `layerNAND_output` as the 6a non-target constants that reach `sorryAx`. Any further 6b definition
that reaches `sorryAx` must be named, with the admitted declarations it goes through, in the dependency trace.

**Targets.** Every `target` row of `targets.txt` is a `theorem` whose body is `sorry`, with a docstring that:
1. opens with the statement in words, its formula written out (arguments in Lean order);
2. gives the `[TAG, location, anchor]` tag from r3 §H5 (anchors per r3 §H1), or says "Glue" for technical lemmas;
3. states every deviation from the source (r3 §H8 item 17: BV14's coordinate 1 against `σ 0`; the fan-in padding;
   literal inputs and layering; the carry-save tree inside `decryptFormula`; the reconstructed key chain and hybrid
   order; worst case against probabilistic, r3 §H8 item 10; the public output level; the evaluation key under the
   user's own `pk`);
4. ends with a `**Proof sketch.**` paragraph naming the steps a fill will follow (policy §3), with the readers, host
   lemmas and phase-5/6a lemmas it will use (by name; `pins.txt` gives where they are). The sketch is the fill's plan;
   a target whose sketch you cannot write is not ready.

**Citations** (`targets.txt` kind `citation`: G11, L1) are stated, and **proved now** when the proof is one step from
the public lemma after reading the file's own definition (LE-g45's `const_eval`); otherwise admitted. `REPORT.md` says
which, and *Overlap and reuse* names the public lemma.

**Names and shapes** are fixed now. Adjust a name, binder or argument order where Lean requires it, keeping the
meaning; record each change in `REPORT.md` § *Statement changes against r3* with the reason. A change of meaning (a
weaker or stronger statement, a new hypothesis) needs a probe that shows r3's form false or unprovable, and goes to
Seyoon as a question in the report; never silently. Settle every constant marked *(fix)* (`decDepth_le`,
`bootNoise_le`, `pBoot`) by hand and with `decide`/`#eval` checks, and record the derivation; the ledger of r3 §H6 is
the target, with **no depth term linear in `ℓ`** (r3 §H3.3, §H8 item 1).

**File-specific notes** (r3 §H5 has the sketches; these are the known pitfalls):
- **Branching (G1–G3).** `select P C U V := mul P (gadget P − C) U + mul P C V` (fresh selector on the left, Gate 41).
  `homEvalPBP P B cts V := B.evalWith (select P) cts V` consumes the H18 host; G2 is stated for
  `B.IsPermutation`, start `Pi.single s₀ (gadget P)`, noise `B.length * (2 * (P.columns * β))`. `homEvalFormula`
  runs `barrington c σ` for one fixed five-cycle (`sigma1` is fine) and reads **coordinate `σ 0`**, not BV14's
  coordinate 1 (C16 `barrington_yield_zero`; G6A-F11, Gate 45 r1 "C16 reading": coordinate `0` would encode the
  complement). Barrington needs `[NeZero k]`.
- **DecryptFormula (G5–G8).** `keyBits P s := decomposeVec P (secretVector P s)` (the bits `evk` encrypts, P6-Q8);
  `decConstants P C : Fin P.columns → ZMod q` is `Gᵀ` applied to `decryptColumn P C` (r3 §H3.2);
  `decryptFormula P C := modSumInterval (fun i => (decConstants P C i).val) q (decodeLo P.lwe) (decodeHi P.lwe)` (F9
  with O2: `modSumInterval_eval` needs `a i < q`, `lo ≤ hi ≤ q`); `nandFormula P C₁ C₂ :=
  (and2 (decryptFormula P C₁) (decryptFormula P C₂)).neg`, **one key block** (r3 G7). `decDepth P` is built from
  `modSumDepth` (F10). The formulas' input count `P.columns` needs `NeZero` for Barrington; `P.lwe.modulus ≥ 2` and
  `modulus ≤ 2 ^ width` give `width ≥ 1`.
- **Bootstrap (G9–G13, G18).** `bootNoise P β = 4 ^ (decDepth P + 1) * (2 * (P.columns * β))`; G9 in the
  key-switching form (`evk` under `t'`, decryptions under `s`, no hypothesis on `C₁, C₂`); `bootGate` pads fan-in 1 to
  `(a, a)` and fan-in 0 to `(G, G)` and is the `runWith` gate function of `fheEval` (H19); `fheEvalCircuit P evk Cc hC
  cts := fheEval P evk (Cc.toNANDForm hC) cts`; `evalKey P pk s R i := encrypt P pk (keyBits P s i) (R i)` (P6-Q8).
  Compactness by typing goes in the docstrings of `fheEval`, `fheEvalCircuit` (and `leveledEval`), no theorem.
- **Circular (G14–G15).** `fheView P χ μ` samples honest keys and returns `(pk, evalKey …, encrypt pk μ R)`
  [BV14, §2.5, p007-b001]. `WeakCircularSecure P χ D ε` per distinguisher (P6-Q15 A), with its `_iff` reader; its
  docstring explains why per distinguisher (an unbounded function recovers `s`). G14 per Q-6B-1. **G15** is stated
  over the evk-dropped projection of `fheView` (the view `(pk, encrypt pk μ R)` read off `fheView`'s seeds), so that its
  content is the transport of phase-5 `distAdv_encrypt_le` (`Security.lean:248`) along the coin regrouping; stated over
  `realView` it would restate that theorem (G45-01).
- **Leveled (L1–L3).** r3 §H5.13 exactly: `levelKey … (d : Fin L)` encrypts `keyBits P (ss d.castSucc)` under
  `pks d.succ`; `literalCts P cts := Fin.append cts (fun j => homNot P [cts j])` in `litInput`'s order;
  `leveledEval` runs `runWith` over a layered NAND circuit on `k + k` inputs, a gate at level `d ≥ 1` (its `depthAt`) is
  `bootGate` with `levelKey ⟨d − 1, _⟩`; `leveledEvalCircuit := leveledEval … ((Cc.toNANDForm hC).layerNAND)
  (literalCts P cts)` with `[NeZero k]`. Decryption uses the public output level `Cc.depth` (disclosed; BV11 Def 3.6's
  `Dec` is level-agnostic). The P6-Q19 disclosure in every docstring of this file.
- **LeveledSecurity (L4–L5).** The view of the `L+1` public keys, the `L` level keys and `Enc_{pk_0}(μ)`; the
  hybrid top-down (`d = L, …, 1`, then the phase-5 challenge step); `levelReduction` composes `hybridPlant` with
  phase-5 `reduction`, and `levelTerm` is its two DLWE advantages plus `2 · (N · Regev.extractionError)` (the shape of
  `distAdv_encrypt_le`'s right-hand side); r3 §H8 item 12: each step's messages are random bits of `s_{d−1}`, fixed
  inside the reduction's coins. Reuse `distAdv_multi_le_sum` and `abs_sub_le_sum_hybrids`, never a local hybrid lemma.
- **Ratio and PolyRatio (G16–G17).** `LWE.Family.RatioBounded F B p` with `_iff`; `Parameters.ofFamily F κ` with
  `lwe := F.parameters κ`, `width := F.residueBits.eval κ`, `modulus_le := F.modulus_le_pow κ`, non-simp `simps`
  (type-level Rule 10: `(ofFamily F κ).lwe` against `F.parameters κ` only through those readers); `pBoot` an explicit
  `PolyExpr`.
- **Asymptotic (A1–A3).** Encodings from `LWE.encodeChallenge` and `Encoding.Modular.encodeMatrix` (with `_eq` and
  `_length` readers); `WeakCircularSecureFamily`, `ReductionEfficient`, `LeveledReductionEfficient` exactly in r3
  §H5.16's quantifier structure (domination, not construction; the advice remark), each with `_iff`. A1 and A3 from the
  unchanged `LWE.DLWEAssumption` (`dlweAssumption_iff`, `Family.advantageAt_eq`; `Pseudorandom/Generators/LWE/
  Basic.lean`'s `pseudorandom_under_DLWE` is a model of the reading). `negligible_polyExpr_mul` exists twice
  (`Asymptotic/EnsemblesLemmas.lean:377`, `SecureComputation/ComposeSecurity/Probability.lean:110`) and as
  `Negligible.polyExpr_mul` (`Asymptotic/ReductionSupport.lean:267`): cite one in the sketches (r3: `EnsemblesLemmas`)
  and add no fourth.

## O2 (series 1; owner-side, proved)

In `TCSlib/Cryptography/LWE/BitEncoding.lean` (namespace `TCSlib.Cryptography.LWE.BitEncoding`), after `decode_eq`,
add r3 §H5.8:
- `def decodeLo (P : Parameters) : ℕ` with `decodeLo_eq : decodeLo P = P.modulus / 2 / 2 + 1`;
- `def decodeHi (P : Parameters) : ℕ` with `decodeHi_eq : decodeHi P = (P.modulus + P.modulus / 2 + 1) / 2`;
- `theorem decode_iff_mem_Ico (P : Parameters) (v : ZMod P.modulus) :
  decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P`, **proved** (r3: 60–90 lines), reading `decode`,
  `distance` and `codepoint` through `decode_eq`, `distance_eq`, `codepoint_eq` and Mathlib's `ZMod.valMinAbs` lemmas.
  `tools/o2check.py` finds 0 mismatches for every residue of every `2 ≤ q ≤ 2000`.

Each with a formula docstring ("Glue for the file's `decode`", r3), and a `**Proof sketch.**` on the theorem. Update the
module docstring's `## Main definitions`/`## Main results`. Nothing else in the file changes. Evidence: decls2 exactly
5 ADDED, 0 CHANGED, 0 REMOVED; the frozen check of `BitEncoding.lean` (insertions only); axioms standard only; the
seal of `BitEncoding.lean` with a paired control on `decodeLo`/`decodeHi`; the sweep of its 18 `DOWN` modules.

## Multi-agent work (up to 3 sub-agents) and Lean parallelism

- **The lead owns the job:** both branches, every commit, the integration, the sweep, the root build, the seals, the
  delivery and `REPORT.md`. Only the lead commits on `owner/o2-decode` and `stmt/gsw-6b`, runs `lake`, fetches the cache
  and pushes.
- **Suggested split** (disjoint files; record any other split in `REPORT.md`). The files depend on each other's
  definitions (statements, not proofs), so order matters: the lead does O2, `Branching`, `DecryptFormula`,
  `Bootstrap` and `Circular` first (checkpoint 1); then sub-agent `lev` writes `Leveled` and `LeveledSecurity`, and
  sub-agent `asy` writes `LWE/Ratio`, `PolyRatio` and `Asymptotic` (its `LeveledReductionEfficient` waits for `lev`'s
  `levelReduction`); sub-agent `probe` writes the probes and the census, clash and duplication scans under
  `evidence/`. Sub-agents may draft from r3 before checkpoint 1 but compile only from the lead's commits.
- **No cross-file copies** (GF-F02): a definition or lemma that two files need is stated once, public, with its
  reader, in the upstream file, and imported; never a `private` copy in each.
- Each sub-agent owns its files exclusively, works in its own git worktree with its own TCSlib olean tree and
  `.lake/packages` linked to the lead's, and hands its files to the lead as patches. Sub-agent logs go under
  `evidence/subagents/<name>/`; `REPORT.md` records who wrote what.
- **Lean pool** (addendum, *Adaptation*; `workflow.md` §4.1): all agents share one memory-sized pool of Lean processes
  (a counting semaphore), at most `nproc` and keeping about 2 GB or 15% of memory available, in dependency order,
  never two processes on one module or one output file. Record the pool size, its changes and peak memory.

## Proof discipline for the proofs this job does write (readers, obligations, citations, O2)

- **Rule 10 (readers only; policy §1).** Read other files' definitions only through their published readers and
  lemmas, including generated matchers and projections. Core and Mathlib definitions may reduce in a `rfl`, `decide` or
  `show` step but are never passed to `simp`, `rw` or `unfold`. Each new file may read its own definitions directly;
  the new files are foreign to each other and to every other file.
- **Duplication (binding; policy §1; G45-01, G44-01, G48-01, GF-F01, GF-F02).** **Search TCSlib, core, Batteries and
  Mathlib before stating any definition, helper or target that might already exist**: by name, by `exact?`/`apply?`
  on its statement in a scratch probe, and by grep for its conclusion's shape. Then:
  - **No restatement of a public lemma.** A target, citation or helper whose statement is a public lemma's (exactly,
    up to argument order, or behind a new definition that unfolds to the old one) is not written: cite the existing
    lemma. An admitted restatement is a major (G45-01), disclosed or not; disclosure is not acceptance (G44-01).
  - **No re-derivation.** An inline proof of a Mathlib or TCSlib fact is a major (G48-01, GF-F01): use the lemma.
  - Specializations to a new definition are allowed as *citations* (above) and disclosed in *Overlap and reuse*.
  - Known near-relatives to check and disclose: phase-5 `eval_encrypts`/`decrypt_keygen_eval` (the leveled
    multiplicative evaluation, a different scheme from `fheEval`); `homGate`/`homNot` (reuse `homNot` for the negative
    literals, never a copy); `encrypts_encrypt`/`encrypts_keygen_encrypt` (G11, L1); `distAdv_encrypt_le` (G15);
    `view`/`realView`/`reduction` (reuse in `fheView` and the hybrid); `Regev.extractionError`; `decode_codepoint_add`
    (O2 must not re-prove it); `vecMul_secretVector_augmented`, `gadget_mulVec_decomposeVec` (G5);
    `Encrypts.nand` (the leveled multiplicative NAND, r3 §H2, not bootstrapping's); the three `polyExpr_mul` copies.
- **Docstrings and sketches (policy §2–§3).** Every public declaration has a docstring stating it in words with its
  formula. Every proof of about 20 lines or more has a `**Proof sketch.**`. Never fabricate a quotation, location or
  anchor; glue says "Glue".

## Checks and evidence

Run Python as `python3 -I`. Never run `lake build` or an unfiltered `lake exe cache get`; compile each module with
`scripts/lean_check_tree.sh` (the addendum). Count errors in both forms (`^\S+\.lean:\d+:\d+: error[:(]`) in every
log, and keep every raw log.

1. **Bootstrap and sweep.** Bootstrap `prefix.txt` (288 modules) at the base: rc 0, 0 errors, and exactly the `sorry`
   warnings of `base-sorries.txt` restricted to it. Insert the new modules after their imports (facades after their
   children; `evidence/build/order-final.txt`). At the O2 head and at the final head, rebuild every module whose source
   differs from its olean's, then check every `DOWN` module of `closures.txt` (18) and the 9 new ones, each rc 0 and 0
   errors in both forms. Bind every checked source to `git show HEAD` (`evidence/build/summary.txt`: module, rc, errors
   in both forms, `sorry` warnings, source SHA-256).
2. **Root build.** Build the rest of `order.txt` (1,443 modules) and the root `TCSlib` last, from the final head:
   `evidence/build/root/summary.txt`. If the host cannot finish, follow the addendum (marked incomplete, not a failure).
3. **Statements.** `python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py . <base> <files…>` over every new
   and changed Lean file (ADDED/CHANGED/REMOVED against the base: only ADDED, and in `BitEncoding.lean` exactly O2's
   five), and a `StmtDump` probe printing every new constant with its full name and type. `REPORT.md` maps every row of
   `targets.txt` to its declarations (kind as delivered: target, citation proved, citation admitted, reader-only), and
   lists every definition with its readers.
4. **Admissions, exact.** At the O2 head: exactly `base-sorries.txt` (289 declarations in 55 modules). At the final:
   exactly those plus the delivered targets, **23 to 26 declarations in the 8 new GSW files** (`targets.txt`, *Counts*),
   none in `LWE/Ratio.lean`, `BitEncoding.lean` or a facade. A script compares the root build's `sorry` warnings (or,
   if the root is incomplete, the sweep's plus the syntactic scan of `tools/graph.py`) with that list name for name.
5. **Axioms.** Print the axioms of every declaration and auxiliary constant of the new and changed modules. Expect
   `propext`, `Classical.choice`, `Quot.sound` only, except `sorryAx` in exactly the targets and in the definitions and
   readers that reach an admitted proof (expected: `fheEvalCircuit` through N2; `leveledEvalCircuit` through N2, N12,
   N13; their readers and anything stated through them, named). Run a **dependency trace** that walks each constant's
   closure and names, for every constant reaching `sorryAx`, the admitted declarations through which it does (6a
   targets or 6b targets). O2's constants: standard axioms only.
6. **Rule 10.**
   - **Seals** A and B, strict and coe (**coe-A canonical**), with `-DmaxErrors=0`, over the full TCSlib import closure,
     of every new file, of `BitEncoding.lean` at the O2 head and the final head, and of the two facades. Report each
     seal's request count and every failing declaration, attributed by its raw log; **no failing declaration**. Use
     chunking (`SEAL_CHUNK`) if a run overflows.
   - **Paired controls on every new owner** (the 9 new files and `BitEncoding.lean` for O2): a negative control that
     reads one of its new definitions from another file by `rfl`/`Iff.rfl`/`unfold` (passes unsealed, fails sealed
     exactly once) and a positive control through its published reader (passes sealed). Pretest unsealed; strict and
     coe both. A file that defines nothing gets no pair, and the report says so.
   - **Notation, never sealed:** reducible abbreviations (`Parameters.columns`, `Ciphertext`, the new type
     abbreviations), `PolyExpr.eval`, projection coercions, the `FinDist` coercion (DW-10 Q3).
   - **Explicit-unfold scan** over the new and changed files: 0 foreign.
   - **Reader census** (G6A-F03): for every foreign definition a definition body or a target's sketch reads, its
     reader (`path:line`) or MISSING with the proposed one-line reader. `census.txt` is the staging census (static;
     confirm each entry and add what it misses). Expected MISSING: `hybridPlant`. Every MISSING reader is listed in
     `REPORT.md` as a fill prerequisite for Seyoon (6a's Q3 precedent), never worked around.
7. **Probes** (under `evidence/probes/`, outside the library, against the final tree; kernel `decide` or `rfl` where the
   kernel can reduce, otherwise `#eval` output recorded as evidence, never as a proof; never `native_decide`). One probe
   for each statement that could be wrong, on toy parameters (for example `n = 1`, `q ∈ {4, 5, 8}`, `ℓ = 3`):
   - P1 *selector*: `select` on noise-free encryptions of bits gives `(1 − b)·u + b·v`; G1's noise bound on small
     error vectors.
   - P2 *PBP and formula*: `homEvalPBP` on a permutation program and `homEvalFormula` on a depth-2 formula, noise-free:
     coordinate `σ 0` encrypts the formula's value (and coordinate 0 its complement), on every input.
   - P3 *O2*: `decode_iff_mem_Ico` by kernel `decide` for every `q < 64` (and `#eval` beyond).
   - P4 *decryption formula*: `decryptFormula P C` on `keyBits P s` equals `decrypt P s C` for every `s` and sampled
     `C`; `nandFormula`; `decConstants` against G5's sum.
   - P5 *bootstrapping*: `bootNAND` and `fheEval` noise-free on an XOR circuit in NAND form, including fan-in 1 and 0
     gates (the padding).
   - P6 *leveled*: `literalCts`, `leveledEval` and `leveledEvalCircuit` on the XOR and odd-gap circuits of 6a's probe P9
     with noise-free keys: the output decrypts under the key of the circuit's depth.
   - P7 *constants*: `decDepth_le`, `bootNoise_le` and `pBoot` numerically over a range of `(n, q, ℓ)`; no term linear
     in `ℓ` in `decDepth`.
   - P8 *types*: every asymptotic statement instantiated at a sample `LWE.Family` elaborates; `ofFamily`'s readers.
8. **Frozen-file check.** A `python3 -I` script that extracts every declaration of each changed existing Lean file at
   base and final and compares headers and whole definitions byte for byte, allowing only O2's insertions in
   `BitEncoding.lean` and the imports and docstring in the two facades; with controls (one altered character reports
   exactly one difference; one deleted reader reports exactly one removal). `git diff --stat <base>` lists only the
   9 new files and the 3 changed ones. Output under `evidence/headers/`.
9. **Lint.** `python3 -I scripts/style_lint.py <new and changed Lean files>`: 0 findings (0 in the three changed files
   at the base). `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and final; the
   maintainer's run at the base: **92 FAIL / 104 WARN over 529 files** (`AdvancedEncryption/Homomorphic` 0 / 0 over
   7; `LWE` 0 / 1 over 9, the pre-existing `DLWEAssumption` check-8 WARN). Diff the line sets: no new FAIL line, and
   no new WARN line except one you disclose and justify.
10. **File sizes.** Lines and maximum width of every new and changed file, at both heads, with a `python3 -I` script,
    against r3 §H7's fill estimates (every file must stay under 1,000 lines filled).
11. **Name-clash and shadow scans.** (a) No new full name, public or private (namespaces resolved), is already declared
    in `TCSlib/` or `audits/` at the base, or in #355's head `d3c7cb00092ad5913904654d922f30fc7d5fce4a`, or is a GF-W1
    reserved name. (b) List every new short name that exists elsewhere (`pins.txt` shows several: `encrypt`, `view`,
    `realView`, `reduction`, `decrypt_eq`). (c) Show that no unqualified use in a `DOWN` module changes its resolution.
12. **Reuse and overlap** (`REPORT.md` § *Overlap and reuse*), with the searches you ran: for every new declaration that
    restates, specializes or re-proves existing material, its nearest relative (`path:line`), the relation and why it
    is not reused; confirm or correct each r3 §H2 cryptography finding and every near-relative listed under
    *Duplication*. Any exact restatement found is removed before delivery, not disclosed.
13. **Reproduction.** `git am` of both patch series at the base, in a scratch clone with `COMMITS.tsv`'s committer data,
    reproduces every hash; `src/` and `src-o2/` equal the heads' files byte for byte.

**Checkpoints** (at least one mid-way): checkpoint 1 is O2 complete (its series, checks 1, 3–6, 8 for it) with
`Branching`, `DecryptFormula`, `Bootstrap` and `Circular` compiled, delivered with `src/`, both patch series and the
head hashes; the final has everything.

If a probe shows an r3 statement false, stop that line, keep r3's form out of the branch, and put the counterexample
and your proposed statement in `REPORT.md` as a question for Seyoon. Do not weaken a statement silently.

## Sources and citations

- Cite only ingested passages: [BV14], [BV11], [AP14], [GSW13], [Pei16], [Bar89] at the base, with the anchors of
  r3 §H1. **Never fabricate** a quotation, location or anchor. **No `[Gen09]`** anywhere (P6-Q19 B); the leveled
  disclosure text instead. Glue declarations carry no tag and say "Glue".
- Record point (r3 §H1): BV14's "[BV11, Lemma 4.1]" (Prop 3.4) is **Lemma 4.5** in the BV11 version held; cite
  [BV11, Lemma 4.5] and note BV14's numbering.
- Do not add reference files, edit `blueprint/` or run `scripts/sources.py`.

## Report

`REPORT.md` gives: the base (`mkbase.sh` output or the merge reproduction), the records tip seen at delivery and the
merge-tree with it, both heads (full hashes) and every commit; the preflight figures, the pool and peak memory, and
who wrote what; the statement list (check 3) with the `targets.txt` row map; the definitions and their readers;
§ *Statement changes against r3*; the constants settled with their derivations; Q-6B-1 as applied; the builds (checks
1–2); admissions (check 4); axioms and the dependency trace (check 5); the Rule 10 seals, controls and reader census
(check 6); the probes (check 7); the frozen-file check; lint; sizes; the clash scans; § *Overlap and reuse*;
§ *Scope requests* (none, or each with Seyoon's answer); the reproduction; questions for Seyoon, if any, numbered
`G6B-W1`, … with the recommended option first; the evidence, with its manifest.

### Evidence completeness

Every file that `evidence/SHA256SUMS` names is delivered: build, sweep and root logs with their summaries, the
admission comparison, decls2 output, the `StmtDump`, the axiom prints and the trace, seal and control sources,
manifests, request records and raw logs, the unfold scan, the census, the probes and their outputs, the frozen check
with its controls, lint outputs, the size script and output, the clash and shadow scans, the duplication searches, the
reproduction log, sub-agent logs, `pool.log` and the tools used. If the evidence is too large for one commit, deliver
it in several commits or numbered ZIP parts, each with an entry list; leave nothing out for size.

## Blockers: stop and report

- **E-RES (environment).** The addendum's preflight or cache rules fail. Stop and report the numbers.
- **E-BASE.** The pinned commits cannot be fetched, or `mkbase.sh` (or the merge recipe) gives another tree or commit.
- **E-SCOPE (frozen files).** A definition or statement needs a reader, promotion, import or module the *Scope* does
  not permit. Stop that line and ask Seyoon (*Scope*); continue the other files meanwhile.
- **E-ROUTE (statement).** An r3 statement looks false, vacuous or unstatable as sketched, or its only form restates a
  public lemma. State the exact issue with a counterexample probe or the existing lemma, and propose a form.
- **How to report.** Push a checkpoint `stmt gsw-6b: checkpoint N (blocked: <code>)` whose `REPORT.md` opens with the
  blocker, the exact obligation or request, and the logs. Keep everything that already passes. Never work around a
  blocker by weakening a statement, editing a frozen file without approval, unfolding a foreign definition, or using a
  private stand-in.

The maintainer replays both series on the then records tip, reviews them (static, then a merged-tree replay), and
opens O2 and the statement PR for Seyoon; Gate 46 follows.

**Ready to dispatch**

## ===== briefs/lattice-gsw/phase6/issued-6b-r1/targets.txt (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

# gsw-6b-statements: the statement rows of plan section r3 for 6b (§H5.8 O2, §H5.9-§H5.16), per unit (§H7 units table).
# Columns: unit<TAB>row<TAB>file (under TCSlib/, new unless marked)<TAB>r3 name(s), as sketched<TAB>kind<TAB>note.
# kind: target = a theorem admitted by `sorry` with its formula docstring, tag and proof sketch; proved = O2, proved,
# never admitted; citation = state it and prove it now when its proof is one step from a public lemma after reading
# the file's own definition (the LE-g45 precedent for const_eval), else admit it; either way REPORT says which;
# reader-only = no theorem of its own: the definition's `_iff` reader is the statement (ruling Q-6B-1 A, default).
# Names and shapes are fixed at the statement phase (brief, *Names and shapes*); REPORT maps every row to its final
# declaration(s). Admissions at the final = base-sorries.txt (289 in 55 modules) + exactly the delivered targets.
O2	G4	Cryptography/LWE/BitEncoding.lean (existing; O2 series)	decode_iff_mem_Ico	proved	with defs decodeLo, decodeHi and the readers decodeLo_eq, decodeHi_eq (r3 §H5.8; tools/o2check.py: 0 mismatches for 2 <= q <= 2000)
U12	G1	Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean	Encrypts.select	target	selector step, additive 2N·β (BV14 Eq. (5)-(6), Lemma 3.6; AP14 Eq. (4.1), Lemma 4.1)
U12	G2	Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean	encrypts_homEvalPBP	target	permutation program, noise length·2N·β (BV14 Lemma 3.6, worst case)
U12	G3	Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean	encrypts_homEvalFormula	target	Barrington then G2, output coordinate σ 0 (BV14 Thm 3.5 with Lemma 3.6; Pei16 §6.1.3)
U13	G5	Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean	vecMul_secretVector_eq_sum	target	binary subset sum of the public constants Gᵀc (AP14 §5.1; Pei16 §5.4.3)
U13	G6	Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean	decryptFormula_eval	target	the decryption formula from F9 and O2 (BV14 Prop 3.4; BV11 Lemma 4.5)
U13	G7	Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean	nandFormula_eval	target	BV14's f_{c1,c2}, one key block (BV14 Def 2.13; BV11 Def 3.7)
U13	G8	Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean	depth_nandFormula_le	target	depth ≤ decDepth P + 1 (BV14 Lemma 4.4)
U13	G8	Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean	maxFanin_nandFormula_le	target	fan-in two
U13	G8	Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean	decDepth_le	target	closed form, constants (fix) at the statement phase
U14	G9	Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean	encrypts_bootNAND	target	key-switching form, no hypothesis on C1, C2 (BV14 Thm 2.14, Lemma 4.4; BV11 Thm 3.1)
U14	G10	Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean	decrypt_fheEval	target	pure FHE, NAND form, every depth; padding (a, a) and (G, G) (BV14 Thm 2.14 second part; BV11 Thm 3.2, Def 3.5)
U14	G18	Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean	decrypt_fheEvalCircuit	target	every fan-in-2 circuit through N3-N4 (BV14 Thm 2.14; BV11 Def 3.5)
U14	G11	Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean	encrypts_evalKey	citation	specializes phase-5 encrypts_encrypt (Scheme.lean:161) to evalKey (BV11 Def 3.8; BV14 Lemma 4.4)
U14	G12	Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean	decrypt_keygen_fheEvalCircuit	target	honest keys, every circuit (BV14 Thm 3.7, worst case)
U14	G13	Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean	bootNoise_le	target	closed form of bootNoise, constants (fix)
U15	G14	Cryptography/AdvancedEncryption/Homomorphic/GSW/Circular.lean	distAdv_fheView_le	reader-only	restates weakCircularSecure_iff (Q-6B-1); under Q-6B-1 B a proved citation, never admitted
U15	G15	Cryptography/AdvancedEncryption/Homomorphic/GSW/Circular.lean	distAdv_fheView_noEvk_le	target	over the evk-dropped projection of fheView, not realView (else it restates Security.lean:248 distAdv_encrypt_le); GSW13 §3.2; AP14 §5.3
U16	L1	Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean	encrypts_levelKey	citation	specializes encrypts_encrypt / encrypts_keygen_encrypt (Scheme.lean:161/186) to levelKey; reconstruction disclosure (P6-Q19 B)
U16	L2	Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean	encrypts_leveledEval	target	layered NAND form, depth ≤ L, every vertex at level d under s_d (BV14 Thm 2.14 first part; BV11 Thm 3.1, Def 3.6)
U16	L3	Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean	decrypt_keygen_leveledEvalCircuit	target	honest keys, every fan-in-2 circuit of NAND depth ≤ L, public output level (BV14 Thm 3.7)
U17	L4	Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean	distAdv_levelHybrid_le	target	one level, N positions, via distAdv_multi_le_sum over distAdv_encrypt_le (AP14 §5.3; GSW13 §3.2, Lemma 1)
U17	L5	Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean	distAdv_leveledView_le	target	IND-CPA of leveled GSW-FHE from DLWE, top-down hybrid (BV14 Thm 2.14 first part, Thm 3.7; BV11 Thm 3.1)
U18	G16	Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean	bootRatio_le_poly	target	explicit PolyExpr pBoot (BV14 Thm 3.7, worst-case analogue); LWE/Ratio.lean holds RatioBounded with its reader only
U18	G17	Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean	decrypt_fheEval_of_ratio	target	pure and leveled correctness at a polynomial ratio (G12, L3); one lemma per scheme if that reads better (BV14 §3.4)
U19	A1	Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean	indCPA_of_dlweAssumption	target	asymptotic IND-CPA of public-key GSW, evk-free view, from DLWEAssumption and ReductionEfficient (GSW13 §3.2; BV11 Def 3.1)
U19	A2	Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean	fheView_negligible	reader-only	restates weakCircularSecureFamily_iff (Q-6B-1); under Q-6B-1 B a proved citation, never admitted
U19	A3	Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean	leveledINDCPA_of_dlweAssumption	target	asymptotic IND-CPA of leveled GSW-FHE from DLWE and LeveledReductionEfficient (BV14 Thm 3.7; BV11 Thm 3.1)
# Counts (rows; lemmas). U12: 3; 3 targets. U13: 4; 6 targets. U14: 6; 5 targets + 1 citation. U15: 2; 1 target + 1
# reader-only. U16: 3; 2 targets + 1 citation. U17: 2; 2 targets. U18: 2; 2 targets (3 if G17 is split). U19: 3;
# 2 targets + 1 reader-only. O2: 1 proved. Total: 25 r3 rows; 23 targets (24 if G17 is split), 2 citations (each
# admitted only if its proof is not one step), 2 reader-only rows (Q-6B-1). Expected admissions at the final: 289 +
# 23 to 26 declarations in 63 modules (the 55 at the base + the 8 new files that hold targets; LWE/Ratio holds none).

## ===== briefs/lattice-gsw/phase6/issued-6b-r1/census.txt (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

gadget	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean:90	gadget_apply:95 gadget_mulVec_decomposeVec:164 gadget_mul_decompose:185
decomposeVec	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean:112	decomposeVec_eq:117 decomposeVec_block_eq_false:200
lift	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean:138	lift_apply:142
mul	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Noise.lean:64	mul_eq:68 Encrypts.mul_bit:247 Encrypts.mul_le:259
Encrypts	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Noise.lean:97	encrypts_iff:105 encrypts_gadget:118 encrypts_zero:128 encrypts_chain:296
secretVector	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean:66	secretVector_eq:71
encrypt	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean:102	encrypt_eq:109
halfVector	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean:118	halfVector_eq:122 halfVector_eq_zero_of_ne_last:201
decryptColumn	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean:129	decryptColumn_eq:134
decrypt	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean:141	decrypt_eq:146 decrypt_eq_decode_errorSum:213 decrypt_of_encrypts:272 decrypt_of_encrypts_dyadic:293 decrypt_keygen_encrypt:354
homNot	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean:78	homNot_eq:82
homGate	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean:96	homGate_eq:103 homGate_encrypts:181
eval	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean:122	eval_eq:127 eval_encrypts:250
view	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean:59	view_eq:68
realView	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean:77	realView_eq:86
reduction	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean:113	reduction_eq:122
decode	TCSlib/Cryptography/LWE/BitEncoding.lean:108	decode_eq:112 decode_codepoint_add:123
codepoint	TCSlib/Cryptography/LWE/BitEncoding.lean:42	codepoint_eq:46
sample	TCSlib/Cryptography/LWE/Basic.lean:101	sample_fst:109 sample_snd:116
noisyValues	TCSlib/Cryptography/LWE/Basic.lean:59	noisyValues_apply:67
Bounded	TCSlib/Cryptography/LWE/Noise.lean:57	bounded_iff:61
decisionAdvantage	TCSlib/Cryptography/LWE/Experiments.lean:44	decisionAdvantage_eq:53
encodeChallenge	TCSlib/Cryptography/LWE/Encoding.lean:42	encodeChallenge_eq:49 encodeChallenge_length:60 encodeChallenge_injective:72
advantageAt	TCSlib/Cryptography/LWE/Assumption.lean:117	advantageAt_eq:124
DLWEAssumption	TCSlib/Cryptography/LWE/Assumption.lean:136	dlweAssumption_iff:141
keygen	TCSlib/Cryptography/Encryption/PublicKey/Regev/Basic.lean:45	keygen_fst:53 keygen_snd:59
decrypt	TCSlib/Cryptography/Encryption/PublicKey/Regev/Basic.lean:89	decrypt_eq:94 decrypt_encrypt:146 decrypt_keygen_encrypt:161
augmented	TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean:166	augmented_eq:173 augmented_bijective:182
extractionError	TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean:227	extractionError_eq:232
encodeMatrix	TCSlib/Cryptography/Encoding/Modular.lean:65	encodeMatrix_eq:71 encodeMatrix_length:89 encodeMatrix_injective:126
encodeVector	TCSlib/Cryptography/Encoding/Modular.lean:51	encodeVector_eq:57 encodeVector_length:79 encodeVector_injective:101
acceptProb	TCSlib/Cryptography/Foundations/Experiments.lean:72	acceptProb_def:98 acceptProb_comp_equiv:107 acceptProb_eq_uexp_sum_map:137
distAdv	TCSlib/Cryptography/Foundations/Experiments.lean:78	distAdv_def:102 distAdv_le_statDist:173
Negligible	TCSlib/Cryptography/Foundations/Negligible.lean:57	negligible_iff:62 negligible_two_pow_neg:153 negligible_zero:169
NUPPT.distinguisherL	TCSlib/Cryptography/Asymptotic/Adversary.lean:351	_root_.Complexity.NUPPT.distinguisherL_eq:356
hybridPlant	TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean:110	MISSING
yield	TCSlib/Complexity/BranchingPrograms/Defs.lean:151	yield_eq:155 yield_append:224 yield_nil:232 yield_conj:242 yield_complementLast:271
IsPermutation	TCSlib/Complexity/BranchingPrograms/Defs.lean:98,161,378	Instr.isPermutation_iff:103 Instr.isPermutation_ofPerm:117 isPermutation_iff:288 isPermutation_iff:382
evalWith	TCSlib/Complexity/BranchingPrograms/Eval.lean:83	evalWith_eq:89 evalWith_nil:99 evalWith_append:108 evalWith_rel:143 evalWith_single:167
Instr.stepWith	TCSlib/Complexity/BranchingPrograms/Eval.lean:65	Instr.stepWith_apply:73 Instr.stepWith_of_isPermutation:124
IsFiveCycle	TCSlib/Complexity/BranchingPrograms/Barrington.lean:83	isFiveCycle_iff:87 isFiveCycle_sigma1:331 isFiveCycle_sigma2:338 isFiveCycle_commutator:352
barrington	TCSlib/Complexity/BranchingPrograms/Barrington.lean:259	barrington_lit_true:278 barrington_lit_false:284 barrington_node_true_nil:290 barrington_node_false_nil:296 barrington_node_singleton:301 barrington_node_true_cons_cons:307 barrington_node_false_cons_cons:316 barrington_recognizes:417 barrington_length_le:430 barrington_length_pos:441 barrington_yield_zero:463
TreeCircuit.neg	TCSlib/Complexity/CircuitComplexity/FormulaArith/Combinators.lean:272	TreeCircuit.neg_lit:285 TreeCircuit.neg_node:295 TreeCircuit.neg_eval:308
TreeCircuit.and2	TCSlib/Complexity/CircuitComplexity/FormulaArith/Combinators.lean:452	TreeCircuit.and2_eq:457 TreeCircuit.and2_eval:507
modSumInterval	TCSlib/Complexity/CircuitComplexity/FormulaArith/ModSum.lean:82	modSumInterval_eq:94 modSumInterval_eval:131
modSumDepth	TCSlib/Complexity/CircuitComplexity/FormulaArith/ModSum.lean:142	modSumDepth_eq:147 modSumDepth_le:179
csaLevels	TCSlib/Complexity/CircuitComplexity/FormulaArith/CarrySave.lean:200	csaLevels_of_le_two:204 csaLevels_of_two_lt:213 csaLevels_le:292
DAGGate.IsNAND	TCSlib/Complexity/CircuitComplexity/NANDForm.lean:83	DAGGate.isNAND_iff:86
DAGCircuit.IsNANDForm	TCSlib/Complexity/CircuitComplexity/NANDForm.lean:95	DAGCircuit.isNANDForm_iff:98
DAGCircuit.toNANDForm	TCSlib/Complexity/CircuitComplexity/NANDForm.lean:234	DAGCircuit.toNANDForm_eq:240 DAGCircuit.toNANDForm_eval:252 DAGCircuit.toNANDForm_isNANDForm:260 DAGCircuit.toNANDForm_depth_le:268 DAGCircuit.toNANDForm_size_le:279
DAGCircuit.IsLayered	TCSlib/Complexity/CircuitComplexity/NANDLayering.lean:105	DAGCircuit.isLayered_iff:111
litInput	TCSlib/Complexity/CircuitComplexity/NANDLayering.lean:124	litInput_eq:127 litInput_castAdd:130 litInput_natAdd:134
DAGCircuit.layerNAND	TCSlib/Complexity/CircuitComplexity/NANDLayering.lean:315	DAGCircuit.layerNAND_eval:336 DAGCircuit.layerNAND_isLayered:349 DAGCircuit.layerNAND_isNANDForm:359 DAGCircuit.layerNAND_depth:367 DAGCircuit.layerNAND_size_le:383
TreeCircuit.eval	TCSlib/Complexity/CircuitComplexity/Basic.lean:110,148,388,394	Lit.eval_eq:114 TreeCircuit.eval_lit:154 TreeCircuit.eval_node_true_iff:159 TreeCircuit.eval_node_false_iff:167
TreeCircuit.depth	TCSlib/Complexity/CircuitComplexity/Basic.lean:180,433,439	TreeCircuit.depth_lit:217 TreeCircuit.depth_node:229 TreeCircuit.depth_le_maxDepth:265
TreeCircuit.maxFanin	TCSlib/Complexity/CircuitComplexity/Basic.lean:198	TreeCircuit.maxFanin_lit:225 TreeCircuit.maxFanin_node:239 TreeCircuit.maxFanin_le_maxFaninL:273 TreeCircuit.maxFanin_le_size:301
DAGGate.eval	TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:123,488	eval_eq:131 DAGGate.eval_congr:249 DAGGate.eval_remap:318 eval_eq:492
runWith	TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:149	runWith_nil:158 runWith_cons:162 runWith_append:166 runWith_singleton:171 runWith_eq_append:183 runWith_getD_of_lt:192 runWith_getD_last:198 runWith_getD_gate:207 runWith_getD_take:221 runWith_remap_rel:346 runWith_rel:637
values	TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:480	values_eq:484 values_getD_input:548 values_getD_gate:559
eval	TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:123,488	eval_eq:131 DAGGate.eval_congr:249 DAGGate.eval_remap:318 eval_eq:492
depths	TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:497	depths_eq:613
depthAt	TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:501	depthAt_input:554 depthAt_gate:569 depthAt_eq:617
depth	TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:139,505	DAGGate.depth_congr:259 DAGGate.depth_eq:583 depth_eq:621
size	TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean:508	size_eq:511

## ===== pr376-description.md (this pack) =====

Owner-side PR **O2** of GSW phase 6b (P6-Q7, r3 §H5.8): the decoding interval of `LWE/BitEncoding.lean`. It adds `decodeLo` and `decodeHi` with their `rfl` readers `decodeLo_eq` and `decodeHi_eq`, and `decode_iff_mem_Ico`, proved: `decode P v ↔ decodeLo P ≤ v.val < decodeHi P`. The 6b statement PR (#377) is stacked on this one.

## Scope and commit
- **Head:** `04ba2446f541c39dd02aefaa97a9eb31dbbda748`, a maintainer-signed cherry-pick (`-S`) of the worker's `5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd` (delivery `inbox/fills/gsw-6b-statements/` at exchange `3b340824dde77433b2135a3c8d20c7ed194cf18c`). The worker's message and trailers are kept.
- **Base:** the records tip `38123ccbebef878cd25dd2d2761de1b40ba7e421`, which is Lean-equal to olean snapshot #10's T `cf6a2266` (#366 and #368 merged; all 6a targets proved). The tree `8b615e06` equals `git merge-tree` of the tip and `5bd5ada5`.
- **Range-diff** against the delivered series: 1/1 `=`.
- **Files:** `TCSlib/Cryptography/LWE/BitEncoding.lean` only, insertions only (+58/−0): two module-docstring entries and the five declarations above. Each has a formula docstring and "Glue"; the theorem has a proof sketch, rewriting both distances with Mathlib's `ZMod.valMinAbs_natAbs_eq_min`.

## Rulings
- **P6-Q7:** O2 lands owner-side before the statements. It reproduces hash for hash on the issued base (phase 1).
- **Q-6B-W1, W2, W3** (accepted as delivered), **Q-6B-F1** (LE-6b1..3) and **Q-6B-F2** (`decDepth_le` stays admitted) apply to the statement PR. This PR has no landing edit.

## Checks (maintainer phase 2: this head replayed on olean snapshot #10; `briefs/lattice-gsw/phase6/final-6b-r1/phase2.md`, R1)
- **Build:** the tree was a `cp -al` copy of snapshot #10 with the Mathlib overlay. BitEncoding and its 18 downstream modules rebuilt, 1428 were reused. All 19 have rc 0, 0 `error:` and 0 `error(`, and 0 `sorry`. The 3 warnings are pre-existing and equal to the delivery's O2 sweep logs. The state check gives 1447/1447 OK, and the 19 rebuilt oleans have link count 1. Snapshot #10 rehashed 0/0/0 before, after and at the end.
- **Admissions:** 192 at the tip and 192 here (+0). The per-module census is identical.
- **decls2** (tip against the head): **5 ADDED** (`decodeLo`, `decodeHi`, `decodeLo_eq`, `decodeHi_eq`, `decode_iff_mem_Ico`), 0 CHANGED, 0 REMOVED.
- **Axioms:** all 24 BitEncoding constants are standard. `decodeLo`, `decodeHi` and their readers use none; `decode_iff_mem_Ico` uses `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx`.
- **Rule 10** on `BitEncoding`:
  - seals strict A/B and coe A/B: 9/9/9/9 requests, 0 errors, install and EOF records `requested = verified`;
  - the delivery's 5 paired controls on `decodeLo`, run unchanged: ALL_OK. The unsealed body read gives 0 errors. Sealed, strict and coe, the negative gives exactly 1 error, in the example, and the reader 0;
  - explicit-unfold scan: 54 items, 0 foreign.
- **Lint:** `campaign_style_lint TCSlib/Cryptography --check8b` FAIL/WARN lines are identical to the tip's (92/103). `style_lint` finds 0 problems.
- **Output map** (Mathlib excluded): 1478 entries, `e1d210bf…`. Against snapshot #10, only `LWE/BitEncoding` differs.

## Disclosed
- The inline step `hsub`, the two-case value of `v − ⌊q/2⌋`, has no `ZMod` lemma in Mathlib. Phase 1 checked this.
- The issued `o2check.py` gives 0 mismatches for 2 ≤ q ≤ 2000. The delivery's kernel `decide` probe covers q ≤ 63.

## Review and merge order
- **Verdict:** **ACCEPT** (`briefs/lattice-gsw/phase6/final-6b-r1/review.md`, phases 1 and 2). **Gate 46 (Codex) audits both** this PR and the stacked statement PR (#377).
- **Merge order:** this PR merges **first**. Then the statement PR, stacked on `land/gsw-6b-o2`, is retargeted to `cryptography/pass-shelat-ch2-4`.
- **Snapshot:** on merge, if the merge's Lean paths equal tree `8b615e06`, `olean-replay-6b-o2` can be adopted (map `e1d210bf…`).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== pr377-description.md (this pack) =====

The statement PR of GSW phase 6b: bootstrapping, circular security and the leveled chain. It contains **24 admitted targets**, each with a formula docstring, a source tag and a `**Proof sketch.**`, and the definitions and readers they need. It is stacked on PR O2 (#376, `land/gsw-6b-o2`) and is retargeted to `cryptography/pass-shelat-ch2-4` once O2 merges.

## Scope
- **New modules (9):**
  - `LWE/Ratio.lean`;
  - under `AdvancedEncryption/Homomorphic/GSW/`: `Branching` (G1–G3), `DecryptFormula` (G5–G8), `Bootstrap` (G9–G13, G18), `Circular` (G14–G15), `Leveled` (L1–L3), `LeveledSecurity` (L4–L5), `PolyRatio` (G16–G17) and `Asymptotic` (A1–A3).
- **Changed:** the facades `GSW.lean` and `LWE.lean`, which only add imports and contents lines.
- **Size:** 12 files from the tip, +2202/−1, counting O2. No file is over 362 lines or over 99 characters wide.
- **Targets (24):**
  - Branching 3, DecryptFormula 6, Bootstrap 5, Circular 1, Leveled 2, LeveledSecurity 2, PolyRatio 3 and Asymptotic 2.
  - They are exactly the 23 target rows of `issued-6b-r1/targets.txt`, plus G17 split into `decrypt_fheEval_of_ratio` and `decrypt_leveledEval_of_ratio`, which `targets.txt` allows.
  - G11 `encrypts_evalKey` and L1 `encrypts_levelKey` are proved citations.
  - G14 and A2 are reader-only (ruling Q-6B-1 A): `weakCircularSecure_iff` and `weakCircularSecureFamily_iff`.

## Commits
- Five maintainer-signed cherry-picks (`-S`) of the worker's `7a814546..8f92fe7d` (delivery `inbox/fills/gsw-6b-statements/`, exchange `3b340824dde77433b2135a3c8d20c7ed194cf18c`), which keep the worker's messages:
  - `47aae69d` Branching and DecryptFormula;
  - `c10e0d3e` Bootstrap and Circular;
  - `80366e7f` Leveled and LeveledSecurity;
  - `52f52dc7` Ratio, PolyRatio and Asymptotic;
  - `75c683b2` facades.
- Range-diff against the delivered series: **5/5 `=`**. The tree of `75c683b2` equals `git merge-tree` of the tip and `8f92fe7d` (`22349e8e`).
- **`680be9fa45a9cf5deeb7a59820e8e86aaaa4f068`**: one signed landing-edit commit. It applies LE-6b1, LE-6b2 and LE-6b3 byte-identical to `briefs/lattice-gsw/phase6/final-6b-r1/landing-edits-proposed.diff` (5 files, +17/−21).
- **`7563734a8badba842223e0687c719b3b4692e9d2`** (head, tree `c56db4c4`): one signed commit, **LE-g46**, from the Gate 46 pre-dispatch sweep (4 files, +63/−27; below).

## Landing edits and rulings
- **LE-6b1** (G6B-F01, F09; docstrings). This base contains #366 and #368, so the following prose is stale and is corrected:
  - **DecryptFormula**, G6 `decryptFormula_eval` sketch: `decrypt_eq_decode_dotProduct` is no longer called "**MISSING** at the base … lands owner-side before this fill". It is named as the owner-side reader in `GSW/Scheme.lean` (#368, ruling Q-C1).
  - **Bootstrap**, `fheEvalCircuit`: the sentence "While 6a's N2 (`nandGadget_correct`) is admitted, `sorryAx` reaches this definition …" is dropped, because #366 proves N2.
  - **Leveled**, `leveledEvalCircuit`: the same sentence for N2, N12 and N13 is dropped.
  - **LeveledSecurity**, L4 `distAdv_levelHybrid_le` sketch: names the reader `hybridPlant_eq` (#368) for the planted position.
  - A scan of the 12 files finds no other passage that calls `decrypt_eq_decode_dotProduct` or the `hybridPlant` reader missing, or that calls 6a admitted. Outside the series, `Scheme.lean` and `EnsembleSecurity.lean` were already corrected by LE-g50e.
- **LE-6b2** (G6B-F02, F03; docstrings):
  - PolyRatio's constant is exactly `2^70`; r3 drafted `c < 2^70` with the factor `4`.
  - `Leveled` names its extra citations, [BV14, Def 2.12, §3.3] and [Bar89, Thm 1], for compactness and the literal inputs.
  - `LeveledSecurity` adds [BV14, §2.5] to its disclosed list.
- **LE-6b3** (G6B-F04; proof only): `Parameters.neZero_columns` now goes through core `Nat.one_lt_two_pow_iff` instead of the `pow_zero` case contradiction. **It compiles, so it is kept.** The comment-stripped diff of the commit is exactly this proof. The other four files are comment-strip identical, with mutation controls caught.
- **Rulings (Seyoon, 2026-11-18):**
  - **Q-6B-W1** A: G16 uses the factor 8, so `pBoot`'s constant is `2^70`. r3's factor 4 fails G17 at `q = 4y + 1`.
  - **Q-6B-W2** A: `LeveledReductionEfficient` includes the challenge reductions.
  - **Q-6B-W3** A: the μ-dependent `levelTerm` and the two-chain L5 bound.
  - **Q-6B-F1** A: apply LE-6b1, LE-6b2 and LE-6b3.
  - **Q-6B-F2** A: `decDepth_le` stays an admitted target.
  - **Q-6B-1** A: G14 and A2 are reader-only.
  - **Q-C1**: `decrypt_eq_decode_dotProduct` lives owner-side (landed in #368).
- **LE-g46** (rulings of 2026-11-18 on the Gate 46 sweep, `briefs/lattice-gsw/gates/46-gsw-6b/dup-sweep.md`):
  - **S1 / DL-61, proof only.** `GSW.encodeFheView_length` and `GSW.encodeLeveledView_length` (`Asymptotic.lean`) no longer re-derive inline the length of a flatten of constant-length blocks (`List.length_flatten`, `List.ofFn_comp'`, `List.ofFn_const`, `List.sum_replicate_nat`). They apply the public `TCSlib.Cryptography.length_flatten_map_const` (`Foundations/BitLists.lean`) after Mathlib's `List.ofFn_eq_map`, with core's `List.length_finRange`. Statements and docstrings are unchanged; the comment-stripped diff of `Asymptotic.lean` is exactly the two proofs.
  - **[Gen09] citations, docs only.** The Gentry thesis passages were ingested on 2026-11-16 (records `bdcadd85`, `blueprint/src/references/gentry-2009-fhe-thesis.md`). The sentences "no ingested passage gives them … will be cited here once it is ingested" in `Leveled` (module docstring and `levelKey`), `LeveledSecurity`, `PolyRatio` and `Asymptotic` are replaced by the citations: the key chain [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003], its reverse order (p056-b002; Gentry's level `i` is level `L − i` here), the layered circuits (p057-b001), correctness [Gen09, Thm 4.2.1, p059-b001] and the hybrid [Gen09, Thm 4.2.3 and its proof, pp. 50–51, p060-b001, p061-b001], with the remaining deviations (zeros instead of a fresh key's bits, position hybrids, DLWE steps, phase 5's challenge step). Each file's References gains [Gen09]. `Leveled`, `LeveledSecurity` and `PolyRatio` are comment-strip identical to `680be9fa`, with mutation controls caught.

## Checks (maintainer phase 2: the head replayed on R1 = tip × O2, from olean snapshot #10; `briefs/lattice-gsw/phase6/final-6b-r1/phase2.md`, R2)
- **Build:**
  - The tree was a `cp -al` copy of R1. 14 modules were rebuilt (the 9 new ones, `LWE`, `GSW`, `Homomorphic`, `AdvancedEncryption` and the root) and 1442 were reused.
  - All 14 have rc 0, 0 `error:` and 0 `error(`. The only warnings are the 24 `declaration uses 'sorry'`.
  - The state check gives 1456/1456 OK, and the rebuilt oleans have link count 1.
  - Snapshot #10 rehashed 0/0/0 before, after R1, after R2 and at the end.
- **Admissions:** 192 at the tip, 192 at R1, **216** at R2 (+24, in 8 modules). Every `sorry` warning maps to a target, and the match with the 24 targets is EXACT.
- **decls2** (tip against the head): **136 ADDED, 0 CHANGED, 0 REMOVED**, the same as phase 1 apart from line numbers. The landing-edit commit changes no header (0/0/0 against `75c683b2`).
- **Axioms** (the delivery's `AxiomProbe.lean`, unchanged):
  - 175 constants. The only non-standard axiom is `sorryAx`, which is **in exactly the 24 targets**, each tracing only itself.
  - **`fheEvalCircuit`, `fheEvalCircuit_eq`, `leveledEvalCircuit` and `leveledEvalCircuit_eq` are now standard** (`propext`, `Classical.choice`, `Quot.sound`), because 6a is fully proved.
  - Against the delivery's log, the only other change is LE-6b3's. `neZero_columns` drops `Quot.sound`, and its auxiliary `_proof_1` disappears; with it, `levelMsgs._proof_1` and `levelAssemble._proof_1`, which use `NeZero.ne P.columns`, drop `Quot.sound` too.
- **Rule 10** (owners: the 9 new modules, both facades and `BitEncoding`):
  - **Seals, strict A/B and coe A/B:** 48 probes, **0 errors**, install and EOF `requested = verified`. Requests per owner: Ratio 947/948/946/947, Branching 200, DecryptFormula 381/381/380/380, Bootstrap 445/445/444/444, Circular 465/465/464/464, Leveled 480/480/479/479, LeveledSecurity 1562/1563/1561/1562, PolyRatio 1395/1396/1394/1395, Asymptotic 1654/1655/1653/1654, `GSW` 1663/1664/1662/1663, `LWE` 966/967/965/966, BitEncoding 9.
  - The request sets differ from the delivery's only by closure drift since its base: 17 names from modules the tip changed (6a fills, `BitLists`, `IterateFind`), and 4 `IterateFind` matcher names that no longer exist.
  - **Paired controls** (`mkctl_g6b.py`: the delivery's 10 rows with their statements verbatim): in both strict and coe, 28 probes, 70 sealed negatives, each failing exactly once, 70 positives with 0 failures, and 140 unsealed controls with 0 errors. **ALL_OK** in both. All 10 rows are exercised.
  - **The delivery's own 50 control files** (unchanged):
    - 34/50 OK;
    - the 16 sealed files of `Ratio`, `PolyRatio`, `LeveledSecurity` and `Asymptotic` stop at harness install. Their baked request sets name the 4 `IterateFind` matchers that are absent at this tip;
    - with only those 4 entries (and the expected count) removed, all 16 are OK: 16/16, with negatives failing exactly once in the example.
  - **Explicit-unfold scan:** 101 items (91 THEOREM, 5 OWNED_DEFINITION, the file's own `bootGate`/`levelGate`, and 5 LOCAL), **0 foreign**.
- **Lint:** the `campaign_style_lint TCSlib/Cryptography --check8b` FAIL/WARN lines are identical to the tip's (92/103 over 540 files). `style_lint` gives 0 findings in the 12 files.
- **Output map** (Mathlib excluded): 1487 entries, `52ed7825…`.

## LE-g46 recheck (`briefs/lattice-gsw/gates/46-gsw-6b/le-g46.md`)
- **Replay** on `olean-replay-6b-stmt-g46`, a `cp -al` copy of R2: 8 modules rebuilt (`Leveled`, `LeveledSecurity`, `PolyRatio`, `Asymptotic`, `GSW`, `Homomorphic`, `AdvancedEncryption`, root), 1448 reused. All rc 0, 0 `error:`/`error(`; the `sorry` warnings are exactly the same 24 targets (EXACT; only line numbers shift). State check 1456/1456 OK; rebuilt oleans link count 1. Against R2 only the 4 edited oleans change (docstrings are stored in oleans). Snapshot #10 and R2 rehash 0/0/0. Output map `65ca0263…`.
- **Admissions 216**, per module equal to R2. **decls2** `680be9fa` → head: 0 ADDED, 0 CHANGED, 0 REMOVED.
- **Axioms:** the two lemmas still use `[propext, Quot.sound]`; their dependency closures grow from 913/914 to 1009 constants (they now reach `length_flatten_map_const`, `List.ofFn_eq_map`, `List.length_finRange`). No declaration uses either lemma. The census has 174 constants: the only change is the dropped auxiliary `encodeLeveledView_length._simp_1_1`; `sorryAx` is in exactly the 24 targets.
- **Canonical coe-A** on the 4 edited owners: 0 errors; request sets equal R2's (Leveled 479, LeveledSecurity 1561, PolyRatio 1394, Asymptotic 1653). Asymptotic stores 25 constants instead of 26 (the dropped auxiliary).
- **Lint:** `campaign_style_lint --check8b` FAIL/WARN identical (92/103 over 540 files; only the 4 line-count INFO lines change); `style_lint` 0 findings in the 12 files.

## Disclosed
- The phase-1 infos stand:
  - G6B-F05: `decDepth_le` weakens F10's `modSumDepth_le` and stays admitted;
  - G6B-F06: probe coverage is partial (P2c, P5b, P6, P4 kernel);
  - G6B-F07: Bootstrap, LeveledSecurity and Asymptotic project above 600 lines at fill time, all under 1,000;
  - G6B-F08: process notes;
  - G6B-F09: the census names `hybridPlant_apply`, but the landed reader is `hybridPlant_eq`.
- The worker's 22 statement deviations from r3 are in its REPORT §5.
- The P6-Q19 B disclosure in the leveled module docstrings now cites [Gen09] for the key chain and the hybrid order (LE-g46) and states the remaining deviations.
- The root coe-A seal was not re-run. The root file is unchanged and owns no declaration, and both changed facades were sealed in all four variants.

## Review
- **Verdict:** **ACCEPT WITH LANDING EDITS**, applied (`briefs/lattice-gsw/phase6/final-6b-r1/review.md`, phases 1 and 2).
- **Gate 46 (Codex) audits both** this PR and PR O2 (#376). Its pre-dispatch sweep found S1, fixed by LE-g46.
- **Merge order:** O2 first, then this PR, retargeted to the records branch. On merge, `olean-replay-6b-stmt-g46` is adoptable if the merge's Lean paths equal tree `c56db4c4` (the head's tree; LE-g46). `olean-replay-6b-stmt` (tree `956fc086`) is superseded for this PR.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== verification.zip:records/extracts/decision-log-lattice.md (this pack) =====

# Extract: LatticeCryptographyPlan.md decision-log rows from the 6b staging ruling on (records 9ae6b909305f868f51f5cc05787c66e4d336bf74, lines 567-596; re-staged after LE-g46)

| 2026-11-17 | **6b staging ruling (Seyoon): stage the 6b statement job now**, based on #359 (`d154c883`) × #360 (`cc05f76c`) as frozen 6a statements, as for the 6a fills, with a re-pin if Gate 45 round 2 changes anything. Package `phase6/issued-6b-r1/` (job `gsw-6b-statements`, U12–U19 and O2) is in preparation. In parallel, 6a fills phase 2 builds `land/gsw-6a-fills` on snapshot #6 with LE-gf1..4 and the #360 addendum. | 6b staging |
| 2026-11-17 | **Gate 45 round 2 (Codex): CLEAR**, 0/0/0/0; #358 CLEAR and #359 CLEAR; G45-01..03 closed (`gates/45-gsw-6a/findings-r2.md`, `resolutions-r2.md`). Codex judged the move of `eval_node_nil` into `Combinators` acceptable and confirmed the carry-forward. **Gate 45 is closed.** Merge conditions: #358 then #359, after the snapshot-#6 re-replay (running); mark ready when it passes. | G45 closed |
| 2026-11-17 | **gsw-6b-statements staged** (`phase6/issued-6b-r1/`; records pin `e913abe5`, dispatch `3a6ef33a`, exchange `32e54c43`, 25/25 + 8/8). The base `3e51b5f2` (tree `b69a66a3`) is the tip `036d8239` (Lean = snapshot #6) × (#359 `d154c883` × #360 `cc05f76c`); `tools/mkbase.sh` and the merge recipe agree. **O2 is still needed** (`decode_iff_mem_Ico`, `decodeLo`/`decodeHi`) and goes in as its own proved series, checked for moduli 2–2000. There are 23 admitted targets over U12–U19, plus G11 and L1 as citations (proved if one step). The brief adds the no-restatement rule (G45-01), no cross-file private copies (GF-F02), and `src/` on every checkpoint. G15 is stated over `fheView` (over `realView` it would restate `distAdv_encrypt_le`). Reader census: `hybridPlant` (`EnsembleSecurity.lean:110`) has no reader and needs an owner-side reader before the L4 fill. **Q-6B-1 ruling (Seyoon): reader-only.** G14 and A2 get no theorem of their own; `weakCircularSecure_iff`/`weakCircularSecureFamily_iff` are the statements, cited to [BV11, Thm 3.2] and [BV14, Thm 2.14]. | 6b staged |
| 2026-11-17 | **gsw-6b-statements dispatched (Seyoon)** to an external Claude worker: exchange `32e54c43`, records pin `e913abe5`, base `3e51b5f2`. Deliveries are watched under `inbox/fills/gsw-6b-statements/` (checkpoint 1: O2 plus Branching/DecryptFormula/Bootstrap/Circular). Gate 46 follows the final. | 6b out |
| 2026-11-17 | **6a re-replay on snapshot #6: PASS, but not adoptable** (`final-6a-r1/phase2.md` § "Re-replay on snapshot #6", zip `81c11830…`). R1' = tip × #358 = `f7247ea3` (9/9 rc 0, state 1434 OK). R2' = R1' × #359 = `901bf528` (20/20 rc 0, 97 `sorry`, state 1445 OK). All rebuilt oleans are byte-identical to the #5/LE-g45b references, and the axiom logs are byte-identical. coe-A: 4 + 16 owners and Hierarchy match (TreeNCAC 2, Hierarchy 2 pre-existing). Root: 14,082 requests, 0 errors, +8 names, all from #357. Lint unchanged. #347/#355 merged during the run, and their paths reach `CircuitComplexity`, `ComputationalModels` and the root, so #358/#359 re-replay once more on snapshot #7. That run is small: 3 aggregates plus root seals, and 17 of the 20 modules are reused byte-identically. Disk incident: another job's export dropped free disk to 43 MB, so the statement seals were aborted and re-run from scratch, with the aborted run kept in the evidence. | 6a re-replay #6 |
| 2026-11-17 | **Ownership (Seyoon):** the lattice campaign's open issues are this maintainer's responsibility. DL-54 (move `TreeCircuit.reidx`/`reidx_eval`/`reidx_depth` into `Complexity/…/Combinators`) is scheduled after the 6a landing merges, as a small owner PR. | DL-54 ours |
| 2026-11-17 | **gsw-6b-statements checkpoint 1 delivered** (exchange `1e0647b9`, 18:37). The maintainer's static checkpoint review is running (`phase6/checkpoint1-6b-review.md`). | 6b C1 in |
| 2026-11-17 | **6a fills phase 2: PASS; draft PR #366** (`land/gsw-6a-fills` `ccca6f80`, on tip `036d8239`, which is Lean-equal to snapshot #6; `fills-final-r1/phase2.md`, zip `68d89dff…`; `review.md` final verdict **ACCEPT**). 19 signed first-parent commits: merges of #358, #359 and #360; the #360 addendum (4 promotions, LE-gf3 part 1); in-house U1/U2, U3, U8 (LE-g45's `const_eval` kept) and U6; the worker's 7 cherry-picks (range-diff 7/7 `=`); then LE-gf1, LE-gf3 part 2 (14 private copies deleted), LE-gf2 and LE-gf4 (it compiles, so it is kept). **All 98 6a targets are proved, with 0 `sorry` in the 13 6a modules.** Library admissions 192. Standard axioms, and no `sorryAx` reaches anything. Rule 10: 0 new failures, controls ALL_OK, 0 new foreign unfolds. This also provides #360's full downstream replay. The branch predates the Stage 1 merge, so it re-replays on snapshot #7 before merge. Next: Gate 50 (the 6a fills gate) on #366. | #366 |
| 2026-11-17 | **gsw-6b-statements checkpoint 1 review: PROCEED WITH NOTES** (`phase6/checkpoint1-6b-review.md`). Base and both series reproduce (O2 `dd84941f`, stmt `57815173`). O2 is proved and matches r3 (0 mismatches up to q = 600). The four statement files have 15 targets with sketches and tags; G11 is proved and G14 is reader-only. No restatement and no cross-file copies. **G6B-C1-F01 (major, fix before final):** O2's `habs` re-proves Mathlib's `ZMod.valMinAbs_natAbs_eq_min`. F02 (minor): G15's sketch should name `uprob_fst`. F03: the G6 fill needs the Regev-residual step, which is private in `GSW/Scheme.lean`. **Q-C1 ruling (Seyoon): an owner-side lemma before the fill.** A public `decrypt_eq_decode_dotProduct` in `Scheme.lean`, promoted from the private proof's first step, lands with the `hybridPlant` reader before the 6b fills; the statement job lists it as MISSING in its census. Worker feedback is relayed via Seyoon. | 6b C1 reviewed |
| 2026-11-17 | **6b checkpoint-1 feedback relayed (Seyoon)** to the gsw-6b-statements worker: fix O2's `habs` (use `ZMod.valMinAbs_natAbs_eq_min`); G15's sketch names `uprob_fst`; list `decrypt_eq_decode_dotProduct` as MISSING in the census (Q-C1, owner-side); the admissions comparison must reach the new modules. | 6b C1 feedback |
| 2026-11-17 | **6b owner prerequisites: draft PR #368** (`land/gsw-6b-owner-prereqs` `1953898b` on tip `55f55371`, Lean = snapshot #7; `phase6/owner-prereqs-6b/evidence.zip` `77620ab8…`). New `decrypt_eq_decode_dotProduct` in `GSW/Scheme.lean`, promoted from step 1 of the private `decrypt_eq_decode_errorSum` (proof body only). New `hybridPlant_eq` reader in `Encryption/PublicKey/EnsembleSecurity.lean` (`rfl`). decls2 2/0/0. Replay of 67 modules on a copy of #7: rc 0, state OK, #7 0/0/0. Admissions 192. Standard axioms. coe-A Scheme 101/0, EnsembleSecurity 1268/6 (pre-existing). Lint unchanged. Its gate is pending Seyoon's choice. | #368 |
| 2026-11-17 | **#368 gating (Seyoon): fold into Gate 50**, with the 6a landing #366. Gate 50 is staged once #366's snapshot-#7 re-replay passes. | #368 → G50 |
| 2026-11-17 | **#366 brought onto snapshot #7 + #365: PASS** (`fills-final-r1/phase2.md` § "Re-replay on snapshot #7", zip `1799ff74…`). Head `93ae671e` (tree `c8ba8961`) has two signed merges of the tip (`e4d77a5e` at Lean = #7, then `93ae671e` adding #365). The 6a diff is byte-equal to phase 2's. Replay `olean-replay-6a-land7`: 564 + 22 modules rc 0, state 1447 OK, #7 0/0/0. The 256 modules with unchanged keys are byte-equal. 0 `sorry` in 6a. Admissions 192. Axiom log byte-equal (98 targets OK, no `sorryAx`). coe-A on 22 owners identical to phase 2 (pre-existing failures only). decls2 289/1/0 as phase 2. Lint as phase 2. Map `11d9fbfd…`; adoptable at a merge whose Lean equals `c8ba8961`. Next: snapshot #8 (#365) adoption, then Gate 50 on #366 + #368. | #366 on #7 |
| 2026-11-17 | **Gate 50 pre-dispatch sweep ruling (Seyoon): fix now in #366.** The sweep stopped staging on three unledgered items, all in our code. **U1:** in-house U8's `depth_subst_le`/`maxFanin_subst_le` redo inductions that #366's public `maxDepth_le_of_forall`/`maxFaninL_le_of_forall` give. **U2:** TreeNCAC's private `maxDepth_map_le`/`maxFaninL_map_le` are now instances of those lemmas. The phase-1 review noted U1/U2 but never filed them (the BS-F02 pattern). **U3 (borderline):** in-house U3's private `IsFiveCycle.pow_apply_eq_iff` re-derives a case of Mathlib's `IsCycleOn.pow_apply_eq_pow_apply`. Fix: landing edit **LE-g50** on #366, proof-only, deleting TreeNCAC's private pair, which also clears its G6A-F05 seal failures. Then a short re-replay and Gate 50 staging. Process lesson: every review disposition that defers a duplicate must file a ledger row the same day. | G50 sweep → LE-g50 |
| 2026-11-17 | **#368 re-replay on snapshot #8: PASS** (`owner-prereqs-6b/evidence-s8.zip` `e97aed58…`). R = tip × `1953898b` = `ab098201` (its Lean is #8 plus the two files). 67 modules rc 0, state 1434 OK, #8 0/0/0. All 67 oleans and logs are byte-equal to the #7 run. Admissions 192; axiom log byte-equal; coe-A Scheme 101/0, EnsembleSecurity 1268/6 (pre-existing), byte-equal. Map `5a88ccf5…`; adoptable at a merge whose Lean equals `ab098201`. If #366 lands first, it re-replays. | #368 on #8 |
| 2026-11-17 | **LE-g50 on #366: PASS** (`597fb736`, tree `df05652d`; `fills-final-r1/phase2.md` § LE-g50, zip `51151f44…`). Proof-only, +24/−51. U1 uses the public `_le_of_forall` lemmas. U2 deletes TreeNCAC's private pair, which **clears its G6A-F05 seal failures (2 → 0)**. U3 proves `IsFiveCycle.pow_apply_eq_iff` from Mathlib's `IsCycleOn.pow_apply_eq_pow_apply`. Replay: 16 modules rc 0, state 1447 OK, #8 0/0/0, map `963ddeb4…`. 0 `sorry` in 6a. Axioms standard. No new seal failures; root coe-A 14,105/0. decls2 unchanged. Next: stage Gate 50 on #366 `597fb736` + #368. | LE-g50 |
| 2026-11-17 | **Gate 50 (Codex) staged**, round 1: #366 at `597fb736` (LE-g50 included) and #368 at `1953898b`. Records pin `b1392d06`, dispatch `7fd530e9`, exchange `b14712e5` (`gates/50-gsw-6a-fills/`, `outbox/gates/50-gsw-6a-fills-gate/`, 16/16). The re-sweep of the LE-g50 delta is clean. Nine audit questions, including correctness of all 98 proofs and the process note on U1/U2. Known slips are carried, including stale PR-body lines and `evidence-s8.zip`'s self-listing manifest entry. | G50 staged |
| 2026-11-17 | **Gate 50 round 1 dispatched (Seyoon)** to Codex: exchange `b14712e5`, records `b1392d06`, #366 `597fb736` and #368 `1953898b`. **Activity paused** (out of tokens) until Seyoon returns. Open on return: Gate 50 findings; the gsw-6b-statements final (check `inbox/fills/gsw-6b-statements/`); S2-A planning after the 6a merges. | G50 dispatched; pause |
| 2026-11-18 | **Gate 50 round 1 (Codex): CLEAR**, with 0 blockers, 0 majors, 4 minors and 1 note. #366 CLEAR (1 minor, 1 note) and #368 CLEAR (3 minors) (`gates/50-gsw-6a-fills/findings-r1.md`). All 98 proofs are confirmed against the Gate-45 freeze: 0 changed headers, 36 sketch-only docstring changes plus LE-gf2. 853 constants, standard, no `sorryAx`. Rule 10 checked over 74 records; TreeNCAC 2 → 0. All replays bind. GF-F01..F09 and sweep U1–U3 are graded; GF-F03 and U1–U3 regraded major historically, all closed. **G50-01:** stale "admitted"/"missing reader" module and statement prose in Defs, Eval, Barrington, NANDForm and Combinators, and `barrington_length_pos_aux` lacks a glue note. **G50-02:** `hybridPlant_eq` has no equation or glue line; the two sketches don't name `decrypt_eq_decode_dotProduct`. **G50-03:** `evidence-s8.zip`'s manifest lists itself. **G50-04:** #368's description names old gating and only the #7 replay. **G50-05 (note):** record duplication dispositions when found, and keep name/body scans distinct from statement-shape review. Also: **gsw-6b-statements final delivered** (exchange `3b340824`, 2026-11-17 23:48); the phase-1 review is running. | G50 CLEAR; 6b final in |
| 2026-11-18 | **Gate 50 docs ruling (Seyoon): fix before merging.** Docs-only landing edits: **LE-g50d** on #366 (G50-01: correct the stale "admitted"/"missing reader" module and statement prose in Defs, Eval, Barrington, NANDForm and Combinators, under a documentation exception for frozen prose; glue note on `barrington_length_pos_aux`) and **LE-g50e** on #368 (G50-02: `hybridPlant_eq` equation and glue line; the two sketches name `decrypt_eq_decode_dotProduct`). Each is checked by comment-strip code identity plus a short re-replay; no gate round is needed for comment-only edits. G50-03: replace `evidence-s8.zip` with a manifest that excludes itself. G50-04: #368's description is updated to name Gate 50 and the #8 replay. | G50 docs → LE-g50d/e |
| 2026-11-18 | **gsw-6b-statements final, phase-1 review: interim ACCEPT WITH LANDING EDITS** (`phase6/final-6b-r1/review.md`, zip `eed236ae…`; exchange `3b340824`). 0 blockers, 0 majors, 3 minors (docstrings), 6 infos. Six commits reproduce (O2 `5bd5ada5`, statements `8f92fe7d`), and all four checkpoint fixes are done. O2: 5 declarations, proved, 0 mismatches up to q = 2000. Statements: decls2 136/0/0, 24 targets each with formula, tag and sketch. G11/L1 proved; G14/A2 reader-only; G15 over `fheView`. No `[Gen09]`; 123 anchors exist. Evidence recount: 1,452 modules rc 0; admissions 313 = 289 + 24; `sorryAx` only in the 24 targets plus the four N2/N12–N13 dependents; seals 0 errors; controls OK. **Duplication: none found** (one borderline info, `neZero_columns`, with optional LE-6b3). Minors: G6B-F01 (docstrings go stale once #366/#368 merge; fixed by LE-6b1), F02 (the PolyRatio constant is `2^70`; LE-6b2), F03 (the "only three sources" claims; LE-6b2). Questions Q-6B-W1..W3 and F1, F2 go to Seyoon. Landing after #366/#368: an O2 PR, then the stacked statement PR; expected admissions 216. | 6b P1 |
| 2026-11-18 | **6b statements rulings (Seyoon), all as recommended.** **Q-6B-W1:** accept G16 with factor 8 (constant exactly `2^70`), since r3's factor 4 fails G17 at q = 4y + 1. **Q-6B-W2:** `LeveledReductionEfficient` includes the challenge reductions (A3 needs them). **Q-6B-W3:** accept the μ-dependent `levelTerm` and the two-chain L5 bound. **Q-6B-F1:** apply LE-6b1, LE-6b2 and LE-6b3 at landing, dropping LE-6b3 if it fails to compile. **Q-6B-F2:** `decDepth_le` stays an admitted target. Landing waits for #366/#368 to merge: an O2 PR, then the stacked statement PR, then phase 2 on the then-current snapshot and Gate 46. | 6b ruled |
| 2026-11-18 | **LE-g50d on #366 and LE-g50e on #368: PASS, pushed.** Records: `le-g50d-evidence.zip` `4e5908fe…` and `le-g50e-evidence.zip` `0cabae40…`. #366 is now `bae0d84d` (tree `fbba5d38`); the commit fixes 6 files (+19/−14) of stale admitted/missing-reader prose under the documentation exception, including two more stale sketches the sweep found (N2, N12), and adds the glue note. #368 is now `052e2b05`: `hybridPlant_eq`'s equation and glue line, and the sketches name `decrypt_eq_decode_dotProduct`. Comment-strip code identity holds with controls. Re-replays on `-land9` (20 modules) and `-prereq9` (67) are rc 0, state OK, #8 0/0/0. Admissions 192; axiom logs byte-identical; spot coe-A equal. Maps `9bb4a0d0…` and `3316e252…`. G50-03: `evidence-s8.zip` replaced (`d3373171…`, 184/184). G50-04/05: both PR descriptions updated. **#366 and #368 are marked ready.** Merge #366 first: adopt `-land9` if the merge's Lean equals `fbba5d38`. #368 then needs a combined re-replay. | #366/#368 ready |
| 2026-11-18 | **#366 and #368 merged (Seyoon)** as `523a00a6` and `cf6a2266`. **GSW phase 6a is complete on the records branch:** all 98 targets are proved, with 0 `sorry` in the 6a modules. #358, #359 and #360 land inside #366. The #366 merge's Lean equals `fbba5d38` (step-3 diff empty), so `olean-replay-6a-land9` (map `9bb4a0d0…`) is adoptable as **snapshot #9** at `523a00a6`. The #368 merge adds its two files on top, so it needs a 67-module replay on #9 before becoming **snapshot #10** at `cf6a2266`. Next: the snapshot work, then the 6b landing (O2 PR, statement PR with LE-6b1..3) with phase 2 on #10, then Gate 46. | 6a complete |
| 2026-11-18 | **Olean snapshot #9 adopted** at T `523a00a6` (the #366 merge) from `olean-replay-6a-land9`, map `9bb4a0d0…` (`maintainer/olean-snapshot-9-adopt/`, `snapshots.md`). The #368 replay on #9 is running, for snapshot #10. | snapshot #9 |
| 2026-11-18 | **Olean snapshot #10 adopted** at T `cf6a2266` (the #368 merge). #368's merge tree `d52cf05b` was replayed on #9: 67 modules rc 0, logs byte-equal to LE-g50e's, admissions 192, axiom log byte-equal. Map `84d88738…`, 1478 entries; init + basecheck OK; swap; rehash 0/0/0 (`maintainer/olean-snapshot-10-adopt/`). The superseded trees are deleted, so the only olean tree is the snapshot. Next: the 6b landing and phase 2 on #10. | snapshot #10 |
| 2026-11-18 | **GSW 6b landed as draft PRs; phase 2 PASS on snapshot #10.** #376 (O2, `land/gsw-6b-o2` `04ba2446`, LWE/BitEncoding +58) and #377 (24 statement targets, base #376; `land/gsw-6b-statements` `680be9fa`: 5 worker picks, range-diff 5/5 `=`, plus LE-6b1..3 byte-identical to the proposed diff; LE-6b3 compiles). Stale "admitted" prose for N2/N12/N13 and G6/L4 sketches fixed in the LE commit. Replays R1 (19 rebuilt, 1447/1447) and R2 (14 rebuilt, 1456/1456): rc 0, admissions 192 → 216 (exactly the 24 targets), `sorryAx` only in the targets; `fheEvalCircuit`/`leveledEvalCircuit` now standard; seals 48/48 0 errors; controls pass (16 delivery controls needed 4 stale `IterateFind` names pruned, G6B-F11); unfold scan 0 foreign; lint unchanged. Disclosed G6B-F10 (LE-6b3 drops `Quot.sound` from `neZero_columns`), F12 (root coe-A seal not re-run). Records `final-6b-r1/phase2.md`, evidence zip `60cfe326…`. Next: Gate 46 (Codex) on #376 + #377. | open |
| 2026-11-18 | **Gate 46 staged; pre-dispatch sweep found one duplicate (Seyoon's rulings).** `briefs/lattice-gsw/gates/46-gsw-6b/` (pack, dispatch, dup-sweep, diffs, sources/verification zips); exchange stage commit `4fa8ad88` on local `stage/gate46-exchange` (not pushed). S1: `GSW.encodeFheView_length`/`encodeLeveledView_length` (`GSW/Asymptotic.lean:123`, `:152`) re-prove the public `length_flatten_map_const` (`Foundations/BitLists.lean:175`) inline, undisclosed: **fix now as LE-g46** (proof-only), DL-61 recorded today. Stale "[Gen09] not ingested" docstrings in Leveled, LeveledSecurity, PolyRatio, Asymptotic (§4.1 and Thm 4.2.3 were ingested 2026-11-16, records `bdcadd85`): **docs-only fix folded into LE-g46**. Then re-replay, re-pin, dispatch. | open |
| 2026-11-18 | **Efficiency is mandatory (Seyoon).** "Addressing efficiency concerns for honest parties and in security reductions is MANDATORY." Honest algorithms must be proved efficient (uniform forms only) and every security reduction must be a proved non-uniform PPT machine connecting to the NUPPT-stated assumptions; existing gaps are holes to plug, not debt; briefs, fills and gates check it, and a missing efficiency proof is at least a major. Standing rule 15 in `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2. Next: a careful reductions audit plus an axiom sweep, then a remediation plan. | ruled |
| 2026-11-18 | **Efficiency baked into definitions (Seyoon).** Every primitive's definition carries its honest algorithms' efficiency (uniform forms) as part of the structure; no instance exists without the proof. Constructions may be built first as raw algorithm bundles with correctness/security, the primitive being inhabited only once efficiency is proved. Added to standing rule 15. Existing interfaces lacking efficiency fields (e.g. `IBEScheme`, `SecretSharing`, LWE `Family` samplers) are to be found by the reductions/definitions audit and retrofitted. | ruled |

## ===== verification.zip:records/extracts/duplication-ledger-DL54-DL61.md (this pack) =====

# Extract: briefs/pass-shelat-ch5-8/duplication-ledger.md (header at dab31951abb5c892dc6279c229e49497ec95de10; DL-54 at dab31951abb5c892dc6279c229e49497ec95de10; DL-61 added at staging, filed at the records pin; DL-61 updated to "Repaid by LE-g46" at re-staging, filed at the records pin)

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|

| DL-54 | (none landed: LE-ren drops the delivered `TreeCircuit.rename`, `rename_eval`, `depth_rename` from the GSW phase 6a statements, G6A-F01) | `TreeCircuit.reidx`, `reidx_eval`, `reidx_depth` (`BooleanAnalysis/LMN/CircuitReindex.lean:24/29/46`), which the 6a formula layer uses instead | Accepted (Seyoon, 2026-11-17, 6a ruling Q1) | Move the `reidx` family into the `Complexity/` formula combinators (`Combinators`) later, so the core formula layer need not import a `BooleanAnalysis/LMN` file (deferred, out of the Pass–shelat cleanup). |
| DL-61 | `GSW.encodeFheView_length`, `GSW.encodeLeveledView_length` (#377, `AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean:123`, `:152`; proved readers): each rebuilds inline that a flatten of constant-length blocks has length count × block (`List.length_flatten`, `← List.ofFn_comp'`, `List.ofFn_const`, `List.sum_replicate_nat`); undisclosed; found by the Gate 46 pre-dispatch sweep on 2026-11-18 (`briefs/lattice-gsw/gates/46-gsw-6b/dup-sweep.md`, S1), missed by the 6b phase-1 review | `TCSlib.Cryptography.length_flatten_map_const` (`Foundations/BitLists.lean:175`, in the import closure of `GSW/Asymptotic`; applies through Mathlib `List.ofFn_eq_map` and core `List.length_finRange`); the exact `List.ofFn` form `Authentication.length_flatten_ofFn` (`Authentication/Signatures/Lamport.lean:123`, not in the closure) | **Repaid by LE-g46** (Seyoon, 2026-11-18, Q-G46-S1: fix now, proof-only; recorded the day it was found, lesson G50-05) | **Repaid in #377 by landing edit LE-g46** (`7563734a8badba842223e0687c719b3b4692e9d2`, before Gate 46 dispatch): both proofs now apply `length_flatten_map_const` after Mathlib `List.ofFn_eq_map` and core `List.length_finRange`; the inline `List.length_flatten`/`List.ofFn_comp'`/`List.ofFn_const`/`List.sum_replicate_nat` chains are gone (statements and docstrings unchanged; replay rc 0, axioms unchanged; `briefs/lattice-gsw/gates/46-gsw-6b/le-g46.md`). Nothing left for this row. The pre-existing flatten-length family (`length_flatten_ofFn` in Lamport, HybridMachine and CommitmentLemmas; BitLists' `length_flatten_map_const`/`_map_range`; `Programs/Util/List.lean`'s `length_flatMap_finRange`/`_range`; `PSubsetPPolyTableau.length_flatMap_const`; EnsemblesLemmas' `length_flatMap_range`; sweep note N11) is not 6b's and stays a Cleanup Stage 2 question. |

## ===== verification.zip:MANIFEST.md (this pack) =====

# verification.zip · Gate 46 round 1 (GSW 6b: #376 O2 and #377 statements)

Staged 2026-11-18 by the maintainer's staging session. No Lean, no `lake`; git objects, `python3 -I` and grep only.

**Re-staged 2026-11-18 after LE-g46** (#377 head `7563734a8badba842223e0687c719b3b4692e9d2`, tree `c56db4c4`; records tip
at re-staging `9ae6b909305f868f51f5cc05787c66e4d336bf74`, Lean-equal to `38123ccb`). The scripts in `tools/` were re-pointed
to that head and tip (`anchors.py` also resolves [Gen09] anchors; `leanequal.sh` checks the adoption tree `c56db4c4`;
`leident.sh` still checks LE-6b1..3 at `680be9fa`, output unchanged), and every `checks/` file except
`evidence-verify.txt` (extended) was regenerated. `evidence/le-g46/` holds LE-g46's record, diff and evidence ZIP
(the only part of this ZIP that rests on Lean runs). `records/extracts/` are re-cut at the re-staging tip; `pr/` is the
REST state after the PR #377 body update.
`SHA256SUMS` lists every other entry of this ZIP.

- `checks/` (git-object checks at staging; scripts in `tools/`):
  - `series.txt` (`tools/series.sh`): both PRs' commits (tree, parents, author, committer, signature presence, numstat),
    the PR diff stats, the changed paths, and per-file blob equality with the worker heads `5bd5ada5`/`8f92fe7d`.
  - `lean-equality.txt` (`tools/leanequal.sh`): Lean equality of the PR cut tip `38123ccb`, #376's REST base `1a9a3295`
    and the staging records tip `dab31951` with snapshot #10's T `cf6a2266`; the scope (exactly 12 paths, no 6a or
    phase-5 file); merge-tree of each head with `dab31951` and its Lean equality with the adoption trees.
  - `le-identity.txt` (`tools/leident.sh`): `landing-edits-proposed.diff` applied to the worker's files equals #377's
    head (5/5); the comment-stripped diff of the LE commit (`tools/strip.py`).
  - `targets.txt` (`tools/targets.py`): every comment-stripped `sorry`, its declaration, tag/Glue and sketch presence,
    and the mapping to `issued-6b-r1/targets.txt`.
  - `anchors.txt` (`tools/anchors.py`): every `pNNN-bNNN` anchor resolved in the ingest of its tag at `dab31951`.
  - `sizes.tsv` (`tools/sourcehead.py`): lines, widths, tabs and trailing spaces of the 12 files.
  - `dup-sweep.txt` (`tools/dupsweep46.sh`, `tools/closure.py`): the pre-dispatch duplication sweep's greps; the
    judgement is `dup-sweep.md` in the gate directory.
  - `evidence-verify.txt`: the records' evidence sums, the inner manifests of the phase-1/phase-2 ZIPs from fresh
    extracts, the axiom summary, the DECL reconciliation and the admissions result.
- `evidence/`: `gsw-6b-final-r1-phase1-evidence.zip`, `gsw-6b-final-r1-phase2-evidence.zip`,
  `landing-edits-proposed.diff` and `evidence-SHA256SUMS`, copied unchanged from
  `briefs/lattice-gsw/phase6/final-6b-r1/` at the records tip.
- `records/`: copies at the records tip `dab31951abb5c892dc6279c229e49497ec95de10` (equal at the pin):
  `phase6/final-6b-r1/{review,phase2}.md`, `phase6/checkpoint1-6b-review.md`, `phase6/plan-section.md` (r3),
  `phase6/rulings.md`, the issued package `phase6/issued-6b-r1/` (README, brief, dispatch, addendum, targets, census,
  pins, SHA256SUMS), `policy.md`, Gate 45's findings r1/r2, Gate 50's findings r1, and `extracts/` (decision-log rows
  567-593; the ledger header, DL-54 and DL-61, the last added at staging).
- `evidence/le-g46/`: `le-g46.md`, `le-g46.diff.txt` (`git diff 680be9fa 7563734a`) and `le-g46-evidence.zip` (inner
  `SHA256SUMS`), as filed in the gate directory.
- `pr/`: the REST fields of #376/#377 at re-staging (with the SHA-256 of each body, equal to the gate directory's
  `pr376-description.md`/`pr377-description.md`).

## ===== verification.zip:POINTERS.md (this pack) =====

# POINTERS (not copied, or copied whole)

- Phase-1 evidence: `evidence/gsw-6b-final-r1-phase1-evidence.zip`, SHA-256
  `eed236aeedb3efa32b7dbdfc084686d0f881ba565145ee7984d707a3a364d7cf` (records `final-6b-r1/evidence-SHA256SUMS`);
  inner manifest 25/25 at staging.
- Phase-2 evidence: `evidence/gsw-6b-final-r1-phase2-evidence.zip`, SHA-256
  `60cfe32649c5692e50b12c86713498810aab10e9cabaa4e11545542ff3aa22af`; inner manifest 598/598 at staging.
- The worker's delivery is not copied: `inbox/fills/gsw-6b-statements/` on `exchange/pass-shelat-ch5-8` at
  `3b340824dde77433b2135a3c8d20c7ed194cf18c` (2,688 files; phase 1 verified its manifests 2,687/2,687 and 2,664/2,664).
- #368's evidence (Gate 50, merged): `briefs/lattice-gsw/phase6/owner-prereqs-6b/` (3/3 at staging).
- The replay trees `olean-replay-6b-o2` (map `e1d210bf…`, #376) and `olean-replay-6b-stmt-g46` (map `65ca0263…`, #377 at
  `7563734a`, a `cp -al` of `olean-replay-6b-stmt`, map `52ed7825…`, which it supersedes for #377) are on the maintainer
  host, kept for adoption.

## ===== verification.zip:checks/series.txt (this pack) =====

# series.txt
tip 38123ccbebef878cd25dd2d2761de1b40ba7e421; staging records 9ae6b909305f868f51f5cc05787c66e4d336bf74; #376 04ba2446f541c39dd02aefaa97a9eb31dbbda748; #377 7563734a8badba842223e0687c719b3b4692e9d2

## commits (hash tree parents | author | committer | gpgsig lines | subject)
04ba2446f541c39dd02aefaa97a9eb31dbbda748 8b615e060f72d72749f67abd39f820d117e0a806 38123ccbebef878cd25dd2d2761de1b40ba7e421 | Claude <noreply@anthropic.com> | Claude <noreply@anthropic.com> 2026-11-18T04:24:17+00:00 | gpgsig 1 | O2: decodeLo, decodeHi and decode_iff_mem_Ico in LWE/BitEncoding
    58	0	TCSlib/Cryptography/LWE/BitEncoding.lean
47aae69d8e48a2983bfa1fd3148bbba375d20cae e602bd80fec4b6031ef1d8debdca4878f4c3af41 04ba2446f541c39dd02aefaa97a9eb31dbbda748 | Claude <noreply@anthropic.com> | Claude <noreply@anthropic.com> 2026-11-18T04:24:28+00:00 | gpgsig 1 | GSW 6b statements: Branching (G1-G3) and DecryptFormula (G5-G8)
    179	0	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean
    220	0	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean
c10e0d3ef40d852bb08c8ad00309a5ddd51c21f2 77686ac000fedbb51c84bc539fdb9589aca248b8 47aae69d8e48a2983bfa1fd3148bbba375d20cae | Claude <noreply@anthropic.com> | Claude <noreply@anthropic.com> 2026-11-18T04:24:28+00:00 | gpgsig 1 | GSW 6b statements: Bootstrap (G9-G13, G18) and Circular (G14-G15)
    351	0	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean
    146	0	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Circular.lean
80366e7fe52e8157024e75294b00a4175030dfc2 72d0d23b1abb37d7df20c3044a88d774c3239c32 c10e0d3ef40d852bb08c8ad00309a5ddd51c21f2 | Claude <noreply@anthropic.com> | Claude <noreply@anthropic.com> 2026-11-18T04:24:28+00:00 | gpgsig 1 | GSW 6b statements: Leveled (L1-L3) and LeveledSecurity (L4-L5)
    283	0	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
    351	0	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
52f52dc7aa58bc4dc948a3f6a1d9fdeb187e6839 04ae3302e6a2d9b06afab8573423606725eb0303 80366e7fe52e8157024e75294b00a4175030dfc2 | Claude <noreply@anthropic.com> | Claude <noreply@anthropic.com> 2026-11-18T04:24:28+00:00 | gpgsig 1 | GSW 6b statements: LWE/Ratio, PolyRatio (G16-G17) and Asymptotic (A1-A3)
    324	0	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean
    174	0	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
    59	0	TCSlib/Cryptography/LWE/Ratio.lean
75c683b295cca1a6cba918eb49a5d7c256739b7a 22349e8e15450f72782d29f3e105c919afcc166f 52f52dc7aa58bc4dc948a3f6a1d9fdeb187e6839 | Claude <noreply@anthropic.com> | Claude <noreply@anthropic.com> 2026-11-18T04:24:28+00:00 | gpgsig 1 | GSW 6b statements: facades GSW.lean and LWE.lean
    23	1	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean
    2	0	TCSlib/Cryptography/LWE.lean
680be9fa45a9cf5deeb7a59820e8e86aaaa4f068 956fc086044551e8f04298ab70dd5aa451069c16 75c683b295cca1a6cba918eb49a5d7c256739b7a | Claude <noreply@anthropic.com> | Claude <noreply@anthropic.com> 2026-11-18T04:25:18+00:00 | gpgsig 1 | GSW 6b landing edits LE-6b1, LE-6b2, LE-6b3 (rulings Q-6B-F1 A)
    1	3	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean
    4	8	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean
    6	5	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
    2	2	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
    4	3	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
7563734a8badba842223e0687c719b3b4692e9d2 c56db4c403ccab179a994143c5f989d4f3718910 680be9fa45a9cf5deeb7a59820e8e86aaaa4f068 | Claude <noreply@anthropic.com> | Claude <noreply@anthropic.com> 2026-11-18T07:22:49+00:00 | gpgsig 1 | GSW 6b landing edit LE-g46 (Gate 46 sweep S1; [Gen09] citations)
    23	9	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean
    16	9	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
    16	5	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
    8	4	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean

## trailers of the landing-edit commit
Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA


## the PR diffs
#376 38123ccbebef878cd25dd2d2761de1b40ba7e421..04ba2446f541c39dd02aefaa97a9eb31dbbda748:
 1 file changed, 58 insertions(+)
#377 04ba2446f541c39dd02aefaa97a9eb31dbbda748..7563734a8badba842223e0687c719b3b4692e9d2:
 11 files changed, 2144 insertions(+), 1 deletion(-)
paths changed 38123ccbebef878cd25dd2d2761de1b40ba7e421..7563734a8badba842223e0687c719b3b4692e9d2:
M	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean
A	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean
A	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean
A	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean
A	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Circular.lean
A	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean
A	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
A	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
A	TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
M	TCSlib/Cryptography/LWE.lean
M	TCSlib/Cryptography/LWE/BitEncoding.lean
A	TCSlib/Cryptography/LWE/Ratio.lean

## range identity with the worker series (tree equality per file)
TCSlib/Cryptography/LWE/BitEncoding.lean O2-head fd564ef81f92258ae00e27dfb47cd870d0148a28 worker fd564ef81f92258ae00e27dfb47cd870d0148a28
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean picks(~1) 5984d64b789a3e0ae2733ca7c06b9f0588ed6763 worker 5984d64b789a3e0ae2733ca7c06b9f0588ed6763 head 5984d64b789a3e0ae2733ca7c06b9f0588ed6763
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean picks(~1) c2d0f76930fc5da61527fa5796871bbce7342e83 worker c2d0f76930fc5da61527fa5796871bbce7342e83 head 180c8eaf58cbccb61a98c340aae6df17875fe401
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean picks(~1) 9c69ef4c4921c25e75e8ab7f4cfc4947c5efc6ef worker fb8a0c9b3a3d023a2651cdefdb6b9505e900a2c9 head 9c69ef4c4921c25e75e8ab7f4cfc4947c5efc6ef
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean picks(~1) a5420c769eb60aea3abefe8412c7cbc6a7267f5f worker a5420c769eb60aea3abefe8412c7cbc6a7267f5f head a5420c769eb60aea3abefe8412c7cbc6a7267f5f
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Circular.lean picks(~1) e72596abe87caf1d8374676650add71eaa08f67b worker e72596abe87caf1d8374676650add71eaa08f67b head e72596abe87caf1d8374676650add71eaa08f67b
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean picks(~1) a4f9cb41864e66e19c2bf43fa62cf029073719f5 worker 0f2ee7ab5a3a411fbd3ef7c79c1fe52e83ef3c6a head a4f9cb41864e66e19c2bf43fa62cf029073719f5
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean picks(~1) 9ff44259053b0cb9e64ef3402fa0fa65eccd9f39 worker 4f32cd5c585af65946635e8ba8916f00458b29a9 head 70e29cbf3e8b0461fb79b9d6635a93b88f40a0ae
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean picks(~1) 2455962c8bf1a25daa0a2fa45cd2e68a5f61a3fb worker f35498ec7fdb5808b3af7ccf0133ee68a9864db9 head a07967b4b4bdf7c87dff47af9c0b3d8de18eb751
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean picks(~1) 3341360509894da357cff7f26bd0ffe9c814dc24 worker 1ebe41f07b2c5d878e3c68341bbc89b3756d8342 head 2995b996e443f252cc245793b261657c774e4f64
TCSlib/Cryptography/LWE.lean picks(~1) f41508218fa1792a1644720600519cc817e85d12 worker f41508218fa1792a1644720600519cc817e85d12 head f41508218fa1792a1644720600519cc817e85d12
TCSlib/Cryptography/LWE/Ratio.lean picks(~1) 5dff56fba4255a6502558b0143efcfb53df3cb86 worker 5dff56fba4255a6502558b0143efcfb53df3cb86 head 5dff56fba4255a6502558b0143efcfb53df3cb86

## ===== verification.zip:checks/lean-equality.txt (this pack) =====

# lean-equality.txt
snapshot #10 T cf6a2266e9556ca8ad61e56f7232266ccc6d4e62; PR cut tip 38123ccbebef878cd25dd2d2761de1b40ba7e421; staging records tip 9ae6b909305f868f51f5cc05787c66e4d336bf74; #376 REST base.sha 1a9a32959cc58d7a882d0f6a7e2b0003b52f82ae
Lean paths cf6a2266e9556ca8ad61e56f7232266ccc6d4e62 -> 38123ccbebef878cd25dd2d2761de1b40ba7e421: 0 changed
Lean paths cf6a2266e9556ca8ad61e56f7232266ccc6d4e62 -> 1a9a32959cc58d7a882d0f6a7e2b0003b52f82ae: 0 changed
Lean paths cf6a2266e9556ca8ad61e56f7232266ccc6d4e62 -> 9ae6b909305f868f51f5cc05787c66e4d336bf74: 0 changed
ancestry: S10<=TIP TIP<=RESTbase RESTbase<=REC
records-only commits TIP..REC: 31; their paths outside briefs/ and the plan: 0

# scope: paths of TIP..#377 against the issued brief's 12
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Circular.lean
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
TCSlib/Cryptography/LWE.lean
TCSlib/Cryptography/LWE/BitEncoding.lean
TCSlib/Cryptography/LWE/Ratio.lean
count 12
6a (Complexity/) or phase-5 GSW files touched: 0

# merge-tree with the staging records tip (git 2.43.0)
9ae6b909305f868f51f5cc05787c66e4d336bf74 x 04ba2446f541c39dd02aefaa97a9eb31dbbda748: rc 0 tree 20c1e4141cd7c1336f74194bb5e0f953d747d015
9ae6b909305f868f51f5cc05787c66e4d336bf74 x 7563734a8badba842223e0687c719b3b4692e9d2: rc 0 tree b66cb519eb381fbe7da17430a347cb8932a5cc71
adoption trees: R1 8b615e060f72d72749f67abd39f820d117e0a806 = 8b615e060f72d72749f67abd39f820d117e0a806 (#376 head tree); R2-g46 c56db4c403ccab179a994143c5f989d4f3718910 = c56db4c403ccab179a994143c5f989d4f3718910 (#377 head tree)
Lean diff merge-tree(REC,04ba2446f541c39dd02aefaa97a9eb31dbbda748) vs 8b615e060f72d72749f67abd39f820d117e0a806: 0 paths
Lean diff merge-tree(REC,7563734a8badba842223e0687c719b3b4692e9d2) vs c56db4c403ccab179a994143c5f989d4f3718910: 0 paths

## ===== verification.zip:checks/le-identity.txt (this pack) =====

# le-identity.txt
proposed diff f1a189c1a4d9 sha256 d0e547f904d2c8fb6731690e24053f8a7f30f5765c5108266ad791949c6ef1eb
git apply: rc 0
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean proposal-applied 9c69ef4c4921c25e75e8ab7f4cfc4947c5efc6ef head 9c69ef4c4921c25e75e8ab7f4cfc4947c5efc6ef IDENTICAL
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean proposal-applied a4f9cb41864e66e19c2bf43fa62cf029073719f5 head a4f9cb41864e66e19c2bf43fa62cf029073719f5 IDENTICAL
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean proposal-applied 9ff44259053b0cb9e64ef3402fa0fa65eccd9f39 head 9ff44259053b0cb9e64ef3402fa0fa65eccd9f39 IDENTICAL
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean proposal-applied 2455962c8bf1a25daa0a2fa45cd2e68a5f61a3fb head 2455962c8bf1a25daa0a2fa45cd2e68a5f61a3fb IDENTICAL
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean proposal-applied 3341360509894da357cff7f26bd0ffe9c814dc24 head 3341360509894da357cff7f26bd0ffe9c814dc24 IDENTICAL

## files of the LE commit whose comment-stripped text changes (tools/strip.py)
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean: code EQUAL
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean: code DIFFERS
    10,14c10,11
    <   ⟨Nat.mul_ne_zero (Nat.succ_ne_zero _) fun h => by
    <     have hle := P.modulus_le
    <     have hq := P.lwe.modulus_ge_two
    <     rw [h, pow_zero] at hle
    <     omega⟩
    ---
    >   ⟨Nat.mul_ne_zero (Nat.succ_ne_zero _)
    >     (Nat.one_lt_two_pow_iff.mp (Nat.lt_of_lt_of_le P.lwe.modulus_ge_two P.modulus_le))⟩
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean: code EQUAL
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean: code EQUAL
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean: code EQUAL

## ===== verification.zip:checks/targets.txt (this pack) =====

# targets.txt (rev 7563734a8badba842223e0687c719b3b4692e9d2; comment-stripped `sorry` occurrences)
Asymptotic.lean:304	indCPA_of_dlweAssumption	tag=yes	sketch=yes
Asymptotic.lean:336	leveledINDCPA_of_dlweAssumption	tag=yes	sketch=yes
Bootstrap.lean:241	encrypts_bootNAND	tag=yes	sketch=yes
Bootstrap.lean:272	decrypt_fheEval	tag=yes	sketch=yes
Bootstrap.lean:291	decrypt_fheEvalCircuit	tag=yes	sketch=yes
Bootstrap.lean:330	decrypt_keygen_fheEvalCircuit	tag=yes	sketch=yes
Bootstrap.lean:347	bootNoise_le	tag=Glue	sketch=yes
Branching.lean:124	Encrypts.select	tag=yes	sketch=yes
Branching.lean:153	encrypts_homEvalPBP	tag=yes	sketch=yes
Branching.lean:177	encrypts_homEvalFormula	tag=yes	sketch=yes
Circular.lean:144	distAdv_fheView_noEvk_le	tag=yes	sketch=yes
DecryptFormula.lean:147	vecMul_secretVector_eq_sum	tag=yes	sketch=yes
DecryptFormula.lean:167	decryptFormula_eval	tag=yes	sketch=yes
DecryptFormula.lean:179	nandFormula_eval	tag=yes	sketch=yes
DecryptFormula.lean:190	depth_nandFormula_le	tag=yes	sketch=yes
DecryptFormula.lean:200	maxFanin_nandFormula_le	tag=yes	sketch=yes
DecryptFormula.lean:214	decDepth_le	tag=yes	sketch=yes
Leveled.lean:254	encrypts_leveledEval	tag=yes	sketch=yes
Leveled.lean:289	decrypt_keygen_leveledEvalCircuit	tag=yes	sketch=yes
LeveledSecurity.lean:333	distAdv_levelHybrid_le	tag=yes	sketch=yes
LeveledSecurity.lean:360	distAdv_leveledView_le	tag=yes	sketch=yes
PolyRatio.lean:117	bootRatio_le_poly	tag=yes	sketch=yes
PolyRatio.lean:148	decrypt_fheEval_of_ratio	tag=yes	sketch=yes
PolyRatio.lean:177	decrypt_leveledEval_of_ratio	tag=yes	sketch=yes
total 24 distinct declarations 24 per file {'Asymptotic.lean': 2, 'Bootstrap.lean': 5, 'Branching.lean': 3, 'Circular.lean': 1, 'DecryptFormula.lean': 6, 'Leveled.lean': 2, 'LeveledSecurity.lean': 2, 'PolyRatio.lean': 3}

## issued targets.txt rows (kind target) against the admitted set
G1	Encrypts.select	ADMITTED
G2	encrypts_homEvalPBP	ADMITTED
G3	encrypts_homEvalFormula	ADMITTED
G5	vecMul_secretVector_eq_sum	ADMITTED
G6	decryptFormula_eval	ADMITTED
G7	nandFormula_eval	ADMITTED
G8	depth_nandFormula_le	ADMITTED
G8	maxFanin_nandFormula_le	ADMITTED
G8	decDepth_le	ADMITTED
G9	encrypts_bootNAND	ADMITTED
G10	decrypt_fheEval	ADMITTED
G18	decrypt_fheEvalCircuit	ADMITTED
G12	decrypt_keygen_fheEvalCircuit	ADMITTED
G13	bootNoise_le	ADMITTED
G15	distAdv_fheView_noEvk_le	ADMITTED
L2	encrypts_leveledEval	ADMITTED
L3	decrypt_keygen_leveledEvalCircuit	ADMITTED
L4	distAdv_levelHybrid_le	ADMITTED
L5	distAdv_leveledView_le	ADMITTED
G16	bootRatio_le_poly	ADMITTED
G17	decrypt_fheEval_of_ratio	ADMITTED
A1	indCPA_of_dlweAssumption	ADMITTED
A3	leveledINDCPA_of_dlweAssumption	ADMITTED

## admitted names not in targets.txt: ['decrypt_leveledEval_of_ratio']

## ===== verification.zip:checks/anchors.txt (this pack) =====

# anchors.txt (Lean 7563734a8badba842223e0687c719b3b4692e9d2, ingests at 9ae6b909305f868f51f5cc05787c66e4d336bf74)
ingest anchor counts: {'BV14': 25, 'BV11': 11, 'AP14': 22, 'GSW13': 17, 'Pei16': 15, 'Bar89': 12, 'Gen09': 15}
anchor occurrences 140; resolved in the cited ingest 140; missing 0; unattributed 0
[Gen09] occurrences: 20

## ===== verification.zip:checks/sizes.tsv (this pack) =====

path	base_lines	head_lines	head_max_width	over100	tabs	trailing	head_sha256
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean	35	57	96	0	0	0	3a8a8de22da8dddd682c567e33939d0a06c87d2385e64ba7ed5e1753b1ba1b2c
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean	-	338	99	0	0	0	ffd8ac2b85285c931339171f6aaae7925b074e55e0265c7cc82b4dd6bd6467cb
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean	-	349	99	0	0	0	5fabe2779a18980f5c3176111d280e7827a8aa041881066eafb67513b504cbc6
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean	-	179	97	0	0	0	128a478e9c39f6dd34b6c7bb5326b17af4dc08b3dfd487c556451087315e304b
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Circular.lean	-	146	95	0	0	0	385c809d92fba846d673d1a961765c300edf797817be1e05fc1e5061f38e6b39
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean	-	216	98	0	0	0	58e041c0e6526d0750129a596e459f0bcdaaa011266c76464c762f4d6fb3d9db
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean	-	291	99	0	0	0	c78bb8d48dd7eac3dc76cdf57718402798d73957fd3d38831c2fcf918e171e8d
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean	-	362	98	0	0	0	e6b55d7dca0c0712b9a30e75020c1152513a2e0b7b886403c20abfaa21a84e60
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean	-	179	98	0	0	0	f8647ed421e6e1757718f99322ad8b384cc6ec666d69e3f1c09ebc92efc08167
TCSlib/Cryptography/LWE.lean	38	40	93	0	0	0	2aba9e161b9cd02b9272427d1a6f6387575def442906b3d4e7c690e9d9966a0d
TCSlib/Cryptography/LWE/BitEncoding.lean	142	200	97	0	0	0	74cf46e41c434ef593c5904dcd4f064ad5551e841bf058823916af5b4c3123a4
TCSlib/Cryptography/LWE/Ratio.lean	-	59	93	0	0	0	8338d6058a48f9d86bbae9ccdcd181591f781efd65498fdc9c7aa571b9331a68

## ===== verification.zip:checks/evidence-verify.txt (this pack) =====

# evidence-verify.txt (staging, 2026-11-18T07:03:25Z)
## records evidence sums
gsw-6b-final-r1-phase1-evidence.zip: OK
gsw-6b-final-r1-phase2-evidence.zip: OK
evidence.zip: OK
evidence-s8.zip: OK
le-g50e-evidence.zip: OK
## inner manifests (fresh extracts)
phase 1: 25/25 OK; files 26 (manifest included)
phase 2: 598/598 OK; files 599 (manifest included)
## phase-2 axiom summary (axioms/r2/axsum.txt, head)
constants 175 (DECL 153, AUX 22)
non-standard axioms other than sorryAx: 0 []
sorryAx in 24; equal to the 24 targets: True; extra []; missing []
traces: 24; each target traces only itself: True []
## DECL reconciliation: probe DECL names minus decls2 names (153 - 136 = 17)
TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily_lwe
TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily_width
TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootGate.match_1
TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.fheView_fst
TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.fheView_snd
TCSlib.Cryptography.LWE.BitEncoding.codepoint
TCSlib.Cryptography.LWE.BitEncoding.codepoint_eq
TCSlib.Cryptography.LWE.BitEncoding.decode
TCSlib.Cryptography.LWE.BitEncoding.decode_codepoint_add
TCSlib.Cryptography.LWE.BitEncoding.decode_eq
TCSlib.Cryptography.LWE.BitEncoding.distance
TCSlib.Cryptography.LWE.BitEncoding.distance_add_right
TCSlib.Cryptography.LWE.BitEncoding.distance_codepoints
TCSlib.Cryptography.LWE.BitEncoding.distance_eq
TCSlib.Cryptography.LWE.BitEncoding.distance_intCast_zero_le
TCSlib.Cryptography.LWE.BitEncoding.distance_symm
TCSlib.Cryptography.LWE.BitEncoding.distance_triangle
## admissions (admissions/r2-warnings-vs-targets.txt, tail)
ADMITTED	PolyRatio.lean	decrypt_leveledEval_of_ratio	157	target
ADMITTED	Asymptotic.lean	indCPA_of_dlweAssumption	281	target
ADMITTED	Asymptotic.lean	leveledINDCPA_of_dlweAssumption	312	target
targets 24; admitted 24; matched 24; not a target []; twice []; missing []
RESULT EXACT

## LE-g46 evidence (re-staging, 2026-11-18)
le-g46-evidence.zip sha256 313c8f4d8a841b3c53849cfd5ec238caf6f3ac5c80c4ecf048f91b753c886ae1; fresh extract: inner 224/224 OK
le-g46.diff.txt sha256 13267e45ba16bc23d8a47e2c2c2176bc7f4a0fdaa33f7733707c98af0d6c24f4 = git diff 680be9fa 7563734a: 13267e45ba16bc23d8a47e2c2c2176bc7f4a0fdaa33f7733707c98af0d6c24f4

## ===== verification.zip:checks/dup-sweep.txt (this pack) =====

# dup-sweep.txt (Gate 46 staging greps, no Lean)
records 9ae6b909305f868f51f5cc05787c66e4d336bf74 (Lean = PR cut tip 38123ccbebef878cd25dd2d2761de1b40ba7e421 = snapshot #10); main acea851c1dbafae140d481d91827dcf72ba31c74; #376 04ba2446f541c39dd02aefaa97a9eb31dbbda748; #377 7563734a8badba842223e0687c719b3b4692e9d2
Mathlib 029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e; Batteries 39260e31b7b3f7f05643da95242463b462dc05f1; core leanprover--lean4---v4.25.0

## 1. inventory
decls2 (phase 2, tip -> #377 head): 136 rows, kinds:  136 ADDED;
of which in BitEncoding.lean (#376, O2): 5
independent count of added keyword lines (theorem|lemma|def|abbrev|instance|structure), tip -> #377:
      9 abbrev
     41 def
      1 instance
     85 theorem
private declarations added: 0
simps-generated names (not in decls2): Parameters.ofFamily_lwe, _width; fheView_fst, _snd
GSW.Asymptotic.lean:100	AdvancedEncryption.Homomorphic.GSW.encodeView_eq	theorem
GSW.Asymptotic.lean:104	AdvancedEncryption.Homomorphic.GSW.encodeView_length	theorem
GSW.Asymptotic.lean:114	AdvancedEncryption.Homomorphic.GSW.encodeFheView	def
GSW.Asymptotic.lean:120	AdvancedEncryption.Homomorphic.GSW.encodeFheView_eq	theorem
GSW.Asymptotic.lean:127	AdvancedEncryption.Homomorphic.GSW.encodeFheView_length	theorem
GSW.Asymptotic.lean:143	AdvancedEncryption.Homomorphic.GSW.encodeLeveledView	def
GSW.Asymptotic.lean:150	AdvancedEncryption.Homomorphic.GSW.encodeLeveledView_eq	theorem
GSW.Asymptotic.lean:158	AdvancedEncryption.Homomorphic.GSW.encodeLeveledView_length	theorem
GSW.Asymptotic.lean:189	AdvancedEncryption.Homomorphic.GSW.WeakCircularSecureFamily	def
GSW.Asymptotic.lean:199	AdvancedEncryption.Homomorphic.GSW.weakCircularSecureFamily_iff	theorem
GSW.Asymptotic.lean:216	AdvancedEncryption.Homomorphic.GSW.ReductionEfficient	def
GSW.Asymptotic.lean:226	AdvancedEncryption.Homomorphic.GSW.reductionEfficient_iff	theorem
GSW.Asymptotic.lean:244	AdvancedEncryption.Homomorphic.GSW.LeveledReductionEfficient	def
GSW.Asymptotic.lean:261	AdvancedEncryption.Homomorphic.GSW.leveledReductionEfficient_iff	theorem
GSW.Asymptotic.lean:295	AdvancedEncryption.Homomorphic.GSW.indCPA_of_dlweAssumption	theorem
GSW.Asymptotic.lean:326	AdvancedEncryption.Homomorphic.GSW.leveledINDCPA_of_dlweAssumption	theorem
GSW.Asymptotic.lean:80	AdvancedEncryption.Homomorphic.GSW.encodeCiphertext	def
GSW.Asymptotic.lean:84	AdvancedEncryption.Homomorphic.GSW.encodeCiphertext_eq	theorem
GSW.Asymptotic.lean:89	AdvancedEncryption.Homomorphic.GSW.encodeCiphertext_length	theorem
GSW.Asymptotic.lean:96	AdvancedEncryption.Homomorphic.GSW.encodeView	def
GSW.Bootstrap.lean:102	AdvancedEncryption.Homomorphic.GSW.KeySeed	abbrev
GSW.Bootstrap.lean:107	AdvancedEncryption.Homomorphic.GSW.KeySeed_eq	theorem
GSW.Bootstrap.lean:117	AdvancedEncryption.Homomorphic.GSW.bootNoise	def
GSW.Bootstrap.lean:121	AdvancedEncryption.Homomorphic.GSW.bootNoise_eq	theorem
GSW.Bootstrap.lean:127	AdvancedEncryption.Homomorphic.GSW.bootNAND	def
GSW.Bootstrap.lean:132	AdvancedEncryption.Homomorphic.GSW.bootNAND_eq	theorem
GSW.Bootstrap.lean:141	AdvancedEncryption.Homomorphic.GSW.bootGate	def
GSW.Bootstrap.lean:150	AdvancedEncryption.Homomorphic.GSW.bootGate_of_args_eq_nil	theorem
GSW.Bootstrap.lean:158	AdvancedEncryption.Homomorphic.GSW.bootGate_of_args_eq_singleton	theorem
GSW.Bootstrap.lean:166	AdvancedEncryption.Homomorphic.GSW.bootGate_of_args_eq_cons_cons	theorem
GSW.Bootstrap.lean:178	AdvancedEncryption.Homomorphic.GSW.fheEval	def
GSW.Bootstrap.lean:184	AdvancedEncryption.Homomorphic.GSW.fheEval_eq	theorem
GSW.Bootstrap.lean:193	AdvancedEncryption.Homomorphic.GSW.fheEvalCircuit	def
GSW.Bootstrap.lean:199	AdvancedEncryption.Homomorphic.GSW.fheEvalCircuit_eq	theorem
GSW.Bootstrap.lean:207	AdvancedEncryption.Homomorphic.GSW.evalKey	def
GSW.Bootstrap.lean:212	AdvancedEncryption.Homomorphic.GSW.evalKey_eq	theorem
GSW.Bootstrap.lean:235	AdvancedEncryption.Homomorphic.GSW.encrypts_bootNAND	theorem
GSW.Bootstrap.lean:264	AdvancedEncryption.Homomorphic.GSW.decrypt_fheEval	theorem
GSW.Bootstrap.lean:282	AdvancedEncryption.Homomorphic.GSW.decrypt_fheEvalCircuit	theorem
GSW.Bootstrap.lean:299	AdvancedEncryption.Homomorphic.GSW.encrypts_evalKey	theorem
GSW.Bootstrap.lean:322	AdvancedEncryption.Homomorphic.GSW.decrypt_keygen_fheEvalCircuit	theorem
GSW.Bootstrap.lean:344	AdvancedEncryption.Homomorphic.GSW.bootNoise_le	theorem
GSW.Bootstrap.lean:73	AdvancedEncryption.Homomorphic.GSW.PublicKey	abbrev
GSW.Bootstrap.lean:78	AdvancedEncryption.Homomorphic.GSW.PublicKey_eq	theorem
GSW.Bootstrap.lean:84	AdvancedEncryption.Homomorphic.GSW.Secret	abbrev
GSW.Bootstrap.lean:88	AdvancedEncryption.Homomorphic.GSW.Secret_eq	theorem
GSW.Bootstrap.lean:93	AdvancedEncryption.Homomorphic.GSW.Coins	abbrev
GSW.Bootstrap.lean:97	AdvancedEncryption.Homomorphic.GSW.Coins_eq	theorem
GSW.Branching.lean:100	AdvancedEncryption.Homomorphic.GSW.homEvalFormula_eq	theorem
GSW.Branching.lean:120	AdvancedEncryption.Homomorphic.GSW.Encrypts.select	theorem
GSW.Branching.lean:147	AdvancedEncryption.Homomorphic.GSW.encrypts_homEvalPBP	theorem
GSW.Branching.lean:171	AdvancedEncryption.Homomorphic.GSW.encrypts_homEvalFormula	theorem
GSW.Branching.lean:63	AdvancedEncryption.Homomorphic.GSW.select	def
GSW.Branching.lean:67	AdvancedEncryption.Homomorphic.GSW.select_eq	theorem
GSW.Branching.lean:76	AdvancedEncryption.Homomorphic.GSW.homEvalPBP	def
GSW.Branching.lean:81	AdvancedEncryption.Homomorphic.GSW.homEvalPBP_eq	theorem
GSW.Branching.lean:93	AdvancedEncryption.Homomorphic.GSW.homEvalFormula	def
GSW.Circular.lean:104	AdvancedEncryption.Homomorphic.GSW.WeakCircularSecure	def
GSW.Circular.lean:110	AdvancedEncryption.Homomorphic.GSW.weakCircularSecure_iff	theorem
GSW.Circular.lean:137	AdvancedEncryption.Homomorphic.GSW.distAdv_fheView_noEvk_le	theorem
GSW.Circular.lean:59	AdvancedEncryption.Homomorphic.GSW.FheView	abbrev
GSW.Circular.lean:63	AdvancedEncryption.Homomorphic.GSW.FheView_eq	theorem
GSW.Circular.lean:68	AdvancedEncryption.Homomorphic.GSW.Seeds	abbrev
GSW.Circular.lean:72	AdvancedEncryption.Homomorphic.GSW.Seeds_eq	theorem
GSW.Circular.lean:81	AdvancedEncryption.Homomorphic.GSW.fheView	def
GSW.Circular.lean:88	AdvancedEncryption.Homomorphic.GSW.fheView_eq	theorem
GSW.DecryptFormula.lean:104	AdvancedEncryption.Homomorphic.GSW.decryptFormula_eq	theorem
GSW.DecryptFormula.lean:113	AdvancedEncryption.Homomorphic.GSW.nandFormula	def
GSW.DecryptFormula.lean:117	AdvancedEncryption.Homomorphic.GSW.nandFormula_eq	theorem
GSW.DecryptFormula.lean:124	AdvancedEncryption.Homomorphic.GSW.decDepth	def
GSW.DecryptFormula.lean:128	AdvancedEncryption.Homomorphic.GSW.decDepth_eq	theorem
GSW.DecryptFormula.lean:143	AdvancedEncryption.Homomorphic.GSW.vecMul_secretVector_eq_sum	theorem
GSW.DecryptFormula.lean:165	AdvancedEncryption.Homomorphic.GSW.decryptFormula_eval	theorem
GSW.DecryptFormula.lean:176	AdvancedEncryption.Homomorphic.GSW.nandFormula_eval	theorem
GSW.DecryptFormula.lean:188	AdvancedEncryption.Homomorphic.GSW.depth_nandFormula_le	theorem
GSW.DecryptFormula.lean:198	AdvancedEncryption.Homomorphic.GSW.maxFanin_nandFormula_le	theorem
GSW.DecryptFormula.lean:211	AdvancedEncryption.Homomorphic.GSW.decDepth_le	theorem
GSW.DecryptFormula.lean:65	AdvancedEncryption.Homomorphic.GSW.Parameters.neZero_columns	instance
GSW.DecryptFormula.lean:73	AdvancedEncryption.Homomorphic.GSW.keyBits	def
GSW.DecryptFormula.lean:78	AdvancedEncryption.Homomorphic.GSW.keyBits_eq	theorem
GSW.DecryptFormula.lean:85	AdvancedEncryption.Homomorphic.GSW.decConstants	def
GSW.DecryptFormula.lean:89	AdvancedEncryption.Homomorphic.GSW.decConstants_eq	theorem
GSW.DecryptFormula.lean:98	AdvancedEncryption.Homomorphic.GSW.decryptFormula	def
GSW.Leveled.lean:101	AdvancedEncryption.Homomorphic.GSW.levelKey	def
GSW.Leveled.lean:107	AdvancedEncryption.Homomorphic.GSW.levelKey_eq	theorem
GSW.Leveled.lean:115	AdvancedEncryption.Homomorphic.GSW.literalCts	def
GSW.Leveled.lean:120	AdvancedEncryption.Homomorphic.GSW.literalCts_eq	theorem
GSW.Leveled.lean:125	AdvancedEncryption.Homomorphic.GSW.literalCts_castAdd	theorem
GSW.Leveled.lean:131	AdvancedEncryption.Homomorphic.GSW.literalCts_natAdd	theorem
GSW.Leveled.lean:141	AdvancedEncryption.Homomorphic.GSW.levelGate	def
GSW.Leveled.lean:146	AdvancedEncryption.Homomorphic.GSW.levelGate_of_lt	theorem
GSW.Leveled.lean:153	AdvancedEncryption.Homomorphic.GSW.levelGate_of_le	theorem
GSW.Leveled.lean:166	AdvancedEncryption.Homomorphic.GSW.leveledEval	def
GSW.Leveled.lean:173	AdvancedEncryption.Homomorphic.GSW.leveledEval_eq	theorem
GSW.Leveled.lean:185	AdvancedEncryption.Homomorphic.GSW.leveledEvalCircuit	def
GSW.Leveled.lean:192	AdvancedEncryption.Homomorphic.GSW.leveledEvalCircuit_eq	theorem
GSW.Leveled.lean:208	AdvancedEncryption.Homomorphic.GSW.encrypts_levelKey	theorem
GSW.Leveled.lean:243	AdvancedEncryption.Homomorphic.GSW.encrypts_leveledEval	theorem
GSW.Leveled.lean:277	AdvancedEncryption.Homomorphic.GSW.decrypt_keygen_leveledEvalCircuit	theorem
GSW.Leveled.lean:87	AdvancedEncryption.Homomorphic.GSW.LevelCoins	abbrev
GSW.Leveled.lean:91	AdvancedEncryption.Homomorphic.GSW.LevelCoins_eq	theorem
GSW.LeveledSecurity.lean:105	AdvancedEncryption.Homomorphic.GSW.leveledView	def
GSW.LeveledSecurity.lean:114	AdvancedEncryption.Homomorphic.GSW.leveledView_eq	theorem
GSW.LeveledSecurity.lean:128	AdvancedEncryption.Homomorphic.GSW.levelHybrid	def
GSW.LeveledSecurity.lean:138	AdvancedEncryption.Homomorphic.GSW.levelHybrid_eq	theorem
GSW.LeveledSecurity.lean:152	AdvancedEncryption.Homomorphic.GSW.levelMsgs	def
GSW.LeveledSecurity.lean:159	AdvancedEncryption.Homomorphic.GSW.levelMsgs_eq	theorem
GSW.LeveledSecurity.lean:172	AdvancedEncryption.Homomorphic.GSW.levelAssemble	def
GSW.LeveledSecurity.lean:187	AdvancedEncryption.Homomorphic.GSW.levelAssemble_eq	theorem
GSW.LeveledSecurity.lean:210	AdvancedEncryption.Homomorphic.GSW.levelReduction	def
GSW.LeveledSecurity.lean:225	AdvancedEncryption.Homomorphic.GSW.levelReduction_eq	theorem
GSW.LeveledSecurity.lean:246	AdvancedEncryption.Homomorphic.GSW.levelTerm	def
GSW.LeveledSecurity.lean:255	AdvancedEncryption.Homomorphic.GSW.levelTerm_eq	theorem
GSW.LeveledSecurity.lean:267	AdvancedEncryption.Homomorphic.GSW.challengeDist	def
GSW.LeveledSecurity.lean:275	AdvancedEncryption.Homomorphic.GSW.challengeDist_eq	theorem
GSW.LeveledSecurity.lean:288	AdvancedEncryption.Homomorphic.GSW.challengeTerm	def
GSW.LeveledSecurity.lean:296	AdvancedEncryption.Homomorphic.GSW.challengeTerm_eq	theorem
GSW.LeveledSecurity.lean:329	AdvancedEncryption.Homomorphic.GSW.distAdv_levelHybrid_le	theorem
GSW.LeveledSecurity.lean:354	AdvancedEncryption.Homomorphic.GSW.distAdv_leveledView_le	theorem
GSW.LeveledSecurity.lean:80	AdvancedEncryption.Homomorphic.GSW.LeveledSeeds	abbrev
GSW.LeveledSecurity.lean:84	AdvancedEncryption.Homomorphic.GSW.LeveledSeeds_eq	theorem
GSW.LeveledSecurity.lean:89	AdvancedEncryption.Homomorphic.GSW.LeveledView	abbrev
GSW.LeveledSecurity.lean:94	AdvancedEncryption.Homomorphic.GSW.LeveledView_eq	theorem
GSW.PolyRatio.lean:113	AdvancedEncryption.Homomorphic.GSW.bootRatio_le_poly	theorem
GSW.PolyRatio.lean:133	AdvancedEncryption.Homomorphic.GSW.decrypt_fheEval_of_ratio	theorem
GSW.PolyRatio.lean:161	AdvancedEncryption.Homomorphic.GSW.decrypt_leveledEval_of_ratio	theorem
GSW.PolyRatio.lean:69	AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily	def
GSW.PolyRatio.lean:81	AdvancedEncryption.Homomorphic.GSW.pBoot	def
GSW.PolyRatio.lean:90	AdvancedEncryption.Homomorphic.GSW.pBoot_eq	theorem
LWE/BitEncoding.lean:121	TCSlib.Cryptography.LWE.BitEncoding.decodeLo	def
LWE/BitEncoding.lean:125	TCSlib.Cryptography.LWE.BitEncoding.decodeLo_eq	theorem
LWE/BitEncoding.lean:130	TCSlib.Cryptography.LWE.BitEncoding.decodeHi	def
LWE/BitEncoding.lean:134	TCSlib.Cryptography.LWE.BitEncoding.decodeHi_eq	theorem
LWE/BitEncoding.lean:151	TCSlib.Cryptography.LWE.BitEncoding.decode_iff_mem_Ico	theorem
LWE/Ratio.lean:49	TCSlib.Cryptography.LWE.Family.RatioBounded	def
LWE/Ratio.lean:54	TCSlib.Cryptography.LWE.Family.ratioBounded_iff	theorem

## 2. same last component declared elsewhere (TCSlib + audits at records and main; Mathlib; Batteries)
-- 9ae6b909305f868f51f5cc05787c66e4d336bf74
TCSlib/Complexity/Randomized/PPT.lean:223:abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
TCSlib/Complexity/TuringMachine/Build/Embed.lean:1092:def Cfg.select {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
TCSlib/Cryptography/RSA.lean:476:structure PublicKey where
TCSlib/Cryptography/Randomness/Extraction/Rejection.lean:185:def select (D : α → Bool) : (t : ℕ) → (Fin (t + 1) → α) → α
TCSlib/Cryptography/SecureComputation/Hybrid.lean:146:abbrev Coins (n : ℕ) : Type := H.main.ExecCoins H.main.P (List.replicate n true)
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:132:abbrev Coins (S : Strategy) (n : ℕ) : Type := Fin (S.coinLen n) → Bool
-- acea851c1dbafae140d481d91827dcf72ba31c74
TCSlib/Complexity/TuringMachine/Build/Embed.lean:1092:def Cfg.select {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
TCSlib/Cryptography/RSA.lean:476:structure PublicKey where
-- Mathlib + Batteries (generic short names select/Coins/PublicKey/Secret/Seeds/KeySeed excluded)
(end)

## 3. every proof body at the head that is not rfl / Iff.rfl / sorry (read by hand)
Asymptotic.lean:91:   rw [encodeCiphertext_eq, Encoding.Modular.encodeMatrix_length]
Asymptotic.lean:108:   rw [encodeView_eq, List.length_append, LWE.encodeChallenge_length, encodeCiphertext_length]
Asymptotic.lean:132:   rw [encodeFheView_eq, List.length_append, List.length_append, LWE.encodeChallenge_length,
Asymptotic.lean:163:   have hcts : ∀ (n : ℕ) (f : Fin n → Ciphertext P),
Asymptotic.lean:168:   rw [encodeLeveledView_eq, List.length_append, List.length_append, encodeCiphertext_length,
Bootstrap.lean:153:   unfold bootGate
Bootstrap.lean:154:   rw [h]
Bootstrap.lean:161:   unfold bootGate
Bootstrap.lean:162:   rw [h]
Bootstrap.lean:169:   unfold bootGate
Bootstrap.lean:170:   rw [h]
Bootstrap.lean:305:   rw [evalKey_eq]
Bootstrap.lean:306:   exact encrypts_encrypt P A s e B he (keyBits P s i) (R i)
DecryptFormula.lean:66:   ⟨Nat.mul_ne_zero (Nat.succ_ne_zero _)
Leveled.lean:127:   rw [literalCts_eq, Fin.append_left]
Leveled.lean:133:   rw [literalCts_eq, Fin.append_right]
Leveled.lean:149:   unfold levelGate
Leveled.lean:150:   rw [dif_pos h]
Leveled.lean:156:   unfold levelGate
Leveled.lean:157:   rw [dif_neg (Nat.not_lt.mpr h)]
Leveled.lean:214:   rw [levelKey_eq, evalKey_eq]
Leveled.lean:215:   exact encrypts_keygen_encrypt P χ (rgs d.succ) B hχ _ (R d j)
BitEncoding.lean:67:   rw [distance_eq, distance_eq, ← neg_sub x y, ZMod.natAbs_valMinAbs_neg]
BitEncoding.lean:75:   rw [distance_eq, distance_eq, distance_eq, ← sub_add_sub_cancel x y z]
BitEncoding.lean:76:   exact (ZMod.natAbs_valMinAbs_add_le (x - y) (y - z)).trans
BitEncoding.lean:84:   rw [distance_eq, distance_eq, add_sub_add_right_eq_sub]
BitEncoding.lean:93:   rw [codepoint_eq, codepoint_eq]
BitEncoding.lean:94:   simp only [Bool.false_eq_true, if_false, if_true]
BitEncoding.lean:95:   rw [distance_eq, zero_sub, ZMod.natAbs_valMinAbs_neg,
BitEncoding.lean:105:   rw [distance_eq, sub_zero]
BitEncoding.lean:106:   exact ZMod.natAbs_min_of_le_div_two P.modulus _ e
BitEncoding.lean:153:   have hq := P.modulus_ge_two
BitEncoding.lean:154:   have hv := ZMod.val_lt v
BitEncoding.lean:156:   have hh : P.modulus / 2 < P.modulus := by omega
BitEncoding.lean:157:   have hsub : (v - ((P.modulus / 2 : ℕ) : ZMod P.modulus)).val =
BitEncoding.lean:169:   rw [decode_eq, decide_eq_true_iff, distance_eq, distance_eq, codepoint_eq, codepoint_eq]
BitEncoding.lean:170:   simp only [if_true, Bool.false_eq_true, if_false, sub_zero]
BitEncoding.lean:171:   rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.valMinAbs_natAbs_eq_min, hsub, decodeLo_eq, decodeHi_eq]
BitEncoding.lean:172:   split_ifs <;> omega
BitEncoding.lean:191:   have htri := distance_triangle P (codepoint P false)
BitEncoding.lean:193:   rw [distance_codepoints, distance_symm P (codepoint P false)] at htri
BitEncoding.lean:194:   cases b
BitEncoding.lean:195:   · rw [decode_eq]
BitEncoding.lean:197:   · rw [decode_eq]

## 4. shape greps
### 4a. length of a flatten of constant-length blocks (encodeFheView_length, encodeLeveledView_length)
TCSlib/Complexity/CircuitComplexity/Encoding.lean:361:theorem gateClauses_flatten_length {n : ℕ} (b : Bool) (cs : List (TreeCircuit n)) :
TCSlib/Complexity/CircuitComplexity/Encoding.lean:382:theorem tseitin_flatten_length_le {n : ℕ} (C : TreeCircuit n) :
TCSlib/Complexity/CircuitComplexity/Encoding.lean:406:theorem toCNF_flatten_length_le {n : ℕ} (C : TreeCircuit n) :
TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean:240:theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) {c : ℕ}
TCSlib/Complexity/ClassPSPACE/TQBFHardTseitin.lean:88:private theorem length_le_length_flatMap {α β : Type} {f : α → List β} {a : α} {l : List α}
TCSlib/Complexity/Randomized/Build/StateLoop.lean:97:theorem length_flatMap_range_le (f : ℕ → List Bool) (M : ℕ) :
TCSlib/Complexity/Randomized/NPPoly.lean:191:private theorem length_flatMap_dup {α : Type*} (l : List α) :
TCSlib/Complexity/Randomized/NPPoly.lean:207:private theorem length_flatMap_range {α : Type*} (g : ℕ → List α) {c : ℕ} :
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:11873:theorem length_joinFields_add_one {Γ : Type*} (fs : List (List Γ)) (hfs : fs ≠ []) :
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean:445:theorem length_flatMap_range (F : ℕ → List Bool) {q ℓ : ℕ} (hF : ∀ i < q, (F i).length = ℓ) :
TCSlib/Cryptography/Asymptotic/UniversalLemmas.lean:217:theorem length_le_length_flatMap {α : Type*} (l : List α) (f : α → List Bool)
TCSlib/Cryptography/Authentication/Signatures/Lamport.lean:123:theorem length_flatten_ofFn {B : ℕ} : ∀ {q : ℕ} (g : Fin q → List Bool),
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Machines.lean:81:private theorem length_flatMap_range_lt (N L : ℕ) :
TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean:126:theorem length_flatMap_of_length {α : Type*} (f : α → List Bool) (b : ℕ) :
TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean:535:theorem length_flatten_of_length (b : ℕ) : ∀ L : List (List Bool),
TCSlib/Cryptography/Encryption/PublicKey/HybridMachine.lean:105:theorem length_flatten_ofFn {L : ℕ} : ∀ (j : ℕ) (f : Fin j → Fin L → Bool),
TCSlib/Cryptography/Foundations/BitLists.lean:175:theorem length_flatten_map_const {α β : Type*} (l : List α) (g : α → List β) (k : ℕ)
TCSlib/Cryptography/Foundations/BitLists.lean:182:theorem length_flatten_map_range {β : Type*} (k r : ℕ) (g : ℕ → List β)
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean:211:theorem length_flatten_ofFn {j L : ℕ} (f : Fin j → Fin L → Bool) :
TCSlib/Programs/Util/List.lean:141:theorem length_flatMap_range {k : ℕ} (n : ℕ) (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) :
TCSlib/Programs/Util/List.lean:155:theorem length_flatMap_finRange {n k : ℕ} (f : Fin n → List α) (hf : ∀ i, (f i).length = k) :
TCSlib/Programs/Util/List.lean:198:theorem length_flatMap_le (l : List α) (f : α → List β) (c : ℕ)
-- closure of GSW/Asymptotic at #377 (tools/closure.py): 134 modules; members among the files above:
TCSlib.Complexity.Randomized.Build.StateLoop
TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
TCSlib.Cryptography.Encryption.PublicKey.HybridMachine
TCSlib.Cryptography.Foundations.BitLists
-- the statements
/-- Blocks of `k` entries, one per element: `|(l.map g).flatten| = |l|·k` when every `g x` has
`k` entries (`List.length_flatten`, a sum of the constant `k`). -/
theorem length_flatten_map_const {α β : Type*} (l : List α) (g : α → List β) (k : ℕ)
    (hg : ∀ x, (g x).length = k) : (l.map g).flatten.length = l.length * k := by
  rw [List.length_flatten, List.map_map, show (List.length ∘ g) = fun _ => k from funext hg,
    List.map_const', List.sum_replicate_nat]

/-- The concatenation of `q` blocks of `B` bits has `q · B` bits. -/
theorem length_flatten_ofFn {B : ℕ} : ∀ {q : ℕ} (g : Fin q → List Bool),
    (∀ i, (g i).length = B) → (List.ofFn g).flatten.length = q * B
/-- The length of the concatenation of `j` strings of `L` bits. -/
theorem length_flatten_ofFn {L : ℕ} : ∀ (j : ℕ) (f : Fin j → Fin L → Bool),
    (List.ofFn fun i => List.ofFn (f i)).flatten.length = j * L
/-- The concatenation of `j` strings of `L` bits has `j · L` bits. -/
theorem length_flatten_ofFn {j L : ℕ} (f : Fin j → Fin L → Bool) :
    (List.ofFn fun i => List.ofFn (f i)).flatten.length = j * L := by
-- core / Mathlib / Batteries
core:Init/Data/List/Lemmas.lean:1869:@[simp, grind _=_] theorem length_flatten {L : List (List α)} : L.flatten.length = (L.map length).sum := by
core:Init/Data/List/Lemmas.lean:2046:theorem length_flatMap {l : List α} {f : α → List β} :
core:Init/Data/List/Lemmas.lean:2350:@[simp] theorem sum_replicate_nat {n : Nat} {a : Nat} : (replicate n a).sum = n * a := by
core:Init/Data/List/FinRange.lean:28:@[simp, grind =] theorem length_finRange {n : Nat} : (List.finRange n).length = n := by
Mathlib/Data/List/OfFn.lean:117:theorem ofFn_const : ∀ (n : ℕ) (c : α), (ofFn fun _ : Fin n => c) = replicate n c
Mathlib/Data/List/FinRange.lean:87:theorem ofFn_eq_map {n} {f : Fin n → α} : ofFn f = (finRange n).map f := by
(end)
-- the two proofs
        (List.ofFn fun i => encodeCiphertext P (v.2.1 i)).flatten ++ encodeCiphertext P v.2.2 :=
  rfl

/-- An encoded FHE view has `m·(n + 1)·ℓ + N·((n + 1)·N·ℓ) + (n + 1)·N·ℓ` bits. -/
theorem encodeFheView_length (P : Parameters) (v : FheView P) :
    (encodeFheView P v).length =
      P.lwe.samples * (P.lwe.dimension + 1) * P.width +
        P.columns * ((P.lwe.dimension + 1) * P.columns * P.width) +
      (List.ofFn fun d => LWE.encodeChallenge P.lwe P.width (v.1 d)).flatten ++
        (List.ofFn fun e => (List.ofFn fun j => encodeCiphertext P (v.2.1 e j)).flatten).flatten ++
        encodeCiphertext P v.2.2 := rfl

/-- An encoded leveled view has `(L + 1)·(m·(n + 1)·ℓ) + L·(N·((n + 1)·N·ℓ)) + (n + 1)·N·ℓ`
bits. -/
theorem encodeLeveledView_length (P : Parameters) (L : ℕ) (v : LeveledView P L) :
    (encodeLeveledView P L v).length =
      (L + 1) * (P.lwe.samples * (P.lwe.dimension + 1) * P.width) +
### 4b. O2 (decode_iff_mem_Ico's inline steps): ZMod val/sub lemmas in Mathlib; TCSlib
Mathlib/Data/ZMod/Basic.lean:635:theorem val_add_of_lt {n : ℕ} {a b : ZMod n} (h : a.val + b.val < n) :
Mathlib/Data/ZMod/Basic.lean:646:theorem val_add_of_le {n : ℕ} [NeZero n] {a b : ZMod n} (h : n ≤ a.val + b.val) :
Mathlib/Data/ZMod/Basic.lean:1003:theorem neg_val' {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = (n - a.val) % n :=
Mathlib/Data/ZMod/Basic.lean:1012:theorem neg_val {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = if a = 0 then 0 else n - a.val := by
Mathlib/Data/ZMod/Basic.lean:1021:theorem val_neg_of_ne_zero {n : ℕ} [nz : NeZero n] (a : ZMod n) [na : NeZero a] :
Mathlib/Data/ZMod/Basic.lean:1024:theorem val_sub {n : ℕ} [NeZero n] {a b : ZMod n} (h : b.val ≤ a.val) :
core:Init/Data/Fin/Lemmas.lean:1076:theorem coe_sub_iff_le {a b : Fin n} : (↑(a - b) : Nat) = a - b ↔ b ≤ a := by
core:Init/Data/Fin/Lemmas.lean:1089:theorem coe_sub_iff_lt {a b : Fin n} : (↑(a - b) : Nat) = n + a - b ↔ a < b := by
TCSlib/BooleanAnalysis/ThresholdFunctions/Polynomial.lean:71:lemma eval_sub (F G : MultilinearPolynomial n) :
TCSlib/Complexity/Randomized/AlgCircuit.lean:349:theorem eval_subCircuit {C C' : AlgCircuit n} (hC : C.gates ≠ []) (hC' : C'.gates ≠ [])
TCSlib/Complexity/Randomized/PolyExpr.lean:134:theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n) := by
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean:191:theorem eval_subst_tagLen (q : PolyExpr) (n : ℕ) : (q.subst tagLen).eval n = q.eval (2 * n) := by
(end)
### 4c. NeZero P.columns, width positivity (neZero_columns, LE-6b3)
(end)
core:Init/Data/Nat/Lemmas.lean:1123:@[simp] protected theorem one_lt_two_pow_iff : 1 < 2 ^ n ↔ n ≠ 0 :=
### 4d. definitions: bodies of the new definitions against phase 5, LWE, Regev and 6a (same body anywhere else?)
(end)
### 4e. G15 (distAdv_fheView_noEvk_le) and its relatives
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean:156:theorem real_uniformKey_advantage {ρ : Type*} [Fintype ρ] [Nonempty ρ]
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean:248:theorem distAdv_encrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean:287:theorem distAdv_encrypt_le_of_width {ρ : Type*} [Fintype ρ] [Nonempty ρ]
TCSlib/Cryptography/Foundations/Experiments.lean:107:theorem acceptProb_comp_equiv (e : σ ≃ τ) (X : τ → γ) (D : γ → ρ → Bool) :
TCSlib/Cryptography/Foundations/Probability.lean:175:theorem uprob_fst [Nonempty β] (p : α → Prop) : uprob (fun z : α × β => p z.1) = uprob p := by
TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean:73:theorem acceptProb_fst [Nonempty τ] (X : σ → γ) (D : γ → ρ → Bool) :
TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean:83:theorem acceptProb_snd [Nonempty τ] (X : σ → γ) (D : γ → ρ → Bool) :
TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean:141:theorem distAdv_comp (P : γ → δ) (X : σ → γ) (Y : τ → γ) (D : δ → ρ → Bool) :
### 4f. G8 decDepth_le against F10, G11/L1 against phase 5, G14/A2 readers
TCSlib/Complexity/CircuitComplexity/FormulaArith/ModSum.lean:193:theorem modSumInterval_eval {M : ℕ} {a : Fin M → ℕ} {q lo hi : ℕ} (ha : ∀ i, a i < q)
TCSlib/Complexity/CircuitComplexity/FormulaArith/ModSum.lean:365:theorem modSumDepth_le (M q : ℕ) :
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean:181:theorem homGate_encrypts (g : DAGGate) (hfan : g.args.length ≤ 2) (vals : List Bool)
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean:250:theorem eval_encrypts {k : ℕ} (Cc : DAGCircuit k) (hfan : ∀ g ∈ Cc.gates, g.args.length ≤ 2)
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean:300:theorem decrypt_keygen_eval (χ : LWE.Noise)
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean:164:theorem gadget_mulVec_decomposeVec (P : Parameters)
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean:82:theorem vecMul_secretVector_augmented (P : Parameters)
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean:162:theorem decrypt_eq_decode_dotProduct (P : Parameters)
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean:182:theorem encrypts_encrypt (P : Parameters)
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean:207:theorem encrypts_keygen_encrypt (P : Parameters) (χ : LWE.Noise)
TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean:121:theorem hybridPlant_eq {π μ γ ρ ρ' : Type*} {q : ℕ} (E : π → μ → ρ → γ)
TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean:146:theorem distAdv_multi_le_sum {κ π μ γ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ']
TCSlib/Cryptography/Foundations/Probability.lean:218:theorem abs_sub_le_sum_hybrids (P : ℕ → ℝ) (t : ℕ) :
TCSlib/Cryptography/LWE/BitEncoding.lean:123:theorem decode_codepoint_add (P : Parameters) (B : ℕ) (b : Bool) (e : ℤ)
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean:377:theorem negligible_polyExpr_mul (p : PolyExpr) {μ : ℕ → ℝ} (hμ : Negligible μ) :
TCSlib/Cryptography/Asymptotic/ReductionSupport.lean:267:theorem Negligible.polyExpr_mul {μ : ℕ → ℝ} (hμ : Negligible μ) (p : PolyExpr) :
TCSlib/Cryptography/SecureComputation/ComposeSecurity/Probability.lean:110:theorem negligible_polyExpr_mul {μ : ℕ → ℝ} (hμ : Negligible μ) (p : PolyExpr) :
### 4g. other bootstrapping / circular-security / leveled-FHE material in TCSlib
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean
TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Noise.lean
(end)

## 5. ledger and records mentions of the swept names (records 9ae6b909305f868f51f5cc05787c66e4d336bf74)
LatticeCryptographyPlan.md:587:| 2026-11-18 | **gsw-6b-statements final, phase-1 review: interim ACCEPT WITH LANDING EDITS** (`phase6/final-6b-r1/review.md`, zip `eed236ae…`; ex
LatticeCryptographyPlan.md:588:| 2026-11-18 | **6b statements rulings (Seyoon), all as recommended.** **Q-6B-W1:** accept G16 with factor 8 (constant exactly `2^70`), since r3's f
LatticeCryptographyPlan.md:593:| 2026-11-18 | **GSW 6b landed as draft PRs; phase 2 PASS on snapshot #10.** #376 (O2, `land/gsw-6b-o2` `04ba2446`, LWE/BitEncoding +58) and #377 (2
LatticeCryptographyPlan.md:594:| 2026-11-18 | **Gate 46 staged; pre-dispatch sweep found one duplicate (Seyoon's rulings).** `briefs/lattice-gsw/gates/46-gsw-6b/` (pack, dispatch,
briefs/lattice-gsw/phase6/final-6b-r1/review.md:57:| **O2** | The diff base → `5bd5ada5` is insertions only: two docstring entries, plus `decodeLo`, `decodeHi`, `decodeLo_eq`, `
briefs/lattice-gsw/phase6/final-6b-r1/review.md:139:- **`decDepth_le`** is a *weakening* of F10's `modSumDepth_le`: `ℓ` replaces `⌈log₂ q⌉` behind `decDepth`.
briefs/lattice-gsw/phase6/final-6b-r1/review.md:146:- **O2.** `hsub` has no `ZMod` lemma (see *O2*); `hcast` is a cast identity; `hh : q/2 < q` is one `omega`.
briefs/lattice-gsw/phase6/final-6b-r1/review.md:147:- **`Parameters.neZero_columns`** derives `P.width ≠ 0` from `2 ≤ q ≤ 2^ℓ` by `rw [h, pow_zero] at hle; omega`. This
briefs/lattice-gsw/phase6/final-6b-r1/review.md:152:  `List.length_flatten`, `List.ofFn_const`, `List.sum_replicate_nat`).
briefs/lattice-gsw/phase6/final-6b-r1/review.md:196:| G6B-F04 | info (borderline re-derivation) | `Parameters.neZero_columns` (`DecryptFormula.lean:65–70`) proves `P.width ≠ 0
briefs/lattice-gsw/phase6/final-6b-r1/review.md:197:| G6B-F05 | info (specialization, disclosed) | `decDepth_le` (G8) is F10's `modSumDepth_le` at `M = N` behind `decDepth`, weake
briefs/lattice-gsw/phase6/final-6b-r1/review.md:226:- **Q-6B-F2 (`decDepth_le`).**
briefs/lattice-gsw/phase6/final-6b-r1/review.md:274:compiles, so nothing is dropped); F2 A, so `decDepth_le` stays admitted.
briefs/pass-shelat-ch5-8/duplication-ledger.md:93:| DL-61 | `GSW.encodeFheView_length`, `GSW.encodeLeveledView_length` (#377, `AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean:1
(end)

## ===== pr376.diff.txt (this pack) =====

diff --git a/TCSlib/Cryptography/LWE/BitEncoding.lean b/TCSlib/Cryptography/LWE/BitEncoding.lean
index 50927a0a4..fd564ef81 100644
--- a/TCSlib/Cryptography/LWE/BitEncoding.lean
+++ b/TCSlib/Cryptography/LWE/BitEncoding.lean
@@ -17,10 +17,13 @@ set_option autoImplicit false
 * `BitEncoding.codepoint`: zero for false and `floor(q/2)` for true.
 * `BitEncoding.distance`: circular distance using Mathlib's minimal integer lift.
 * `BitEncoding.decode`: choose the nearer codepoint, breaking ties toward false.
+* `BitEncoding.decodeLo`, `BitEncoding.decodeHi`: the ends of the decoding interval.
 
 ## Main results
 
 The distance lemmas and `decode_codepoint_add` are proved below.
+`decode_iff_mem_Ico` reads decoding as the interval test
+`decodeLo P ≤ v.val < decodeHi P`.
 The last theorem gives perfect decoding under the strict separation condition
 `2 * B < q / 2`, with natural-number division.
 
@@ -113,6 +116,61 @@ theorem decode_eq (P : Parameters) (x : ZMod P.modulus) :
     decode P x =
       decide (distance P x (codepoint P true) < distance P x (codepoint P false)) := rfl
 
+/-- The lower end of the decoding interval: `decodeLo P = ⌊⌊q/2⌋/2⌋ + 1`, the least
+representative that decodes to true. Glue for the file's `decode`. -/
+def decodeLo (P : Parameters) : ℕ :=
+  P.modulus / 2 / 2 + 1
+
+/-- `decodeLo P` is `P.modulus / 2 / 2 + 1`. -/
+theorem decodeLo_eq (P : Parameters) : decodeLo P = P.modulus / 2 / 2 + 1 := rfl
+
+/-- The upper end, exclusive, of the decoding interval: `decodeHi P = ⌊(q + ⌊q/2⌋ + 1)/2⌋`,
+one more than the greatest representative that decodes to true. Glue for the file's
+`decode`. -/
+def decodeHi (P : Parameters) : ℕ :=
+  (P.modulus + P.modulus / 2 + 1) / 2
+
+/-- `decodeHi P` is `(P.modulus + P.modulus / 2 + 1) / 2`. -/
+theorem decodeHi_eq (P : Parameters) : decodeHi P = (P.modulus + P.modulus / 2 + 1) / 2 := rfl
+
+/-- **Decoding is an interval test**: a residue decodes to true exactly when its canonical
+representative lies in `[decodeLo P, decodeHi P)`,
+`decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P`. With `h = ⌊q/2⌋` the interval
+is `[⌊h/2⌋ + 1, ⌊(q + h + 1)/2⌋)`. Glue for the file's `decode`, consumed by the GSW
+decryption formula as an interval of the modular subset sum.
+
+**Proof sketch.** Write `v` for the representative `v.val < q` and `h = ⌊q/2⌋ < q`. By
+Mathlib's `ZMod.valMinAbs_natAbs_eq_min`, the natural absolute value of the minimal lift of a
+residue `y` is `min y.val (q − y.val)`; this gives both distances through `distance_eq`.
+The distance to the false codepoint (`codepoint_eq`) reads `v`. For the true codepoint `h`,
+the representative of `v − h` is `v − h` when `h ≤ v` (`ZMod.val_sub`) and `v + q − h`
+otherwise (the difference is the cast of `v + q − h`, by `ZMod.natCast_self` and
+`ZMod.natCast_zmod_val`, below `q`). `decode_eq` compares the two distances strictly; after
+the case split every case is linear arithmetic with `min` and divisions by `2`, which `omega`
+closes against `decodeLo_eq` and `decodeHi_eq`. -/
+theorem decode_iff_mem_Ico (P : Parameters) (v : ZMod P.modulus) :
+    decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P := by
+  have hq := P.modulus_ge_two
+  have hv := ZMod.val_lt v
+  -- Step 1: the representative of `v − ⌊q/2⌋`.
+  have hh : P.modulus / 2 < P.modulus := by omega
+  have hsub : (v - ((P.modulus / 2 : ℕ) : ZMod P.modulus)).val =
+      if P.modulus / 2 ≤ v.val then v.val - P.modulus / 2
+      else v.val + P.modulus - P.modulus / 2 := by
+    split_ifs with hle
+    · rw [ZMod.val_sub (by rwa [ZMod.val_natCast_of_lt hh]), ZMod.val_natCast_of_lt hh]
+    · have hcast : v - ((P.modulus / 2 : ℕ) : ZMod P.modulus) =
+          ((v.val + P.modulus - P.modulus / 2 : ℕ) : ZMod P.modulus) := by
+        rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, ZMod.natCast_zmod_val,
+          add_zero]
+      rw [hcast, ZMod.val_natCast_of_lt (by omega)]
+  -- Step 2: both distances as `min` of a representative and its complement
+  -- (`ZMod.valMinAbs_natAbs_eq_min`); linear arithmetic in every case.
+  rw [decode_eq, decide_eq_true_iff, distance_eq, distance_eq, codepoint_eq, codepoint_eq]
+  simp only [if_true, Bool.false_eq_true, if_false, sub_zero]
+  rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.valMinAbs_natAbs_eq_min, hsub, decodeLo_eq, decodeHi_eq]
+  split_ifs <;> omega
+
 /-- An error of absolute value at most `B` preserves the encoded bit whenever
 `2 * B < floor(q/2)` [Wu24, Definition 20.5 and Lecture 21, bounded-error refinement].
 

## ===== pr377-le.diff.txt (this pack) =====

diff --git a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean
index fb8a0c9b3..9c69ef4c4 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean
@@ -189,9 +189,7 @@ theorem fheEval_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k :
 /-- **Pure fully homomorphic evaluation of any fan-in-2 circuit** [BV14, Thm 2.14, p008-b003;
 BV11, Def 3.5, p014-b001]: `fheEval` on the NAND form of `Cc` (6a's conversion
 `DAGCircuit.toNANDForm`), `fheEvalCircuit P evk Cc hC cts = fheEval P evk (Cc.toNANDForm hC)
-cts`. Computable. **Compactness by typing**: the result is a `Ciphertext P` whatever `Cc`.
-While 6a's N2 (`nandGadget_correct`) is admitted, `sorryAx` reaches this definition through
-`toNANDForm` only. -/
+cts`. Computable. **Compactness by typing**: the result is a `Ciphertext P` whatever `Cc`. -/
 def fheEvalCircuit (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ}
     (Cc : DAGCircuit k) (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) :
     Ciphertext P :=
diff --git a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean
index 0f2ee7ab5..a4f9cb418 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean
@@ -63,11 +63,8 @@ open Encryption.PublicKey
 /-- The ciphertext width `N = (n+1)·ℓ` is positive: `2 ≤ q ≤ 2^ℓ` forces `ℓ ≥ 1`. The
 decryption formula has `N` inputs, and Barrington's construction needs at least one. -/
 instance Parameters.neZero_columns (P : Parameters) : NeZero P.columns :=
-  ⟨Nat.mul_ne_zero (Nat.succ_ne_zero _) fun h => by
-    have hle := P.modulus_le
-    have hq := P.lwe.modulus_ge_two
-    rw [h, pow_zero] at hle
-    omega⟩
+  ⟨Nat.mul_ne_zero (Nat.succ_ne_zero _)
+    (Nat.one_lt_two_pow_iff.mp (Nat.lt_of_lt_of_le P.lwe.modulus_ge_two P.modulus_le))⟩
 
 /-- The **key bits** of a secret `s`: the `N = (n+1)·ℓ` bits `G⁻¹(t)` of the key vector
 `t = (−s, 1)`, `keyBits P s = decomposeVec P (secretVector P s)`. They are what the
@@ -157,9 +154,8 @@ the formula layer (module docstring).
 
 **Proof sketch.** Decryption is `decode` of `⟨t, c⟩` with `t = (−s, 1)`, by the owner-side
 reader `decrypt_eq_decode_dotProduct : decrypt P s C = LWE.BitEncoding.decode P.lwe
-(secretVector P s ⬝ᵥ decryptColumn P C)` in `GSW/Scheme.lean`. It is **MISSING** at the base
-(the step exists only inside the private `decrypt_eq_decode_errorSum`), listed in the reader
-census, and lands owner-side before this fill (ruling Q-C1); the fill does not re-derive it.
+(secretVector P s ⬝ᵥ decryptColumn P C)` in `GSW/Scheme.lean` (owner-side, ruling Q-C1); the
+fill does not re-derive it.
 By G5, `⟨t, c⟩` is `∑ᵢ xᵢ·aᵢ` in `ZMod q`. Its representative is `(∑ᵢ xᵢ·aᵢ.val) mod q`
 (`ZMod.val_natCast`, `Nat.cast_sum`, `ZMod.natCast_zmod_val`).
 `LWE.BitEncoding.decode_iff_mem_Ico` (O2) turns `decode` into the interval test, and
diff --git a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
index 4f32cd5c5..9ff442590 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
@@ -44,8 +44,10 @@ L2 and L3 are admitted; L1 is proved.
 
 **Sources and reconstruction (P6-Q19 B).** The key-chain construction and the hybrid order are
 reconstructed: no ingested passage gives them. BV11 and BV14 attribute leveled bootstrapping
-to Gentry's work; that passage will be cited here once it is ingested. The statements cite
-[BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3] only.
+to Gentry's work; that passage will be cited here once it is ingested. For the leveled scheme
+the statements cite [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and
+[AP14, §5.3] only; [BV14, Def 2.12, §3.3] and [Bar89, Thm 1] are cited for compactness and the
+literal inputs.
 
 ## References
 
@@ -171,9 +173,8 @@ theorem leveledEval_eq (P : Parameters) {L k : ℕ} (lk : Fin L → Fin P.column
 part, p008-b003; BV11, Def 3.6, p014-b001]: `leveledEval` of the layered NAND form
 `(Cc.toNANDForm hC).layerNAND` (6a's N3–N13) on the literal ciphertexts,
 `leveledEvalCircuit P lk Cc hC cts = leveledEval P lk (Cc.toNANDForm hC).layerNAND
-(literalCts P cts)`. Computable. **Compactness by typing**. While 6a's N2, N12 and N13 are
-admitted, `sorryAx` reaches this definition through `toNANDForm` and `layerNAND` only.
-Reconstruction disclosed (module docstring). -/
+(literalCts P cts)`. Computable. **Compactness by typing**. Reconstruction disclosed (module
+docstring). -/
 def leveledEvalCircuit (P : Parameters) {L k : ℕ} [NeZero k]
     (lk : Fin L → Fin P.columns → Ciphertext P) (Cc : DAGCircuit k)
     (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) : Ciphertext P :=
diff --git a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
index f35498ec7..2455962c8 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
@@ -36,7 +36,7 @@ Both are admitted statement-phase targets.
 reconstructed: no ingested passage gives them. BV11 and BV14 attribute leveled bootstrapping
 to Gentry's work; that passage will be cited here once it is ingested. The statements cite
 [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3] only, with
-[GSW13, §3.2, Lemma 1] and [BV11, Def 3.1] for the one-key steps and the view.
+[GSW13, §3.2, Lemma 1], [BV11, Def 3.1] and [BV14, §2.5] for the one-key steps and the view.
 
 ## References
 
@@ -308,7 +308,7 @@ reduction's coins, r3 §H8 item 12, so the multi-ciphertext lemma is applied per
 other seeds or its proof is followed with them in the coins). The gap at `i = j` is the gap of
 `levelReduction P χ L μ e j b D` between a real LWE key and a uniform key, plus the gap
 between `b = true` and `b = false` under a uniform key: `levelReduction_eq`, `reduction_eq`,
-`hybridPlant`'s planted position, `levelAssemble_eq`, `levelHybrid_eq`, `Regev.keygen_fst`
+`hybridPlant_eq` (the planted position), `levelAssemble_eq`, `levelHybrid_eq`, `Regev.keygen_fst`
 (the planted key is distributed as `pk_{e+1}`, whose secret is otherwise unused in `H_{e+1}`),
 and the seed regrouping (`acceptProb_comp_equiv`, `OneWay.uprob_update`). As in phase 5's
 `distAdv_encrypt_le`: the two DLWE gaps are the exact advantages (`real_uniformKey_advantage`,
diff --git a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
index 1ebe41f07..334136050 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
@@ -45,9 +45,10 @@ is ingested.
 * [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
   8 June 2013: §3.1 (parameters).
 
-**Deviations.** Worst case, with an explicit polynomial (r3 §H6: `c < 2^70`), not
-[BV14, Thm 3.7]'s `Θ̃` noise rate. The constant `8` (r3 G16 wrote `4`) absorbs the floor in the
-decryption condition `2·(ℓ·β) < ⌊q/2⌋`, so that `pBoot(κ)·B(κ) < q(κ)` suffices in G17.
+**Deviations.** Worst case, with an explicit polynomial (constant `2^70`; r3 §H6 drafted
+`c < 2^70` with the factor `4`), not [BV14, Thm 3.7]'s `Θ̃` noise rate. The constant `8`
+(r3 G16 wrote `4`) absorbs the floor in the decryption condition `2·(ℓ·β) < ⌊q/2⌋`, so that
+`pBoot(κ)·B(κ) < q(κ)` suffices in G17.
 -/
 
 namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== le-g46.md (this pack) =====

# Gate 46 · landing edit LE-g46 on #377: S1 fixed (DL-61) and the [Gen09] citations

**Verdict: PASS, pushed.** `land/gsw-6b-statements` (PR #377) is now
**`7563734a8badba842223e0687c719b3b4692e9d2`** (tree `c56db4c403ccab179a994143c5f989d4f3718910`), a fast-forward of
`680be9fa45a9cf5deeb7a59820e8e86aaaa4f068` (tree `956fc086`). The base is unchanged: `land/gsw-6b-o2` at `04ba2446` (#376).

- **Rulings** (Seyoon, 2026-11-18; `LatticeCryptographyPlan.md`, last row): S1 is fixed now, proof-only (DL-61, question
  Q-G46-S1, option A); the stale "[Gen09] not ingested" docstrings are fixed in the same commit, docs only.
- **The edit:** 4 files, +63/−27 (`le-g46.diff.txt`, SHA-256
  `13267e45ba16bc23d8a47e2c2c2176bc7f4a0fdaa33f7733707c98af0d6c24f4`).
  - **S1, proof only** (`GSW/Asymptotic.lean`): `encodeFheView_length` and `encodeLeveledView_length` apply the public
    `TCSlib.Cryptography.length_flatten_map_const` (`Foundations/BitLists.lean:175`) after Mathlib's `List.ofFn_eq_map`
    and core's `List.length_finRange`. Their statements and docstrings are byte-identical.
  - **[Gen09], docs only:** `GSW/Leveled.lean` (module docstring and `levelKey`), `LeveledSecurity.lean`,
    `PolyRatio.lean` and `Asymptotic.lean`.
- **Replay:** 8 modules rebuilt on a `cp -al` copy of R2, all rc 0 with 0 errors; the `sorry` warnings are exactly the
  same 24 targets. State check 1456/1456 OK. Rebuilt oleans have link count 1. Snapshot #10 and R2 rehash 0/0/0.
- **Checks:** admissions 216, equal per module to R2. Axioms of the two lemmas unchanged, only their closure sizes
  change. Canonical coe-A on the 4 edited owners: 0 errors, request sets equal to R2's. decls2 `680be9fa` → head
  0/0/0. Lint unchanged.
- **New replay tree:** `$SP/olean-replay-6b-stmt-g46`, kept for snapshot adoption (output map, Mathlib excluded, 1487
  entries, SHA-256 **`65ca02637e05f1f781c13fcbabcc69f9fcd59d511cfca63d11820d6a7fc07f18`**).
- **The #377 description** records LE-g46 and ends with the standard two attribution lines; the REST read-back equals
  the text sent.

Run on 2026-11-18, about 07:15–07:45 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`; the job's directory is
`$SP/le-g46-work`.
- **Evidence:** `le-g46-evidence.zip`, beside this file, under `le-g46/`. Its SHA-256 is
  `313c8f4d8a841b3c53849cfd5ec238caf6f3ac5c80c4ecf048f91b753c886ae1`. Its inner `SHA256SUMS` lists 224 files and does not
  list itself; `PROVENANCE.txt` and `tools/TOOLS.txt` describe the layout.
- **Builds:** no `lake build` and no cache get. Modules ran through the recipe's `runner.py`
  (`scripts/lean_check_tree.sh`), probes and seals through `runner_full.py` (`lean -DmaxErrors=0`, no `-o`). Every
  call went through a slot gate (`pgrep -c -x lean`, wait while 3 or more run). This job ran one Lean process at a
  time; at most one other job's `lean` was running. No process was signalled.
- **Records:** nothing was committed by this job. This file, `le-g46.diff.txt`, the zip, the DL-61 update and the
  Gate 46 re-staging are left for the maintainer.

## The edit

### S1 (proof only)
- **Before** (`680be9fa`, `Asymptotic.lean:128–130`, `:157–160`): `List.length_flatten`, `← List.ofFn_comp'`,
  `List.ofFn_const` and `List.sum_replicate_nat` for each `(List.ofFn fun i => encodeCiphertext P (…)).flatten` block.
- **After:**
  - `encodeFheView_length`: `rw [encodeFheView_eq, List.length_append, List.length_append,
    LWE.encodeChallenge_length, encodeCiphertext_length, List.ofFn_eq_map, length_flatten_map_const (List.finRange
    P.columns) _ _ fun i => encodeCiphertext_length P (v.2.1 i), List.length_finRange]`.
  - `encodeLeveledView_length`: a local `hcts` (the length of `(List.ofFn fun j => encodeCiphertext P (f j)).flatten`
    for any `f : Fin n → Ciphertext P`, by the same three lemmas), then one `rw` applying `length_flatten_map_const`
    to the public-key blocks (with `LWE.encodeChallenge_length`) and to the level-key blocks (with `hcts`).
- **Code identity:** the comment-stripped diff of `Asymptotic.lean` (`stripdiff.py`, `run/commentstrip/
  stripdiff-Asymptotic.txt`) is exactly these two proofs. The raw diff touches only the module docstring and the two
  proofs; the `_length` statements and docstrings are byte-identical.
- **Direct constants** (`AxiomsG46` probe, `run/axioms/axdirect.txt`): both proofs drop `List.length_flatten`,
  `List.ofFn_comp'`, `List.ofFn_const`, `List.sum_replicate_nat` (and `encodeLeveledView_length._simp_1_1`), and now
  use `TCSlib.Cryptography.length_flatten_map_const`, `List.ofFn_eq_map` and `List.length_finRange`.

### [Gen09] citations (docs only)
- **The ingest:** `blueprint/src/references/gentry-2009-fhe-thesis.md` (DW-8, records `bdcadd85`, 2026-11-16); tag
  `Gen09` in `blueprint/src/references/sources.json`. Anchors use the physical PDF page (printed page = p − 10). No Lean
  file used the tag before this edit.
- **Passages verified in the ingest and cited:**

  | Anchor | Passage (printed page) | Cited for |
  |---|---|---|
  | `p056-b002` | §4.1, construction of `E^(d)`: "we encrypt the secret keys in reverse order" (p. 46) | the index reversal |
  | `p056-b003` | §4.1, `KeyGen` of `E^(d)`: `(sk_i, pk_i)` for `i ∈ [0, d]`, `sk̄_ij ← Encrypt(pk_{i−1}, sk_ij)` for `i ∈ [1, d]` (pp. 46–47) | the key chain |
  | `p057-b001` | §4.1, `Evaluate`: "each wire in `C_δ` connects gates at consecutive levels; if not, add trivial gates" (p. 47) | layered circuits |
  | `p059-b001` | §4.2, Thm 4.2.1, correctness (statement only ingested) (p. 49) | PolyRatio's leveled correctness |
  | `p060-b001`, `p061-b001` | §4.2, Thm 4.2.3 with its proof: Games `0..d+1`, the reduction planting `pk_k` (pp. 50–51) | the hybrid order |

- **The correspondence stated:** Gentry's level `i` is level `L − i` here. His `Enc(pk_{i−1}, sk_i)` is
  `levelKey (L − i)` (`s_{L−i}` under `pk_{L−i+1}`); his Game `k` (keys `i ≤ k` replaced) is `H_{L−k}`; his step `k → k+1`
  plants `pk_k` (here `pk_{e+1}`, `e = L − k − 1`), whose secret occurs only in encryptions already replaced. So the
  top-down order of L4/L5 is Gentry's order under the renumbering.
- **The remaining deviations, stated in `LeveledSecurity`:** a replaced level key encrypts `0`, not the bits of an
  unrelated fresh key; each level step is a hybrid over the `N` positions, not one challenge of Gentry's `ℓ`-fold
  scheme; each step reduces to DLWE (phase 5), not to the base scheme's semantic security; and the middle step between
  the two chains is phase 5's challenge step, not Gentry's Game `d + 1`.
- **Per file:**
  - `Leveled.lean`: the module's *Sources and reconstruction* paragraph (chain, reverse order, layering, the hybrid
    pointer; "Besides [Gen09] for the chain, the statements … cite …"); `levelKey`'s docstring (the chain with the
    renumbering); `## References` gains [Gen09].
  - `LeveledSecurity.lean`: the paragraph (chain, Thm 4.2.3's game order and its renumbering, the deviations);
    References.
  - `PolyRatio.lean`: the paragraph (chain, Thm 4.2.1, a pointer to Thm 4.2.3); References.
  - `Asymptotic.lean`: the paragraph (chain, Thm 4.2.3, whose loss `ℓ(d + 1)` is linear in the depth, with `L(κ)` a
    polynomial); References.
- **Kept:** the declaration-level "Reconstruction disclosed (module docstring)" pointers (L4, L5, A3, G17-leveled,
  `levelReduction` and others). They point at the updated module paragraphs. No target docstring gains a [Gen09] tag;
  that is a possible follow-up if Gate 46 asks for it (policy §2, declaration level).
- **Line widths:** every new line is at most 99 characters. Sizes: Leveled 284 → 291, LeveledSecurity 351 → 362,
  PolyRatio 175 → 179, Asymptotic 324 → 338 lines (all under 400).

### Code identity of the docs-only files (LE-g50d/e's method)
- `commentstrip50.py` (unchanged from phase 2) on `680be9fa` against the worktree before the commit and against
  `7563734a` after it: **Leveled, LeveledSecurity and PolyRatio RESULT EQUAL**, overall **RESULT OK**
  (`run/commentstrip/`).

  | File | Stripped SHA-256 (both revisions) | Comment chars | Code chars |
  |---|---|---|---|
  | `Leveled.lean` | `5f1fc80c250fac03de88f41e85eaba466107b5bf66e8fb33ed6db72d751a5929` | 11390 → 12110 | 6023 = 6023 |
  | `LeveledSecurity.lean` | `a7afe34246a05e3b42d10be0f314c8269b3273bd7dde0637eba87b0ee22908d8` | 12238 → 13205 | 9197 = 9197 |
  | `PolyRatio.lean` | `6887b3ddb681b5fd697ad355f125dd2d7737c155d3ed24f3fdc2028d10d7a058` | 6157 → 6495 | 3657 = 3657 |

- **Controls** (`controls-g46.json`, `tools/mkctl46.py`): M1 (a space after the first code `:=`), M2 (one code token)
  and M3 (one code line commented out) are caught (DIFFER) in all three files; M2/M3 are phase 2's. The negative control
  N1 changes one word inside the new [Gen09] text of each file and stays EQUAL.
- `Asymptotic.lean` is not docs-only; its stripped diff is the two proofs (above).

## Commit and push
- **Worktree:** the existing `$SP/g6b-p2/land`, on `land/gsw-6b-statements` at `680be9fa` (= `origin`), clean.
- **Commit:** `git commit -S -F <msg> -- <4 paths>` after `git add` of the same 4 paths. Subject "GSW 6b landing edit
  LE-g46 (Gate 46 sweep S1; [Gen09] citations)"; the message ends with exactly the two required trailers (raw object
  checked). Author and committer `Claude <noreply@anthropic.com>`. SSHSIG key
  `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`, the same as `680be9fa` and the records tip (key identity only,
  `sigkey.py`).
- **Push** after the replay passed: `ls-remote` gave `680be9fa`; `git push origin HEAD:land/gsw-6b-statements` gave
  `680be9fa4..7563734a8` (no force); `ls-remote` then gave `7563734a`. GitHub's REST head for #377 is `7563734a`.
- `git merge-tree --write-tree 38123ccb 7563734a` = `c56db4c4` = the head's tree. The records tip at the job
  (`e48a576c`, and `9ae6b909` at the end) is Lean-equal to `38123ccb` (0 paths under `TCSlib`, `TCSlib.lean`,
  `audits`, `scripts`, the manifests).

## Replay (snapshot recipe, on R2)
- **Pre-check:** snapshot #10 `snapmap.py verify` against `olean-snapshot.map-cf6a2266.tsv` (`84d88738…`): 1478, 0/0/0,
  RESULT OK. R2 (`$SP/olean-replay-6b-stmt`) against its map `olean-replay-6b-stmt.map-680be9fa.noMathlib.tsv`
  (`52ed7825…`): equal 1487, changed 0, added 0, removed 0. R2's `state.json` (`d76b49a7…`) checks 1456/1456 OK at
  `680be9fa` on R2 and on the copy.
- **Copy:** `cp -al $SP/olean-replay-6b-stmt $SP/olean-replay-6b-stmt-g46` (1488 files, 3346 Mathlib symlinks).
- **Export:** `git archive 7563734a` of the recipe paths into `$SP/le-g46-work/wtx`: 1608 files, 0/0/0 against the
  commit (`exportcheck.py`).
- **Plan:** `downorder.py 7563734a 680be9fa`: changed 4, **down 8**. `fullorder.py`: 1456, equal to R2's. `stateplan
  plan`: **8 to build, 1448 reused**; the queue equals `down.txt`.
- **Build** (07:24:22–07:24:37, max RSS 4.6 GB, `tools/run-build-g46.sh`, the recipe's `runner.py` unmodified, one
  module per call): `Leveled`, `LeveledSecurity`, `PolyRatio`, `Asymptotic`, `GSW`, `Homomorphic`,
  `AdvancedEncryption`, `TCSlib`. **8/8 rc 0**; `permod.py`: `error:` 0, `error(` 0, substring 0, 9 warnings, all
  `declaration uses 'sorry'` (Leveled 2, LeveledSecurity 2, PolyRatio 3, Asymptotic 2), no log/record mismatch.
  `warncmp` against R2's logs: 4 SAME (the facades and root, 0 warnings) and 4 SAME-TEXT (the edited files; line
  numbers shift only).
- **The 24 targets:** `admmap6b.py` over R2's 14 module logs with these 8 on top: 24 targets, 24 admitted, 24 matched,
  none extra, none twice, none missing: **RESULT EXACT**. The admitted (file, name) set equals R2's (0 diff lines
  ignoring line numbers).
- **Accept:** `stateplan update` took 8 modules; `check` at `7563734a`: **1456/1456 RESULT OK** (again at the end;
  `state.json` `ffd4d6bf…`). `linkcheck.py` against R2: rebuilt 8 with link count 1; 1448 reused hard-linked to R2's
  inodes; 0 `.ilean`; no stray symlinks; `Mathlib/` = 3346 symlinks + NthRootLemmas `c0a9cff0…`.
- **Output map:** `olean-replay-6b-stmt-g46.map-7563734a.noMathlib.tsv`, 1487 entries, `65ca0263…`. Against R2: 1483
  equal, **4 changed** (`Asymptotic`, `Leveled`, `LeveledSecurity`, `PolyRatio`; the docs files change because oleans
  store docstrings), 0 added, 0 removed. The facades and the root rebuild byte-identical. Re-verified at the end: equal.
- **Rehashes:** snapshot #10 0/0/0 at the start, after the build and at the end; R2 equal 1487 / 0 / 0 / 0 at the same
  three points, and its state check at `680be9fa` 1456/1456 OK at the end.

## Checks
- **Admissions:** `sorryscan.py` over the full order at `7563734a`: **216 in 52 modules**, byte-equal to R2's
  `lib-r2.txt` (0 diff lines).
- **decls2** (`decls2.py` over the 12 series files): **`680be9fa` → `7563734a`: 0 ADDED, 0 CHANGED, 0 REMOVED**, empty
  `.err`. Tip `38123ccb` → head: 136 ADDED / 0 / 0, identical to phase 2's ignoring line numbers.
- **Axioms:**
  - `AxiomsG46.lean` (new; `#print axioms` plus closure size and direct constants), run unchanged on R2 and on the new
    tree: `encodeFheView_length`, `encodeLeveledView_length` and `length_flatten_map_const` all use
    **`[propext, Quot.sound]`, unchanged**. Closure sizes: `encodeFheView_length` 913 → 1009,
    `encodeLeveledView_length` 914 → 1009, `length_flatten_map_const` 297 = 297.
  - **Consumers:** no declaration in `TCSlib/` or `audits/` at the head uses either lemma (`git grep`), so there are no
    consumers to re-probe.
  - The delivery's census probe (`AxiomsStmt.lean`, unchanged) on the new tree: 174 constants (153 DECL, 21 AUX); no
    non-standard axiom besides `sorryAx`; `sorryAx` in exactly the 24 targets, each tracing only itself; the named
    checks as in phase 2. Against R2's log: 198 lines equal, 0 only here, 1 only in R2: the auxiliary
    `encodeLeveledView_length._simp_1_1` (`[Quot.sound, propext]`), generated by the old `simp only` and gone with it.
- **Rule 10, canonical coe-A** (`tools/rule10_g46.sh`: phase 2's harness, collector `NmCollect` and `mkseals_coe.py`
  unchanged, `touched.json` against `38123ccb`, `SEAL_CHUNK=1000`; owners the 4 edited modules):

  | Owner | Requests (LE-g46 / R2) | Errors | Request set | Install / EOF |
  |---|---|---|---|---|
  | `GSW/Leveled` | 479 / 479 | 0 | equal | 1 / 1 |
  | `GSW/LeveledSecurity` | 1561 / 1561 | 0 | equal | 1 / 1 |
  | `GSW/PolyRatio` | 1394 / 1394 | 0 | equal | 1 / 1 |
  | `GSW/Asymptotic` | 1653 / 1653 | 0 | equal | 1 / 1 |

  Term names, term exclusions and closure modules are equal. The sealsum rows are equal. The only record difference:
  `Asymptotic` stores 25 constants instead of 26 (the dropped `_simp_1_1`), so `sealcmp46.py` prints FAIL on that field
  alone (`run/rule10/sealcmp.txt`).
- **Lint** (from the export): `campaign_style_lint TCSlib/Cryptography --check8b`: 92 FAIL / 103 WARN over 540 files;
  the FAIL/WARN line set equals R2's (0 diff lines); only the 4 INFO line-count lines change. `style_lint` on the 12
  series files: "0 findings in 12 files", byte-identical to R2's output; on the 4 edited files: 0 findings.

## PR description (#377)
- Read first with `pull_request_read` (its text matched the gate copy `pr377-description.md`, which the edits were
  applied to by exact-once replacements, `tools/prbody46.py`), then updated with
  `update_pull_request`, and read back over REST: the stored body equals the text sent (12,541 characters).
- **Added:** the LE-g46 commit and tree in *Commits*; an LE-g46 entry under *Landing edits and rulings*; an *LE-g46
  recheck* section; the merge-order line now names `olean-replay-6b-stmt-g46` and tree `c56db4c4`.
- **Changed:** size line (+2202/−1 from the tip; at most 362 lines); the P6-Q19 B disclosure line; Gate 46's line
  notes S1 fixed by LE-g46.
- **Fixed slip** (Gate 46 staging): the footer "_Generated by [Claude Code](…)_" is replaced; the body now ends with
  exactly the two standard attribution lines.

## Notes for the maintainer
- **Adoption:** on #377's merge (after #376), adopt `$SP/olean-replay-6b-stmt-g46` (map `65ca0263…` after removing
  `Mathlib/`) if the merge's Lean paths equal `c56db4c4`. `$SP/olean-replay-6b-stmt` (R2) is no longer adoptable for
  #377; it is kept because the new tree's 1448 reused oleans are its hard links (deleting it frees nothing but its 4
  superseded oleans, and R1 `olean-replay-6b-o2` stays the #376 adoption tree).
- `CLAUDE.md` asks agents to use the LeanInfoView rather than build commands for proof state. This job ran the
  snapshot recipe's checker and probes (no `lake build`) because the maintainer's phase-2 recipe requires them.
- **Cleanup:** the export `$SP/le-g46-work/wtx`, the evidence staging tree and the other scratch were removed; kept are
  `$SP/olean-replay-6b-stmt-g46` and `$SP/le-g46-work/{run,tools,probe-src}` (the run as zipped).

## ===== le-g46.diff.txt (this pack) =====

diff --git a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean
index c2d0f7693..180c8eaf5 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean
@@ -39,9 +39,11 @@ of the hypothesis [BV11, Thm 3.2; BV14, Thm 2.14 second part]: pure-FHE security
 **Compactness** holds by typing (`GSW/Bootstrap.lean`, `GSW/Leveled.lean`).
 
 **Sources and reconstruction (P6-Q19 B), for the leveled statements** (`LeveledReductionEfficient`,
-A3). The key-chain construction and the hybrid order are reconstructed: no ingested passage
-gives them. BV11 and BV14 attribute leveled bootstrapping to Gentry's work; that passage will
-be cited here once it is ingested.
+A3). The key chain is Gentry's [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003], with
+his reverse order of the levels undone (`GSW/Leveled.lean`). The level hybrid of L4–L5 follows
+[Gen09, Thm 4.2.3 and its proof, pp. 50–51, p060-b001, p061-b001] (`GSW/LeveledSecurity.lean`),
+whose reduction loses the factor `ℓ(d + 1)` (Gentry's `ℓ` is the key length), linear in the
+depth; here the number of levels `L(κ)` is a polynomial.
 
 ## References
 
@@ -54,6 +56,8 @@ be cited here once it is ingested.
   8 June 2013: §3.2.
 * [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
   17 February 2016, Definition 4.2.3.
+* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
+  September 2009: §4.1, Thm 4.2.3.
 
 **Deviations.** The asymptotic statements are over an `LWE.Family` with
 `P_κ = Parameters.ofFamily F κ` and the canonical encodings above. Machine efficiency of GSW
@@ -126,8 +130,10 @@ theorem encodeFheView_length (P : Parameters) (v : FheView P) :
         P.columns * ((P.lwe.dimension + 1) * P.columns * P.width) +
         (P.lwe.dimension + 1) * P.columns * P.width := by
   rw [encodeFheView_eq, List.length_append, List.length_append, LWE.encodeChallenge_length,
-    encodeCiphertext_length, List.length_flatten, ← List.ofFn_comp']
-  simp only [encodeCiphertext_length, List.ofFn_const, List.sum_replicate_nat]
+    encodeCiphertext_length, List.ofFn_eq_map,
+    length_flatten_map_const (List.finRange P.columns) _ _
+      fun i => encodeCiphertext_length P (v.2.1 i),
+    List.length_finRange]
 
 /-- The canonical encoding of a leveled view: the `L + 1` public keys, the `L` level keys of
 `N` ciphertexts each (level by level, position by position), and the challenge,
@@ -154,10 +160,18 @@ theorem encodeLeveledView_length (P : Parameters) (L : ℕ) (v : LeveledView P L
       (L + 1) * (P.lwe.samples * (P.lwe.dimension + 1) * P.width) +
         L * (P.columns * ((P.lwe.dimension + 1) * P.columns * P.width)) +
         (P.lwe.dimension + 1) * P.columns * P.width := by
-  rw [encodeLeveledView_eq, List.length_append, List.length_append, List.length_flatten,
-    ← List.ofFn_comp', List.length_flatten, ← List.ofFn_comp', encodeCiphertext_length]
-  simp only [LWE.encodeChallenge_length, List.length_flatten, ← List.ofFn_comp',
-    encodeCiphertext_length, List.ofFn_const, List.sum_replicate_nat]
+  have hcts : ∀ (n : ℕ) (f : Fin n → Ciphertext P),
+      (List.ofFn fun j => encodeCiphertext P (f j)).flatten.length =
+        n * ((P.lwe.dimension + 1) * P.columns * P.width) := fun n f => by
+    rw [List.ofFn_eq_map, length_flatten_map_const (List.finRange n) _ _
+      fun j => encodeCiphertext_length P (f j), List.length_finRange]
+  rw [encodeLeveledView_eq, List.length_append, List.length_append, encodeCiphertext_length,
+    List.ofFn_eq_map,
+    length_flatten_map_const (List.finRange (L + 1)) _ _
+      fun d => LWE.encodeChallenge_length P.lwe P.width (v.1 d),
+    List.ofFn_eq_map,
+    length_flatten_map_const (List.finRange L) _ _ fun e => hcts P.columns (v.2.1 e),
+    List.length_finRange, List.length_finRange]
 
 /-! ### The asymptotic hypotheses -/
 
diff --git a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
index 9ff442590..70e29cbf3 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean
@@ -42,12 +42,17 @@ L2 and L3 are admitted; L1 is proved.
 `Ciphertext P` whatever the circuit [BV14, Def 2.12, p008-b001]; only the evaluation key
 (`N·L` ciphertexts) depends on `L` [BV11, Thm 3.1, p015-b001].
 
-**Sources and reconstruction (P6-Q19 B).** The key-chain construction and the hybrid order are
-reconstructed: no ingested passage gives them. BV11 and BV14 attribute leveled bootstrapping
-to Gentry's work; that passage will be cited here once it is ingested. For the leveled scheme
-the statements cite [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and
-[AP14, §5.3] only; [BV14, Def 2.12, §3.3] and [Bar89, Thm 1] are cited for compactness and the
-literal inputs.
+**Sources and reconstruction (P6-Q19 B).** The key chain is Gentry's [Gen09, §4.1, `KeyGen` of
+`E^(d)`, pp. 46–47, p056-b003]: `d + 1` independent key pairs and, for `i ∈ [1, d]`, the
+encryptions under `pk_{i−1}` of the representation of `sk_i` as plaintexts. Gentry encrypts the
+keys in reverse order [Gen09, §4.1, p. 46, p056-b002], so his evaluation runs down the index
+(inputs under `pk_d`, decryption under `sk_0`); here it runs up, and his level `i` is level
+`L − i` (`levelKey`). His circuits are layered as well: every wire joins consecutive levels,
+with trivial gates added where needed [Gen09, §4.1, p. 47, p057-b001]. The hybrid order is
+[Gen09, Thm 4.2.3, pp. 50–51, p060-b001, p061-b001] (`GSW/LeveledSecurity.lean`). Besides
+[Gen09] for the chain, the statements of the leveled scheme cite [BV11, Thm 3.1, Def 3.6],
+[BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3]; [BV14, Def 2.12, §3.3] and
+[Bar89, Thm 1] are cited for compactness and the literal inputs.
 
 ## References
 
@@ -60,6 +65,8 @@ literal inputs.
 * [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
   exactly those languages in NC¹*, J. Comput. System Sci. 38(1) (1989), 150–164: Thm 1
   ("inputs and negated inputs").
+* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
+  September 2009: §4.1 (`KeyGen` of `E^(d)`, the reverse order, layered circuits), Thm 4.2.3.
 
 **Deviations.** `L + 1` independent key pairs in a consecutive chain (P6-Q14 B): `evk_{d+1}`
 encrypts under `pk_{d+1}` the `N` key bits of `s_d`, `N·L` ciphertexts in all. Circuits are
@@ -88,9 +95,9 @@ theorem LevelCoins_eq (P : Parameters) (L : ℕ) :
 length of the evaluation key depends on the level L"; BV14, Thm 2.14 first part, p008-b003]:
 for `d : Fin L`, the encryptions under `pk_{d+1}` of the `N` key bits of `s_d`, with the coins
 `R d`, `levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d)`. In all `N·L`
-ciphertexts. The key-chain construction is reconstructed: no ingested passage gives it; BV11
-and BV14 attribute leveled bootstrapping to Gentry's work, and that passage will be cited here
-once it is ingested. -/
+ciphertexts. The chain is [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003] with the
+levels renumbered: Gentry encrypts `sk_i` under `pk_{i−1}`, in reverse order [Gen09, §4.1,
+p. 46, p056-b002], and his level `i` is level `L − i` here. -/
 def levelKey (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P)
     (ss : Fin (L + 1) → Secret P) (R : LevelCoins P L) (d : Fin L) :
     Fin P.columns → Ciphertext P :=
diff --git a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
index 2455962c8..a07967b4b 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean
@@ -32,11 +32,20 @@ set_option autoImplicit false
 
 Both are admitted statement-phase targets.
 
-**Sources and reconstruction (P6-Q19 B).** The key-chain construction and the hybrid order are
-reconstructed: no ingested passage gives them. BV11 and BV14 attribute leveled bootstrapping
-to Gentry's work; that passage will be cited here once it is ingested. The statements cite
-[BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3] only, with
-[GSW13, §3.2, Lemma 1], [BV11, Def 3.1] and [BV14, §2.5] for the one-key steps and the view.
+**Sources and reconstruction (P6-Q19 B).** The key chain is Gentry's [Gen09, §4.1, `KeyGen` of
+`E^(d)`, pp. 46–47, p056-b003], with his reverse order of the levels undone: his level `i` is
+level `L − i` here (`GSW/Leveled.lean`). The hybrid order is his [Gen09, Thm 4.2.3 and its
+proof, pp. 50–51, p060-b001, p061-b001]: Game `k` replaces the encryptions under `pk_{i−1}` of
+`sk_i` for `i ∈ [1, k]`, and the step from Game `k` to Game `k + 1` plants the challenge key as
+`pk_k`, whose secret occurs only in encryptions already replaced. Renumbered, Game `k` is
+`H_{L−k}`, and the order is the top-down order below. The statements cite [BV11, Thm 3.1,
+Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3], with [GSW13, §3.2, Lemma 1],
+[BV11, Def 3.1] and [BV14, §2.5] for the one-key steps and the view; [Gen09] is cited here, for
+the construction. Deviations from [Gen09, Thm 4.2.3]: a replaced level key encrypts `0`, not
+the bits of an unrelated fresh key; each level step is a hybrid over the `N` positions, not one
+challenge of Gentry's `ℓ`-fold scheme `(E)^ℓ`; each step reduces to DLWE (phase 5), not to the
+semantic security of the base scheme; and the middle step between the two chains is phase 5's
+challenge step, not Gentry's Game `d + 1` (a random plaintext).
 
 ## References
 
@@ -48,6 +57,8 @@ to Gentry's work; that passage will be cited here once it is ingested. The state
   CRYPTO 2014; IACR ePrint 2014/094: §5.3.
 * [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
   8 June 2013: §3.2, Lemma 1.
+* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
+  September 2009: §4.1, Thm 4.2.3 (with its proof).
 
 **Deviations.** Levels are indexed from `0`: the level key `e : Fin L` encrypts the bits of
 `s_e` under `pk_{e+1}` (r3's `evk_d`, `d = e + 1`). The hybrid runs top-down: step `e` (from
diff --git a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
index 334136050..2995b996e 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean
@@ -31,10 +31,12 @@ set_option autoImplicit false
 All three are admitted statement-phase targets. With `LWE.Family.RatioBounded F B p` the
 condition `pBoot(κ)·B(κ) < q(κ)` is the regime of a polynomial ratio `q/B` (assumption (A2)).
 
-**Sources and reconstruction (P6-Q19 B), for the leveled statement.** The key-chain
-construction and the hybrid order are reconstructed: no ingested passage gives them. BV11 and
-BV14 attribute leveled bootstrapping to Gentry's work; that passage will be cited here once it
-is ingested.
+**Sources and reconstruction (P6-Q19 B), for the leveled statement.** The key chain is
+Gentry's [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003], with his reverse order of
+the levels undone (`GSW/Leveled.lean`); his correctness theorem for the leveled scheme is
+[Gen09, Thm 4.2.1, p. 49, p059-b001] (only its statement is ingested). The hybrid order,
+[Gen09, Thm 4.2.3, pp. 50–51, p060-b001, p061-b001], concerns security and is used in
+`GSW/LeveledSecurity.lean`, not here.
 
 ## References
 
@@ -44,6 +46,8 @@ is ingested.
   (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Thm 3.1, Def 3.6.
 * [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
   8 June 2013: §3.1 (parameters).
+* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
+  September 2009: §4.1, Thm 4.2.1, Thm 4.2.3.
 
 **Deviations.** Worst case, with an explicit polynomial (constant `2^70`; r3 §H6 drafted
 `c < 2^70` with the factor `4`), not [BV14, Thm 3.7]'s `Θ̃` noise rate. The constant `8`

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Gadget
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Security
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Asymptotic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# GSW homomorphic encryption from LWE: leveled, bootstrapped, and pure and leveled FHE

The folder also covers NAND bootstrapping, pure and leveled fully homomorphic encryption,
their security statements and the polynomial modulus-to-noise ratio (phase 6b).

## Contents

* `Gadget`: parameters, the gadget `G = I ⊗ gᵗ` and deterministic binary decomposition `G⁻¹`.
* `Noise`: the key-agnostic invariant `tᵗC = x·tᵗG + e`, asymmetric multiplication, NAND,
  sums and right-associative product chains.
* `Scheme`: public-key GSW on the existing Regev/LWE key, fresh noise and decryption.
* `Eval`: homomorphic evaluation of `BoolCircuit.DAGCircuit` and leveled correctness.
* `Security`: concrete IND-CPA hybrids from DLWE and column leftover hashing.
* `Symmetric`: batched secret-key GSW and its direct DLWE bound (optional unit).
* `Branching`: the homomorphic selector and the evaluation of permutation branching programs
  and of formulas through Barrington's construction.
* `DecryptFormula`: the key bits, decryption as a formula in them, and the augmented NAND
  formula with its depth.
* `Bootstrap`: NAND bootstrapping, pure FHE evaluation of NAND-form and fan-in-2 circuits, and
  the evaluation key.
* `Circular`: the FHE view and concrete, per-distinguisher weak circular security.
* `Leveled`: the leveled scheme, a consecutive key chain over layered NAND circuits.
* `LeveledSecurity`: IND-CPA of the leveled scheme from DLWE by a top-down key hybrid.
* `PolyRatio`: GSW parameters of an LWE family and correctness at a polynomial ratio.
* `Asymptotic`: encodings, the asymptotic hypotheses and asymptotic IND-CPA statements.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016, Section 6.1.3.
* [AP14] J. Alperin-Sheriff, C. Peikert, ePrint 2014/094, version dated 13 June 2014, Section 3.
-/

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic security of public-key, pure and leveled GSW-FHE

## Main definitions

* `encodeCiphertext`, `encodeView`, `encodeFheView`, `encodeLeveledView`: canonical bit
  encodings, built from `LWE.encodeChallenge` (public keys) and
  `Encoding.Modular.encodeMatrix` (ciphertexts), with `_eq` and `_length` readers.
* `WeakCircularSecureFamily F`: the headline hypothesis (A1), every non-uniform PPT
  distinguisher has negligible advantage on the encoded FHE views.
* `ReductionEfficient F`, `LeveledReductionEfficient F L`: the explicit reduction-efficiency
  hypotheses (A4), domination statements, not machine constructions.

## Main results

* `indCPA_of_dlweAssumption` (A1): asymptotic IND-CPA of public-key GSW (the view without the
  evaluation key) from `DLWEAssumption F` and (A4).
* `leveledINDCPA_of_dlweAssumption` (A3): asymptotic IND-CPA of leveled GSW-FHE from
  `DLWEAssumption F` and (A4), with no circular-security assumption.

Both are admitted statement-phase targets. Ruling Q-6B-1 A: r3's A2 (`fheView_negligible`) is
not a theorem; the reader `weakCircularSecureFamily_iff` is that statement, the pure-FHE reading
of the hypothesis [BV11, Thm 3.2; BV14, Thm 2.14 second part]: pure-FHE security *is* (A1).

**Compactness** holds by typing (`GSW/Bootstrap.lean`, `GSW/Leveled.lean`).

**Sources and reconstruction (P6-Q19 B), for the leveled statements** (`LeveledReductionEfficient`,
A3). The key chain is Gentry's [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003], with
his reverse order of the levels undone (`GSW/Leveled.lean`). The level hybrid of L4–L5 follows
[Gen09, Thm 4.2.3 and its proof, pp. 50–51, p060-b001, p061-b001] (`GSW/LeveledSecurity.lean`),
whose reduction loses the factor `ℓ(d + 1)` (Gentry's `ℓ` is the key length), linear in the
depth; here the number of levels `L(κ)` is a polynomial.

## References

* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.1, Thm 3.1, Thm 3.2,
  Def 3.8.
* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Thm 2.14, Thm 3.7.
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
  8 June 2013: §3.2.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.3.
* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
  September 2009: §4.1, Thm 4.2.3.

**Deviations.** The asymptotic statements are over an `LWE.Family` with
`P_κ = Parameters.ofFamily F κ` and the canonical encodings above. Machine efficiency of GSW
encryption is not proved: there is no machine-level GSW encryptor (out of scope, as for phase 5),
so the encryption reductions are covered by the explicit hypotheses (A4), stated as domination of
real-valued advantages, which needs no transport between `(ofFamily F κ).lwe` and
`F.parameters κ`.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Complexity
open Encryption.PublicKey

/-! ### Encodings -/

/-- The canonical bit encoding of a ciphertext: its `(n+1) × N` entries row by row, `ℓ` bits
each, `encodeCiphertext P C = Encoding.Modular.encodeMatrix P.width C` [Pei16, Def 4.2.3,
p024-b001, the binary representation convention]. -/
def encodeCiphertext (P : Parameters) (C : Ciphertext P) : List Bool :=
  Encoding.Modular.encodeMatrix P.width C

/-- `encodeCiphertext P C` is `Encoding.Modular.encodeMatrix P.width C`. -/
theorem encodeCiphertext_eq (P : Parameters) (C : Ciphertext P) :
    encodeCiphertext P C = Encoding.Modular.encodeMatrix P.width C := rfl

/-- An encoded ciphertext has `(n + 1)·N·ℓ` bits:
`(encodeCiphertext P C).length = (P.lwe.dimension + 1) * P.columns * P.width`. -/
theorem encodeCiphertext_length (P : Parameters) (C : Ciphertext P) :
    (encodeCiphertext P C).length = (P.lwe.dimension + 1) * P.columns * P.width := by
  rw [encodeCiphertext_eq, Encoding.Modular.encodeMatrix_length]

/-- The canonical encoding of a phase-5 view `(pk, ct)`: the public key as an LWE challenge
(`LWE.encodeChallenge`, width `ℓ`) followed by the ciphertext,
`encodeView P v = LWE.encodeChallenge P.lwe P.width v.1 ++ encodeCiphertext P v.2`. -/
def encodeView (P : Parameters) (v : PublicKey P × Ciphertext P) : List Bool :=
  LWE.encodeChallenge P.lwe P.width v.1 ++ encodeCiphertext P v.2

/-- `encodeView P v` is `LWE.encodeChallenge P.lwe P.width v.1 ++ encodeCiphertext P v.2`. -/
theorem encodeView_eq (P : Parameters) (v : PublicKey P × Ciphertext P) :
    encodeView P v = LWE.encodeChallenge P.lwe P.width v.1 ++ encodeCiphertext P v.2 := rfl

/-- An encoded view has `m·(n + 1)·ℓ + (n + 1)·N·ℓ` bits. -/
theorem encodeView_length (P : Parameters) (v : PublicKey P × Ciphertext P) :
    (encodeView P v).length =
      P.lwe.samples * (P.lwe.dimension + 1) * P.width +
        (P.lwe.dimension + 1) * P.columns * P.width := by
  rw [encodeView_eq, List.length_append, LWE.encodeChallenge_length, encodeCiphertext_length]

/-- The canonical encoding of an FHE view `(pk, evk, ct)`: the public key, the `N`
evaluation-key ciphertexts in order, and the challenge,
`encodeFheView P v = LWE.encodeChallenge P.lwe P.width v.1 ++
(List.ofFn fun i => encodeCiphertext P (v.2.1 i)).flatten ++ encodeCiphertext P v.2.2`. -/
def encodeFheView (P : Parameters) (v : FheView P) : List Bool :=
  LWE.encodeChallenge P.lwe P.width v.1 ++
    (List.ofFn fun i => encodeCiphertext P (v.2.1 i)).flatten ++ encodeCiphertext P v.2.2

/-- `encodeFheView P v` is `LWE.encodeChallenge P.lwe P.width v.1 ++
(List.ofFn fun i => encodeCiphertext P (v.2.1 i)).flatten ++ encodeCiphertext P v.2.2`. -/
theorem encodeFheView_eq (P : Parameters) (v : FheView P) :
    encodeFheView P v =
      LWE.encodeChallenge P.lwe P.width v.1 ++
        (List.ofFn fun i => encodeCiphertext P (v.2.1 i)).flatten ++ encodeCiphertext P v.2.2 :=
  rfl

/-- An encoded FHE view has `m·(n + 1)·ℓ + N·((n + 1)·N·ℓ) + (n + 1)·N·ℓ` bits. -/
theorem encodeFheView_length (P : Parameters) (v : FheView P) :
    (encodeFheView P v).length =
      P.lwe.samples * (P.lwe.dimension + 1) * P.width +
        P.columns * ((P.lwe.dimension + 1) * P.columns * P.width) +
        (P.lwe.dimension + 1) * P.columns * P.width := by
  rw [encodeFheView_eq, List.length_append, List.length_append, LWE.encodeChallenge_length,
    encodeCiphertext_length, List.ofFn_eq_map,
    length_flatten_map_const (List.finRange P.columns) _ _
      fun i => encodeCiphertext_length P (v.2.1 i),
    List.length_finRange]

/-- The canonical encoding of a leveled view: the `L + 1` public keys, the `L` level keys of
`N` ciphertexts each (level by level, position by position), and the challenge,
`encodeLeveledView P L v = (List.ofFn fun d => LWE.encodeChallenge P.lwe P.width (v.1 d)).flatten
++ (List.ofFn fun e => (List.ofFn fun j => encodeCiphertext P (v.2.1 e j)).flatten).flatten ++
encodeCiphertext P v.2.2`. -/
def encodeLeveledView (P : Parameters) (L : ℕ) (v : LeveledView P L) : List Bool :=
  (List.ofFn fun d => LWE.encodeChallenge P.lwe P.width (v.1 d)).flatten ++
    (List.ofFn fun e => (List.ofFn fun j => encodeCiphertext P (v.2.1 e j)).flatten).flatten ++
    encodeCiphertext P v.2.2

/-- `encodeLeveledView P L v` is the concatenation of the encoded public keys, the encoded level
keys and the encoded challenge (the formula of `encodeLeveledView`'s docstring). -/
theorem encodeLeveledView_eq (P : Parameters) (L : ℕ) (v : LeveledView P L) :
    encodeLeveledView P L v =
      (List.ofFn fun d => LWE.encodeChallenge P.lwe P.width (v.1 d)).flatten ++
        (List.ofFn fun e => (List.ofFn fun j => encodeCiphertext P (v.2.1 e j)).flatten).flatten ++
        encodeCiphertext P v.2.2 := rfl

/-- An encoded leveled view has `(L + 1)·(m·(n + 1)·ℓ) + L·(N·((n + 1)·N·ℓ)) + (n + 1)·N·ℓ`
bits. -/
theorem encodeLeveledView_length (P : Parameters) (L : ℕ) (v : LeveledView P L) :
    (encodeLeveledView P L v).length =
      (L + 1) * (P.lwe.samples * (P.lwe.dimension + 1) * P.width) +
        L * (P.columns * ((P.lwe.dimension + 1) * P.columns * P.width)) +
        (P.lwe.dimension + 1) * P.columns * P.width := by
  have hcts : ∀ (n : ℕ) (f : Fin n → Ciphertext P),
      (List.ofFn fun j => encodeCiphertext P (f j)).flatten.length =
        n * ((P.lwe.dimension + 1) * P.columns * P.width) := fun n f => by
    rw [List.ofFn_eq_map, length_flatten_map_const (List.finRange n) _ _
      fun j => encodeCiphertext_length P (f j), List.length_finRange]
  rw [encodeLeveledView_eq, List.length_append, List.length_append, encodeCiphertext_length,
    List.ofFn_eq_map,
    length_flatten_map_const (List.finRange (L + 1)) _ _
      fun d => LWE.encodeChallenge_length P.lwe P.width (v.1 d),
    List.ofFn_eq_map,
    length_flatten_map_const (List.finRange L) _ _ fun e => hcts P.columns (v.2.1 e),
    List.length_finRange, List.length_finRange]

/-! ### The asymptotic hypotheses -/

/-- **Weak circular security, asymptotic: the headline hypothesis** (A1; P6-Q15 A)
[BV11, Def 3.8 with Def 3.1, p015-b001, p013-b002; BV14, Thm 2.14, p008-b003]: every
non-uniform PPT distinguisher `D` has negligible advantage between the encoded FHE views of `0`
and `1` at `P_κ = Parameters.ofFamily F κ`,
`WeakCircularSecureFamily F ↔ ∀ D : NUPPT, Negligible fun κ => distAdv
(fheView P_κ (F.noise κ) false) (fheView P_κ (F.noise κ) true)
(fun v r => D.distinguisherL κ (encodeFheView P_κ v) r)`. Equivalently, each `D` satisfies the
concrete `WeakCircularSecure` at every `κ` with a negligible `ε`. Its reader
`weakCircularSecureFamily_iff` is r3's A2, the pure-FHE security statement [BV11, Thm 3.2,
p015-b001; BV14, Thm 2.14 second part, p008-b003] (ruling Q-6B-1 A). A hypothesis, never derived
from LWE. -/
def WeakCircularSecureFamily (F : LWE.Family) : Prop :=
  ∀ D : NUPPT, Negligible fun κ =>
    distAdv (fheView (Parameters.ofFamily F κ) (F.noise κ) false)
      (fheView (Parameters.ofFamily F κ) (F.noise κ) true)
      (fun v r => D.distinguisherL κ (encodeFheView (Parameters.ofFamily F κ) v) r)

/-- `WeakCircularSecureFamily F` holds exactly when every `D : NUPPT` has negligible advantage
`distAdv (fheView P_κ (F.noise κ) false) (fheView P_κ (F.noise κ) true)
(fun v r => D.distinguisherL κ (encodeFheView P_κ v) r)`, `P_κ = Parameters.ofFamily F κ`. This
reader is r3's A2 (Q-6B-1 A). -/
theorem weakCircularSecureFamily_iff (F : LWE.Family) :
    WeakCircularSecureFamily F ↔ ∀ D : NUPPT, Negligible fun κ =>
      distAdv (fheView (Parameters.ofFamily F κ) (F.noise κ) false)
        (fheView (Parameters.ofFamily F κ) (F.noise κ) true)
        (fun v r => D.distinguisherL κ (encodeFheView (Parameters.ofFamily F κ) v) r) :=
  Iff.rfl

/-- **(A4) Reduction efficiency, explicit hypothesis** (P6-Q10): for every non-uniform PPT
distinguisher `D` of encoded phase-5 views and every bit `μ`, some non-uniform PPT `D'` has, at
every `κ`, DLWE advantage at least that of phase 5's encryption reduction run on `D`,
`decisionAdvantage P_κ.lwe χ_κ (reduction P_κ μ D_κ) ≤ F.advantageAt D' κ`, with
`P_κ = ofFamily F κ`, `χ_κ = F.noise κ` and `D_κ v r = D.distinguisherL κ (encodeView P_κ v) r`
[GSW13, §3.2, Lemma 1, p009-b002, p010-b001]. It says that encrypting a fixed bit under the
challenge key with fresh binary coins, re-encoding and running `D` is polynomial-time. A
domination statement, not a machine construction: the library has no machine-level GSW
encryptor (out of scope, as for phase 5). Real-valued on both sides, so no transport between
`(ofFamily F κ).lwe` and `F.parameters κ` is needed. -/
def ReductionEfficient (F : LWE.Family) : Prop :=
  ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
    LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
        (reduction (Parameters.ofFamily F κ) μ fun v r =>
          D.distinguisherL κ (encodeView (Parameters.ofFamily F κ) v) r) ≤
      F.advantageAt D' κ

/-- `ReductionEfficient F` holds exactly when for every `D : NUPPT` and `μ` some `D' : NUPPT`
has `decisionAdvantage P_κ.lwe (F.noise κ) (reduction P_κ μ D_κ) ≤ F.advantageAt D' κ` at every
`κ` (the formula of `ReductionEfficient`'s docstring). -/
theorem reductionEfficient_iff (F : LWE.Family) :
    ReductionEfficient F ↔ ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
      LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
          (reduction (Parameters.ofFamily F κ) μ fun v r =>
            D.distinguisherL κ (encodeView (Parameters.ofFamily F κ) v) r) ≤
        F.advantageAt D' κ :=
  Iff.rfl

/-- **(A4) for the leveled hybrid** (P6-Q10, P6-Q11): for every non-uniform PPT distinguisher
`D` of encoded leveled views (`L(κ)` levels) and every bit `μ`, one non-uniform PPT `D'`
dominates, at every `κ`, the DLWE advantages of every level reduction
`levelReduction P_κ χ_κ L(κ) μ e j b D_κ` (every level `e`, position `j` and side `b`, L4) and
of the challenge reductions `reduction P_κ μ' (challengeDist P_κ χ_κ L(κ) D_κ)` (L5), with
`D_κ v r = D.distinguisherL κ (encodeLeveledView P_κ L(κ) v) r`. One `D'` serves every
`(e, j, b)`: non-uniform advice can select the worst one at each `κ` (r3 §H8 item 13). A
domination statement, not a construction; real-valued, so no type-level transport. Deviation: r3
names only the level reductions; the challenge reductions of L5's last step are added, since A3
needs them. Reconstruction disclosed (module docstring). -/
def LeveledReductionEfficient (F : LWE.Family) (L : PolyExpr) : Prop :=
  ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
    (∀ (e : Fin (L.eval κ)) (j : Fin (Parameters.ofFamily F κ).columns) (b : Bool),
      LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
          (levelReduction (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) μ e j b fun v r =>
            D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v) r) ≤
        F.advantageAt D' κ) ∧
    ∀ μ' : Bool,
      LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
          (reduction (Parameters.ofFamily F κ) μ'
            (challengeDist (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) fun v r =>
              D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v) r)) ≤
        F.advantageAt D' κ

/-- `LeveledReductionEfficient F L` holds exactly when for every `D : NUPPT` and `μ` some
`D' : NUPPT` dominates at every `κ` the DLWE advantages of every level reduction and of the
challenge reductions (the formula of `LeveledReductionEfficient`'s docstring). -/
theorem leveledReductionEfficient_iff (F : LWE.Family) (L : PolyExpr) :
    LeveledReductionEfficient F L ↔ ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
      (∀ (e : Fin (L.eval κ)) (j : Fin (Parameters.ofFamily F κ).columns) (b : Bool),
        LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
            (levelReduction (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) μ e j b fun v r =>
              D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v) r) ≤
          F.advantageAt D' κ) ∧
      ∀ μ' : Bool,
        LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
            (reduction (Parameters.ofFamily F κ) μ'
              (challengeDist (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) fun v r =>
                D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v)
                  r)) ≤
          F.advantageAt D' κ :=
  Iff.rfl

/-! ### Targets A1, A3 -/

/-- **A1. Asymptotic IND-CPA of public-key GSW** (the view without the evaluation key): for an
LWE family `F` with `DLWEAssumption F`, the reduction-efficiency hypothesis (A4) and the width
condition `(n + 1)·ℓ + 2κ ≤ m` at every `κ`, every non-uniform PPT `D` has negligible advantage
between the encoded real views of `false` and `true` at `P_κ = ofFamily F κ`,
`Negligible fun κ => distAdv (realView P_κ (F.noise κ) false) (realView P_κ (F.noise κ) true)
(fun v r => D.distinguisherL κ (encodeView P_κ v) r)` [GSW13, §3.2, p009-b002; BV11, Def 3.1,
p013-b002]. Deviation: concrete reductions covered by (A4).

**Proof sketch.** At each `κ`, phase 5's `distAdv_encrypt_le_of_width` with `w = ℓ`
(`q ≤ 2^ℓ` by the family's `modulus_le_pow`, `hm` read through `Parameters.ofFamily_lwe` and
`Parameters.ofFamily_width`) bounds the advantage by the two DLWE advantages of `reduction`
plus `N·2^{−κ}`. `heff` (`reductionEfficient_iff`) gives `D'₀`, `D'₁` dominating them by
`F.advantageAt D'ᵢ κ`, negligible by `dlweAssumption_iff`. `N = (n + 1)·ℓ` is at most
`(d(κ) + 1)·ℓ(κ)` (`dimension_le`, `PolyExpr.eval`), so `negligible_polyExpr_mul`
(`Asymptotic/EnsemblesLemmas.lean`) with `negligible_two_pow_neg` makes the last term negligible;
`Negligible.add` and `Negligible.mono` (`distAdv` is nonnegative) finish. -/
theorem indCPA_of_dlweAssumption (F : LWE.Family) (hF : LWE.DLWEAssumption F)
    (heff : ReductionEfficient F)
    (hm : ∀ κ, ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤
      (F.parameters κ).samples)
    (D : NUPPT) :
    Negligible fun κ =>
      distAdv (realView (Parameters.ofFamily F κ) (F.noise κ) false)
        (realView (Parameters.ofFamily F κ) (F.noise κ) true)
        (fun v r => D.distinguisherL κ (encodeView (Parameters.ofFamily F κ) v) r) := by
  sorry

/-- **A3. Asymptotic IND-CPA of leveled GSW-FHE from DLWE**: for an LWE family `F` with
`DLWEAssumption F`, a polynomial number of levels `L`, the leveled reduction-efficiency
hypothesis (A4) and the width condition at every `κ`, every non-uniform PPT `D` has negligible
advantage between the encoded leveled views of `false` and `true` at `P_κ = ofFamily F κ` with
`L(κ)` levels,
`Negligible fun κ => distAdv (leveledView P_κ (F.noise κ) (L.eval κ) false)
(leveledView P_κ (F.noise κ) (L.eval κ) true)
(fun v r => D.distinguisherL κ (encodeLeveledView P_κ (L.eval κ) v) r)` [BV14, Thm 3.7,
p016-b001; BV11, Thm 3.1, p015-b001]. No circular-security assumption. Reconstruction
disclosed (module docstring).

**Proof sketch.** At each `κ`, L5 (`distAdv_leveledView_le`) bounds the advantage by
`∑_{e < L(κ)} ∑_{j < N} (levelTerm₀ + levelTerm₁) + challengeTerm`. `heff`
(`leveledReductionEfficient_iff`) for `μ = false` and `μ = true` gives `D'₀`, `D'₁` dominating
every DLWE advantage in `levelTerm_eq` and `challengeTerm_eq`; `Regev.two_extractionError_le`
with `hm` bounds `2·ε_LHL ≤ 2^{−κ}`. So the bound is at most
`(2·L(κ)·N + 1)·(2·(advantageAt D'₀ κ + advantageAt D'₁ κ) + N·2^{−κ})`, a polynomial
(`(d(κ) + 1)·ℓ(κ)` bounds `N`; `PolyExpr.eval`) times negligible functions
(`dlweAssumption_iff`, `negligible_two_pow_neg`, `negligible_polyExpr_mul` from
`Asymptotic/EnsemblesLemmas.lean`, `Negligible.add`, `Negligible.mono`). -/
theorem leveledINDCPA_of_dlweAssumption (F : LWE.Family) (L : PolyExpr)
    (hF : LWE.DLWEAssumption F) (heff : LeveledReductionEfficient F L)
    (hm : ∀ κ, ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤
      (F.parameters κ).samples)
    (D : NUPPT) :
    Negligible fun κ =>
      distAdv (leveledView (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) false)
        (leveledView (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) true)
        (fun v r => D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v)
          r) := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula
import TCSlib.Complexity.CircuitComplexity.NANDForm

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# NAND bootstrapping and pure fully homomorphic evaluation (GSW)

## Main definitions

* `PublicKey`, `Secret`, `Coins`, `KeySeed`: reducible names for the phase-5 types of a public
  key, a secret, a binary coin matrix and a key-generation seed.
* `bootNoise`: the bootstrapped noise `4^(decDepth P + 1)·(2·(N·β))`.
* `bootNAND`: one bootstrapped NAND gate, the formula evaluation of `nandFormula` on the
  evaluation key.
* `bootGate`: `bootNAND` on a gate's arguments, fan-in 1 padded to `(a, a)` and fan-in 0 to
  `(G, G)`.
* `fheEval`: a NAND-form circuit run by the host `runWith` (registry row H19) with `bootGate`.
* `fheEvalCircuit`: any fan-in-2 circuit, through the NAND conversion `toNANDForm`.
* `evalKey`: the evaluation key, encryptions under the user's own `pk` of the key bits.

## Main results

* `encrypts_bootNAND` (G9): bootstrapped NAND in the key-switching form.
* `decrypt_fheEval` (G10), `decrypt_fheEvalCircuit` (G18): pure FHE correctness for circuits
  of every depth.
* `encrypts_evalKey` (G11): evaluation-key noise `m·B`, a proved citation of phase 5's
  `encrypts_encrypt`.
* `decrypt_keygen_fheEvalCircuit` (G12): correctness for honest keys and every circuit.
* `bootNoise_le` (G13): `bootNoise P β ≤ 4^33·N^19·(ℓ + ⌈log₂ N⌉ + 3)^4·(2·β)`.

The targets G9, G10, G12, G13 and G18 are admitted; G11 is proved.

**Compactness** [BV14, Def 2.12, p008-b001; BV11, Def 3.4, p014-b001; Lemma 3.3, p015-b001]
holds by typing: `fheEval` and `fheEvalCircuit` return a `Ciphertext P`, an `(n+1) × N` matrix,
whatever the circuit, so the decryption circuit is independent of the evaluated function. No
separate theorem states it (P6-Q10).

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Def 2.12, Def 2.13, Thm 2.14, Thm 3.7, Lemma 4.4.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Defs 3.4–3.5, Thms 3.1–3.2,
  Def 3.8, Lemma 3.3.

**Deviations.** Bootstrapping is NAND only (P6-Q9): a circuit is evaluated in NAND form, every
gate by the augmented formula of [BV14, Def 2.13]. A NAND gate of fan-in 1 is padded to
`(a, a)` (`NAND(a, a) = ¬a`) and one of fan-in 0 to `(G, G)` (`G` encrypts `1` with zero noise
and `NAND(1, 1) = 0 = NAND()`) (r3 §H3.9). The evaluation key holds public-key encryptions under
the user's own `pk` (P6-Q8; [BV11, Def 3.8]'s `{Enc_pk(sk[i])}_i`), not [BV14, Lemma 4.4]'s
secret-key encryptions, which costs a factor `m` in the noise. Noise and correctness are worst
case for every key and coin, not with overwhelming probability [BV14, Thm 3.7].
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

/-! ### Key and coin types -/

/-- A GSW public key: an LWE public key `(A, b)` with `A ∈ Z_q^{m×n}` and `b ∈ Z_q^m`, the type
of `Regev.keygen`'s first component and of `encrypt`'s key. Reducible notation. -/
abbrev PublicKey (P : Parameters) : Type :=
  Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
    (Fin P.lwe.samples → ZMod P.lwe.modulus)

/-- `PublicKey P` is `Matrix (Fin m) (Fin n) (ZMod q) × (Fin m → ZMod q)`. -/
theorem PublicKey_eq (P : Parameters) :
    PublicKey P = (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) := rfl

/-- A GSW secret `s ∈ Z_q^n`, the type of `Regev.keygen`'s second component. Reducible
notation. -/
abbrev Secret (P : Parameters) : Type :=
  Fin P.lwe.dimension → ZMod P.lwe.modulus

/-- `Secret P` is `Fin n → ZMod q`. -/
theorem Secret_eq (P : Parameters) : Secret P = (Fin P.lwe.dimension → ZMod P.lwe.modulus) :=
  rfl

/-- The binary coin matrix `R ∈ {0,1}^{m×N}` of one public-key GSW encryption (`encrypt`).
Reducible notation. -/
abbrev Coins (P : Parameters) : Type :=
  Matrix (Fin P.lwe.samples) (Fin P.columns) Bool

/-- `Coins P` is `Matrix (Fin m) (Fin N) Bool`. -/
theorem Coins_eq (P : Parameters) : Coins P = Matrix (Fin P.lwe.samples) (Fin P.columns) Bool :=
  rfl

/-- A key-generation seed: the public matrix, the secret and one noise seed per sample, the
seed type of `Regev.keygen P.lwe χ`. Reducible notation. -/
abbrev KeySeed (P : Parameters) (χ : LWE.Noise) : Type :=
  Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
    ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))

/-- `KeySeed P χ` is `Matrix (Fin m) (Fin n) (ZMod q) × ((Fin n → ZMod q) × (Fin m → χ.Coins))`. -/
theorem KeySeed_eq (P : Parameters) (χ : LWE.Noise) :
    KeySeed P χ = (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) := rfl

/-! ### Bootstrapping -/

/-- The **bootstrapped noise** for evaluation-key noise `β`:
`bootNoise P β = 4^(decDepth P + 1)·(2·(N·β))`, the noise of `homEvalFormula` on the augmented
NAND formula, whose depth is at most `decDepth P + 1` (r3 §H6) [BV14, Lemma 4.4, p019-b001].
It does not depend on the noise of the ciphertexts being bootstrapped. -/
def bootNoise (P : Parameters) (β : ℕ) : ℕ :=
  4 ^ (decDepth P + 1) * (2 * (P.columns * β))

/-- `bootNoise P β` is `4 ^ (decDepth P + 1) * (2 * (P.columns * β))`. -/
theorem bootNoise_eq (P : Parameters) (β : ℕ) :
    bootNoise P β = 4 ^ (decDepth P + 1) * (2 * (P.columns * β)) := rfl

/-- **One bootstrapped NAND gate** [BV14, Def 2.13, p008-b002, Thm 2.14, p008-b003; Lemma 4.4,
p019-b001]: homomorphically evaluate the augmented formula `f_{C₁,C₂}` on the evaluation key,
`bootNAND P evk C₁ C₂ = homEvalFormula P (nandFormula P C₁ C₂) evk`. Computable. -/
def bootNAND (P : Parameters) (evk : Fin P.columns → Ciphertext P) (C₁ C₂ : Ciphertext P) :
    Ciphertext P :=
  homEvalFormula P (nandFormula P C₁ C₂) evk

/-- `bootNAND P evk C₁ C₂` is `homEvalFormula P (nandFormula P C₁ C₂) evk`. -/
theorem bootNAND_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P)
    (C₁ C₂ : Ciphertext P) : bootNAND P evk C₁ C₂ = homEvalFormula P (nandFormula P C₁ C₂) evk :=
  rfl

/-- The **bootstrapped gate function** of `fheEval`: a gate is read as a NAND gate on its first
two arguments' ciphertexts (`cts.getD a 0`), fan-in 1 padded to `(a, a)` and fan-in 0 to
`(G, G)` (r3 §H3.9, disclosed). The gate's kind is not read: on a NAND-form circuit every gate
is a `¬` gate of fan-in at most two (`DAGGate.IsNAND`). It is the gate function given to the
host `runWith` (H19). Computable. -/
def bootGate (P : Parameters) (evk : Fin P.columns → Ciphertext P) (g : DAGGate)
    (cts : List (Ciphertext P)) : Ciphertext P :=
  match g.args with
  | [] => bootNAND P evk (gadget P) (gadget P)
  | [a] => bootNAND P evk (cts.getD a 0) (cts.getD a 0)
  | a :: b :: _ => bootNAND P evk (cts.getD a 0) (cts.getD b 0)

/-- A gate of fan-in 0 is bootstrapped on `(G, G)`:
`g.args = [] → bootGate P evk g cts = bootNAND P evk (gadget P) (gadget P)`. -/
theorem bootGate_of_args_eq_nil (P : Parameters) (evk : Fin P.columns → Ciphertext P)
    (g : DAGGate) (cts : List (Ciphertext P)) (h : g.args = []) :
    bootGate P evk g cts = bootNAND P evk (gadget P) (gadget P) := by
  unfold bootGate
  rw [h]

/-- A gate of fan-in 1 is bootstrapped on `(a, a)`:
`g.args = [a] → bootGate P evk g cts = bootNAND P evk (cts.getD a 0) (cts.getD a 0)`. -/
theorem bootGate_of_args_eq_singleton (P : Parameters) (evk : Fin P.columns → Ciphertext P)
    (g : DAGGate) (cts : List (Ciphertext P)) (a : ℕ) (h : g.args = [a]) :
    bootGate P evk g cts = bootNAND P evk (cts.getD a 0) (cts.getD a 0) := by
  unfold bootGate
  rw [h]

/-- A gate of fan-in at least 2 is bootstrapped on its first two arguments:
`g.args = a :: b :: l → bootGate P evk g cts = bootNAND P evk (cts.getD a 0) (cts.getD b 0)`. -/
theorem bootGate_of_args_eq_cons_cons (P : Parameters) (evk : Fin P.columns → Ciphertext P)
    (g : DAGGate) (cts : List (Ciphertext P)) (a b : ℕ) (l : List ℕ) (h : g.args = a :: b :: l) :
    bootGate P evk g cts = bootNAND P evk (cts.getD a 0) (cts.getD b 0) := by
  unfold bootGate
  rw [h]

/-- **Pure fully homomorphic evaluation** of a NAND-form circuit [BV14, Thm 2.14 second part,
p008-b003; BV11, Thm 3.2, Def 3.5, p015-b001, p014-b001]: run the host `runWith` (H19) over the
gates with the gate function `bootGate P evk`, from the input ciphertexts, and read the output
vertex (the noiseless `0` out of range):
`fheEval P evk Cc cts = (runWith (bootGate P evk) Cc.gates (List.ofFn cts)).getD Cc.output 0`.
Computable. **Compactness by typing**: the result is a `Ciphertext P` whatever `Cc`. -/
def fheEval (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ} (Cc : DAGCircuit k)
    (cts : Fin k → Ciphertext P) : Ciphertext P :=
  (runWith (bootGate P evk) Cc.gates (List.ofFn cts)).getD Cc.output 0

/-- `fheEval P evk Cc cts` is `(runWith (bootGate P evk) Cc.gates (List.ofFn cts)).getD
Cc.output 0`. -/
theorem fheEval_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ}
    (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) :
    fheEval P evk Cc cts = (runWith (bootGate P evk) Cc.gates (List.ofFn cts)).getD Cc.output 0 :=
  rfl

/-- **Pure fully homomorphic evaluation of any fan-in-2 circuit** [BV14, Thm 2.14, p008-b003;
BV11, Def 3.5, p014-b001]: `fheEval` on the NAND form of `Cc` (6a's conversion
`DAGCircuit.toNANDForm`), `fheEvalCircuit P evk Cc hC cts = fheEval P evk (Cc.toNANDForm hC)
cts`. Computable. **Compactness by typing**: the result is a `Ciphertext P` whatever `Cc`. -/
def fheEvalCircuit (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ}
    (Cc : DAGCircuit k) (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) :
    Ciphertext P :=
  fheEval P evk (Cc.toNANDForm hC) cts

/-- `fheEvalCircuit P evk Cc hC cts` is `fheEval P evk (Cc.toNANDForm hC) cts`. -/
theorem fheEvalCircuit_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ}
    (Cc : DAGCircuit k) (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) :
    fheEvalCircuit P evk Cc hC cts = fheEval P evk (Cc.toNANDForm hC) cts := rfl

/-- **The evaluation key** (P6-Q8) [BV11, Def 3.8, p015-b001: `{Enc_pk(sk[i])}_i`; BV14,
Lemma 4.4, p019-b001]: the public-key encryptions under the user's own `pk` of the `N` key bits
of `s`, `evalKey P pk s R i = encrypt P pk (keyBits P s i) (R i)`, one coin matrix per bit.
Deviation: BV14's Lemma 4.4 uses secret-key encryptions. -/
def evalKey (P : Parameters) (pk : PublicKey P) (s : Secret P) (R : Fin P.columns → Coins P)
    (i : Fin P.columns) : Ciphertext P :=
  encrypt P pk (keyBits P s i) (R i)

/-- `evalKey P pk s R i` is `encrypt P pk (keyBits P s i) (R i)`. -/
theorem evalKey_eq (P : Parameters) (pk : PublicKey P) (s : Secret P)
    (R : Fin P.columns → Coins P) (i : Fin P.columns) :
    evalKey P pk s R i = encrypt P pk (keyBits P s i) (R i) := rfl

/-! ### Targets G9–G13, G18 -/

/-- **G9. Bootstrapped NAND, key-switching form.** If every evaluation-key ciphertext `evk i`
encrypts the key bit `keyBits P s i` under the key vector `t'` with noise at most `βk`, then for
**all** ciphertexts `C₁`, `C₂` the bootstrapped gate encrypts, under `t'`, the NAND of their
decryptions under `s`, with noise at most `bootNoise P βk`:
`Encrypts P t' (!(decrypt P s C₁ && decrypt P s C₂)).toNat (bootNoise P βk)
(bootNAND P evk C₁ C₂)` [BV14, Thm 2.14, p008-b003; Lemma 4.4, p019-b001; BV11, Thm 3.1,
p015-b001]. No hypothesis on `C₁`, `C₂`. Pure FHE takes `t' = secretVector P s`; the leveled
scheme takes `s = s_{d−1}` and `t' = t_d`. Deviation: worst case; BV14's coordinate `1` is
`σ 0` here (`homEvalFormula`).

**Proof sketch.** `bootNAND_eq`, then G3 (`encrypts_homEvalFormula`) for the formula
`nandFormula P C₁ C₂` on `N` inputs (instance `Parameters.neZero_columns`) with fan-in at most
two (`maxFanin_nandFormula_le`, G8) and inputs `evk i` encrypting `keyBits P s i` (`hk`). Its
message is `(nandFormula P C₁ C₂).eval (keyBits P s)`, which is
`!(decrypt P s C₁ && decrypt P s C₂)` by G7 (`nandFormula_eval`). Its noise
`4^depth·(2·(N·βk))` is at most `bootNoise P βk` by `depth_nandFormula_le` (G8),
`Nat.pow_le_pow_right` and `bootNoise_eq`, through `Encrypts.mono`. -/
theorem encrypts_bootNAND (P : Parameters)
    {t' : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus} (s : Secret P) (βk : ℕ)
    (evk : Fin P.columns → Ciphertext P)
    (hk : ∀ i, Encrypts P t' ((keyBits P s i).toNat : ℤ) βk (evk i)) (C₁ C₂ : Ciphertext P) :
    Encrypts P t' ((!(decrypt P s C₁ && decrypt P s C₂)).toNat : ℤ) (bootNoise P βk)
      (bootNAND P evk C₁ C₂) := by
  sorry

/-- **G10. Pure-FHE correctness for NAND-form circuits of every depth.** Let `evk` encrypt
the key bits of `s` under `t = secretVector P s` with noise at most `βk`, and the inputs
`cts j` encrypt the bits `x j` with noise at most `βin`. If `2·(ℓ·βin) < ⌊q/2⌋` and
`2·(ℓ·bootNoise P βk) < ⌊q/2⌋`, then for every NAND-form circuit `Cc`, of any depth,
`decrypt P s (fheEval P evk Cc cts) = Cc.eval x` [BV14, Thm 2.14 second part, p008-b003; BV11,
Thm 3.2, Def 3.5, p015-b001, p014-b001]. Deviations: the padding of fan-in 1 to `(a, a)` and
of fan-in 0 to `(G, G)`; worst case.

**Proof sketch.** Apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from
`List.ofFn x` and `bootGate P evk` from `List.ofFn cts`, with the vertex relation "the
ciphertext encrypts the vertex's value under `t` with noise at most `βin` (an input) or
`bootNoise P βk` (a gate)", as `eval_encrypts` does for phase 5. Inputs: `hin`. A gate `g`
(a NAND gate by `isNANDForm_iff`, `DAGGate.isNAND_iff`): its arguments are earlier vertices
(`Cc.args_lt`), so they decrypt to their values by `decrypt_of_encrypts` with `hβin` or
`hboot`; the padded `G` decrypts to `true` (`encrypts_gadget`, noise `0`, `q ≥ 2`). By the
three case readers `bootGate_of_args_eq_nil`/`_singleton`/`_cons_cons` and G9
(`encrypts_bootNAND`, `t' = t`), the gate's ciphertext encrypts `!(d₁ && d₂)` with noise
`bootNoise P βk`, which is the gate's value by `DAGGate.eval_of_isNAND` (N1): `NAND() = false
= NAND(1, 1)` and `NAND(a) = ¬a = NAND(a, a)`. The output vertex is in range (`Cc.output_lt`);
`decrypt_of_encrypts` with `hβin` or `hboot` and `DAGCircuit.eval_eq`, `values_eq` finish,
through `fheEval_eq`. -/
theorem decrypt_fheEval (P : Parameters) {k : ℕ} (Cc : DAGCircuit k) (hNAND : Cc.IsNANDForm)
    (s : Secret P) (evk : Fin P.columns → Ciphertext P) (βk βin : ℕ)
    (hevk : ∀ i, Encrypts P (secretVector P s) ((keyBits P s i).toNat : ℤ) βk (evk i))
    (x : Fin k → Bool) (cts : Fin k → Ciphertext P)
    (hin : ∀ j, Encrypts P (secretVector P s) ((x j).toNat : ℤ) βin (cts j))
    (hβin : 2 * (P.width * βin) < P.lwe.modulus / 2)
    (hboot : 2 * (P.width * bootNoise P βk) < P.lwe.modulus / 2) :
    decrypt P s (fheEval P evk Cc cts) = Cc.eval x := by
  sorry

/-- **G18. Pure-FHE correctness for every fan-in-2 circuit**, through the NAND conversion:
under the hypotheses of G10, for every circuit `Cc` whose gates have at most two arguments,
`decrypt P s (fheEvalCircuit P evk Cc hC cts) = Cc.eval x` [BV14, Thm 2.14, p008-b003; BV11,
Def 3.5, p014-b001]. Deviation: NAND only (P6-Q9), through 6a's conversion.

**Proof sketch.** `fheEvalCircuit_eq`; G10 (`decrypt_fheEval`) for `Cc.toNANDForm hC`, which
is in NAND form (`DAGCircuit.toNANDForm_isNANDForm`, N4) and computes `Cc.eval`
(`DAGCircuit.toNANDForm_eval`, N3). -/
theorem decrypt_fheEvalCircuit (P : Parameters) {k : ℕ} (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (s : Secret P)
    (evk : Fin P.columns → Ciphertext P) (βk βin : ℕ)
    (hevk : ∀ i, Encrypts P (secretVector P s) ((keyBits P s i).toNat : ℤ) βk (evk i))
    (x : Fin k → Bool) (cts : Fin k → Ciphertext P)
    (hin : ∀ j, Encrypts P (secretVector P s) ((x j).toNat : ℤ) βin (cts j))
    (hβin : 2 * (P.width * βin) < P.lwe.modulus / 2)
    (hboot : 2 * (P.width * bootNoise P βk) < P.lwe.modulus / 2) :
    decrypt P s (fheEvalCircuit P evk Cc hC cts) = Cc.eval x := by
  sorry

/-- **G11. Evaluation-key noise.** For an honest public key `(A, A s + e)` with errors of
magnitude at most `B`, every evaluation-key ciphertext encrypts its key bit under
`t = secretVector P s` with noise at most `m·B`:
`Encrypts P (secretVector P s) (keyBits P s i).toNat (P.lwe.samples * B)
(evalKey P (A, LWE.noisyValues P.lwe A s e) s R i)` [BV11, Def 3.8, p015-b001; BV14, Lemma 4.4,
p019-b001]. A citation, proved: it is phase 5's `encrypts_encrypt` read through `evalKey_eq`. -/
theorem encrypts_evalKey (P : Parameters)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus)) (s : Secret P)
    (e : Fin P.lwe.samples → ℤ) (B : ℕ) (he : ∀ i, (e i).natAbs ≤ B)
    (R : Fin P.columns → Coins P) (i : Fin P.columns) :
    Encrypts P (secretVector P s) ((keyBits P s i).toNat : ℤ) (P.lwe.samples * B)
      (evalKey P (A, LWE.noisyValues P.lwe A s e) s R i) := by
  rw [evalKey_eq]
  exact encrypts_encrypt P A s e B he (keyBits P s i) (R i)

/-- **G12. Correctness for honest keys and every circuit.** For a `B`-bounded noise law, every
key-generation seed, evaluation-key coins `R`, input bits `x` with encryption coins `R'`, and
every fan-in-2 circuit `Cc`, if `2·(ℓ·bootNoise P (m·B)) < ⌊q/2⌋` then the pure FHE evaluation
under the honest evaluation key decrypts to `Cc.eval x`:
`decrypt P sk (fheEvalCircuit P (evalKey P pk sk R) Cc hC fun j => encrypt P pk (x j) (R' j)) =
Cc.eval x` with `(pk, sk) = Regev.keygen P.lwe χ rg` [BV14, Thm 3.7, p016-b001, worst case and
any depth]. Deviation: worst case for every seed; the ratio condition is explicit.

**Proof sketch.** `Regev.keygen_fst`, `Regev.keygen_snd`, `LWE.sample_fst`, `LWE.sample_snd`
write the key as `(A, A s + e)` with `eᵢ = χ.sample(seedᵢ)` bounded by `B`
(`LWE.Noise.bounded_iff`). The inputs encrypt with noise `m·B` (`encrypts_keygen_encrypt`), and
the evaluation key with noise `m·B` (G11, `encrypts_evalKey`). Since `N ≥ 1`
(`Parameters.neZero_columns`), `m·B ≤ bootNoise P (m·B)` (`bootNoise_eq`), so `hsep` also gives
the input condition. Then G18 (`decrypt_fheEvalCircuit`). -/
theorem decrypt_keygen_fheEvalCircuit (P : Parameters) (χ : LWE.Noise) (rg : KeySeed P χ)
    (B : ℕ) (hχ : χ.Bounded B) (R : Fin P.columns → Coins P) {k : ℕ} (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (x : Fin k → Bool) (R' : Fin k → Coins P)
    (hsep : 2 * (P.width * bootNoise P (P.lwe.samples * B)) < P.lwe.modulus / 2) :
    decrypt P (Regev.keygen P.lwe χ rg).2
        (fheEvalCircuit P (evalKey P (Regev.keygen P.lwe χ rg).1 (Regev.keygen P.lwe χ rg).2 R)
          Cc hC fun j => encrypt P (Regev.keygen P.lwe χ rg).1 (x j) (R' j)) =
      Cc.eval x := by
  sorry

/-- **G13. Closed form of the bootstrapped noise.** For every noise bound `β`,
`bootNoise P β ≤ 4 ^ 33 * P.columns ^ 19 * (P.width + Nat.clog 2 P.columns + 3) ^ 4 * (2 * β)`:
polynomial in `N` and `ℓ`, with no factor exponential in `ℓ` (r3 §H3.3, §H6). Glue; the
constants of r3 G13 *(fix)* are settled here: `c₀ = 33`, `c₁ = 9`, `c₂ = 2`.

**Proof sketch.** `bootNoise_eq`. If `N = 0` both sides are `0`. Otherwise `decDepth_le` (G8)
gives `decDepth P + 1 ≤ 9a + 2b + 22` with `a = ⌈log₂ N⌉` and `b = ⌈log₂ X⌉`,
`X = ℓ + ⌈log₂ N⌉ + 3 ≥ 1`. For `y ≥ 1`, `2^⌈log₂ y⌉ < 2y` (`Nat.pow_pred_clog_lt_self` for
`y ≥ 2`; `Nat.clog_one_right` for `y = 1`), so `4^⌈log₂ y⌉ ≤ 4y²`. Hence
`4^(decDepth P + 1) ≤ 4^22·(4N²)^9·(4X²)^2 = 4^33·N^18·X^4` (`Nat.pow_le_pow_right`,
`Nat.pow_le_pow_left`, `pow_mul`), and multiplying by `2·(N·β)` gives the bound
(`Nat.mul_le_mul_right`, `ring_nf`). -/
theorem bootNoise_le (P : Parameters) (β : ℕ) :
    bootNoise P β ≤
      4 ^ 33 * P.columns ^ 19 * (P.width + Nat.clog 2 P.columns + 3) ^ 4 * (2 * β) := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import TCSlib.Complexity.BranchingPrograms.Eval
import TCSlib.Complexity.BranchingPrograms.Barrington

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Homomorphic evaluation of permutation branching programs and formulas (GSW)

## Main definitions

* `select`: the homomorphic selector `select P C U V = (G − C) ⊡ U + C ⊡ V`, fresh selector
  on the left.
* `homEvalPBP`: a branching program run homomorphically, the shared host
  `BranchingProgram.evalWith` (registry row H18) instantiated with `select P`.
* `homEvalFormula`: a fan-in-2 formula through Barrington's program (output `sigma1`), read at
  coordinate `sigma1 0`.

## Main results

* `Encrypts.select` (G1): one selector step costs an additive `2·N·β`.
* `encrypts_homEvalPBP` (G2): a permutation program of length `L` gives noise `L·2·N·β`.
* `encrypts_homEvalFormula` (G3): a formula of depth `d` gives noise `4^d·2·N·β`.

All three are statement-phase targets (admitted); the definitions are total and computable.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: §3.3 (Eq. (4), Eval with Eq. (5)–(6)), Thm 3.5, Lemma 3.6 with its
  proof.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: Eq. (4.1), Lemma 4.1.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, §6.1.3 (bootstrapping).
* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1) (1989), 150–164: Thm 1.

**Deviations.** The selector carries the fresh ciphertext on the left of both products
(`(G − C) ⊡ U`, `C ⊡ V`), mirroring [BV14, Eq. (5)–(6)], which multiplies the state on the
left; with the library's `⊡` (`GSW.mul`, right operand decomposed) this order makes the noise
of a step additive in the state's noise. Noise bounds are worst case, not probabilistic
([BV14, Lemma 3.6] holds with overwhelming probability). The formula's output is coordinate
`σ 0` of the state started at `0` (Barrington's C16 reading), not [BV14]'s coordinate `1`:
a five-cycle moves `0`, so coordinate `0` would encode the complement.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit

/-- **The homomorphic selector** `select P C U V = (G − C) ⊡ U + C ⊡ V`: if `C` encrypts the
bit `b`, the result encrypts `(1 − b)·u + b·v`, selecting `U`'s message when `b = 0` and `V`'s
when `b = 1` [BV14, §3.3, Eq. (5)–(6), p014-b002, mirrored; AP14, Eq. (4.1), p011-b001].
The fresh selector ciphertext is on the left of both products (Gate 41's convention). -/
def select (P : Parameters) (C U V : Ciphertext P) : Ciphertext P :=
  mul P (gadget P - C) U + mul P C V

/-- `select P C U V` is `mul P (gadget P - C) U + mul P C V`. -/
theorem select_eq (P : Parameters) (C U V : Ciphertext P) :
    select P C U V = mul P (gadget P - C) U + mul P C V := rfl

/-- **Homomorphic evaluation of a branching program**: the host
`BranchingProgram.evalWith` (H18) with values and selectors in `Ciphertext P` and selector
`select P`, `homEvalPBP P B cts V = B.evalWith (select P) cts V`; instruction `ι` selects with
the input ciphertext `cts ι.var` [BV14, §3.3, Eval, p014-b002; AP14, Eq. (4.1), p011-b001].
For a permutation program each step is the pull form `V'_i = select (cts var) (V (σ₀⁻¹ i))
(V (σ₁⁻¹ i))` (`Instr.stepWith_of_isPermutation`). Computable. -/
def homEvalPBP (P : Parameters) {w k : ℕ} (B : BranchingProgram w k)
    (cts : Fin k → Ciphertext P) (V : Fin w → Ciphertext P) : Fin w → Ciphertext P :=
  B.evalWith (select P) cts V

/-- `homEvalPBP P B cts V` is `B.evalWith (select P) cts V`. -/
theorem homEvalPBP_eq (P : Parameters) {w k : ℕ} (B : BranchingProgram w k)
    (cts : Fin k → Ciphertext P) (V : Fin w → Ciphertext P) :
    homEvalPBP P B cts V = B.evalWith (select P) cts V := rfl

/-- **Homomorphic evaluation of a formula** [BV14, §3.3, Eval, p014-b002, with Thm 3.5,
p014-b001; Pei16, §6.1.3, p070-b001]: convert the formula `c` on `k ≥ 1` inputs to
Barrington's width-5 permutation program with output five-cycle `sigma1`, run it
homomorphically from the state `Pi.single 0 G` (an encryption of the one-hot state `0` with
zero noise), and read coordinate `sigma1 0`:
`homEvalFormula P c cts = homEvalPBP P (barrington c sigma1) cts (Pi.single 0 (gadget P))
(sigma1 0)`. Deviation: [BV14] outputs the state's coordinate `1`; here the accepting
coordinate is `σ 0` (`barrington_yield_zero`, r3 §H3.7). Computable (P6-Q13). -/
def homEvalFormula (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) : Ciphertext P :=
  homEvalPBP P (BranchingProgram.barrington c BranchingProgram.sigma1) cts
    (Pi.single 0 (gadget P)) (BranchingProgram.sigma1 0)

/-- `homEvalFormula P c cts` is `homEvalPBP P (barrington c sigma1) cts (Pi.single 0 (gadget P))`
at coordinate `sigma1 0`. -/
theorem homEvalFormula_eq (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) :
    homEvalFormula P c cts =
      homEvalPBP P (BranchingProgram.barrington c BranchingProgram.sigma1) cts
        (Pi.single 0 (gadget P)) (BranchingProgram.sigma1 0) := rfl

/-! ### Targets G1–G3 -/

/-- **G1. The selector step.** If `C` encrypts a bit `b ∈ {0, 1}` with noise at most `β` and
`U`, `V` encrypt `u`, `v` with noise at most `βV`, all under the key vector `t`, then
`select P C U V` encrypts `(1 − b)·u + b·v` with noise at most `βV + 2·(N·β)`, `N = P.columns`:
`Encrypts P t ((1 - b) * u + b * v) (βV + 2 * (P.columns * β)) (select P C U V)`
[BV14, §3.3, Eq. (5)–(6), p014-b002; Lemma 3.6 proof, p015-b002, mirrored; AP14, Eq. (4.1),
p011-b001; Lemma 4.1, p012-b001]. Deviation: worst case, and the selector sits on the left.

**Proof sketch.** `encrypts_gadget` and `Encrypts.sub` give `G − C` encrypting `1 − b` with
noise `0 + β`. `Encrypts.mul` gives `(G − C) ⊡ U` with noise `N·β + |1 − b|·βV` and `C ⊡ V` with
noise `N·β + |b|·βV`, the two products that `select_eq` exposes. `Encrypts.add` sums the
two; since `b ∈ {0, 1}`, `|1 − b| + |b| = 1`, so the noise is at most `βV + 2·(N·β)` by
`Encrypts.mono`, and the message is `(1 − b)·u + b·v`. -/
theorem Encrypts.select (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}
    {b u v : ℤ} {β βV : ℕ} {C U V : Ciphertext P} (hC : Encrypts P t b β C)
    (hU : Encrypts P t u βV U) (hV : Encrypts P t v βV V) (hb : b = 0 ∨ b = 1) :
    Encrypts P t ((1 - b) * u + b * v) (βV + 2 * (P.columns * β)) (select P C U V) := by
  sorry

/-- **G2. Homomorphic permutation-program evaluation.** For a permutation program `B` of
width `w` on `k` inputs, input ciphertexts `cts j` encrypting the bits `x j` with noise at most
`β` under `t`, and the start state `Pi.single s₀ G`, coordinate `i` of the evaluated state
encrypts the indicator of `B.yield x s₀ = i` with noise at most `B.length·(2·(N·β))`:
`Encrypts P t (decide (B.yield x s₀ = i)).toNat (B.length * (2 * (P.columns * β)))
(homEvalPBP P B cts (Pi.single s₀ (gadget P)) i)`
[BV14, Lemma 3.6, p015-b001, with its proof, p015-b002; AP14, Lemma 4.1, p012-b001].
Deviation: worst case (BV14: with overwhelming probability), for every permutation program.

**Proof sketch.** Apply the host lemma `BranchingProgram.evalWith_rel` (C7) to the
homomorphic run and to the Boolean run `evalWith (fun b u v => if b then v else u) x
(Pi.single s₀ 1)` (whose result is `Pi.single (B.yield x s₀) 1` by `evalWith_single`, C8),
with the relation at step `τ`: every coordinate `i` of the ciphertext state encrypts the
natural number at coordinate `i` of the Boolean state, with noise at most `τ·(2·(N·β))`. At
step `0`: `Pi.single` coordinates are `G` (`encrypts_gadget`) and `0` (`encrypts_zero`). Step:
the instruction is a permutation (`isPermutation_iff`), so both steps are pull forms
(`Instr.stepWith_of_isPermutation`, C6); coordinate `i` is `select (cts var) U V` with `U`, `V`
the predecessors' ciphertexts, and `Encrypts.select` (G1) with `βV = τ·(2·(N·β))` gives
`(τ + 1)·(2·(N·β))`; the messages agree because the Boolean coordinates are `0`/`1` and the
selector picks the branch of `x var`. At `τ = B.length` read `evalWith_single` and
`Pi.single_apply`. Uses the `homEvalPBP_eq` reader. -/
theorem encrypts_homEvalPBP (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}
    {w k : ℕ} (B : BranchingProgram w k) (hB : B.IsPermutation) (x : Fin k → Bool)
    (cts : Fin k → Ciphertext P) (β : ℕ)
    (hin : ∀ j, Encrypts P t ((x j).toNat : ℤ) β (cts j)) (s₀ i : Fin w) :
    Encrypts P t ((decide (B.yield x s₀ = i)).toNat : ℤ) (B.length * (2 * (P.columns * β)))
      (homEvalPBP P B cts (Pi.single s₀ (gadget P)) i) := by
  sorry

/-- **G3. Homomorphic formula evaluation.** For a formula `c` of fan-in at most two on
`k ≥ 1` inputs and input ciphertexts `cts j` encrypting the bits `x j` with noise at most `β`
under `t`, `homEvalFormula P c cts` encrypts `c.eval x` with noise at most
`4^(c.depth)·(2·(N·β))`:
`Encrypts P t (c.eval x).toNat (4 ^ c.depth * (2 * (P.columns * β))) (homEvalFormula P c cts)`
[BV14, Thm 3.5, p014-b001, with Lemma 3.6, p015-b001; Pei16, §6.1.3, p070-b001; Bar89, Thm 1,
p003-b002]. Deviation: the output coordinate is `σ 0` (BV14: coordinate `1`), worst case.

**Proof sketch.** `homEvalFormula_eq`, then G2 (`encrypts_homEvalPBP`) for the program
`barrington c sigma1`, which is a permutation program (`isPermutation_barrington`, C15), at
`s₀ = 0` and `i = sigma1 0`. Its message is `decide (yield x 0 = sigma1 0)`; by
`barrington_yield_zero` (C16, with `isFiveCycle_sigma1`) the yield at `0` is `sigma1 0` if
`c.eval x` and `0` otherwise, and `sigma1 0 ≠ 0` (a five-cycle has no fixed point:
`isFiveCycle_iff`, or by `decide` on `Fin 5`), so the message is `(c.eval x).toNat`. The noise
`length·(2·(N·β))` is at most `4^(c.depth)·(2·(N·β))` by `barrington_length_le` (C14) and
`Encrypts.mono`. -/
theorem encrypts_homEvalFormula (P : Parameters)
    {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus} {k : ℕ} [NeZero k]
    (c : TreeCircuit k) (hc : c.maxFanin ≤ 2) (x : Fin k → Bool) (cts : Fin k → Ciphertext P)
    (β : ℕ) (hin : ∀ j, Encrypts P t ((x j).toNat : ℤ) β (cts j)) :
    Encrypts P t ((c.eval x).toNat : ℤ) (4 ^ c.depth * (2 * (P.columns * β)))
      (homEvalFormula P c cts) := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Circular.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Security

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Weak circular security of public-key GSW (concrete, per distinguisher)

## Main definitions

* `FheView`, `Seeds`: reducible names for the FHE view `(pk, evk, ct)` and its seed type.
* `fheView`: the FHE view of a bit from honest key generation, the evaluation key of P6-Q8 and
  one public-key encryption.
* `WeakCircularSecure P χ D ε`: one distinguisher `D` has advantage at most `ε` between the
  FHE views of `0` and `1`; with its reader `weakCircularSecure_iff`.

## Main results

* `distAdv_fheView_noEvk_le` (G15): with the evaluation key dropped, the view inherits phase
  5's IND-CPA bound `distAdv_encrypt_le` (two DLWE advantages plus `2·N·ε_LHL`).

Ruling Q-6B-1 A: r3's G14 (`distAdv_fheView_le`) is not a theorem. The reader
`weakCircularSecure_iff` is that statement: under the hypothesis `WeakCircularSecure P χ D ε`
the advantage on the FHE views is at most `ε`. It is the security half of [BV11, Thm 3.2] and
[BV14, Thm 2.14 second part]: pure-FHE security *is* the hypothesis (A1).

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: §2.5, Thm 2.14.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.1, Thm 3.2, Def 3.8.
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
  8 June 2013: §3.2.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: §5.3.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, §6.1.2 (circular security).

**Deviations.** [BV11, Def 3.8] is asymptotic; `WeakCircularSecure` is its concrete form for
one distinguisher (P6-Q15 A), and the asymptotic `WeakCircularSecureFamily`
(`GSW/Asymptotic.lean`) is the headline hypothesis. Weak circular security is an explicit
hypothesis (A1), never derived from LWE: its truth for GSW is open [Pei16, §6.1.2].
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- The FHE view `(pk, evk, ct)`: a public key, the `N` evaluation-key ciphertexts and one
challenge ciphertext. Reducible notation. -/
abbrev FheView (P : Parameters) : Type :=
  PublicKey P × (Fin P.columns → Ciphertext P) × Ciphertext P

/-- `FheView P` is `PublicKey P × (Fin P.columns → Ciphertext P) × Ciphertext P`. -/
theorem FheView_eq (P : Parameters) :
    FheView P = (PublicKey P × (Fin P.columns → Ciphertext P) × Ciphertext P) := rfl

/-- The seeds of the FHE view: a key-generation seed, the coins of the `N` evaluation-key
encryptions and the coins of the challenge encryption. Reducible notation. -/
abbrev Seeds (P : Parameters) (χ : LWE.Noise) : Type :=
  KeySeed P χ × (Fin P.columns → Coins P) × Coins P

/-- `Seeds P χ` is `KeySeed P χ × (Fin P.columns → Coins P) × Coins P`. -/
theorem Seeds_eq (P : Parameters) (χ : LWE.Noise) :
    Seeds P χ = (KeySeed P χ × (Fin P.columns → Coins P) × Coins P) := rfl

/-- **The FHE view of a bit** `μ` [BV14, §2.5, p007-b001: "the adversary is given both pk and
evk"; BV11, Def 3.1, p013-b002]: from a seed `r = (rg, R, R₀)`, honest key generation
`(pk, s) = Regev.keygen P.lwe χ rg`, the evaluation key `evalKey P pk s R` (P6-Q8) and the
challenge `encrypt P pk μ R₀`:
`fheView P χ μ r = (pk, evalKey P pk s r.2.1, encrypt P pk μ r.2.2)`. -/
@[simps! (config := { isSimp := false }) fst snd]
def fheView (P : Parameters) (χ : LWE.Noise) (μ : Bool) (r : Seeds P χ) : FheView P :=
  ((Regev.keygen P.lwe χ r.1).1,
    evalKey P (Regev.keygen P.lwe χ r.1).1 (Regev.keygen P.lwe χ r.1).2 r.2.1,
    encrypt P (Regev.keygen P.lwe χ r.1).1 μ r.2.2)

/-- `fheView P χ μ r` is `(pk, evalKey P pk s r.2.1, encrypt P pk μ r.2.2)` with
`(pk, s) = Regev.keygen P.lwe χ r.1`. -/
theorem fheView_eq (P : Parameters) (χ : LWE.Noise) (μ : Bool) (r : Seeds P χ) :
    fheView P χ μ r =
      ((Regev.keygen P.lwe χ r.1).1,
        evalKey P (Regev.keygen P.lwe χ r.1).1 (Regev.keygen P.lwe χ r.1).2 r.2.1,
        encrypt P (Regev.keygen P.lwe χ r.1).1 μ r.2.2) := rfl

/-- **Weak circular security, concrete, for one distinguisher** (P6-Q15 A) [BV11, Def 3.8,
p015-b001; BV14, Thm 2.14, p008-b003; Pei16, §6.1.2, p068-b001]: the distinguisher `D`, with
coins in `ρ`, has advantage at most `ε` between the FHE views of `0` and `1`,
`WeakCircularSecure P χ D ε ↔ distAdv (fheView P χ false) (fheView P χ true) D ≤ ε`. A
hypothesis (A1), never derived from LWE (phase-5 Q15). Its reader `weakCircularSecure_iff` is
the security half of [BV11, Thm 3.2, p015-b001] and [BV14, Thm 2.14 second part, p008-b003]
(ruling Q-6B-1 A: r3's G14). Deviation: BV11's definition is asymptotic, and
`WeakCircularSecureFamily` is the headline form. It is stated per distinguisher because,
quantified over **every** function `FheView P → ρ → Bool`, it would hold only for `ε` near `1`:
an unbounded distinguisher recovers `s` from `pk` and decrypts the challenge. -/
def WeakCircularSecure (P : Parameters) (χ : LWE.Noise) {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (D : FheView P → ρ → Bool) (ε : ℝ) : Prop :=
  distAdv (fheView P χ false) (fheView P χ true) D ≤ ε

/-- `WeakCircularSecure P χ D ε` holds exactly when
`distAdv (fheView P χ false) (fheView P χ true) D ≤ ε`. This reader is r3's G14 (Q-6B-1 A). -/
theorem weakCircularSecure_iff (P : Parameters) (χ : LWE.Noise) {ρ : Type*} [Fintype ρ]
    [Nonempty ρ] (D : FheView P → ρ → Bool) (ε : ℝ) :
    WeakCircularSecure P χ D ε ↔ distAdv (fheView P χ false) (fheView P χ true) D ≤ ε :=
  Iff.rfl

/-! ### Target G15 -/

/-- **G15. Without the evaluation key, the FHE view is phase 5's.** For every distinguisher
`D` of `(pk, ct)` pairs and all bits `μ₀`, `μ₁`, the views `(pk, encrypt pk μ R₀)` read off
`fheView`'s seeds (the evaluation key dropped) differ by at most two DLWE advantages plus
`2·(N·ε_LHL)`, phase 5's bound:
`distAdv (fun r => ((fheView P χ μ₀ r).1, (fheView P χ μ₀ r).2.2))
(fun r => ((fheView P χ μ₁ r).1, (fheView P χ μ₁ r).2.2)) D ≤
decisionAdvantage P.lwe χ (reduction P μ₀ D) + decisionAdvantage P.lwe χ (reduction P μ₁ D) +
2 * (P.columns * Regev.extractionError P.lwe)` [GSW13, §3.2, p009-b002; AP14, §5.3,
p015-b002]. Stated over the projection of `fheView`, not over `realView`, of which it would be
a restatement (G45-01); its content is the transport of `distAdv_encrypt_le` along the coin
regrouping.

**Proof sketch.** Through `fheView_fst`, `fheView_snd` (or `fheView_eq`), `Regev.keygen_fst`
and `realView_eq`, `view_eq`, the projected view at a seed `(rg, R, R₀)` is
`realView P χ μ (rg, R₀)`: it does not read the evaluation-key coins `R`. Through
`acceptProb_def` and `acceptProb_comp_equiv`, regroup the seed-and-coin space so that the
unused coins `R` form the second factor, `((KeySeed P χ × Coins P) × ρ) × (Fin N → Coins P)`
(`Equiv.prodComm`, `Equiv.prodAssoc`); the marginalization lemma `uprob_fst`
(`Foundations/Probability.lean`) then drops that factor, so each `acceptProb` equals that of
`realView P χ μ`. Then `distAdv_def` and phase 5's `distAdv_encrypt_le`. -/
theorem distAdv_fheView_noEvk_le (P : Parameters) (χ : LWE.Noise) {ρ : Type*} [Fintype ρ]
    [Nonempty ρ] (μ₀ μ₁ : Bool) (D : PublicKey P × Ciphertext P → ρ → Bool) :
    distAdv (fun r : Seeds P χ => ((fheView P χ μ₀ r).1, (fheView P χ μ₀ r).2.2))
        (fun r : Seeds P χ => ((fheView P χ μ₁ r).1, (fheView P χ μ₁ r).2.2)) D ≤
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
        LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) +
        2 * (P.columns * Regev.extractionError P.lwe) := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The GSW decryption formula and the augmented NAND formula

## Main definitions

* `keyBits`: the `N` key bits `G⁻¹(t)` of `t = (−s, 1)`, the bits the evaluation key encrypts.
* `decConstants`: the public constants `Gᵀc` of a ciphertext, `c` its decryption column.
* `decryptFormula`: decryption as a fan-in-2 formula in the key bits, the modular interval sum
  `FormulaArith.modSumInterval` over the constants with the decoding interval of O2.
* `nandFormula`: BV14's augmented decryption function `f_{C₁,C₂}`, `¬(Dec C₁ ∧ Dec C₂)`, one key
  block.
* `decDepth`: the depth bound `FormulaArith.modSumDepth N q` of the decryption formula.
* The instance `Parameters.neZero_columns`: `N = (n+1)·ℓ ≥ 1`, since `2 ≤ q ≤ 2^ℓ`.

## Main results

* `vecMul_secretVector_eq_sum` (G5): `⟨t, c⟩ = ∑ᵢ xᵢ·(Gᵀc)ᵢ` with `x = keyBits`.
* `decryptFormula_eval` (G6), `nandFormula_eval` (G7): the formulas compute decryption and its
  NAND on the key bits.
* `depth_nandFormula_le`, `maxFanin_nandFormula_le`, `decDepth_le` (G8): depth `decDepth + 1`,
  fan-in two, and the closed form `9⌈log₂ N⌉ + 2⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉ + 21`, with no term
  linear in `ℓ`.

All are statement-phase targets (admitted); the definitions and the instance are proved.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Prop 3.4, Def 2.13, Lemma 4.4.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.7, Lemma 4.5 with its
  proof. [BV14] cites this lemma as "[BV11, Lemma 4.1]"; it is Lemma 4.5 in the version held.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: §5.1.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, §5.4.3 (the gadget `G` and `G⁻¹`).

**Deviations.** Decryption is the library's: the decryption column `c = C·G⁻¹(⌊q/2⌋·e_{n+1})`
decoded by `LWE.BitEncoding.decode`, which is the interval test `decode_iff_mem_Ico` (O2). The
formula is the carry-save modular interval sum of the formula layer (r3 §H3.4; BV11 computes
the bit by subtracting the multiples of `q` and a selection tree), with depth stated by an
explicit constant rather than `O(log N + log log q)`. The augmented formula reads one block of
`N` key bits: the two decryptions share the key, BV14's `f_{c₁,c₂}` literally.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

/-- The ciphertext width `N = (n+1)·ℓ` is positive: `2 ≤ q ≤ 2^ℓ` forces `ℓ ≥ 1`. The
decryption formula has `N` inputs, and Barrington's construction needs at least one. -/
instance Parameters.neZero_columns (P : Parameters) : NeZero P.columns :=
  ⟨Nat.mul_ne_zero (Nat.succ_ne_zero _)
    (Nat.one_lt_two_pow_iff.mp (Nat.lt_of_lt_of_le P.lwe.modulus_ge_two P.modulus_le))⟩

/-- The **key bits** of a secret `s`: the `N = (n+1)·ℓ` bits `G⁻¹(t)` of the key vector
`t = (−s, 1)`, `keyBits P s = decomposeVec P (secretVector P s)`. They are what the
evaluation key encrypts (P6-Q8) [BV11, Def 3.8, p015-b001: encryptions of the bits of the
secret key; AP14, §5.1, p014-b001]. -/
def keyBits (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) :
    Fin P.columns → Bool :=
  decomposeVec P (secretVector P s)

/-- `keyBits P s` is `decomposeVec P (secretVector P s)`. -/
theorem keyBits_eq (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) :
    keyBits P s = decomposeVec P (secretVector P s) := rfl

/-- The **public decryption constants** of a ciphertext `C`: `Gᵀc`, where
`c = decryptColumn P C`, that is `decConstants P C = Matrix.vecMul (decryptColumn P C)
(gadget P)`. Decryption is a binary subset sum of these constants weighted by the key bits
[AP14, §5.1, p014-b001; Pei16, §5.4.3, p052-b001]. -/
def decConstants (P : Parameters) (C : Ciphertext P) : Fin P.columns → ZMod P.lwe.modulus :=
  Matrix.vecMul (decryptColumn P C) (gadget P)

/-- `decConstants P C` is `Matrix.vecMul (decryptColumn P C) (gadget P)`. -/
theorem decConstants_eq (P : Parameters) (C : Ciphertext P) :
    decConstants P C = Matrix.vecMul (decryptColumn P C) (gadget P) := rfl

/-- **The decryption formula** of `C`, on the `N` key bits: the modular interval sum of the
formula layer over the representatives of the public constants, modulo `q`, with the decoding
interval of O2,
`decryptFormula P C = modSumInterval (fun i => (decConstants P C i).val) q (decodeLo P.lwe)
(decodeHi P.lwe)` [BV14, Prop 3.4, p011-b001; BV11, Lemma 4.5, p029-b001]. It tests
`decodeLo ≤ (∑ᵢ xᵢ·aᵢ) mod q < decodeHi`. -/
def decryptFormula (P : Parameters) (C : Ciphertext P) : TreeCircuit P.columns :=
  FormulaArith.modSumInterval (fun i => (decConstants P C i).val) P.lwe.modulus
    (LWE.BitEncoding.decodeLo P.lwe) (LWE.BitEncoding.decodeHi P.lwe)

/-- `decryptFormula P C` is `modSumInterval (fun i => (decConstants P C i).val) q (decodeLo P.lwe)
(decodeHi P.lwe)`. -/
theorem decryptFormula_eq (P : Parameters) (C : Ciphertext P) :
    decryptFormula P C =
      FormulaArith.modSumInterval (fun i => (decConstants P C i).val) P.lwe.modulus
        (LWE.BitEncoding.decodeLo P.lwe) (LWE.BitEncoding.decodeHi P.lwe) := rfl

/-- **The augmented NAND formula** `f_{C₁,C₂}` [BV14, Def 2.13, p008-b002; BV11, Def 3.7,
p014-b002]: the De Morgan negation of the conjunction of the two decryption formulas, on one
block of `N` key bits, `nandFormula P C₁ C₂ = (and2 (decryptFormula P C₁)
(decryptFormula P C₂)).neg`. -/
def nandFormula (P : Parameters) (C₁ C₂ : Ciphertext P) : TreeCircuit P.columns :=
  (TreeCircuit.and2 (decryptFormula P C₁) (decryptFormula P C₂)).neg

/-- `nandFormula P C₁ C₂` is `(and2 (decryptFormula P C₁) (decryptFormula P C₂)).neg`. -/
theorem nandFormula_eq (P : Parameters) (C₁ C₂ : Ciphertext P) :
    nandFormula P C₁ C₂ =
      (TreeCircuit.and2 (decryptFormula P C₁) (decryptFormula P C₂)).neg := rfl

/-- The depth bound of the decryption formula, `decDepth P = modSumDepth N q`, the formula
layer's bound for `N` summands modulo `q` [BV14, Lemma 4.4, p019-b001: the augmented
decryption circuit has depth `c_dec·log(k log(q(k))) + 1`]. -/
def decDepth (P : Parameters) : ℕ :=
  FormulaArith.modSumDepth P.columns P.lwe.modulus

/-- `decDepth P` is `FormulaArith.modSumDepth P.columns P.lwe.modulus`. -/
theorem decDepth_eq (P : Parameters) :
    decDepth P = FormulaArith.modSumDepth P.columns P.lwe.modulus := rfl

/-! ### Targets G5–G8 -/

/-- **G5. Decryption is a binary subset sum of public constants.** For every secret `s` and
ciphertext `C`, the inner product of the key vector `t = (−s, 1)` with the decryption column
`c` is the sum of the public constants `Gᵀc` selected by the key bits:
`secretVector P s ⬝ᵥ decryptColumn P C = ∑ i, ((keyBits P s i).toNat : ZMod q) *
decConstants P C i` [AP14, §5.1, p014-b001; Pei16, §5.4.3, p052-b001, p053-b001].

**Proof sketch.** `keyBits_eq` and `gadget_mulVec_decomposeVec` give `t = G·x` with `x` the
lifted key bits, so `⟨t, c⟩ = ⟨G x, c⟩`. By `Matrix.dotProduct_mulVec` this is
`⟨x, cᵀG⟩ = ⟨x, decConstants P C⟩` (`decConstants_eq`), and `dotProduct` unfolds to the stated
sum (`dotProduct_comm` for the factor order). -/
theorem vecMul_secretVector_eq_sum (P : Parameters)
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (C : Ciphertext P) :
    secretVector P s ⬝ᵥ decryptColumn P C =
      ∑ i, ((keyBits P s i).toNat : ZMod P.lwe.modulus) * decConstants P C i := by
  sorry

/-- **G6. The decryption formula computes decryption.** On the key bits of `s`, the
decryption formula of `C` evaluates to GSW decryption of `C` under `s`:
`(decryptFormula P C).eval (keyBits P s) = decrypt P s C` [BV14, Prop 3.4, p011-b001; BV11,
Lemma 4.5, p029-b001, with its proof, p029-b002]. Deviation: the interval-sum construction of
the formula layer (module docstring).

**Proof sketch.** Decryption is `decode` of `⟨t, c⟩` with `t = (−s, 1)`, by the owner-side
reader `decrypt_eq_decode_dotProduct : decrypt P s C = LWE.BitEncoding.decode P.lwe
(secretVector P s ⬝ᵥ decryptColumn P C)` in `GSW/Scheme.lean` (owner-side, ruling Q-C1); the
fill does not re-derive it.
By G5, `⟨t, c⟩` is `∑ᵢ xᵢ·aᵢ` in `ZMod q`. Its representative is `(∑ᵢ xᵢ·aᵢ.val) mod q`
(`ZMod.val_natCast`, `Nat.cast_sum`, `ZMod.natCast_zmod_val`).
`LWE.BitEncoding.decode_iff_mem_Ico` (O2) turns `decode` into the interval test, and
`FormulaArith.modSumInterval_eval` (F9) evaluates the formula to the same test, with
`aᵢ.val < q` (`ZMod.val_lt`) and `decodeLo ≤ decodeHi ≤ q` (`decodeLo_eq`, `decodeHi_eq`,
`omega`). Both sides are Booleans equal as propositions. -/
theorem decryptFormula_eval (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C : Ciphertext P) : (decryptFormula P C).eval (keyBits P s) = decrypt P s C := by
  sorry

/-- **G7. The augmented NAND formula** computes the NAND of the two decryptions under the
same key: `(nandFormula P C₁ C₂).eval (keyBits P s) = !(decrypt P s C₁ && decrypt P s C₂)`
[BV14, Def 2.13, p008-b002; BV11, Def 3.7, p014-b002]. One key block: both decryptions read
the bits of the same `s` (r3 G7).

**Proof sketch.** `nandFormula_eq`, `TreeCircuit.neg_eval` (F1), `TreeCircuit.and2_eval`
(F3), then G6 for each operand. -/
theorem nandFormula_eval (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C₁ C₂ : Ciphertext P) :
    (nandFormula P C₁ C₂).eval (keyBits P s) = !(decrypt P s C₁ && decrypt P s C₂) := by
  sorry

/-- **G8, depth.** The augmented NAND formula has depth at most `decDepth P + 1`:
`(nandFormula P C₁ C₂).depth ≤ decDepth P + 1` [BV14, Lemma 4.4, p019-b001: depth
`c_dec·log(k log(q(k))) + 1`].

**Proof sketch.** `nandFormula_eq`, `TreeCircuit.depth_neg` (F1),
`TreeCircuit.depth_and2_le` (F3), and `FormulaArith.depth_modSumInterval_le` (F10) for both
operands, read through `decryptFormula_eq` and `decDepth_eq`; `max_le` and `omega`. -/
theorem depth_nandFormula_le (P : Parameters) (C₁ C₂ : Ciphertext P) :
    (nandFormula P C₁ C₂).depth ≤ decDepth P + 1 := by
  sorry

/-- **G8, fan-in.** The augmented NAND formula has fan-in at most two:
`(nandFormula P C₁ C₂).maxFanin ≤ 2` [BV11, Lemma 4.5, p029-b001: "fan-in 2 gates"].

**Proof sketch.** `nandFormula_eq`, `TreeCircuit.maxFanin_neg` (F1),
`TreeCircuit.maxFanin_and2_le` (F3) and `FormulaArith.maxFanin_modSumInterval_le` (F10) for
both operands (`decryptFormula_eq`); `omega`. -/
theorem maxFanin_nandFormula_le (P : Parameters) (C₁ C₂ : Ciphertext P) :
    (nandFormula P C₁ C₂).maxFanin ≤ 2 := by
  sorry

/-- **G8, closed form.** The decryption depth is `O(log N + log log q)` with no term linear in
`ℓ`: `decDepth P ≤ 9 * Nat.clog 2 P.columns + 2 * Nat.clog 2 (P.width + Nat.clog 2 P.columns
+ 3) + 21` [BV14, Lemma 4.4, p019-b001; BV11, Lemma 4.5, p029-b001]. Deviation: an explicit
constant (the *(fix)* of r3 G8, settled here) for BV14's `c_dec`, with `ℓ` for `⌈log₂ q⌉`.

**Proof sketch.** `decDepth_eq`, then `FormulaArith.modSumDepth_le` (F10) for `M = N`; its
inner term `⌈log₂ q⌉ ≤ ℓ` because `q ≤ 2^ℓ` (`P.modulus_le`, `Nat.clog_le_iff_le_pow`), so
`Nat.clog_mono_right` bounds `⌈log₂(⌈log₂ q⌉ + ⌈log₂ N⌉ + 3)⌉` by
`⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉`; `omega`. -/
theorem decDepth_le (P : Parameters) :
    decDepth P ≤
      9 * Nat.clog 2 P.columns + 2 * Nat.clog 2 (P.width + Nat.clog 2 P.columns + 3) + 21 := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
import TCSlib.Complexity.CircuitComplexity.NANDLayering

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Leveled fully homomorphic GSW: the consecutive key chain over layered NAND circuits

## Main definitions

* `LevelCoins`: the coins of the `N·L` level-key encryptions.
* `levelKey`: the level-`d` evaluation key of the consecutive chain, the encryptions under
  `pk_{d+1}` of the key bits of `s_d` (`d : Fin L`, so `evk_{d+1}` in one-based levels).
* `literalCts`: the `2k` level-0 ciphertexts, `cts` followed by their negations `G − cts j`
  (`homNot`).
* `levelGate`: a gate at level `δ ≥ 1` bootstrapped with the level key `δ − 1`.
* `leveledEval`: a layered NAND-form circuit on the `2k` literals run by the host `runWith`
  (registry row H19), each gate by `levelGate` at its level `depthAt`.
* `leveledEvalCircuit`: any fan-in-2 circuit, through `toNANDForm` and the layering
  `layerNAND`.

## Main results

* `encrypts_levelKey` (L1): level-key noise `m·B`, a proved citation of phase 5's
  `encrypts_keygen_encrypt`.
* `encrypts_leveledEval` (L2): the output of a layered NAND circuit of depth at most `L`
  encrypts its value under the key of its level, with noise `max βin (bootNoise P βk)`.
* `decrypt_keygen_leveledEvalCircuit` (L3): honest keys, every fan-in-2 circuit whose NAND form
  has depth at most `L`.

L2 and L3 are admitted; L1 is proved.

**Compactness** holds by typing: `leveledEval` and `leveledEvalCircuit` return a
`Ciphertext P` whatever the circuit [BV14, Def 2.12, p008-b001]; only the evaluation key
(`N·L` ciphertexts) depends on `L` [BV11, Thm 3.1, p015-b001].

**Sources and reconstruction (P6-Q19 B).** The key chain is Gentry's [Gen09, §4.1, `KeyGen` of
`E^(d)`, pp. 46–47, p056-b003]: `d + 1` independent key pairs and, for `i ∈ [1, d]`, the
encryptions under `pk_{i−1}` of the representation of `sk_i` as plaintexts. Gentry encrypts the
keys in reverse order [Gen09, §4.1, p. 46, p056-b002], so his evaluation runs down the index
(inputs under `pk_d`, decryption under `sk_0`); here it runs up, and his level `i` is level
`L − i` (`levelKey`). His circuits are layered as well: every wire joins consecutive levels,
with trivial gates added where needed [Gen09, §4.1, p. 47, p057-b001]. The hybrid order is
[Gen09, Thm 4.2.3, pp. 50–51, p060-b001, p061-b001] (`GSW/LeveledSecurity.lean`). Besides
[Gen09] for the chain, the statements of the leveled scheme cite [BV11, Thm 3.1, Def 3.6],
[BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3]; [BV14, Def 2.12, §3.3] and
[Bar89, Thm 1] are cited for compactness and the literal inputs.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Def 2.12, Thm 2.14 (first part), Thm 3.7.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.6, Thm 3.1.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: §5.3.
* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1) (1989), 150–164: Thm 1
  ("inputs and negated inputs").
* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
  September 2009: §4.1 (`KeyGen` of `E^(d)`, the reverse order, layered circuits), Thm 4.2.3.

**Deviations.** `L + 1` independent key pairs in a consecutive chain (P6-Q14 B): `evk_{d+1}`
encrypts under `pk_{d+1}` the `N` key bits of `s_d`, `N·L` ciphertexts in all. Circuits are
layered NAND circuits on the `2k` literals (6a's `layerNAND`, `litInput`); the negative
literals are `homNot P [C] = G − C`, under the same key with the same noise. Decryption uses
the circuit's output level, which is public, as the key index ([BV11, Def 3.6]'s `Dec` is
level-agnostic). Noise and correctness are worst case. The evaluation keys are public-key
encryptions under the user's own keys (P6-Q8).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

/-- The coins of the level keys: one coin matrix for each of the `N` positions of each of the
`L` levels. Reducible notation. -/
abbrev LevelCoins (P : Parameters) (L : ℕ) : Type :=
  Fin L → Fin P.columns → Coins P

/-- `LevelCoins P L` is `Fin L → Fin P.columns → Coins P`. -/
theorem LevelCoins_eq (P : Parameters) (L : ℕ) :
    LevelCoins P L = (Fin L → Fin P.columns → Coins P) := rfl

/-- **The level key** of the consecutive chain (P6-Q14 B) [BV11, Thm 3.1, p015-b001: "only the
length of the evaluation key depends on the level L"; BV14, Thm 2.14 first part, p008-b003]:
for `d : Fin L`, the encryptions under `pk_{d+1}` of the `N` key bits of `s_d`, with the coins
`R d`, `levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d)`. In all `N·L`
ciphertexts. The chain is [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003] with the
levels renumbered: Gentry encrypts `sk_i` under `pk_{i−1}`, in reverse order [Gen09, §4.1,
p. 46, p056-b002], and his level `i` is level `L − i` here. -/
def levelKey (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P)
    (ss : Fin (L + 1) → Secret P) (R : LevelCoins P L) (d : Fin L) :
    Fin P.columns → Ciphertext P :=
  evalKey P (pks d.succ) (ss d.castSucc) (R d)

/-- `levelKey P pks ss R d` is `evalKey P (pks d.succ) (ss d.castSucc) (R d)`. -/
theorem levelKey_eq (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P)
    (ss : Fin (L + 1) → Secret P) (R : LevelCoins P L) (d : Fin L) :
    levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d) := rfl

/-- **The level-0 literal ciphertexts** [Bar89, Thm 1, p003-b002: "inputs and negated inputs";
BV14, §3.3, p014-b002: the complements `I − C_k`]: the input ciphertexts followed by their
negations `homNot P [cts j] = G − cts j`, in the order of 6a's `litInput`,
`literalCts P cts = Fin.append cts (fun j => homNot P [cts j])`. -/
def literalCts (P : Parameters) {k : ℕ} (cts : Fin k → Ciphertext P) :
    Fin (k + k) → Ciphertext P :=
  Fin.append cts fun j => homNot P [cts j]

/-- `literalCts P cts` is `Fin.append cts (fun j => homNot P [cts j])`. -/
theorem literalCts_eq (P : Parameters) {k : ℕ} (cts : Fin k → Ciphertext P) :
    literalCts P cts = Fin.append cts fun j => homNot P [cts j] := rfl

/-- The first `k` literal ciphertexts are the inputs:
`literalCts P cts (Fin.castAdd k j) = cts j`. -/
theorem literalCts_castAdd (P : Parameters) {k : ℕ} (cts : Fin k → Ciphertext P) (j : Fin k) :
    literalCts P cts (Fin.castAdd k j) = cts j := by
  rw [literalCts_eq, Fin.append_left]

/-- The last `k` literal ciphertexts are the negations:
`literalCts P cts (Fin.natAdd k j) = homNot P [cts j]`. -/
theorem literalCts_natAdd (P : Parameters) {k : ℕ} (cts : Fin k → Ciphertext P) (j : Fin k) :
    literalCts P cts (Fin.natAdd k j) = homNot P [cts j] := by
  rw [literalCts_eq, Fin.append_right]

/-- **The level gate**: a gate at level `δ` (its `depthAt`) with `1 ≤ δ ≤ L` is bootstrapped
(`bootGate`, with its padding) under the level key `δ − 1`, which encrypts the bits of
`s_{δ−1}` under `pk_δ`; above level `L` it gives the noiseless `0` (never read by the output of
a circuit of depth at most `L`),
`levelGate P lk δ g cts = if h : δ - 1 < L then bootGate P (lk ⟨δ - 1, h⟩) g cts else 0`.
Reconstruction disclosed (module docstring). -/
def levelGate (P : Parameters) {L : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P) (δ : ℕ)
    (g : DAGGate) (cts : List (Ciphertext P)) : Ciphertext P :=
  if h : δ - 1 < L then bootGate P (lk ⟨δ - 1, h⟩) g cts else 0

/-- Below the top: `δ - 1 < L → levelGate P lk δ g cts = bootGate P (lk ⟨δ - 1, h⟩) g cts`. -/
theorem levelGate_of_lt (P : Parameters) {L : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (δ : ℕ) (g : DAGGate) (cts : List (Ciphertext P)) (h : δ - 1 < L) :
    levelGate P lk δ g cts = bootGate P (lk ⟨δ - 1, h⟩) g cts := by
  unfold levelGate
  rw [dif_pos h]

/-- Above the top: `L ≤ δ - 1 → levelGate P lk δ g cts = 0`. -/
theorem levelGate_of_le (P : Parameters) {L : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (δ : ℕ) (g : DAGGate) (cts : List (Ciphertext P)) (h : L ≤ δ - 1) :
    levelGate P lk δ g cts = 0 := by
  unfold levelGate
  rw [dif_neg (Nat.not_lt.mpr h)]

/-- **Leveled evaluation** of a layered NAND-form circuit on the `2k` literal ciphertexts
[BV14, Thm 2.14 first part, p008-b003; BV11, Thm 3.1, Def 3.6, p015-b001, p014-b001]: run the
host `runWith` (H19) over the gates, the gate at vertex `v` (the length of the data so far) by
`levelGate` at its level `Cc.depthAt v`, and read the output vertex,
`leveledEval P lk Cc cts = (runWith (fun g vs => levelGate P lk (Cc.depthAt vs.length) g vs)
Cc.gates (List.ofFn cts)).getD Cc.output 0`. Computable. **Compactness by typing**: the
result is a `Ciphertext P` whatever `Cc`. Reconstruction disclosed (module docstring). -/
def leveledEval (P : Parameters) {L k : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (Cc : DAGCircuit (k + k)) (cts : Fin (k + k) → Ciphertext P) : Ciphertext P :=
  (runWith (fun g vs => levelGate P lk (Cc.depthAt vs.length) g vs) Cc.gates
    (List.ofFn cts)).getD Cc.output 0

/-- `leveledEval P lk Cc cts` is `(runWith (fun g vs => levelGate P lk (Cc.depthAt vs.length) g vs)
Cc.gates (List.ofFn cts)).getD Cc.output 0`. -/
theorem leveledEval_eq (P : Parameters) {L k : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (Cc : DAGCircuit (k + k)) (cts : Fin (k + k) → Ciphertext P) :
    leveledEval P lk Cc cts =
      (runWith (fun g vs => levelGate P lk (Cc.depthAt vs.length) g vs) Cc.gates
        (List.ofFn cts)).getD Cc.output 0 := rfl

/-- **Leveled evaluation of any fan-in-2 circuit** on `k ≥ 1` inputs [BV14, Thm 2.14 first
part, p008-b003; BV11, Def 3.6, p014-b001]: `leveledEval` of the layered NAND form
`(Cc.toNANDForm hC).layerNAND` (6a's N3–N13) on the literal ciphertexts,
`leveledEvalCircuit P lk Cc hC cts = leveledEval P lk (Cc.toNANDForm hC).layerNAND
(literalCts P cts)`. Computable. **Compactness by typing**. Reconstruction disclosed (module
docstring). -/
def leveledEvalCircuit (P : Parameters) {L k : ℕ} [NeZero k]
    (lk : Fin L → Fin P.columns → Ciphertext P) (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) : Ciphertext P :=
  leveledEval P lk (Cc.toNANDForm hC).layerNAND (literalCts P cts)

/-- `leveledEvalCircuit P lk Cc hC cts` is `leveledEval P lk (Cc.toNANDForm hC).layerNAND
(literalCts P cts)`. -/
theorem leveledEvalCircuit_eq (P : Parameters) {L k : ℕ} [NeZero k]
    (lk : Fin L → Fin P.columns → Ciphertext P) (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) :
    leveledEvalCircuit P lk Cc hC cts =
      leveledEval P lk (Cc.toNANDForm hC).layerNAND (literalCts P cts) := rfl

/-! ### Targets L1–L3 -/

/-- **L1. Level-key noise.** For a `B`-bounded noise law and honest key generation at every
level, `pk_d = (Regev.keygen P.lwe χ (rgs d)).1` and `s_d = (Regev.keygen P.lwe χ (rgs d)).2`,
every ciphertext of the level key `d` encrypts the key bit `j` of `s_d` under the key vector of
`s_{d+1}` with noise at most `m·B`:
`Encrypts P (secretVector P s_{d+1}) (keyBits P s_d j).toNat (P.lwe.samples * B)
(levelKey P pks ss R d j)` [BV11, Thm 3.1, p015-b001; BV14, Thm 2.14 first part, p008-b003].
A citation, proved: phase 5's `encrypts_keygen_encrypt` read through `levelKey_eq` and
`evalKey_eq`. Reconstruction disclosed (module docstring). -/
theorem encrypts_levelKey (P : Parameters) (χ : LWE.Noise) (B : ℕ) (hχ : χ.Bounded B) {L : ℕ}
    (rgs : Fin (L + 1) → KeySeed P χ) (R : LevelCoins P L) (d : Fin L) (j : Fin P.columns) :
    Encrypts P (secretVector P (Regev.keygen P.lwe χ (rgs d.succ)).2)
      ((keyBits P (Regev.keygen P.lwe χ (rgs d.castSucc)).2 j).toNat : ℤ) (P.lwe.samples * B)
      (levelKey P (fun e => (Regev.keygen P.lwe χ (rgs e)).1)
        (fun e => (Regev.keygen P.lwe χ (rgs e)).2) R d j) := by
  rw [levelKey_eq, evalKey_eq]
  exact encrypts_keygen_encrypt P χ (rgs d.succ) B hχ _ (R d j)

/-- **L2. Leveled correctness, noise form.** Let `ss : Fin (L + 1) → Secret P` be the level
secrets, `lk d` encrypt the key bits of `s_d` under the key vector of `s_{d+1}` with noise at
most `βk`, and the `2k` input ciphertexts encrypt the bits `y j` under `s_0` with noise at most
`βin`. If `2·(ℓ·βin) < ⌊q/2⌋` and `2·(ℓ·bootNoise P βk) < ⌊q/2⌋`, then for every layered
NAND-form circuit `Cc` of depth at most `L`, the output encrypts `Cc.eval y` under the key of
level `Cc.depth` with noise at most `max βin (bootNoise P βk)`:
`Encrypts P (secretVector P (ss ⟨Cc.depth, _⟩)) (Cc.eval y).toNat (max βin (bootNoise P βk))
(leveledEval P lk Cc cts)` [BV14, Thm 2.14 first part, p008-b003; BV11, Thm 3.1, Def 3.6,
p015-b001, p014-b001]. Deviations: layered circuits on literal inputs, the public output level,
worst case; reconstruction disclosed (module docstring).

**Proof sketch.** Apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from
`List.ofFn y` and to the leveled gate function from `List.ofFn cts`, with the vertex relation:
"if `Cc.depthAt v ≤ L`, the ciphertext encrypts the value under `s_{depthAt v}` with noise at most
`max βin (bootNoise P βk)`". Inputs have level `0` (`depthAt_input`): `hin`. A gate at vertex
`v = 2k + i` (`runWith` hands it the data of length `v`, `length_runWith`) has level
`δ = Cc.depthAt v ≥ 1` (`depthAt_gate`, `DAGGate.depth_eq`); if `δ ≤ L`, `levelGate_of_lt`
selects the level key `δ − 1`. The circuit is layered (`isLayered_iff`), so every argument is
at level `δ − 1` and, by the relation and `decrypt_of_encrypts` (with `hβin` or `hboot`),
decrypts under `s_{δ−1}` to its value; the padded `G` decrypts to `true` (`encrypts_gadget`).
The three case readers of `bootGate` and G9 (`encrypts_bootNAND` with `s = s_{δ−1}`,
`t' = t_δ`, `hk`) give an encryption under `s_δ` of the NAND of the argument values with noise
`bootNoise P βk`, which is the gate's value (`isNANDForm_iff`, `DAGGate.eval_of_isNAND`, N1).
Gates above level `L` are unconstrained and are never read by a vertex at level `≤ L`. At the
output (`Cc.output_lt`, level `Cc.depth = depthAt Cc.output` by `depth_eq`, at most `L`), read
`DAGCircuit.eval_eq`, `values_eq` and `leveledEval_eq`. -/
theorem encrypts_leveledEval (P : Parameters) {L k : ℕ} (Cc : DAGCircuit (k + k))
    (hNAND : Cc.IsNANDForm) (hlay : Cc.IsLayered) (hdepth : Cc.depth ≤ L)
    (ss : Fin (L + 1) → Secret P) (lk : Fin L → Fin P.columns → Ciphertext P) (βk βin : ℕ)
    (hk : ∀ d j, Encrypts P (secretVector P (ss d.succ)) ((keyBits P (ss d.castSucc) j).toNat : ℤ)
      βk (lk d j))
    (y : Fin (k + k) → Bool) (cts : Fin (k + k) → Ciphertext P)
    (hin : ∀ j, Encrypts P (secretVector P (ss 0)) ((y j).toNat : ℤ) βin (cts j))
    (hβin : 2 * (P.width * βin) < P.lwe.modulus / 2)
    (hboot : 2 * (P.width * bootNoise P βk) < P.lwe.modulus / 2) :
    Encrypts P (secretVector P (ss ⟨Cc.depth, Nat.lt_succ_of_le hdepth⟩)) ((Cc.eval y).toNat : ℤ)
      (max βin (bootNoise P βk)) (leveledEval P lk Cc cts) := by
  sorry

/-- **L3. Leveled correctness for honest keys and every fan-in-2 circuit of NAND depth at most
`L`.** For a `B`-bounded noise law, honest key generation at every level (seeds `rgs`), level
coins `R`, input bits `x` encrypted under `pk_0` with coins `R'`, and a circuit `Cc` on
`k ≥ 1` inputs whose NAND form has depth at most `L`, if `2·(ℓ·bootNoise P (m·B)) < ⌊q/2⌋` and
`2·(ℓ·(m·B)) < ⌊q/2⌋`, then the leveled evaluation under the chain of level keys decrypts, under
the secret of level `(Cc.toNANDForm hC).depth`, to `Cc.eval x`
[BV14, Thm 3.7, p016-b001: "a leveled FHE scheme, without additional assumptions"]. Deviations:
decryption uses the public output level; worst case; reconstruction disclosed (module
docstring).

**Proof sketch.** `leveledEvalCircuit_eq`. The level keys satisfy L2's `hk` with `βk = m·B` by
L1 (`encrypts_levelKey`). The literal ciphertexts encrypt `litInput x` under `s_0` with noise
`m·B`: the first half by `encrypts_keygen_encrypt` (`literalCts_castAdd`), the second half by
`homNot_eq`, `homAnd_singleton`, `encrypts_gadget` and `Encrypts.sub` (`literalCts_natAdd`,
noise `0 + m·B`), matched with `litInput_castAdd`, `litInput_natAdd`; every `j : Fin (k + k)`
is one of the two (`Fin.addCases`). The layered circuit `(Cc.toNANDForm hC).layerNAND` is in
NAND form (`layerNAND_isNANDForm` with `toNANDForm_isNANDForm`), layered
(`layerNAND_isLayered`) and of depth `(Cc.toNANDForm hC).depth ≤ L` (`layerNAND_depth`), and
evaluates on `litInput x` to `Cc.eval x` (`layerNAND_eval`, `toNANDForm_eval`). L2 then gives
an encryption under the output level's secret with noise `max (m·B) (bootNoise P (m·B))`, and
`decrypt_of_encrypts` with `hin`/`hsep` finishes. -/
theorem decrypt_keygen_leveledEvalCircuit (P : Parameters) (χ : LWE.Noise) (B : ℕ)
    (hχ : χ.Bounded B) {L k : ℕ} [NeZero k] (rgs : Fin (L + 1) → KeySeed P χ)
    (R : LevelCoins P L) (Cc : DAGCircuit k) (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2)
    (hdepth : (Cc.toNANDForm hC).depth ≤ L) (x : Fin k → Bool) (R' : Fin k → Coins P)
    (hsep : 2 * (P.width * bootNoise P (P.lwe.samples * B)) < P.lwe.modulus / 2)
    (hin : 2 * (P.width * (P.lwe.samples * B)) < P.lwe.modulus / 2) :
    decrypt P (Regev.keygen P.lwe χ (rgs ⟨(Cc.toNANDForm hC).depth, Nat.lt_succ_of_le hdepth⟩)).2
        (leveledEvalCircuit P
          (levelKey P (fun e => (Regev.keygen P.lwe χ (rgs e)).1)
            (fun e => (Regev.keygen P.lwe χ (rgs e)).2) R) Cc hC
          fun j => encrypt P (Regev.keygen P.lwe χ (rgs 0)).1 (x j) (R' j)) =
      Cc.eval x := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/LeveledSecurity.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Security
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# IND-CPA of leveled GSW-FHE from DLWE: the top-down key hybrid

## Main definitions

* `LeveledSeeds`, `LeveledView`: the seeds and the view of the leveled scheme.
* `leveledView`: the `L + 1` public keys, the `L` level keys and `Enc_{pk_0}(μ)`.
* `levelHybrid`: the hybrid `H_h` in which the level keys `e ≥ h` encrypt `0` instead of the
  key bits; `H_L` is the real view, `H_0` has no key bits at all.
* `levelMsgs`, `levelAssemble`, `levelReduction`: the reduction of step `e` at position `j`,
  `hybridPlant` (the shared multi-ciphertext hybrid) composed with phase 5's `reduction`.
* `levelTerm`: its two DLWE advantages plus `2·(N·ε_LHL)`.
* `challengeDist`, `challengeTerm`: the final phase-5 step on the challenge under `pk_0`.

## Main results

* `distAdv_levelHybrid_le` (L4): one level, `N` positions.
* `distAdv_leveledView_le` (L5): IND-CPA of leveled GSW-FHE from DLWE.

Both are admitted statement-phase targets.

**Sources and reconstruction (P6-Q19 B).** The key chain is Gentry's [Gen09, §4.1, `KeyGen` of
`E^(d)`, pp. 46–47, p056-b003], with his reverse order of the levels undone: his level `i` is
level `L − i` here (`GSW/Leveled.lean`). The hybrid order is his [Gen09, Thm 4.2.3 and its
proof, pp. 50–51, p060-b001, p061-b001]: Game `k` replaces the encryptions under `pk_{i−1}` of
`sk_i` for `i ∈ [1, k]`, and the step from Game `k` to Game `k + 1` plants the challenge key as
`pk_k`, whose secret occurs only in encryptions already replaced. Renumbered, Game `k` is
`H_{L−k}`, and the order is the top-down order below. The statements cite [BV11, Thm 3.1,
Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3], with [GSW13, §3.2, Lemma 1],
[BV11, Def 3.1] and [BV14, §2.5] for the one-key steps and the view; [Gen09] is cited here, for
the construction. Deviations from [Gen09, Thm 4.2.3]: a replaced level key encrypts `0`, not
the bits of an unrelated fresh key; each level step is a hybrid over the `N` positions, not one
challenge of Gentry's `ℓ`-fold scheme `(E)^ℓ`; each step reduces to DLWE (phase 5), not to the
semantic security of the base scheme; and the middle step between the two chains is phase 5's
challenge step, not Gentry's Game `d + 1` (a random plaintext).

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Thm 2.14 (first part), Thm 3.7.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.1, Def 3.6, Thm 3.1.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: §5.3.
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
  8 June 2013: §3.2, Lemma 1.
* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
  September 2009: §4.1, Thm 4.2.3 (with its proof).

**Deviations.** Levels are indexed from `0`: the level key `e : Fin L` encrypts the bits of
`s_e` under `pk_{e+1}` (r3's `evk_d`, `d = e + 1`). The hybrid runs top-down: step `e` (from
`H_{e+1}` to `H_e`, `e = L − 1, …, 0`) replaces the level key `e` by encryptions of `0`; it is
legitimate because `s_{e+1}`, the secret of `pk_{e+1}`, occurs only in the level key `e + 1`,
already replaced. Each step is a multi-ciphertext hybrid over the `N` positions; its messages,
the bits of `s_e`, are random and are drawn inside the reduction's coins (r3 §H8 item 12).
The challenge bit `μ` enters each step's reduction (which must simulate the challenge), so the
level terms carry `μ`, and the bound of L5 sums the terms of the two chains (`μ₀` and `μ₁`)
where r3 wrote `2·∑`. Concrete statements with function-level distinguishers, as phase 5.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- The seeds of the leveled view: `L + 1` key-generation seeds, the coins of the `N·L` level-key
encryptions and the coins of the challenge. Reducible notation. -/
abbrev LeveledSeeds (P : Parameters) (χ : LWE.Noise) (L : ℕ) : Type :=
  (Fin (L + 1) → KeySeed P χ) × LevelCoins P L × Coins P

/-- `LeveledSeeds P χ L` is `(Fin (L + 1) → KeySeed P χ) × LevelCoins P L × Coins P`. -/
theorem LeveledSeeds_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) :
    LeveledSeeds P χ L = ((Fin (L + 1) → KeySeed P χ) × LevelCoins P L × Coins P) := rfl

/-- The leveled view: `L + 1` public keys, `L` level keys of `N` ciphertexts each, and one
challenge ciphertext. Reducible notation. -/
abbrev LeveledView (P : Parameters) (L : ℕ) : Type :=
  (Fin (L + 1) → PublicKey P) × (Fin L → Fin P.columns → Ciphertext P) × Ciphertext P

/-- `LeveledView P L` is `(Fin (L + 1) → PublicKey P) × (Fin L → Fin P.columns → Ciphertext P) ×
Ciphertext P`. -/
theorem LeveledView_eq (P : Parameters) (L : ℕ) :
    LeveledView P L =
      ((Fin (L + 1) → PublicKey P) × (Fin L → Fin P.columns → Ciphertext P) × Ciphertext P) :=
  rfl

/-- **The leveled FHE view of a bit** `μ` [BV11, Def 3.1, p013-b002, for the leveled scheme;
BV14, §2.5, p007-b001]: from independent honest key generations
`(pk_d, s_d) = Regev.keygen P.lwe χ (r.1 d)`, the public keys, the chain of level keys
`levelKey P pk s r.2.1` and the challenge `encrypt P pk_0 μ r.2.2`,
`leveledView P χ L μ r = (pk, levelKey P pk s r.2.1, encrypt P (pk 0) μ r.2.2)`.
Reconstruction disclosed (module docstring). -/
def leveledView (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (r : LeveledSeeds P χ L) :
    LeveledView P L :=
  (fun d => (Regev.keygen P.lwe χ (r.1 d)).1,
    levelKey P (fun d => (Regev.keygen P.lwe χ (r.1 d)).1)
      (fun d => (Regev.keygen P.lwe χ (r.1 d)).2) r.2.1,
    encrypt P (Regev.keygen P.lwe χ (r.1 0)).1 μ r.2.2)

/-- `leveledView P χ L μ r` is `(pk, levelKey P pk s r.2.1, encrypt P (pk 0) μ r.2.2)` with
`(pk d, s d) = Regev.keygen P.lwe χ (r.1 d)`. -/
theorem leveledView_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool)
    (r : LeveledSeeds P χ L) :
    leveledView P χ L μ r =
      (fun d => (Regev.keygen P.lwe χ (r.1 d)).1,
        levelKey P (fun d => (Regev.keygen P.lwe χ (r.1 d)).1)
          (fun d => (Regev.keygen P.lwe χ (r.1 d)).2) r.2.1,
        encrypt P (Regev.keygen P.lwe χ (r.1 0)).1 μ r.2.2) := rfl

/-- **The level hybrid** `H_h`: as `leveledView`, except that every level key `e` with `h ≤ e`
holds encryptions of `0` under `pk_{e+1}` (same coins) instead of the key bits of `s_e`.
`H_L` is the real view (`h = L` replaces nothing) and `H_0` replaces every level key.
`levelHybrid P χ L μ h r = (pk, fun e j => if h ≤ e then encrypt P (pk e.succ) false (r.2.1 e j)
else levelKey P pk s r.2.1 e j, encrypt P (pk 0) μ r.2.2)`. Glue for the top-down hybrid;
reconstruction disclosed (module docstring). -/
def levelHybrid (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (h : ℕ)
    (r : LeveledSeeds P χ L) : LeveledView P L :=
  (fun d => (Regev.keygen P.lwe χ (r.1 d)).1,
    fun e j => if h ≤ e.val then encrypt P (Regev.keygen P.lwe χ (r.1 e.succ)).1 false (r.2.1 e j)
      else levelKey P (fun d => (Regev.keygen P.lwe χ (r.1 d)).1)
        (fun d => (Regev.keygen P.lwe χ (r.1 d)).2) r.2.1 e j,
    encrypt P (Regev.keygen P.lwe χ (r.1 0)).1 μ r.2.2)

/-- `levelHybrid P χ L μ h r` is `(pk, fun e j => if h ≤ e then encrypt P (pk e.succ) false
(r.2.1 e j) else levelKey P pk s r.2.1 e j, encrypt P (pk 0) μ r.2.2)`. -/
theorem levelHybrid_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (h : ℕ)
    (r : LeveledSeeds P χ L) :
    levelHybrid P χ L μ h r =
      (fun d => (Regev.keygen P.lwe χ (r.1 d)).1,
        fun e j => if h ≤ e.val then
            encrypt P (Regev.keygen P.lwe χ (r.1 e.succ)).1 false (r.2.1 e j)
          else levelKey P (fun d => (Regev.keygen P.lwe χ (r.1 d)).1)
            (fun d => (Regev.keygen P.lwe χ (r.1 d)).2) r.2.1 e j,
        encrypt P (Regev.keygen P.lwe χ (r.1 0)).1 μ r.2.2) := rfl

/-- The messages of step `e`: the `N` key bits of `s_e`, indexed by `Fin (N − 1 + 1)` (the
index shape of `hybridPlant`; `N ≥ 1`),
`levelMsgs P χ L e r i = keyBits P (Regev.keygen P.lwe χ (r.1 e.castSucc)).2 (Fin.cast _ i)`.
Glue. -/
def levelMsgs (P : Parameters) (χ : LWE.Noise) (L : ℕ) (e : Fin L) (r : LeveledSeeds P χ L)
    (i : Fin (P.columns - 1 + 1)) : Bool :=
  keyBits P (Regev.keygen P.lwe χ (r.1 e.castSucc)).2
    (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)) i)

/-- `levelMsgs P χ L e r i` is
`keyBits P (Regev.keygen P.lwe χ (r.1 e.castSucc)).2 (Fin.cast _ i)`. -/
theorem levelMsgs_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (e : Fin L)
    (r : LeveledSeeds P χ L) (i : Fin (P.columns - 1 + 1)) :
    levelMsgs P χ L e r i =
      keyBits P (Regev.keygen P.lwe χ (r.1 e.castSucc)).2
        (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)) i) := rfl

/-- The view assembled by the step-`e` reduction around a planted key `v.1` (as `pk_{e+1}`) and
`N` planted ciphertexts `v.2` (as the level key `e`), from its own seeds `c.1` and running `D`
with the coins `c.2`: the other public keys from `c.1`, the level keys `e' > e` as encryptions of
`0` (the hybrid `H_{e+1}`), the level keys `e' < e` honest, and the challenge `Enc_{pk_0}(μ)`.
`levelAssemble P χ L μ e D v c = D (update pk e.succ v.1, fun e' j => if e' = e then
v.2 (Fin.cast _ j) else if e < e' then encrypt P (pk e'.succ) false (c.1.2.1 e' j) else
levelKey P pk s c.1.2.1 e' j, encrypt P (pk 0) μ c.1.2.2) c.2`. Glue. -/
def levelAssemble (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L) {ρ : Type*}
    (D : LeveledView P L → ρ → Bool)
    (v : PublicKey P × (Fin (P.columns - 1 + 1) → Ciphertext P)) (c : LeveledSeeds P χ L × ρ) :
    Bool :=
  D (Function.update (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1) e.succ v.1,
    fun e' j => if e' = e then v.2 (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
      else if e.val < e'.val then
        encrypt P (Regev.keygen P.lwe χ (c.1.1 e'.succ)).1 false (c.1.2.1 e' j)
      else levelKey P (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1)
        (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).2) c.1.2.1 e' j,
    encrypt P (Regev.keygen P.lwe χ (c.1.1 0)).1 μ c.1.2.2) c.2

/-- `levelAssemble P χ L μ e D v c` runs `D` with the coins `c.2` on the view with `pk_{e+1}`
planted as `v.1`, the level key `e` planted as `v.2`, the keys above `e` encrypting `0`, those
below honest, and the challenge `Enc_{pk_0}(μ)` (the formula of `levelAssemble`'s docstring). -/
theorem levelAssemble_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    {ρ : Type*} (D : LeveledView P L → ρ → Bool)
    (v : PublicKey P × (Fin (P.columns - 1 + 1) → Ciphertext P)) (c : LeveledSeeds P χ L × ρ) :
    levelAssemble P χ L μ e D v c =
      D (Function.update (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1) e.succ v.1,
        fun e' j => if e' = e then
            v.2 (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
          else if e.val < e'.val then
            encrypt P (Regev.keygen P.lwe χ (c.1.1 e'.succ)).1 false (c.1.2.1 e' j)
          else levelKey P (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1)
            (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).2) c.1.2.1 e' j,
        encrypt P (Regev.keygen P.lwe χ (c.1.1 0)).1 μ c.1.2.2) c.2 := rfl

/-- **The reduction of step `e` at position `j`** (side `b`): the DLWE test that, on a challenge
key `pk` and its coins `c = (R₀, Rs, r, ρ)`, plants `pk` as `pk_{e+1}`, encrypts under it the
messages of step `e` (the key bits of `s_e`, from its own seeds `r`) at the positions after `j`
and `0` at the positions before `j`, encrypts at position `j` the bit `b ∧ (bit j of s_e)` with
the coins `R₀`, assembles the rest of the view itself (`levelAssemble`) and runs `D`. It is
`hybridPlant` (`EnsembleSecurity.lean`) composed with phase 5's `reduction`:
`levelReduction P χ L μ e j b D pk c = reduction P (if b then levelMsgs P χ L e c.2.2.1 j' else
false) (hybridPlant (encrypt P) (levelMsgs P χ L e c.2.2.1) (fun _ => false) j'
(levelAssemble P χ L μ e D)) pk c`, with `j' = Fin.cast _ j` [GSW13, §3.2, Lemma 1, p009-b002,
p010-b001; AP14, §5.3, p015-b002]. Reconstruction disclosed (module docstring). -/
def levelReduction (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) (b : Bool) {ρ : Type*} (D : LeveledView P L → ρ → Bool)
    (pk : PublicKey P)
    (c : Coins P × ((Fin (P.columns - 1 + 1) → Coins P) × (LeveledSeeds P χ L × ρ))) : Bool :=
  reduction P
    (if b then
      levelMsgs P χ L e c.2.2.1 (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
    else false)
    (hybridPlant (encrypt P) (levelMsgs P χ L e c.2.2.1) (fun _ => false)
      (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j) (levelAssemble P χ L μ e D))
    pk c

/-- `levelReduction P χ L μ e j b D pk c` is `reduction P (if b then levelMsgs P χ L e c.2.2.1 j'
else false) (hybridPlant (encrypt P) (levelMsgs P χ L e c.2.2.1) (fun _ => false) j'
(levelAssemble P χ L μ e D)) pk c` with `j' = Fin.cast _ j`. -/
theorem levelReduction_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) (b : Bool) {ρ : Type*} (D : LeveledView P L → ρ → Bool)
    (pk : PublicKey P)
    (c : Coins P × ((Fin (P.columns - 1 + 1) → Coins P) × (LeveledSeeds P χ L × ρ))) :
    levelReduction P χ L μ e j b D pk c =
      reduction P
        (if b then
          levelMsgs P χ L e c.2.2.1 (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
        else false)
        (hybridPlant (encrypt P) (levelMsgs P χ L e c.2.2.1)
          (fun _ => false) (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
          (levelAssemble P χ L μ e D))
        pk c := rfl

/-- **The term of step `e` at position `j`**: the two DLWE advantages of its reduction (sides
`true` and `false`) plus `2·(N·ε_LHL)`, `ε_LHL = Regev.extractionError P.lwe`, the shape of
`distAdv_encrypt_le`'s right-hand side,
`levelTerm P χ L μ e j D = decisionAdvantage P.lwe χ (levelReduction P χ L μ e j true D) +
decisionAdvantage P.lwe χ (levelReduction P χ L μ e j false D) +
2 * (P.columns * Regev.extractionError P.lwe)` [GSW13, §3.2, Lemma 1, p009-b002, p010-b001].
Glue. -/
noncomputable def levelTerm (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    ℝ :=
  LWE.decisionAdvantage P.lwe χ (levelReduction P χ L μ e j true D) +
    LWE.decisionAdvantage P.lwe χ (levelReduction P χ L μ e j false D) +
    2 * (P.columns * Regev.extractionError P.lwe)

/-- `levelTerm P χ L μ e j D` is the sum of the two DLWE advantages of `levelReduction` (sides
`true`, `false`) and `2 * (P.columns * Regev.extractionError P.lwe)`. -/
theorem levelTerm_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    levelTerm P χ L μ e j D =
      LWE.decisionAdvantage P.lwe χ (levelReduction P χ L μ e j true D) +
        LWE.decisionAdvantage P.lwe χ (levelReduction P χ L μ e j false D) +
        2 * (P.columns * Regev.extractionError P.lwe) := rfl

/-- The distinguisher of the final step: on a phase-5 view `v = (pk, ct)` and coins `c`, it
plants `pk` as `pk_0` and `ct` as the challenge in the hybrid `H_0` (every level key an
encryption of `0`) built from its own seeds `c.1`, and runs `D` with `c.2`,
`challengeDist P χ L D v c = D (update pk 0 v.1, fun e j => encrypt P (pk e.succ) false
(c.1.2.1 e j), v.2) c.2`. Glue. -/
def challengeDist (P : Parameters) (χ : LWE.Noise) (L : ℕ) {ρ : Type*}
    (D : LeveledView P L → ρ → Bool) (v : PublicKey P × Ciphertext P)
    (c : LeveledSeeds P χ L × ρ) : Bool :=
  D (Function.update (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1) 0 v.1,
    fun e j => encrypt P (Regev.keygen P.lwe χ (c.1.1 e.succ)).1 false (c.1.2.1 e j), v.2) c.2

/-- `challengeDist P χ L D v c` is `D (update pk 0 v.1, fun e j => encrypt P (pk e.succ) false
(c.1.2.1 e j), v.2) c.2`. -/
theorem challengeDist_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) {ρ : Type*}
    (D : LeveledView P L → ρ → Bool) (v : PublicKey P × Ciphertext P)
    (c : LeveledSeeds P χ L × ρ) :
    challengeDist P χ L D v c =
      D (Function.update (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1) 0 v.1,
        fun e j => encrypt P (Regev.keygen P.lwe χ (c.1.1 e.succ)).1 false (c.1.2.1 e j), v.2)
        c.2 := rfl

/-- **The term of the challenge step**: phase 5's bound for the challenge under `pk_0` with the
distinguisher `challengeDist`, `challengeTerm P χ L μ₀ μ₁ D =
decisionAdvantage P.lwe χ (reduction P μ₀ (challengeDist P χ L D)) +
decisionAdvantage P.lwe χ (reduction P μ₁ (challengeDist P χ L D)) +
2 * (P.columns * Regev.extractionError P.lwe)` [GSW13, §3.2, p009-b002]. Glue. -/
noncomputable def challengeTerm (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ₀ μ₁ : Bool)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) : ℝ :=
  LWE.decisionAdvantage P.lwe χ (reduction P μ₀ (challengeDist P χ L D)) +
    LWE.decisionAdvantage P.lwe χ (reduction P μ₁ (challengeDist P χ L D)) +
    2 * (P.columns * Regev.extractionError P.lwe)

/-- `challengeTerm P χ L μ₀ μ₁ D` is the two DLWE advantages of `reduction P μᵢ
(challengeDist P χ L D)` plus `2 * (P.columns * Regev.extractionError P.lwe)`. -/
theorem challengeTerm_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ₀ μ₁ : Bool) {ρ : Type*}
    [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    challengeTerm P χ L μ₀ μ₁ D =
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ (challengeDist P χ L D)) +
        LWE.decisionAdvantage P.lwe χ (reduction P μ₁ (challengeDist P χ L D)) +
        2 * (P.columns * Regev.extractionError P.lwe) := rfl

/-! ### Targets L4–L5 -/

/-- **L4. One level of the key hybrid.** For every level `e : Fin L`, bit `μ` and distinguisher
`D`, replacing the `N` encryptions under `pk_{e+1}` of the key bits of `s_e` by encryptions of
`0` (from `H_{e+1}` to `H_e`) costs at most the sum of the position terms,
`distAdv (levelHybrid P χ L μ (e + 1)) (levelHybrid P χ L μ e) D ≤
∑ j : Fin P.columns, levelTerm P χ L μ e j D` [AP14, §5.3, p015-b002 (independent keys);
GSW13, §3.2, Lemma 1, p009-b002, p010-b001]. Legitimate because `s_{e+1}` occurs only in the
level key `e + 1`, already replaced in `H_{e+1}` (top-down order). Reconstruction disclosed
(module docstring).

**Proof sketch.** Position hybrids `G_i` (`i ≤ N`) between `H_{e+1}` (`G_0`) and `H_e` (`G_N`):
the first `i` ciphertexts of the level key `e` encrypt `0`. `abs_sub_le_sum_hybrids` reduces
to the gaps `|Pr[D(G_i)] − Pr[D(G_{i+1})]|`, as in `distAdv_multi_le_sum` (whose
`hybridPlant` the reduction uses; the messages, the bits of `s_e`, are drawn inside the
reduction's coins, r3 §H8 item 12, so the multi-ciphertext lemma is applied per value of the
other seeds or its proof is followed with them in the coins). The gap at `i = j` is the gap of
`levelReduction P χ L μ e j b D` between a real LWE key and a uniform key, plus the gap
between `b = true` and `b = false` under a uniform key: `levelReduction_eq`, `reduction_eq`,
`hybridPlant_eq` (the planted position), `levelAssemble_eq`, `levelHybrid_eq`, `Regev.keygen_fst`
(the planted key is distributed as `pk_{e+1}`, whose secret is otherwise unused in `H_{e+1}`),
and the seed regrouping (`acceptProb_comp_equiv`, `OneWay.uprob_update`). As in phase 5's
`distAdv_encrypt_le`: the two DLWE gaps are the exact advantages (`real_uniformKey_advantage`,
`LWE.decisionAdvantage_eq`), and the uniform-key gap is at most `2·(N·ε_LHL)` for each value
of the reduction's own seeds (`uniformKey_uniform_advantage_le`, twice), averaged. Sum over
`j` (`levelTerm_eq`). -/
theorem distAdv_levelHybrid_le (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    distAdv (levelHybrid P χ L μ (e.val + 1)) (levelHybrid P χ L μ e.val) D ≤
      ∑ j : Fin P.columns, levelTerm P χ L μ e j D := by
  sorry

/-- **L5. IND-CPA of leveled GSW-FHE from DLWE.** For all bits `μ₀`, `μ₁` and every
distinguisher `D`, the leveled views of `μ₀` and `μ₁` differ by at most the sum of the level
terms of both hybrid chains plus the challenge term,
`distAdv (leveledView P χ L μ₀) (leveledView P χ L μ₁) D ≤
∑ e : Fin L, ∑ j : Fin P.columns, (levelTerm P χ L μ₀ e j D + levelTerm P χ L μ₁ e j D) +
challengeTerm P χ L μ₀ μ₁ D` [BV14, Thm 2.14 first part, p008-b003, and Thm 3.7, p016-b001;
BV11, Thm 3.1, p015-b001]. No circular-security assumption. Deviation: r3's `2·∑ levelTerm`
becomes the sum over the two chains, the level terms depending on the challenge bit;
reconstruction disclosed (module docstring).

**Proof sketch.** `leveledView P χ L μ = levelHybrid P χ L μ L` (`leveledView_eq`,
`levelHybrid_eq`: no `e : Fin L` has `L ≤ e`). The chain `H_L(μ₀), …, H_0(μ₀), H_0(μ₁), …,
H_L(μ₁)`: `abs_sub_le_sum_hybrids` (or the triangle inequality, `abs_sub_le`) on each side
with L4 (`distAdv_levelHybrid_le`) for `e = L − 1, …, 0` (`Fin.sum_univ_eq_sum_range`). The
middle step: `H_0(μ)` is `challengeDist P χ L D` run on phase 5's `realView P χ μ`, after the
seed regrouping (`challengeDist_eq`, `realView_eq`, `view_eq`, `Regev.keygen_fst`, and
`acceptProb_comp_equiv`; the seed of `pk_0` and the unused coordinates are integrated out), so
phase 5's `distAdv_encrypt_le` bounds it by `challengeTerm P χ L μ₀ μ₁ D` (`challengeTerm_eq`).
`linarith`. -/
theorem distAdv_leveledView_le (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ₀ μ₁ : Bool)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    distAdv (leveledView P χ L μ₀) (leveledView P χ L μ₁) D ≤
      ∑ e : Fin L, ∑ j : Fin P.columns,
          (levelTerm P χ L μ₀ e j D + levelTerm P χ L μ₁ e j D) +
        challengeTerm P χ L μ₀ μ₁ D := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
import TCSlib.Cryptography.LWE.Ratio
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bootstrapped GSW at a polynomial modulus-to-noise ratio

## Main definitions

* `Parameters.ofFamily F κ`: the GSW parameters of an LWE family at `κ`, gadget width the
  family's residue width.
* `pBoot F`: an explicit syntactic polynomial in `κ` built from the family's dimension, sample
  and residue-width bounds.

## Main results

* `bootRatio_le_poly` (G16): `8·(ℓ·bootNoise (ofFamily F κ) (m·B κ)) ≤ pBoot(κ)·B(κ)`.
* `decrypt_fheEval_of_ratio`, `decrypt_leveledEval_of_ratio` (G17, split into the pure and the
  leveled scheme): if `pBoot(κ)·B(κ) < q(κ)` and the noise is `B(κ)`-bounded, bootstrapped
  GSW at `κ` is correct on every circuit, pure (G12) and leveled (L3).

All three are admitted statement-phase targets. With `LWE.Family.RatioBounded F B p` the
condition `pBoot(κ)·B(κ) < q(κ)` is the regime of a polynomial ratio `q/B` (assumption (A2)).

**Sources and reconstruction (P6-Q19 B), for the leveled statement.** The key chain is
Gentry's [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003], with his reverse order of
the levels undone (`GSW/Leveled.lean`); his correctness theorem for the leveled scheme is
[Gen09, Thm 4.2.1, p. 49, p059-b001] (only its statement is ingested). The hybrid order,
[Gen09, Thm 4.2.3, pp. 50–51, p060-b001, p061-b001], concerns security and is used in
`GSW/LeveledSecurity.lean`, not here.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: §3.4, Thm 3.7.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Thm 3.1, Def 3.6.
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
  8 June 2013: §3.1 (parameters).
* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
  September 2009: §4.1, Thm 4.2.1, Thm 4.2.3.

**Deviations.** Worst case, with an explicit polynomial (constant `2^70`; r3 §H6 drafted
`c < 2^70` with the factor `4`), not [BV14, Thm 3.7]'s `Θ̃` noise rate. The constant `8`
(r3 G16 wrote `4`) absorbs the floor in the decryption condition `2·(ℓ·β) < ⌊q/2⌋`, so that
`pBoot(κ)·B(κ) < q(κ)` suffices in G17.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Complexity
open Encryption.PublicKey

/-- **The GSW parameters of an LWE family** at the security parameter `κ` [GSW13, §3.1,
p008-b002; phase-5 §G4]: the family's LWE parameters, gadget width `ℓ = F.residueBits(κ)`, and
`q ≤ 2^ℓ` from the family's width bound, `(ofFamily F κ).lwe = F.parameters κ`,
`(ofFamily F κ).width = F.residueBits.eval κ`. Read only through its non-simp `simps` readers
`Parameters.ofFamily_lwe` and `Parameters.ofFamily_width` (type-level Rule 10). -/
@[simps (config := { isSimp := false }) lwe width]
def Parameters.ofFamily (F : LWE.Family) (κ : ℕ) : Parameters where
  lwe := F.parameters κ
  width := F.residueBits.eval κ
  modulus_le := F.modulus_le_pow κ

/-- **The bootstrapping polynomial** of a family (r3 G16 *(fix)*, settled here), with
`d = F.dimensionBound`, `s = F.samplesBound`, `r = F.residueBits`:
`pBoot F = 2^70 · r · ((d + 1)·r)^19 · (r + (d + 1)·r + 3)^4 · s`, evaluating to
`2^70·ℓ·N̂^19·(ℓ + N̂ + 3)^4·m̂` with `N̂ = (d(κ) + 1)·ℓ ≥ N` and `m̂ = s(κ) ≥ m` [BV14, Thm 3.7,
p016-b001, worst-case analogue]. Derivation: `bootNoise_le` (G13) gives
`bootNoise P β ≤ 4^33·N^19·X^4·(2β)` with `X = ℓ + ⌈log₂ N⌉ + 3 ≤ ℓ + N̂ + 3`; times `8·ℓ` and
with `β = m·B`, the constant is `8·4^33·2 = 2^70`. -/
def pBoot (F : LWE.Family) : PolyExpr :=
  .mul (.mul (.mul (.mul (.const (2 ^ 70)) F.residueBits)
      (.pow (.mul (.add F.dimensionBound (.const 1)) F.residueBits) 19))
    (.pow (.add (.add F.residueBits (.mul (.add F.dimensionBound (.const 1)) F.residueBits))
      (.const 3)) 4))
    F.samplesBound

/-- `pBoot F` is the expression `2^70 · r · ((d + 1)·r)^19 · (r + (d + 1)·r + 3)^4 · s` with
`d = F.dimensionBound`, `s = F.samplesBound`, `r = F.residueBits`. -/
theorem pBoot_eq (F : LWE.Family) :
    pBoot F =
      .mul (.mul (.mul (.mul (.const (2 ^ 70)) F.residueBits)
          (.pow (.mul (.add F.dimensionBound (.const 1)) F.residueBits) 19))
        (.pow (.add (.add F.residueBits (.mul (.add F.dimensionBound (.const 1)) F.residueBits))
          (.const 3)) 4))
        F.samplesBound := rfl

/-! ### Targets G16–G17 -/

/-- **G16. The bootstrapped noise is polynomial in the noise bound.** For every family `F`,
noise bound `B` and `κ`, with `P = ofFamily F κ`, `ℓ = P.width` and `m = P.lwe.samples`,
`8 * (P.width * bootNoise P (P.lwe.samples * B κ)) ≤ (pBoot F).eval κ * B κ`
[BV14, Thm 3.7, p016-b001, worst-case analogue]. Deviation: the factor `8` (r3: `4`), see the
module docstring.

**Proof sketch.** `bootNoise_le` (G13) at `β = m·B`. Read `P` through
`Parameters.ofFamily_lwe`, `Parameters.ofFamily_width`, `Parameters.columns_eq`, and `pBoot`
through `pBoot_eq` and `PolyExpr.eval` (notation). Bound `n ≤ d(κ)` and `m ≤ s(κ)` by the family's
`dimension_le` and `samples_le`, so `N = (n + 1)·ℓ ≤ N̂`; `⌈log₂ N⌉ ≤ N`
(`Nat.clog_le_iff_le_pow` with `N < 2^N`, `Nat.lt_two_pow_self`), so `X ≤ ℓ + N̂ + 3`; then
monotonicity of products and powers (`Nat.mul_le_mul`, `Nat.pow_le_pow_left`) and
`8·4^33·2 = 2^70` (`norm_num`). -/
theorem bootRatio_le_poly (F : LWE.Family) (B : ℕ → ℕ) (κ : ℕ) :
    8 * ((Parameters.ofFamily F κ).width *
        bootNoise (Parameters.ofFamily F κ) ((Parameters.ofFamily F κ).lwe.samples * B κ)) ≤
      (pBoot F).eval κ * B κ := by
  sorry

/-- **G17, pure scheme. Correctness at a polynomial ratio.** For every family `F`, noise bound
`B` and `κ`, if the noise law `F.noise κ` is `B κ`-bounded and `pBoot(κ)·B(κ) < q(κ)`, then
the pure bootstrapped GSW at `P = ofFamily F κ` decrypts every fan-in-2 circuit correctly, for
every key seed `rg`, evaluation-key coins `R`, input bits `x` and coins `R'`:
`decrypt P sk (fheEvalCircuit P (evalKey P pk sk R) Cc hC fun j => encrypt P pk (x j) (R' j)) =
Cc.eval x` with `(pk, sk) = Regev.keygen P.lwe (F.noise κ) rg` [BV14, §3.4, Thm 3.7,
p016-b001]. With `LWE.Family.RatioBounded F B p` (`ratioBounded_iff`) this is the regime of a
polynomial ratio. Deviation: worst case.

**Proof sketch.** G12 (`decrypt_keygen_fheEvalCircuit`) at `P`. Its condition
`2·(ℓ·bootNoise P (m·B κ)) < ⌊q/2⌋` follows from G16 (`bootRatio_le_poly`) and `hq`:
`8·y ≤ pBoot(κ)·B(κ) < q` gives `4·y + 2 ≤ q` when `y ≥ 1` (and trivially when `y = 0`, as
`q ≥ 2`), hence `2·y < ⌊q/2⌋` (`omega`), with `y = ℓ·bootNoise`. `q` is read as
`(ofFamily F κ).lwe.modulus` through `Parameters.ofFamily_lwe`. -/
theorem decrypt_fheEval_of_ratio (F : LWE.Family) (B : ℕ → ℕ) (κ : ℕ)
    (hχ : (F.noise κ).Bounded (B κ)) (hq : (pBoot F).eval κ * B κ < (F.parameters κ).modulus)
    (rg : KeySeed (Parameters.ofFamily F κ) (F.noise κ))
    (R : Fin (Parameters.ofFamily F κ).columns → Coins (Parameters.ofFamily F κ)) {k : ℕ}
    (Cc : BoolCircuit.DAGCircuit k) (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (x : Fin k → Bool)
    (R' : Fin k → Coins (Parameters.ofFamily F κ)) :
    decrypt (Parameters.ofFamily F κ)
        (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) rg).2
        (fheEvalCircuit (Parameters.ofFamily F κ)
          (evalKey (Parameters.ofFamily F κ)
            (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) rg).1
            (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) rg).2 R) Cc hC
          fun j => encrypt (Parameters.ofFamily F κ)
            (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) rg).1 (x j) (R' j)) =
      Cc.eval x := by
  sorry

/-- **G17, leveled scheme. Correctness at a polynomial ratio.** For every family `F`, noise
bound `B`, `κ` and level count `L`, if the noise law is `B κ`-bounded and
`pBoot(κ)·B(κ) < q(κ)`, then the leveled bootstrapped GSW at `P = ofFamily F κ` decrypts, under
the secret of the output level, every fan-in-2 circuit on `k ≥ 1` inputs whose NAND form has
depth at most `L`, for every family of key seeds `rgs`, level coins `R`, input bits `x` and
coins `R'` [BV14, §3.4, Thm 3.7, p016-b001; BV11, Thm 3.1, Def 3.6, p015-b001, p014-b001].
Deviations: worst case; the public output level; reconstruction disclosed (module docstring).

**Proof sketch.** L3 (`decrypt_keygen_leveledEvalCircuit`) at `P`. Its two conditions follow
from G16 (`bootRatio_le_poly`) and `hq` as in `decrypt_fheEval_of_ratio`; the input condition
because `m·B ≤ bootNoise P (m·B)` (`bootNoise_eq`, `N ≥ 1` by `Parameters.neZero_columns`). -/
theorem decrypt_leveledEval_of_ratio (F : LWE.Family) (B : ℕ → ℕ) (κ : ℕ)
    (hχ : (F.noise κ).Bounded (B κ)) (hq : (pBoot F).eval κ * B κ < (F.parameters κ).modulus)
    {L k : ℕ} [NeZero k] (rgs : Fin (L + 1) → KeySeed (Parameters.ofFamily F κ) (F.noise κ))
    (R : LevelCoins (Parameters.ofFamily F κ) L) (Cc : BoolCircuit.DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (hdepth : (Cc.toNANDForm hC).depth ≤ L)
    (x : Fin k → Bool) (R' : Fin k → Coins (Parameters.ofFamily F κ)) :
    decrypt (Parameters.ofFamily F κ)
        (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ)
          (rgs ⟨(Cc.toNANDForm hC).depth, Nat.lt_succ_of_le hdepth⟩)).2
        (leveledEvalCircuit (Parameters.ofFamily F κ)
          (levelKey (Parameters.ofFamily F κ)
            (fun e => (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) (rgs e)).1)
            (fun e => (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) (rgs e)).2) R)
          Cc hC fun j => encrypt (Parameters.ofFamily F κ)
            (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) (rgs 0)).1 (x j) (R' j)) =
      Cc.eval x := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/LWE.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Noise
import TCSlib.Cryptography.LWE.Basic
import TCSlib.Cryptography.LWE.Experiments
import TCSlib.Cryptography.LWE.Encoding
import TCSlib.Cryptography.LWE.Assumption
import TCSlib.Cryptography.LWE.SampleSchedules
import TCSlib.Cryptography.LWE.BitEncoding
import TCSlib.Cryptography.LWE.BitNoise
import TCSlib.Cryptography.LWE.Sampling
import TCSlib.Cryptography.LWE.Ratio

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Learning with errors: experiments and the decisional assumption

## Contents

* `Noise`: finite-seed scalar integer noise, with an explicit support-bound predicate.
* `Basic`: numeric parameters and the common-secret sample map.
* `Experiments`: the concrete decisional distinguishing experiment.
* `Encoding`: canonical fixed-width challenges with proved length and injectivity.
* `Assumption`: polynomial representation budgets and fixed-sample hardness against `NUPPT`.
* `SampleSchedules`: explicit sample-count substitution and multi-message row accounting.
* `BitEncoding`: bit codepoints, exact tie conventions and bounded-error decoding statements.
* `BitNoise`: explicit bit-seed laws and centered finite-noise profile statements.
* `Sampling`: actual-law fair-bit implementations of the real and uniform experiments.
* `Ratio`: a polynomially bounded modulus-to-noise ratio for a family.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.2.1 and 4.2.3.
-/

## ===== TCSlib/Cryptography/LWE/BitEncoding.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Basic
import Mathlib.Data.ZMod.ValMinAbs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit codepoints and bounded-error decoding for Regev encryption

## Main definitions

* `BitEncoding.codepoint`: zero for false and `floor(q/2)` for true.
* `BitEncoding.distance`: circular distance using Mathlib's minimal integer lift.
* `BitEncoding.decode`: choose the nearer codepoint, breaking ties toward false.
* `BitEncoding.decodeLo`, `BitEncoding.decodeHi`: the ends of the decoding interval.

## Main results

The distance lemmas and `decode_codepoint_add` are proved below.
`decode_iff_mem_Ico` reads decoding as the interval test
`decodeLo P ≤ v.val < decodeHi P`.
The last theorem gives perfect decoding under the strict separation condition
`2 * B < q / 2`, with natural-number division.

## References

* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 lecture notes,
  compilation last updated 30 April 2024, Definition 20.5 and Lecture 21.

**Deviation.** Nearest-codepoint decoding replaces the notes' informal rounding
notation. The strict separation condition covers arbitrary moduli, both error signs
and all finite parameters. The decoder is total, with an explicit tie rule. No exact
Gaussian sampling, tail bound or machine implementation is asserted.
-/

namespace TCSlib.Cryptography.LWE.BitEncoding

/-- The codepoint for a bit is zero or `floor(q/2)` modulo `q`
[Wu24, Definition 20.5]. -/
def codepoint (P : Parameters) (b : Bool) : ZMod P.modulus :=
  if b then ((P.modulus / 2 : ℕ) : ZMod P.modulus) else 0

/-- `codepoint P b` is `q/2` cast to residues when `b` is true and zero otherwise. -/
theorem codepoint_eq (P : Parameters) (b : Bool) :
    codepoint P b = if b then ((P.modulus / 2 : ℕ) : ZMod P.modulus) else 0 := rfl

/-- Circular distance is the natural absolute value of Mathlib's minimal integer
representative of `x - y`. This is technical decoding infrastructure. -/
def distance (P : Parameters) (x y : ZMod P.modulus) : ℕ :=
  (x - y).valMinAbs.natAbs

/-- The circular distance is `(x - y).valMinAbs.natAbs`. -/
theorem distance_eq (P : Parameters) (x y : ZMod P.modulus) :
    distance P x y = (x - y).valMinAbs.natAbs := rfl

/-- Circular distance is symmetric.

**Proof sketch.** Rewrite `y - x` as the negative of `x - y` and use the public
`ZMod.natAbs_valMinAbs_neg` lemma. -/
theorem distance_symm (P : Parameters) (x y : ZMod P.modulus) :
    distance P x y = distance P y x := by
  rw [distance_eq, distance_eq, ← neg_sub x y, ZMod.natAbs_valMinAbs_neg]

/-- Circular distance satisfies the triangle inequality.

**Proof sketch.** Write `x - z = (x - y) + (y - z)`. Apply
`ZMod.natAbs_valMinAbs_add_le`, then the integer absolute-value triangle inequality. -/
theorem distance_triangle (P : Parameters) (x y z : ZMod P.modulus) :
    distance P x z ≤ distance P x y + distance P y z := by
  rw [distance_eq, distance_eq, distance_eq, ← sub_add_sub_cancel x y z]
  exact (ZMod.natAbs_valMinAbs_add_le (x - y) (y - z)).trans
    (Int.natAbs_add_le _ _)

/-- Adding the same residue to both arguments preserves circular distance.

**Proof sketch.** Cancel the common translation in the difference and read `distance_eq`. -/
theorem distance_add_right (P : Parameters) (x y a : ZMod P.modulus) :
    distance P (x + a) (y + a) = distance P x y := by
  rw [distance_eq, distance_eq, add_sub_add_right_eq_sub]

/-- The two bit codepoints have circular distance `floor(q/2)`
[Wu24, Definition 20.5, exact separation].

**Proof sketch.** Use `ZMod.valMinAbs_natCast_of_le_half` for `q/2` and
`ZMod.natAbs_valMinAbs_neg` if the subtraction has the opposite sign. -/
theorem distance_codepoints (P : Parameters) :
    distance P (codepoint P false) (codepoint P true) = P.modulus / 2 := by
  rw [codepoint_eq, codepoint_eq]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [distance_eq, zero_sub, ZMod.natAbs_valMinAbs_neg,
    ZMod.valMinAbs_natCast_of_le_half (le_refl _), Int.natAbs_natCast]

/-- Reducing an integer error modulo the modulus cannot increase its distance
from zero beyond its original natural absolute value.

**Proof sketch.** Use `ZMod.coe_valMinAbs`, `ZMod.natAbs_valMinAbs_le` and
`ZMod.natAbs_min_of_le_div_two` to compare the minimal lift with the given integer. -/
theorem distance_intCast_zero_le (P : Parameters) (e : ℤ) :
    distance P (e : ZMod P.modulus) 0 ≤ e.natAbs := by
  rw [distance_eq, sub_zero]
  exact ZMod.natAbs_min_of_le_div_two P.modulus _ e
    (ZMod.coe_valMinAbs _) (ZMod.natAbs_valMinAbs_le _)

/-- Decode to true precisely when the true codepoint is strictly nearer;
equidistant inputs decode to false [Wu24, Definition 20.5, specified tie convention]. -/
def decode (P : Parameters) (x : ZMod P.modulus) : Bool :=
  decide (distance P x (codepoint P true) < distance P x (codepoint P false))

/-- Decoding compares the two circular distances, with a strict inequality for true. -/
theorem decode_eq (P : Parameters) (x : ZMod P.modulus) :
    decode P x =
      decide (distance P x (codepoint P true) < distance P x (codepoint P false)) := rfl

/-- The lower end of the decoding interval: `decodeLo P = ⌊⌊q/2⌋/2⌋ + 1`, the least
representative that decodes to true. Glue for the file's `decode`. -/
def decodeLo (P : Parameters) : ℕ :=
  P.modulus / 2 / 2 + 1

/-- `decodeLo P` is `P.modulus / 2 / 2 + 1`. -/
theorem decodeLo_eq (P : Parameters) : decodeLo P = P.modulus / 2 / 2 + 1 := rfl

/-- The upper end, exclusive, of the decoding interval: `decodeHi P = ⌊(q + ⌊q/2⌋ + 1)/2⌋`,
one more than the greatest representative that decodes to true. Glue for the file's
`decode`. -/
def decodeHi (P : Parameters) : ℕ :=
  (P.modulus + P.modulus / 2 + 1) / 2

/-- `decodeHi P` is `(P.modulus + P.modulus / 2 + 1) / 2`. -/
theorem decodeHi_eq (P : Parameters) : decodeHi P = (P.modulus + P.modulus / 2 + 1) / 2 := rfl

/-- **Decoding is an interval test**: a residue decodes to true exactly when its canonical
representative lies in `[decodeLo P, decodeHi P)`,
`decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P`. With `h = ⌊q/2⌋` the interval
is `[⌊h/2⌋ + 1, ⌊(q + h + 1)/2⌋)`. Glue for the file's `decode`, consumed by the GSW
decryption formula as an interval of the modular subset sum.

**Proof sketch.** Write `v` for the representative `v.val < q` and `h = ⌊q/2⌋ < q`. By
Mathlib's `ZMod.valMinAbs_natAbs_eq_min`, the natural absolute value of the minimal lift of a
residue `y` is `min y.val (q − y.val)`; this gives both distances through `distance_eq`.
The distance to the false codepoint (`codepoint_eq`) reads `v`. For the true codepoint `h`,
the representative of `v − h` is `v − h` when `h ≤ v` (`ZMod.val_sub`) and `v + q − h`
otherwise (the difference is the cast of `v + q − h`, by `ZMod.natCast_self` and
`ZMod.natCast_zmod_val`, below `q`). `decode_eq` compares the two distances strictly; after
the case split every case is linear arithmetic with `min` and divisions by `2`, which `omega`
closes against `decodeLo_eq` and `decodeHi_eq`. -/
theorem decode_iff_mem_Ico (P : Parameters) (v : ZMod P.modulus) :
    decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P := by
  have hq := P.modulus_ge_two
  have hv := ZMod.val_lt v
  -- Step 1: the representative of `v − ⌊q/2⌋`.
  have hh : P.modulus / 2 < P.modulus := by omega
  have hsub : (v - ((P.modulus / 2 : ℕ) : ZMod P.modulus)).val =
      if P.modulus / 2 ≤ v.val then v.val - P.modulus / 2
      else v.val + P.modulus - P.modulus / 2 := by
    split_ifs with hle
    · rw [ZMod.val_sub (by rwa [ZMod.val_natCast_of_lt hh]), ZMod.val_natCast_of_lt hh]
    · have hcast : v - ((P.modulus / 2 : ℕ) : ZMod P.modulus) =
          ((v.val + P.modulus - P.modulus / 2 : ℕ) : ZMod P.modulus) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, ZMod.natCast_zmod_val,
          add_zero]
      rw [hcast, ZMod.val_natCast_of_lt (by omega)]
  -- Step 2: both distances as `min` of a representative and its complement
  -- (`ZMod.valMinAbs_natAbs_eq_min`); linear arithmetic in every case.
  rw [decode_eq, decide_eq_true_iff, distance_eq, distance_eq, codepoint_eq, codepoint_eq]
  simp only [if_true, Bool.false_eq_true, if_false, sub_zero]
  rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.valMinAbs_natAbs_eq_min, hsub, decodeLo_eq, decodeHi_eq]
  split_ifs <;> omega

/-- An error of absolute value at most `B` preserves the encoded bit whenever
`2 * B < floor(q/2)` [Wu24, Definition 20.5 and Lecture 21, bounded-error refinement].

**Proof sketch.** Translation invariance and the integer-error bound put the received
residue within `B` of its intended codepoint. The triangle inequality and exact
codepoint separation put its distance to the other codepoint above `B`. The intended
codepoint is uniquely nearer, so the tie rule is immaterial for valid encryptions. -/
theorem decode_codepoint_add (P : Parameters) (B : ℕ) (b : Bool) (e : ℤ)
    (he : e.natAbs ≤ B) (hsep : 2 * B < P.modulus / 2) :
    decode P (codepoint P b + (e : ZMod P.modulus)) = b := by
  have herr : distance P (codepoint P b + (e : ZMod P.modulus)) (codepoint P b) ≤ B := by
    calc
      _ = distance P (e : ZMod P.modulus) 0 := by
        simpa only [zero_add, add_comm] using
          distance_add_right P (e : ZMod P.modulus) 0 (codepoint P b)
      _ ≤ e.natAbs := distance_intCast_zero_le P e
      _ ≤ B := he
  have htri := distance_triangle P (codepoint P false)
    (codepoint P b + (e : ZMod P.modulus)) (codepoint P true)
  rw [distance_codepoints, distance_symm P (codepoint P false)] at htri
  cases b
  · rw [decode_eq]
    exact decide_eq_false (by omega)
  · rw [decode_eq]
    exact decide_eq_true (by omega)

end TCSlib.Cryptography.LWE.BitEncoding

## ===== TCSlib/Cryptography/LWE/Ratio.lean (Lean, at 7563734a8badba842223e0687c719b3b4692e9d2) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.LWE.Assumption

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A polynomially bounded modulus-to-noise ratio for an LWE family

## Main definitions

* `Family.RatioBounded F B p`: at every security parameter `κ` the noise law of `F` is
  `B κ`-bounded and the modulus is at most `p(κ)·B(κ)`, for a syntactic polynomial `p`.

## Main results

* `Family.ratioBounded_iff`: the reader of the predicate.

The predicate is the regime of the phase-5 ruling Q16 (assumption (A2) of the GSW plan): DLWE
for a family whose ratio `q/B` is polynomially bounded. Its consumers are the GSW
polynomial-ratio statements (`GSW/PolyRatio.lean`); no theorem is stated here.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: §3.4, Thm 3.7 (a noise rate `α` inverse-polynomial in `n log q`).
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.3 (decision-LWE).

**Deviations.** [BV14, Thm 3.7] bounds a Gaussian noise rate `α`; here the noise law is the
library's finite-seed `Noise` with a worst-case bound `B`, and the ratio is `q ≤ p(κ)·B(κ)`.
-/

namespace TCSlib.Cryptography.LWE

open Complexity

/-- **A polynomially bounded ratio** (phase-5 Q16; P6-Q12): for every security parameter `κ`,
the noise law `F.noise κ` is `B κ`-bounded and the modulus is at most `p(κ)·B(κ)`,
`F.RatioBounded B p ↔ ∀ κ, (F.noise κ).Bounded (B κ) ∧
(F.parameters κ).modulus ≤ p.eval κ * B κ` [BV14, §3.4, Thm 3.7, p016-b001: the noise rate
`α` inverse-polynomial; Pei16, Def 4.2.3, p024-b001]. Deviation: a worst-case bound on a
finite-seed law instead of a Gaussian rate. -/
def Family.RatioBounded (F : Family) (B : ℕ → ℕ) (p : PolyExpr) : Prop :=
  ∀ κ, (F.noise κ).Bounded (B κ) ∧ (F.parameters κ).modulus ≤ p.eval κ * B κ

/-- `F.RatioBounded B p` holds exactly when, for every `κ`, `(F.noise κ).Bounded (B κ)` and
`(F.parameters κ).modulus ≤ p.eval κ * B κ`. -/
theorem Family.ratioBounded_iff (F : Family) (B : ℕ → ℕ) (p : PolyExpr) :
    F.RatioBounded B p ↔
      ∀ κ, (F.noise κ).Bounded (B κ) ∧ (F.parameters κ).modulus ≤ p.eval κ * B κ :=
  Iff.rfl

end TCSlib.Cryptography.LWE

## ===== blueprint/src/references/brakerski-vaikuntanathan-2014-fhe.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: eab2d1667a8e8a07155968141c72d0ff0be15b1185dd0fd34f291fb41fb812ca -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Lattice-Based FHE as Secure as PKE

Zvika Brakerski and Vinod Vaikuntanathan. *ITCS 2014*, pp. 1–12; IACR ePrint 2013/541, PDF
created 28 August 2013 (21 pages; tag `BV14`).

**Scope.** Only the passages that the GSW Lean (phase 5) and the phase-6 plan use are
transcribed (DW-7; GSW ruling Q14): the leveled-FHE footnote and Theorem 1.1 of §1, the
decomposition routines of §2.3, §2.5 (homomorphic encryption, Definitions 2.12–2.13,
Theorem 2.14), all of §3 (the scheme `NCCrypt`, Definition 3.1, Lemmas 3.2–3.3, Proposition 3.4,
Claims 3.4.1–3.4.2, width-5 permutation branching programs, Equations (4)–(6), Theorem 3.5,
Lemma 3.6, Theorem 3.7), the statement of Lemma 4.4, and Corollary 4.5 with the key-size remark
of §4.2. §2.1, §2.2, §2.4 (the randomization lemmas 2.9–2.11) and §4.1 are not transcribed; the
phase-5 Lean replaces their probabilistic bounds by worst-case ones. The PDF is not committed.
Physical and printed pages coincide. The scoped raw extraction is
`brakerski-vaikuntanathan-2014-fhe.raw.md`. Mathematics is set in LaTeX; the paper's
sans-serif procedure names are written $\mathsf{NCCrypt.Keygen}$ etc. The wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-eab2d1667a8e-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->

**Section 1, footnote 1: leveled FHE and circular security (p. 1).** Here, and in the rest of the
introduction, when we say FHE, we mean a leveled FHE scheme that can evaluate circuits of any
a-priori bounded polynomial depth. The only known way to achieve non-leveled FHE schemes is to
make a circular security assumption, in addition.

<a id="pdf-eab2d1667a8e-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->

**Theorem 1.1.** For every $\epsilon>0$, there exists a leveled fully homomorphic encryption
scheme based on the $\mathsf{DLWE}_{n,q,\alpha}$ assumption ($n$-dimensional decisional LWE
modulo $q$, with discrete Gaussian noise with parameter $\alpha$), where
$\alpha=1/\tilde O(n^{\epsilon}\cdot\sqrt{n\log(q)})$.

Thus, the scheme is secure based on either the quantum worst-case hardness of
$\mathsf{GapSVP}_{\tilde O(n^{1.5+\epsilon})}$, or the classical worst-case hardness of
$\mathsf{GapSVP}_{\tilde O(n^{2+\epsilon})}$.

*Transcription note.* The extraction drops the $\epsilon$ glyphs and scatters the tildes; the
statement is read from the layout. It is context only (the phase-6 plan does not formalize
worst-case lattice factors).

<a id="pdf-eab2d1667a8e-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->

**Section 2.3, vector decomposition (pp. 5–6).** We show how to decompose vectors in a way that
makes their norm smaller, and yet preserves certain inner products. Our notation is generally
adopted from [BGV12].

*Vector Decomposition.* We often break vectors into their bit representations as defined below:

- $\mathsf{BitDecomp}_q(\mathbf x)$: For $\mathbf x\in\mathbb Z^n$, let $w_{i,j}\in\{0,1\}$ be
  such that $\mathbf x[i]=\sum_{j=0}^{\lceil\log q\rceil-1}2^j\cdot w_{i,j}\pmod q$. Output the
  vector
  $(w_{1,\lceil\log q\rceil-1},\dots,w_{1,0},\dots,w_{n,\lceil\log q\rceil-1},\dots,w_{n,0})\in\{0,1\}^{n\cdot\lceil\log q\rceil}$.
- $\mathsf{PowersOfTwo}_q(\mathbf y)$: For $\mathbf y\in\mathbb Z^n$, output
  $\bigl[(2^{\lceil\log q\rceil-1}\mathbf y[1],\dots,2\mathbf y[1],\mathbf y[1],\dots,2^{\lceil\log q\rceil-1}\cdot\mathbf y[n],\dots,2\mathbf y[n],\mathbf y[n])\bigr]_q\in\mathbb Z_q^{n\cdot\lceil\log q\rceil}$.

We will usually omit the subscript $q$ when it is clear from the context.

**Claim 2.7.** For all $q\in\mathbb N$ and $\mathbf x,\mathbf y\in\mathbb Z^n$, it holds that

$$
\langle\mathbf x,\mathbf y\rangle=\langle\mathsf{BitDecomp}_q(\mathbf x),\mathsf{PowersOfTwo}_q(\mathbf y)\rangle\pmod q.
$$

Additionally, we define the procedure Flatten following [GSW13], along with the procedure
Combine. Let
$\mathbf g=(2^{\lceil\log(q)\rceil-1},2^{\lceil\log(q)\rceil-2},\dots,4,2,1)\in\mathbb Z^{\lceil\log q\rceil}$
and let $\mathbf G:=\mathbf g\otimes\mathbf I_n\in\mathbb Z^{n\times(n\cdot\lceil\log q\rceil)}$
denote the tensor product of $\mathbf g$ with the $n$-by-$n$ identity matrix $\mathbf I_n$.

- $\mathsf{Combine}_q(\mathbf z)$: For $\mathbf z\in\mathbb Z^{n\cdot\lceil\log q\rceil}$, output
  $[\mathbf G\cdot\mathbf z]_q\in\mathbb Z_q^n$.
- $\mathsf{Flatten}_q(\mathbf z)$: For $\mathbf z\in\mathbb Z^{n\cdot\lceil\log q\rceil}$, output
  $\mathsf{BitDecomp}_q(\mathsf{Combine}(\mathbf z))\in\{0,1\}^{n\cdot\lceil\log q\rceil}$.

**Claim 2.8.** For all $q\in\mathbb N$, and $\mathbf x,\mathbf z\in\mathbb Z^{n\cdot\lceil\log q\rceil}$,
it holds that

$$
\langle\mathsf{PowersOfTwo}(\mathbf x),\mathbf z\rangle=\langle\mathsf{PowersOfTwo}(\mathbf x),\mathsf{Flatten}(\mathbf z)\rangle\pmod q.
$$

*Transcription note.* BV14 orders bits most significant first, unlike GSW13. In Claim 2.8 the
printed domain of $\mathbf x$ is as transcribed (the claim is used with
$\mathbf x\in\mathbb Z^{n}$). Confidence is lowered because sub- and superscripts are flattened
in the extraction.

<a id="pdf-eab2d1667a8e-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Section 2.5, homomorphic encryption and bootstrapping (pp. 7–8).** We now define homomorphic
encryption and introduce Gentry's bootstrapping theorem. Our definitions are mostly taken from
[BV11, BGV12].

A homomorphic (public-key) encryption scheme
$\mathsf{HE}=(\mathsf{HE.Keygen},\mathsf{HE.Enc},\mathsf{HE.Dec},\mathsf{HE.Eval})$ is a
quadruple of ppt algorithms as follows ($\kappa$ is the security parameter):

- **Key generation** $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$: Outputs a public
  encryption key $pk$, a public evaluation key $evk$ and a secret decryption key $sk$.²
- **Encryption** $c\leftarrow\mathsf{HE.Enc}_{pk}(\mu)$: Using the public key $pk$, encrypts a
  single bit message $\mu\in\{0,1\}$ into a ciphertext $c$.
- **Decryption** $\mu\leftarrow\mathsf{HE.Dec}_{sk}(c)$: Using the secret key $sk$, decrypts a
  ciphertext $c$ to recover the message $\mu\in\{0,1\}$.
- **Homomorphic evaluation** $c_f\leftarrow\mathsf{HE.Eval}_{evk}(f,c_1,\dots,c_\ell)$: Using the
  evaluation key $evk$, applies a function $f:\{0,1\}^\ell\to\{0,1\}$ to $c_1,\dots,c_\ell$, and
  outputs a ciphertext $c_f$.

Footnote 2: We adopt the terminology of [BV11] that treats the evaluation key as a separate
entity from the public key.

A homomorphic encryption scheme is said to be secure if it is semantically secure (note that the
adversary is given both $pk$ and $evk$).

Homomorphism w.r.t depth-bounded circuits and full homomorphism are defined next:

<a id="pdf-eab2d1667a8e-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Definition 2.12 (compactness and full homomorphism).** A homomorphic encryption scheme is
*compact* if its decryption circuit is independent of the evaluated function. A compact scheme is
(pure) *fully homomorphic* if it can evaluate any efficiently computable function. The scheme is
*leveled fully homomorphic* if it takes $1^L$ as additional input in key generation, and can only
evaluate depth $L$ Boolean circuits.

Gentry's bootstrapping theorem shows how to go from limited amount of homomorphism to full
homomorphism. This method has to do with the augmented decryption circuit.

<a id="pdf-eab2d1667a8e-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Definition 2.13.** Consider a homomorphic encryption scheme $\mathsf{HE}$. Let $(sk,pk,evk)$ be
properly generated keys and let $\mathcal C$ be the set of properly decryptable ciphertexts. Then
the set of *augmented decryption functions*, $\{f_{c_1,c_2}\}_{c_1,c_2\in\mathcal C}$ is defined
by $f_{c_1,c_2}(x)=\overline{\mathsf{HE.Dec}_x(c_1)\wedge\mathsf{HE.Dec}_x(c_2)}$. Namely, the function
that uses its input as secret key, decrypts $c_1,c_2$ and returns the NAND of the results.

*Transcription note.* The bar over the conjunction (NAND) is visible in the page image
(150 dpi), not in the extraction, which shows a plain $\wedge$.

<a id="pdf-eab2d1667a8e-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->

**Theorem 2.14 (bootstrapping [Gen09b, Gen09a]).** The bootstrapping theorem is thus as
follows. A scheme that can homomorphically evaluate its family of augmented decryption circuits
can be transformed into a leveled fully homomorphic encryption scheme with the same decryption
circuit, ciphertext space and public key.

Furthermore, if the aforementioned scheme is also weak circular secure (remains secure even
against an adversary who gets encryptions of the bits of the secret key), then it can be made into
a pure fully homomorphic encryption scheme.

<a id="pdf-eab2d1667a8e-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.95 -->

## 3 Our FHE Scheme

**Section 3, opening, and Section 3.1, opening (p. 8).** In this section, we describe an FHE
scheme secure under a polynomial LWE assumption which, using known reductions [Reg05, Pei09],
translates to the worst-case hardness of solving various lattice problems to within polynomial
approximation factors. We start with the basic encryption scheme in Section 3.1, and describe
"proto-homomorphic" addition and multiplication subroutines in Section 3.2. Departing from the
"conventional wisdom" in FHE, our circuit evaluation procedure in Section 3.3 will not be a naive
combination of these proto-homomorphic operations, but rather a carefully designed procedure that
manages the noise growth effectively.

Finally, in Section 3.4, we put this all together to get our FHE scheme under the decisional LWE
assumption $\mathsf{DLWE}_{n,q,\alpha}$ with $\alpha=n^{-c}$ for some constant $c>0$. This
polynomial factor is rather large: thus, in Section 4, we apply a carefully designed variant of
the dimension-modulus reduction procedure of [BV11] to obtain our final FHE scheme that is secure
under the hardness of $\mathsf{DLWE}_{n,q,\alpha}$ with
$\alpha\le1/\tilde O_\kappa(n\cdot\sqrt{n\log(q)})$ which is weakest LWE hardness assumption that
underlies the (non-homomorphic) lattice-based PKE schemes [AD97, Reg04, Reg05, Pei09, BLP+13].

Our basic encryption scheme closely follows the Gentry-Sahai-Waters FHE scheme [GSW13]. We refer
the reader to Section 2.3 for the description of the vector decomposition routines PowersOfTwo,
BitDecomp and Flatten used in the scheme below.

<a id="pdf-eab2d1667a8e-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 3.1, the scheme $\mathsf{NCCrypt}$ (p. 9).**

*System Parameters.* Let $n$ be the LWE dimension and $q$ be an LWE modulus. Define
$N:=(n+1)\cdot\lceil\log q\rceil$. Let $d$ denote the maximal homomorphism depth that is allowed
by the scheme. Let $\chi$ be an error distribution over $\mathbb Z$. Typically $\chi$ will be a
discrete Gaussian $D_{\mathbb Z,\alpha q}$ for
$\alpha=1/\tilde O_\kappa(\sqrt{n\log(q)}\cdot4^d)$. Recall that we identify $\mathbb Z_q$ with
the set $(-q/2,q/2]\cap\mathbb Z$.

- $\mathsf{NCCrypt.Keygen}(1^n,q,4^d)$: Sample a vector $\mathbf s\xleftarrow{\$}\mathbb Z_q^n$.
  Let $m\triangleq(n+1)\cdot(\log q+O(1))$. Sample $\mathbf A\xleftarrow{\$}\mathbb Z_q^{m\times n}$
  and $\mathbf e\xleftarrow{\$}\chi^m$. Compute $\mathbf b:=[\mathbf A\cdot\mathbf s+\mathbf e]_q$,
  and define

  $$
  \mathbf P:=[\mathbf b\,\|-\mathbf A]\in\mathbb Z_q^{m\times(n+1)}.
  $$

  Output $sk=\mathbf s$ and $pk=evk=\mathbf P$.

  We describe public-key as well as secret-key encryption algorithms. Looking ahead, we remark
  that a secret-key encryption of $\mu$ is somewhat less "noisy" than a public-key encryption of
  $\mu$.
- $\mathsf{NCCrypt.PubEnc}(pk,\mu)$: To encrypt a bit $\mu\in\{0,1\}$, using the public key
  $pk=\mathbf P$, we let $\mathbf R\xleftarrow{\$}\{0,1\}^{N\times m}$, and output the ciphertext

  $$
  \mathbf C=\mathsf{Flatten}\left(\mathsf{BitDecomp}(\mathbf R\cdot\mathbf P)+\mu\cdot\mathbf I\right)\in\{0,1\}^{N\times N}.
  $$
- $\mathsf{NCCrypt.SecEnc}(sk,\mu)$: A symmetric encryption of a bit $\mu\in\{0,1\}$, using the
  secret key $sk=\mathbf s$, is performed by sampling
  $\mathbf A\xleftarrow{\$}\mathbb Z_q^{N\times n}$ and $\mathbf e\xleftarrow{\$}\chi^N$,
  computing $\mathbf b:=[\mathbf A\cdot\mathbf s+\mathbf e]_q$, and defining

  $$
  \mathbf C=\mathsf{Flatten}\left(\mathsf{BitDecomp}\left([\mathbf b\,\|-\mathbf A]\right)+\mu\cdot\mathbf I\right)\in\{0,1\}^{N\times N}.
  $$
- $\mathsf{NCCrypt.Dec}(sk,\mathbf C)$: Let $\mathbf c$ be the second row of $\mathbf C$. We use
  standard Regev decryption on $\mathbf c$. Namely, we output $\mu^*=0$ if
  $\bigl|[\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle]_q\bigr|<q/8$, and $\mu^*=1$
  otherwise.

*Transcription note.* The absolute value in $\mathsf{NCCrypt.Dec}$ is visible in the page image
(115 dpi), not in the extraction.

<a id="pdf-eab2d1667a8e-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Section 3.1, correctness; Definition 3.1 and Lemma 3.2 (p. 9).** In order to show correctness
of this scheme, we analyze the noise magnitude of ciphertexts produced by both the public-key and
secret-key encryption algorithms. As we will show shortly, for ciphertexts $\mathbf C$ produced by
either encryption algorithm, we have

$$
\mathbf C\cdot\mathsf{PowersOfTwo}(1,\mathbf s)=\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)+\mathbf e\pmod q
$$

for a noise vector $\mathbf e$ of "small magnitude". This motivates our definition of the noise in
the ciphertext $\mathbf C$ with respect to a secret key vector $\mathbf s$ and a message $\mu$ as
follows.

**Definition 3.1.** For every $\mathbf C\in\{0,1\}^{N\times N}$, $\mathbf s\in\mathbb Z_q^n$ and
$\mu\in\mathbb Z$, we define

$$
\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)\triangleq\bigl\|(\mathbf C-\mu\mathbf I)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\pmod q\bigr\|_\infty
$$

The significance of this definition is captured by the following claims. The first claim shows
that any ciphertext with small noise is decrypted correctly.

**Lemma 3.2.** For every $\mathbf C\in\{0,1\}^{N\times N}$, $\mathbf s\in\mathbb Z_q^n$ and
$\mu\in\mathbb Z$ such that $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)<q/8$,

$$
\mathsf{NCCrypt.Dec}(\mathbf s,\mathbf C)=\mu
$$

<a id="pdf-eab2d1667a8e-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Proof of Lemma 3.2 (p. 10).** Since $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)<q/8$, we have

$$
\mathbf C\cdot\mathsf{PowersOfTwo}(1,\mathbf s)=\eta+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\pmod q
$$

where $\|\eta\|_\infty<q/8$. Thus, for the second row of $\mathbf C$ it holds that

$$
\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle=\eta+2^{\lceil\log(q)\rceil-2}\cdot\mu\pmod q
$$

where $|\eta|<q/8$. Thus, when $\mu=0$,

$$
\bigl|[\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle]_q\bigr|=|\eta|<q/8
$$

When $\mu=1$,

$$
\bigl|[\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle]_q\bigr|\ge q/4-|\eta|\ge q/8
$$

since $q/4\le2^{\lceil\log(q)\rceil-2}<q/2$. This shows correctness of decryption for ciphertexts
with small noise.

*Transcription note.* The vertical bars around $[\cdot]_q$ in the two displays are visible in the
page image (130 dpi), not in the extraction.

<a id="pdf-eab2d1667a8e-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.90 -->

**Section 3.1, fresh noise; Lemma 3.3 and its proof (p. 10).** The next claim demonstrates
parameter settings for which the (public key and secret key) encryption algorithms produce
ciphertexts with small noise.

**Lemma 3.3.** Let $n$ be the LWE dimension, $q$ be the LWE modulus and $\chi=D_{\mathbb Z,\alpha q}$ be the discrete Gaussian
distribution. Then, for every $\mathbf s\in\mathbb Z_q^n$ and $\mu\in\{0,1\}$,

- for $\mathbf C_{pub}\leftarrow\mathsf{NCCrypt.PubEnc}(pk,\mu)$, we have
  $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C_{pub})=\tilde O_\kappa(\alpha q\cdot\sqrt m)$.
- for $\mathbf C_{sec}\leftarrow\mathsf{NCCrypt.SecEnc}(sk,\mu)$, we have
  $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C_{sec})=\tilde O_\kappa(\alpha q)$.

with all but negligible (in $\kappa$) probability over the coins of $\mathsf{NCCrypt.Keygen}$.

In particular, we have correctness of decryption for the public key encryption for
$\alpha<1/\tilde\Omega_\kappa(\sqrt m)$, and for the secret key encryption for
$\alpha<1/\tilde\Omega_\kappa(1)$.

**Proof of Lemma 3.3.** We first show the analysis for the public-key encryption.

$$
\begin{aligned}
\mathbf C_{pub}\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
&=\mathsf{Flatten}\bigl(\mathsf{BitDecomp}(\mathbf R\cdot\mathbf P)+\mu\cdot\mathbf I\bigr)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\bigl(\mathsf{BitDecomp}(\mathbf R\cdot\mathbf P)+\mu\cdot\mathbf I\bigr)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\mathbf R\cdot\mathbf P\cdot(1,\mathbf s)^T+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\mathbf R\cdot\mathbf e+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
\end{aligned}
$$

Thus, by Proposition 2.3,

$$
\mathsf{noise}(\mathbf C_{pub})=\|\mathbf R\cdot\mathbf e\|_\infty=\tilde O_\kappa(\sqrt m\cdot\alpha q)
$$

This is less than $q/8$ by the choice of $\alpha<1/\tilde\Omega_\kappa(\sqrt m)$.

The analysis for the secret key encryption follows analogously, except that

$$
\mathbf C_{sec}\cdot\mathsf{PowersOfTwo}(1,\mathbf s)=\mathbf e+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
$$

Thus,

$$
\mathsf{noise}(\mathbf C_{sec})=\|\mathbf e\|_\infty=\tilde O_\kappa(\alpha q)
$$

which is less than $q/8$ by the choice of $\alpha<1/\tilde\Omega_\kappa(1)$.

*Transcription note.* The tildes and radicals are flattened in the extraction; confidence is
lowered for that reason.

<a id="pdf-eab2d1667a8e-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->

**Section 3.1, security and complexity of decryption; Proposition 3.4 (p. 11).**

*Security.* Semantic security of the scheme follows from the decisional LWE assumption
$\mathsf{DLWE}_{n,q,\alpha}$, similarly to Regev's encryption scheme (see [Reg05, BV11, GSW13]
for similar arguments).

*Complexity of Decryption.* Our decryption algorithm is essentially the same as the decryption
algorithm in Regev's encryption scheme, the complexity of which has been thoroughly studied in the
context of FHE. The following is an immediate corollary from [BV11, Lemma 4.1].

**Proposition 3.4.** There exists a constant $c_{\mathsf{dec}}$ such that the decryption circuit
of the scheme $\mathsf{NCCrypt}$, with parameters $n,q$, has depth at most
$c_{\mathsf{dec}}\cdot\log(n\log q)$.

*Transcription note.* In the 39-page full version of [BV11] used for this campaign
(`brakerski-vaikuntanathan-2011-fhe.md`) the decryption-depth lemma is numbered Lemma 4.5;
"[BV11, Lemma 4.1]" is BV14's reference.

<a id="pdf-eab2d1667a8e-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->

**Section 3.2, proto-homomorphic operations; addition and Claim 3.4.1 (p. 11).** We now describe
proto-homomorphic addition and multiplication algorithms which will be used in Section 3.3 for
homomorphic circuit evaluation. Departing from the "conventional wisdom" in FHE, our circuit
evaluation procedure will not be a naive combination of homomorphic addition and multiplication,
but a carefully designed procedure that manages the noise growth effectively. To further stress
the fact that we do not intend for these procedures to be used independently, we call them
proto-homomorphic operations.

*Proto-Homomorphic Addition.* This is a simple addition of the ciphertext matrices.

- $\mathsf{NCCrypt.ProtoAdd}(\mathbf C_1,\mathbf C_2)$: Output
  $\mathbf C_+:=\mathsf{Flatten}(\mathbf C_1+\mathbf C_2)$.

Jumping ahead, we note that in our use of $\mathsf{NCCrypt.ProtoAdd}$ in Section 3.3, both
$\mathbf C_1$ and $\mathbf C_2$ will be encryptions of bits, and at most one of them will be an
encryption of $1$. The following claim analyzes the noise growth in homomorphic addition.

**Claim 3.4.1 (Noise Growth in $\mathsf{NCCrypt.ProtoAdd}$.).** For every
$\mathbf s\in\mathbb Z_q^n$, $\mu_1,\mu_2\in\mathbb Z$ and
$\mathbf C_1,\mathbf C_2\in\{0,1\}^{N\times N}$, we have

$$
\mathsf{noise}_{\mathbf s,\mu_1+\mu_2}(\mathsf{NCCrypt.ProtoAdd}(\mathbf C_1,\mathbf C_2))
\le\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\mathsf{noise}_{\mathbf s,\mu_2}(\mathbf C_2)
$$

**Proof.** Let $\mathbf C_+\leftarrow\mathsf{NCCrypt.ProtoAdd}(\mathbf C_1,\mathbf C_2)$. We note
that

$$
\begin{aligned}
\mathbf C_+\cdot\mathsf{PowersOfTwo}(1,\mathbf s)&=\mathsf{Flatten}(\mathbf C_1+\mathbf C_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=(\mathbf C_1+\mathbf C_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\mathbf C_1\cdot\mathsf{PowersOfTwo}(1,\mathbf s)+\mathbf C_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=(\mathbf e_1+\mathbf e_2)+(\mu_1+\mu_2)\cdot\mathbf I
\end{aligned}
$$

Thus, by the definition of $\mathsf{noise}_{\mathbf s,\mu_1+\mu_2}$, we have

$$
\mathsf{noise}_{\mathbf s,\mu_1+\mu_2}(\mathbf C_+)\le\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\mathsf{noise}_{\mathbf s,\mu_2}(\mathbf C_2)
$$

*Transcription note.* The last line of the display ends in "$\cdot\,\mathbf I$" as printed (the
intended term is $(\mu_1+\mu_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)$).

<a id="pdf-eab2d1667a8e-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

**Section 3.2, multiplication; Claim 3.4.2 (p. 12).** *Homomorphic Multiplication.* This is
essentially a multiplication of the ciphertext matrices, except that we randomize the first
ciphertext.

- $\mathsf{NCCrypt.ProtoMult}(evk,\mathbf C_1,\mathbf C_2)$:
  - Randomize $\mathbf C_1\in\{0,1\}^{N\times N}$ into a matrix
    $\widetilde{\mathbf C}_1\in\{0,1\}^{N\times N}$ by replacing each row $\mathbf c$ in
    $\mathbf C_1$ by the row
    $\widetilde{\mathbf c}\leftarrow\mathsf{BitDecomp}(\mathsf{Rand}(pk,\mathsf{Combine}(\mathbf c)))$
    where $\mathsf{Rand}$ is the LWE randomization procedure from Section 2.4.
  - Output $\mathbf C_\times\leftarrow\mathsf{Flatten}\bigl(\widetilde{\mathbf C}_1\cdot\mathbf C_2\bigr)$.

Jumping ahead, we remark that when we use $\mathsf{NCCrypt.ProtoMult}$ in our homomorphic circuit
evaluation in Section 3.3, the first ciphertext will be an "evaluated ciphertext" (namely, a
result of previous homomorphic evaluations), whereas the second ciphertext will be a "fresh
ciphertext" (namely an output of the *secret key* encryption algorithm).

The first new idea in this work is that while the order of the arguments does not matter in
homomorphic addition, the homomorphic multiplication algorithm $\mathsf{NCCrypt.ProtoMult}$ is
inherently asymmetric, since it is essentially the (non-commutative) matrix multiplication
operation. This asymmetry turns out to be the key to achieving improved noise growth, as
Claim 3.4.2 below will demonstrate.

**Claim 3.4.2 (Noise Growth in $\mathsf{NCCrypt.ProtoMult}$.).** For every
$\mathbf s\in\mathbb Z_q^n$, $\mu_1,\mu_2\in\{0,1\}$ and $\mathbf C_1\in\{0,1\}^{N\times N}$ and
$\mathbf C_2\leftarrow\mathsf{NCCrypt.SecEnc}(sk,\mu_2)$, we have

$$
\mathsf{noise}_{\mathbf s,\mu_1\mu_2}(\mathsf{NCCrypt.ProtoMult}(\mathbf C_1,\mathbf C_2))
\le|\mu_2|\cdot\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
$$

with all but negligible probability over the randomness of $\mathsf{NCCrypt.Keygen}$,
$\mathsf{NCCrypt.SecEnc}$ and $\mathsf{NCCrypt.ProtoMult}$.

**Remark.** In words, Claim 3.4.2 says that if $\mu_2\in\{0,1\}$ (as will be the case in our
homomorphic circuit evaluation in Section 3.3), the noise in $\mathbf C_\times$ is at most the
noise in $\mathbf C_1$, plus a fixed additive term. What's more, if $\mu_2=0$, then the noise in
$\mathbf C_\times$ is independent of that in $\mathbf C_1$! *These two facts are the key new ideas
that enable our main result.*

<a id="pdf-eab2d1667a8e-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->

**Proof of Claim 3.4.2 (pp. 12–13).** Let
$\mathbf C_\times\leftarrow\mathsf{NCCrypt.ProtoMult}(evk,\mathbf C_1,\mathbf C_2)$. Note that

$$
\begin{aligned}
\mathbf C_\times\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
&=\mathsf{Flatten}(\widetilde{\mathbf C}_1\cdot\mathbf C_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\widetilde{\mathbf C}_1\cdot(\mathbf C_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s))\\
&=\widetilde{\mathbf C}_1\cdot(\mathbf e_2+\mu_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s))\\
&=\widetilde{\mathbf C}_1\cdot\mathbf e_2+\mu_2\cdot\widetilde{\mathbf C}_1\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\widetilde{\mathbf C}_1\cdot\mathbf e_2+\mu_2\cdot(\widetilde{\mathbf e}_1+\mu_1\cdot\mathsf{PowersOfTwo}(1,\mathbf s))\\
&=(\widetilde{\mathbf C}_1\cdot\mathbf e_2+\mu_2\cdot\widetilde{\mathbf e}_1)+\mu_1\mu_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
\end{aligned}\tag{1}
$$

Since $\mathbf e_2\leftarrow D^N_{\mathbb Z,\alpha q}$ and each row of
$\widetilde{\mathbf C}_1\in\{0,1\}^{N\times N}$ is the result of $\mathsf{Rand}$, by Lemma 2.11,
we have

$$
\bigl\|\widetilde{\mathbf C}_1\cdot\mathbf e_2\bigr\|_\infty\le\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})\tag{2}
$$

with all but negligible probability. Also, by lemma 2.10, we have

$$
\|\widetilde{\mathbf e}_1\|_\infty\le\|\mathbf e_1\|_\infty+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})\tag{3}
$$

with all but negligible probability.

Putting together Eq. (1),(2) and (3), we have

$$
\mathsf{noise}_{\mathbf s,\mu_1\mu_2}(\mathbf C_\times)
\le\bigl\|\widetilde{\mathbf C}_1\cdot\mathbf e_2\bigr\|_\infty+|\mu_2|\cdot\|\widetilde{\mathbf e}_1\|_\infty
\le|\mu_2|\cdot\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
$$

which finishes the proof.

<a id="pdf-eab2d1667a8e-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->

**Section 3.3, homomorphic evaluation of circuits: opening (p. 13).** We now describe how to
homomorphically evaluate a Boolean circuit $\Psi$ with two-input NAND gates that takes $\ell$
inputs, and has depth $d$. In particular, our scheme will be able to evaluate circuits of depth
$c\cdot\log n$ (for any constant $c$) under a polynomial LWE assumption, namely
$\mathsf{DLWE}_{n,q,\chi}$ where $\chi=D_{\mathbb Z,\alpha}$ and $\alpha=1/n^{\Theta(c)}$. Since
the depth of the decryption circuit is
$c_{\mathsf{dec}}\cdot\log(n\log(q))\le2c_{\mathsf{dec}}\cdot\log(n)$ (for some constant
$c_{\mathsf{dec}}>0$), the scheme is bootstrappable, and by the bootstrapping theorem
(Theorem 2.14), we get a leveled FHE scheme under the same assumption.

To evaluate a circuit, our scheme first turns it into a width-5 permutation branching program
[BDFP86, Bar89], a model of computation that we describe below.

<a id="pdf-eab2d1667a8e-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.95 -->

**Section 3.3, width-5 permutation branching programs (pp. 13–14).** A permutation branching
program $\Pi$ of length $L$ with input space $\{0,1\}^\ell$ is a sequence of $L$ tuples of the form
$\bigl(\mathsf{var}(t),\sigma_{t,0},\sigma_{t,1}\bigr)$ where

- $\mathsf{var}:[L]\to[\ell]$ is a function that associates the $t$-th tuple with an input bit
  $x_{\mathsf{var}(t)}$.
- $\sigma_{j,0}$ and $\sigma_{j,1}$ are permutations on 5 elements. We will think of $\sigma_{j,0}$
  and $\sigma_{j,1}$ as bijective functions from the set $\{1,2,3,4,5\}$ to itself.

The computation of the program $\Pi$ on input $\mathbf x=(x_1,\dots,x_\ell)$ proceeds as follows.
The state of the computation at any point in time $t$ is a number $\zeta_t\in\{1,2,3,4,5\}$.
Computation starts with the initial state $\zeta_0=1$. The state $\zeta_t$ is computed
recursively as

$$
\zeta_t=\sigma_{t,\mathsf{var}(t)}(\zeta_{t-1})
$$

Finally, after $L$ steps, our state is $\zeta_L$. The output of the computation is $1$ if
$\zeta_L=1$, and $0$ otherwise.

To manage the growth of noise in homomorphic evaluation, we need to work with bits rather than
numbers. Thus, we prefer to represent the state $\zeta_t\in\{1,2,3,4,5\}$ by a 0-1 vector
$\mathbf v_t$ which is the unit vector $\mathbf u_{\zeta_t}$ in 5 dimensions.

The computation then proceeds as follows. The idea is that $\mathbf v_t[i]=1$ if and only if
$\sigma_{t,\mathsf{var}(t)}(\zeta_{t-1})=i$. Turning this around, $\mathbf v_t[i]=1$ if and only
if either:

- $\mathbf v_{t-1}[\sigma_{t,0}^{-1}(i)]=1$ and $x_{\mathsf{var}(t)}=0$; or
- $\mathbf v_{t-1}[\sigma_{t,1}^{-1}(i)]=1$ and $x_{\mathsf{var}(t)}=1$.

The following formula captures this condition. For $t=1,\dots,L$, and $i\in\{1,2,3,4,5\}$, we
have:

$$
\begin{aligned}
\mathbf v_t[i]&:=\mathbf v_{t-1}[\sigma_{t,0}^{-1}(i)]\cdot(1-x_{\mathsf{var}(t)})+\mathbf v_{t-1}[\sigma_{t,1}^{-1}(i)]\cdot x_{\mathsf{var}(t)}\\
&=\mathbf v_{t-1}[\gamma_{t,i,0}]\cdot(1-x_{\mathsf{var}(t)})+\mathbf v_{t-1}[\gamma_{t,i,1}]\cdot x_{\mathsf{var}(t)}
\end{aligned}\tag{4}
$$

where $\gamma_{t,i,0}\triangleq\sigma_{t,0}^{-1}(i)$ and $\gamma_{t,i,1}\triangleq\sigma_{t,1}^{-1}(i)$
are constants that are publicly computable given the description of the branching program. It is
this form that we will work with in our homomorphic evaluation.

The important property that we will use is that circuits of depth $d$ can be simulated by
branching programs of depth $L=4^d$.

*Transcription note.* "$\zeta_t=\sigma_{t,\mathsf{var}(t)}(\zeta_{t-1})$" is as printed (checked
against the page image); the intended permutation is $\sigma_{t,x_{\mathsf{var}(t)}}$, selected by
the value of the input bit, as Equation (4) shows.

<a id="pdf-eab2d1667a8e-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->

**Theorem 3.5 (Barrington's Theorem [Bar89]).** Every Boolean NAND circuit $\Psi$ that acts on
$\ell$ inputs and has depth $d$ can be computed by a width-5 permutation branching program $\Pi$ of
length $4^d$. Given the description of the circuit $\Psi$, the description of the branching
program $\Pi$ can be computed in $\mathrm{poly}(\ell,4^d)$ time.

<a id="pdf-eab2d1667a8e-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->

**Section 3.3, homomorphic evaluation $\mathsf{NCCrypt.Eval}(\Psi,\mathbf C_1,\dots,\mathbf C_\ell)$,
Equations (5)–(6) (p. 14).** The homomorphic evaluation procedure will first convert the depth-$d$
circuit $\Psi$ into a width-5 permutation branching program $\Pi$ of length $L=4^d$.

- **[Initialization]** We will maintain the encrypted state of the computation of the branching
  program for every step $t$. We denote this by
  $\mathbf V_t=(\mathbf V_{t,1},\mathbf V_{t,2},\mathbf V_{t,3},\mathbf V_{t,4},\mathbf V_{t,5})$,
  where each $\mathbf V_t[i]\in\{0,1\}^{N\times N}$ will be an encryption of $\mathbf v_t[i]$.
  - We initialize the state as follows. Compute $\mathbf V_{0,i}:=\mathbf v_0[i]\cdot\mathbf I$.
    Note that $\mathbf V_{0,i}$ is in fact a valid encryption of the bit $\mathbf v_0[i]$ with zero
    noise.
  - We also compute encryptions of the complements of the input bits, for convenience. That is,
    set $\bar{\mathbf C}_k:=\mathbf I-\mathbf C_k$. Note that $\bar{\mathbf C}_k$ is an encryption
    of $\bar x_k=1-x_k$ with the same noise as $\mathbf C_k$.
- **[Evaluation]** The evaluation proceeds iteratively for $t=1,\dots,L$, where $L$ is the length
  of the branching program $\Pi$. Assuming that we have
  $\mathbf V_{t-1}:=(\mathbf V_{t-1,1},\mathbf V_{t-1,2},\dots,\mathbf V_{t-1,5})$, the encryption
  of the state of the branching program computation at time $t-1$, we compute
  $\mathbf V_t:=(\mathbf V_{t,1},\mathbf V_{t,2},\dots,\mathbf V_{t,5})$ by homomorphically
  evaluating Eq. (4) above.

  That is, for $i\in\{1,2,3,4,5\}$, we compute

  $$
  \begin{aligned}
  \mathbf V_{t,i}:=\mathsf{NCCrypt.ProtoAdd}\Bigl(&\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_0},\bar{\mathbf C}_{\mathsf{var}(t)}\bigr),&&(5)\\
  &\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_1},\mathbf C_{\mathsf{var}(t)}\bigr)\Bigr)&&(6)
  \end{aligned}
  $$
- **[Output]** Upon finishing the evaluation stage, we have
  $\mathbf V_L:=(\mathbf V_{L,1},\mathbf V_{L,2},\dots,\mathbf V_{L,5})$. Output $\mathbf V_{L,1}$
  as the result of the homomorphic evaluation.

We now show that the scheme correctly evaluates circuits.

*Transcription note.* In Equations (5)–(6) $\gamma_0,\gamma_1$ abbreviate
$\gamma_{t,i,0},\gamma_{t,i,1}$ of Equation (4).

<a id="pdf-eab2d1667a8e-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->

**Lemma 3.6 (Correctness of Homomorphic Evaluation).** Let $n$ be the LWE dimension, $q$ the LWE
modulus, $\Psi$ be any Boolean circuit of depth $d$, and

$$
\alpha\le1/\tilde\Theta_\kappa(4^d\cdot\sqrt{n\log q})
$$

For every $x_1,\dots,x_\ell\in\{0,1\}$, every Boolean circuit $\Psi$ of depth at most $d$, and
every secret key $sk$, letting $\mathbf C_k\leftarrow\mathsf{NCCrypt.SecEnc}(sk,x_k)$ be the
*secret key* encryptions of the inputs, and
$\mathbf C_\Psi\leftarrow\mathsf{NCCrypt.Eval}(evk,\Psi,\mathbf C_1,\dots,\mathbf C_k)$ be the
evaluated ciphertext, we have:

$$
\mathsf{NCCrypt.Dec}(sk,\mathbf C_\Psi)=\Psi(x_1,\dots,x_\ell)
$$

with overwhelming probability over the coin tosses of all the algorithms. $\mathsf{NCCrypt.Eval}$
runs in time $\mathrm{poly}(4^d,\ell,n,\log q)$.

Note that we stated the correctness of homomorphic evaluation on ciphertexts produced by the
secret-key encryption algorithm $\mathsf{NCCrypt.SecEnc}$. A similar lemma can be shown in the case
of public-key encryption, if $\alpha$ is smaller by a factor of $\sqrt{n\log q}$. However, in our
"optimal FHE" scheme in Section 4, we will only need to invoke this lemma with secret-key
encryption.

*Transcription note.* "$\mathbf C_1,\dots,\mathbf C_k$" in the evaluated ciphertext is as printed
($\mathbf C_1,\dots,\mathbf C_\ell$ is meant).

<a id="pdf-eab2d1667a8e-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->

**Proof of Lemma 3.6 (p. 15).** It is easy to see that each step of the homomorphic evaluation
algorithm, given by Eq. (5), simulates the execution of the branching program, given by Eq. (4).
It remains to bound the noise growth during $\mathsf{NCCrypt.Eval}$. We show this by induction.

In the sequel, we will abbreviate the noise function $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)$ to
$\mathsf{noise}(\mathbf C)$ since the secret key is fixed throughout the evaluation, and the message
$\mu$ is clear from the context.

Clearly, $\mathsf{noise}(\mathbf V_{0,i})=0$, since they $\mathbf V_{0,i}$ are just the messages,
with no noise. Assume, as the inductive hypothesis, that for all $i\in\{1,2,3,4,5\}$,

$$
\mathsf{noise}(\mathbf V_{t-1,i})=(t-1)\cdot\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
$$

We will now bound $\mathsf{noise}(\mathbf V_{t,i})$ for all $i\in\{1,2,3,4,5\}$. Note that

$$
\begin{aligned}
\mathsf{noise}\bigl(\mathbf V_{t,i}\bigr)&\le\mathsf{noise}\Bigl(\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_0},\bar{\mathbf C}_{\mathsf{var}(t)}\bigr)\Bigr)
+\mathsf{noise}\Bigl(\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_1},\mathbf C_{\mathsf{var}(t)}\bigr)\Bigr)\\
&\le|1-x_{\mathsf{var}(t)}|\cdot\mathsf{noise}(\mathbf V_{t-1,\gamma_0})+|x_{\mathsf{var}(t)}|\cdot\mathsf{noise}(\mathbf V_{t-1,\gamma_1})+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
\end{aligned}
$$

where the second inequality holds by Claim 3.4.2 since all the ciphertexts encrypt bits,
$\mathbf C_{\mathsf{var}(t)}$ is a fresh secret-key encryption, and $\bar{\mathbf C}_{\mathsf{var}(t)}$
contains exactly the same noise as $\mathbf C_{\mathsf{var}(t)}$.

Since exactly one of $x_{\mathsf{var}(t)}$ and $1-x_{\mathsf{var}(t)}$ is non-zero, we have

$$
\begin{aligned}
\mathsf{noise}\bigl(\mathbf V_{t,i}\bigr)&\le\max(\mathsf{noise}(\mathbf V_{t-1,\gamma_0}),\mathsf{noise}(\mathbf V_{t-1,\gamma_1}))+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})\\
&\le t\cdot\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
\end{aligned}
$$

by the inductive hypothesis.

Thus, in particular,

$$
\mathsf{noise}(\mathbf V_\Psi)=\mathsf{noise}\bigl(\mathbf V_{L,1}\bigr)\le4^d\cdot\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})<q/8
$$

by our setting of the parameter $\alpha$.

*Transcription note.* The second inequality applies Claim 3.4.2 to the two ProtoMult calls, but
the claim has one additive term per call, so the two calls give two such terms; the printed bound
keeps one $\tilde O$ term, which absorbs the factor 2. In the phase-5 Lean's worst-case form
(fresh ciphertext on the left) the step costs an additive $2N\beta$.

<a id="pdf-eab2d1667a8e-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.90 -->

**Section 3.4, achieving fully homomorphic encryption; Theorem 3.7 (p. 16).** We know by
Lemma 3.4 that the depth of the decryption circuit of $\mathsf{NCCrypt}$ is
$c_{\mathsf{dec}}\cdot\log(n\log q)=c_{\mathsf{dec}}\log N$ for some constant
$c_{\mathsf{dec}}>0$. Setting the depth $d=c\log N$ for some constant $c>c_{\mathsf{dec}}$ in
Lemma 3.6 and $\alpha\le1/\tilde\Theta_\kappa(4^d\cdot\sqrt{n\log q})$ gives us a bootstrappable
encryption scheme. By the bootstrapping theorem (Theorem 2.14), this can be turned into a leveled
FHE scheme, without additional assumptions. We state this theorem below:

**Theorem 3.7.** Let $n$ be the LWE dimension, $q$ be the LWE modulus,
$N:=(n+1)\cdot\lceil\log q\rceil$, and let $c>c_{\mathsf{dec}}$ be a large enough constant (where
$c_{\mathsf{dec}}$ is the decryption depth constant from Proposition 3.4), and

$$
\alpha\le1/\tilde\Theta_\kappa\bigl((n\log q)^{2c+1/2}\bigr)
$$

Then, there is a leveled FHE scheme that is secure under the decisional LWE assumption
$\mathsf{DLWE}_{n,q,\alpha}$.

In the next section, we will use a variant of the dimension-modulus reduction of [BV11], the
effect of which will be to reduce the constant $c$ above to a very small $\epsilon\to0$, thus
achieving a value of $\alpha$ that matches the best known lattice-based PKE schemes.

*Transcription note.* "Lemma 3.4" in the first sentence is as printed (Proposition 3.4 is meant).
Confidence is lowered because the radicals and tildes are flattened in the extraction.

<a id="pdf-eab2d1667a8e-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.95 -->

**Lemma 4.4.** Let $\alpha(n)=1/\tilde O_\kappa(\sqrt{n\log(q)}\cdot n^{\epsilon})$, and let
$q(n)\ge\tilde O(\sqrt n/\alpha(n))$. Consider a set of keys generated by
$(sk,pk,evk)\leftarrow\mathsf{DimReduced.Keygen}(1^k)$, and recall that $sk=(\mathbf s_0,\mathbf s_L)$.
Let $K_i\leftarrow\mathsf{DimReduced.SecEnc}_{sk}(\mathsf{BitDecomp}(\mathbf s_0)[i])$. Namely,
$K_i$ is the symmetric encryption of the $i$th bit of $\mathbf s_0$.

Let $f$ be an augmented decryption circuit as per Definition 2.13. Namely, let
$\mathbf c,\mathbf c'\in\mathbb Z_p^k$ and $\mu,\mu'\in\{0,1\}$ be such that

$$
[\langle\mathbf c,\mathbf s_0\rangle]_p=\mu\cdot\tau p+e,
$$

where $|e|<p/8$, and similarly for $\mathbf c'$. The function $f$ is the function that on input
$x$, treats $x$ as a secret key and decrypts $\mathbf c,\mathbf c'$, and outputs the NAND of their
decryptions.

Let

$$
\mathbf c_0\leftarrow\mathsf{DimReduced.Eval}_{evk}(f,K_1,K_2,\dots),
$$

and note that this is syntactically well defined since $f$ can be represented as a Boolean circuit
of depth $c_{\mathsf{dec}}\cdot\log(k\log(q(k)))+1$.

Then with all but $\mathrm{negl}(\kappa)$ probability,

$$
[\langle\mathbf c_0,\mathbf s_0\rangle]_p=\mu^*\cdot\tau p+e_f,
$$

where $\mu^*=\overline{(\mu\wedge\mu')}$, $|e_f|<p/8$ are as above.

*Transcription note.* The statement is given for the shape of the bootstrapping step (the
evaluation key holds secret-key encryptions $K_i$ of the bits of the secret key; the augmented
decryption circuit has depth $c_{\mathsf{dec}}\cdot\log(\cdot)+1$). $\tau=2^{\lceil\log(q_L)\rceil-2}/q_L$
is defined just before the lemma (p. 18). The radicals and the bar over $(\mu\wedge\mu')$ were
checked against the page image (130 dpi).

<a id="pdf-eab2d1667a8e-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.90 -->

**Section 4.2, Corollary 4.5 and the key-size remark (p. 20).** Finally, we derive the worst-case
lattice approximation factor based on Corollary 2.6. We recall that a bootstrappable homomorphic
encryption scheme implies a leveled FHE scheme under the same assumptions, and a pure FHE scheme
with an additional circular security assumption.

**Corollary 4.5.** For all $\epsilon>0$, there exist:

- A bootstrappable homomorphic encryption scheme based on the worst-case quantum hardness of
  solving $\mathsf{GapSVP}_{\tilde O(n^{1.5+\epsilon})}$ and $\mathsf{SIVP}_{\tilde O(n^{1.5+\epsilon})}$.
- A bootstrappable homomorphic encryption scheme based on the worst-case classical hardness of
  solving $\mathsf{GapSVP}_{\tilde O(n^{2+\epsilon})}$.

The first (quantum) case is derived from Lemma 4.4 by setting $q(n)=\sqrt n/\alpha(n)=\mathrm{poly}(n)$,
and the second (classical) case is derived by setting $q(n)=2^{n/2}$.

*Improving Key and Ciphertext sizes.* The scheme $\mathsf{DimReduced}$ uses a ladder of LWE
instances, ranging from short $(k,p)$ to polynomially larger $(n,q)$. In the description above, the
public key of the scheme is derived from that of $\mathsf{NCCrypt}$, and therefore depends on $n$
and not on $k$. Likewise, the "input ciphertexts" (the ones before homomorphic evaluation) also
depend on $n$.

We note here that this can be fixed in such a way that only the $evk$ depends on $n$, and the rest
of the parameters are exactly the same as Regev's scheme with parameters $(k,p)$. This is done in a
standard way (used e.g. in [BV11]) as follows.

We will generate the public key as a standard Regev public key with parameters $(k,p)$, and in the
evaluation key we will encrypt the bits of the respective secret key using $\mathsf{NCCrypt}$. This
will allow to perform homomorphic operations by evaluating the augmented decryption circuit.
Namely, the ciphertexts visible to the user of the scheme will always be short, but in the process
of homomorphic evaluation, larger ciphertexts are used to accommodate the homomorphic operation,
and once it is done dimension-modulus reduction will be used to shrink the output ciphertext back
to the original size. Since this is standard practice, we omit the technical description.

## ===== blueprint/src/references/brakerski-vaikuntanathan-2011-fhe.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: d3e95f9b9e017ea1133064bed227981ec21e38ee6fc6163eb08585dd238b0c00 -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Efficient Fully Homomorphic Encryption from (Standard) LWE

Zvika Brakerski and Vinod Vaikuntanathan. *FOCS 2011*, pp. 97–106; full version, 39 pages, PDF
created 2 March 2012 (IACR ePrint 2011/344; tag `BV11`). The version facts are from the PDF's
first page ("A preliminary version appeared in Proceedings of the 52nd IEEE Foundations of
Computer Science, 2011") and its creation date; the ePrint number is from BV14's bibliography.

**Scope.** Only the passages that the phase-6 plan uses are transcribed (DW-7; GSW rulings,
addendum): §3.1 (the syntax of homomorphic encryption, Definitions 3.1–3.6), §3.2 (Definition 3.7,
Theorems 3.1–3.2, Definition 3.8 weak circular security, Lemma 3.3), and §4.5 (Lemma 4.5, the
decryption-depth lemma, with its proof; Lemma 4.6; Corollary 4.7). The PDF is not committed.
Anchors use the physical PDF page; the printed page is one less (`p013` is printed page 12). The
scoped raw extraction is `brakerski-vaikuntanathan-2011-fhe.raw.md`. Mathematics is set in LaTeX;
the wording is the paper's. Notes marked *Transcription note* are not part of the source.

**Numbering.** BV14 cites the decryption-depth result as "[BV11, Lemma 4.1]" (BV14,
Proposition 3.4). In this full version it is **Lemma 4.5**; Lemma 4.1 does not occur here (§4
has Theorem 4.1, security). Citations in TCSlib use this version's numbering.

<a id="pdf-d3e95f9b9e01-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

## 3 Homomorphic Encryption: Definitions and Tools

**Section 3 and Section 3.1, opening; key generation (printed p. 11).** In this section we discuss
the definition of homomorphic encryption and its properties as well as some related subjects. We
start by defining homomorphic and fully homomorphic encryption in Section 3.1. Then, in Section 3.2
we discuss Gentry's bootstrapping theorem.

We note that there are a number of ways to define homomorphic encryption and to describe the
bootstrapping theorem. We chose the definitions that best fit the constructions and we urge even
the knowledgeable reader to go over them so as to avoid confusion in interpreting our results.

We now define homomorphic encryption and its desired properties. Throughout this section (and this
work) we use $\kappa$ to indicate the security parameter. In addition, all schemes in this paper
encrypt bit-by-bit and therefore our definitions only refer to this case. The generalization to an
arbitrary message space is immediate.

A homomorphic (public-key) encryption scheme
$\mathsf{HE}=(\mathsf{HE.Keygen},\mathsf{HE.Enc},\mathsf{HE.Dec},\mathsf{HE.Eval})$ is a quadruple
of ppt algorithms as follows.

- **Key generation.** The algorithm $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$ takes a
  unary representation of the security parameter and outputs a public encryption key $pk$, a
  public evaluation key $evk$ and a secret decryption key $sk$.

<a id="pdf-d3e95f9b9e01-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->

**Section 3.1, encryption, decryption, evaluation (printed p. 12).**

- **Encryption.** The algorithm $c\leftarrow\mathsf{HE.Enc}_{pk}(\mu)$ takes the public key $pk$ and
  a single bit message $\mu\in\{0,1\}$ and outputs a ciphertext $c$.
- **Decryption.** The algorithm $\mu^*\leftarrow\mathsf{HE.Dec}_{sk}(c)$ takes the secret key $sk$
  and a ciphertext $c$ and outputs a message $\mu^*\in\{0,1\}$.
- **Homomorphic evaluation.** The algorithm
  $c_f\leftarrow\mathsf{HE.Eval}_{evk}(f,c_1,\dots,c_\ell)$ takes the evaluation key $evk$, a
  function $f:\{0,1\}^\ell\to\{0,1\}$ and a set of $\ell$ ciphertexts $c_1,\dots,c_\ell$, and
  outputs a ciphertext $c_f$.

  The representation of the function $f$ is an important issue. Since the representation can vary
  between schemes, we leave this issue outside of this syntactic definition. We remark, however,
  that in this work, $f$ will be represented by an arithmetic circuit over $GF(2)$.

We note that while one can treat the evaluation key as a part of the public key, as has been done in
the literature so far, we feel that there is an expository value to treating it as a separate
entity and to distinguishing between the public elements that are used for encryption and those
that are used only for homomorphic evaluation.

The only security notion we consider in this chapter is semantic security, namely security w.r.t.
passive adversaries. We use its widely known formulation as IND-CPA security, defined as follows.

<a id="pdf-d3e95f9b9e01-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.95 -->

**Definition 3.1 (CPA security).** A scheme $\mathsf{HE}$ is IND-CPA secure if for any polynomial
time adversary $\mathcal A$ it holds that

$$
\mathrm{Adv}_{\mathrm{CPA}}[\mathcal A]\triangleq\bigl|\Pr[\mathcal A(pk,evk,\mathsf{HE.Enc}_{pk}(0))=1]-\Pr[\mathcal A(pk,evk,\mathsf{HE.Enc}_{pk}(0))=1]\bigr|=\mathrm{negl}(\kappa),
$$

where $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$.

In fact, based on the best known about lattices, the schemes we present in this paper will be secure
against even stronger adversaries. In order for our reductions to make sense for such adversaries as
well, we also consider a parameterized version of CPA security. There, we allow the adversary to run
in time $t$ (which is typically super-polynomial) and succeed with probability $\epsilon$ (which is
typically sub-polynomial).

*Transcription note.* Both probabilities are printed with $\mathsf{HE.Enc}_{pk}(0)$ (checked
against the page image, 110 dpi); the second is meant to be $\mathsf{HE.Enc}_{pk}(1)$. The same
holds in Definition 3.2.

<a id="pdf-d3e95f9b9e01-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.95 -->

**Definition 3.2 ($(t,\epsilon)$-CPA security).** A scheme $\mathsf{HE}$ is $(t,\epsilon)$-IND-CPA
secure if for any adversary $\mathcal A$ that runs in time $t$ for $t=t(\kappa)$ it holds that

$$
\mathrm{Adv}_{\mathrm{CPA}}[\mathcal A]\triangleq\bigl|\Pr[\mathcal A(pk,evk,\mathsf{HE.Enc}_{pk}(0))=1]-\Pr[\mathcal A(pk,evk,\mathsf{HE.Enc}_{pk}(0))=1]\bigr|\le\epsilon=\epsilon(\kappa),
$$

where $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$.

We move on to define the homomorphism property. Note that we do not define the "correctness" of the
scheme as a separate property, but rather (some form of) correctness will follow from our
homomorphism properties.

We start by defining $\mathcal C$-homomorphism, which is homomorphism with respect to a specified
class $\mathcal C$ of functions. This notion is sometimes also referred to as "somewhat
homomorphism".

<a id="pdf-d3e95f9b9e01-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.95 -->

**Definition 3.3 ($\mathcal C$-homomorphism).** Let $\mathcal C=\{\mathcal C_\kappa\}_{\kappa\in\mathbb N}$
be a class of functions (together with their respective representations). A scheme $\mathsf{HE}$ is
$\mathcal C$-homomorphic (or, homomorphic for the class $\mathcal C$) if for any sequence of
functions $f_\kappa\in\mathcal C_\kappa$ and respective inputs $\mu_1,\dots,\mu_\ell\in\{0,1\}$
(where $\ell=\ell(\kappa)$), it holds that

$$
\Pr\left[\mathsf{HE.Dec}_{sk}(\mathsf{HE.Eval}_{evk}(f,c_1,\dots,c_\ell))\neq f(\mu_1,\dots,\mu_\ell)\right]=\mathrm{negl}(\kappa),
$$

where $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$ and $c_i\leftarrow\mathsf{HE.Enc}_{pk}(\mu_i)$.

<a id="pdf-d3e95f9b9e01-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->

**Section 3.1, remarks; Definitions 3.4–3.6 (printed p. 13).** We point out two important
properties that the above definition *does not* require. First of all, we do not require that the
ciphertexts $c_i$ are decryptable themselves, only that they become decryptable after homomorphic
evaluation.¹⁷ Secondly, we do not require that the output of $\mathsf{HE.Eval}$ can undergo
additional homomorphic evaluation.¹⁸

Before we define full homomorphism, let us define the notion of *compactness*.

**Definition 3.4 (compactness).** A homomorphic scheme $\mathsf{HE}$ is compact if there exists a
polynomial $s=s(\kappa)$ such that the output length of $\mathsf{HE.Eval}(\cdots)$ is at most $s$
bits long (regardless of $f$ or the number of inputs).

Note that a $\mathcal C$-homomorphic scheme is not necessarily compact.

We give the minimal definition of fully homomorphic encryption, which suffices for most
applications.

**Definition 3.5 (fully homomorphic encryption).** A scheme $\mathsf{HE}$ is fully homomorphic if it
is both compact and homomorphic for the class of all arithmetic circuits over $GF(2)$.

As in the definition of $\mathcal C$ homomorphism, one can require that the outputs of
$\mathsf{HE.Eval}$ can again be used as inputs for homomorphic evaluation ("multi-hop
homomorphism"). Indeed, all known schemes have this additional property. However, due to the
complexity of the formal definition in this case, we refrain from describing a formal definition.

An important relaxation of fully homomorphic encryption is the following.

**Definition 3.6 (leveled fully homomorphic encryption).** A leveled fully homomorphic encryption
scheme is a homomorphic scheme where the $\mathsf{HE.Keygen}$ gets an additional input $1^L$ (now
$(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa,1^L)$) and the resulting scheme is homomorphic
for all depth-$L$ binary arithmetic circuits. The bound $s(\kappa)$ on the ciphertext length must
remain independent of $L$.

In most cases, the only parameter of the scheme that becomes dependent on $L$ is the bit-length of
the evaluation key $evk$.

Footnote 17: Jumping ahead, while this may seem strange at first, this notion of somewhat
homomorphism is all that is really required in order to bootstrap into full homomorphism and it
also makes our schemes easier to describe. Lastly, note that one can always perform a "blank"
homomorphic operation and then decrypt, so functionality is not hurt. Footnote 18: This is termed
"1-hop homomorphism" in [GHV10a].

<a id="pdf-d3e95f9b9e01-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->

**Section 3.2, Gentry's bootstrapping technique; Definition 3.7 (printed p. 13).** In this section
we formally define the notion of a bootstrappable encryption scheme and present Gentry's
bootstrapping theorem [Gen09b, Gen09a] which implies that a bootstrappable scheme can be converted
into a fully homomorphic one.

**Definition 3.7 (bootstrappable encryption scheme).** Let $\mathsf{HE}$ be
$\mathcal C$-homomorphic, and Let $f_{\mathsf{add}}$ and $f_{\mathsf{mult}}$ be the the augmented
decryption functions of the scheme defined as

$$
f^{c_1,c_2}_{\mathsf{add}}(s)=\mathsf{HE.Dec}_s(c_1)\ \mathit{XOR}\ \mathsf{HE.Dec}_s(c_2)
\qquad\text{and}\qquad
f^{c_1,c_2}_{\mathsf{mult}}(s)=\mathsf{HE.Dec}_s(c_1)\ \mathit{AND}\ \mathsf{HE.Dec}_s(c_2).
$$

Then $\mathcal E$ is bootstrappable if

$$
\bigl\{f^{c_1,c_2}_{\mathsf{add}},f^{c_1,c_2}_{\mathsf{mult}}\bigr\}_{c_1,c_2}\subseteq\mathcal C.
$$

Namely, the scheme can homomorphically evaluate $f_{\mathsf{add}}$ and $f_{\mathsf{mult}}$.

*Transcription note.* BV11 bootstraps with the XOR/AND pair; BV14 (Definition 2.13) uses NAND.
"$\mathcal E$" in "Then $\mathcal E$ is bootstrappable" is as printed ($\mathsf{HE}$ is meant).

<a id="pdf-d3e95f9b9e01-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->

**Section 3.2, Theorems 3.1–3.2, Definition 3.8, Lemma 3.3 (printed p. 14).** We describe two
variants of Gentry's bootstrapping theorem. The first implies leveled fully homomorphic encryption
but requires no additional assumption; where the second makes an additional (weak) circular
security assumption and achieves the stronger (non-leveled) variant of Definition 3.5.

The first variant follows.

**Theorem 3.1 ([Gen09b, Gen09a]).** Let $\mathsf{HE}$ be a bootstrappable scheme, then there exists a
leveled fully homomorphic encryption scheme as per Definition 3.6.

Specifically, the leveled homomorphic scheme is such that only the length of the evaluation key
depends on the level $L$. All other parameters of the scheme are distributed identically regardless
of the value of $L$.

For the second variant, we need to define circular security.

**Definition 3.8 (weak circular security).** A public key encryption scheme
$(\mathsf{Gen},\mathsf{Enc},\mathsf{Dec})$ is weakly circular secure if it is IND-CPA secure even for
an adversary with auxiliary information containing encryptions of all secret key bits:
$\{\mathsf{Enc}_{pk}(sk[i])\}_i$.

Namely, no polynomial time adversary can distinguish an encryption of $0$ from an encryption of $1$
even given the additional information.

We can now state the second theorem.

**Theorem 3.2 ([Gen09b, Gen09a]).** Let $\mathsf{HE}$ be a bootstrappable scheme that is also weakly
circular secure. Then there is a fully homomorphic encryption scheme as per Definition 3.5.

Finally, we want to make a statement regarding the ciphertext length of a bootstrapped scheme. The
following is implicit in [Gen09b, Gen09a].

**Lemma 3.3.** If a scheme $\mathsf{FH}$ is obtained from applying either Theorem 3.1 or Theorem 3.2
to a bootstrappable scheme $\mathsf{HE}$, then both $\mathsf{FH.Enc}$ and $\mathsf{FH.Eval}$ produce
ciphertexts of the same length as $\mathsf{HE.Eval}$ (regardless of the length of the ciphertext
produced by $\mathsf{HE.Enc}$).

<a id="pdf-d3e95f9b9e01-p029-b001"></a>
<!-- pdf-source: page=29; block=1; confidence=0.95 -->

**Section 4.5, bootstrapping and full homomorphism; Lemma 4.5 (printed p. 28).** We now show how to
apply Gentry's bootstrapping theorem (Theorems 3.1, 3.2) to achieve full homomorphism. In order to
do this, we first need to bound the complexity of an augmented decryption circuit. Since our
decryption is essentially a computation of inner product, we bound the complexity of this operation.

**Lemma 4.5.** Let $(\hat{\mathbf v},\hat w)\in\mathbb Z_p^k\times\mathbb Z_p$. There exists an
arithmetic circuit with fan-in 2 gates and $O(\log k+\log\log p)$ depth, that on input
$\hat{\mathbf s}\in\mathbb Z_p^k$ (in binary representation) computes

$$
(\hat w-\langle\hat{\mathbf v},\hat{\mathbf s}\rangle\pmod p)\pmod 2.
$$

<a id="pdf-d3e95f9b9e01-p029-b002"></a>
<!-- pdf-source: page=29; block=2; confidence=0.95 -->

**Proof of Lemma 4.5 (printed p. 28).** We let $\hat{\mathbf s}[i]^{(j)}$ denote the $j$th bit of the
binary representation of $\hat{\mathbf s}[i]\in\mathbb Z_p$. We notice that

$$
\begin{aligned}
\hat w-\langle\hat{\mathbf v},\hat{\mathbf s}\rangle
&=\hat w-\sum_{i=1}^{k}\hat{\mathbf s}[i]\hat{\mathbf v}[i]\pmod p\\
&=\hat w-\sum_{i=1}^{k}\sum_{j=0}^{\lfloor\log p\rfloor}\hat{\mathbf s}[i]^{(j)}\cdot(2^j\cdot\hat{\mathbf v}[i])\pmod p.
\end{aligned}
$$

Therefore computing $\hat w-\langle\hat{\mathbf v},\hat{\mathbf s}\rangle\pmod p$ is equivalent to
summing up $k(1+\lfloor\log p\rfloor)+1$ numbers in $\mathbb Z_p$, and then taking the result modulo
$p$. The summation (over the integers) can be done in depth $O(\log k+\log\log p)$. In order to take
modulo $p$, one needs to subtract, in parallel, all possible multiples of $p$ (there are at most
$O(k\log p)$ options) and check if the result is in $\mathbb Z_p$. This requires depth
$O(\log k+\log\log p)$ again. Then a selection tree of depth $O(\log k+\log\log p)$ is used to
choose the correct result. Once this is done, outputting the least significant bit implements the
final modulo 2 operation.

The total depth is thus $O(\log k+\log\log p)$ as required.

<a id="pdf-d3e95f9b9e01-p029-b003"></a>
<!-- pdf-source: page=29; block=3; confidence=0.95 -->

**Lemma 4.6 and Corollary 4.7 (printed p. 28).** We can now apply the bootstrapping theorem to obtain
a fully homomorphic scheme.

**Lemma 4.6.** There exists $C\in\mathbb N$ such that setting $n=k^{C/\epsilon}$ and the rest of the
parameters as in Theorem 4.2, BTS is bootstrappable as per Definition 3.7.

**Proof.** Lemma 4.5 guarantees that the decryption circuit is in $\mathrm{Arith}[O(\log k),1]$ (note
that $\log\log p=o(\log k)$), since the augmented decryption circuit just adds 1 to the depth, it
follows that the augmented decryption circuits are also in $\mathrm{Arith}[O(\log k),1]$.

Theorem 4.2, on the other hand, guarantees homomorphism for any
$\mathrm{Arith}[\Omega(\epsilon\log n),\sqrt q]$ function. Taking a large enough $C$, it will hold
that $\mathrm{Arith}[O(\log k),1]\subseteq\mathrm{Arith}[\Omega(\epsilon\log n),\sqrt q]$ and the
lemma follows.

Finally, we conclude that there exists an LWE based fully homomorphic encryption based on
Theorem 4.1 and Lemma 4.6.

**Corollary 4.7.** There exists a leveled fully homomorphic encryption based on the
$\mathsf{DLWE}_{n,q,\chi}$ and $\mathsf{DLWE}_{k,p,\hat\chi}$ assumptions.

Furthermore, if BTS is weakly circular secure (see Definition 3.8), then there exists a fully
homomorphic encryption based on the same assumptions.

*Transcription note.* In Lemma 4.6 and its proof the extraction drops the $\epsilon$ glyphs and the
radical; they were checked against the page image (130 dpi): $n=k^{C/\epsilon}$,
$\mathrm{Arith}[\Omega(\epsilon\log n),\sqrt q]$. Lemma 4.5's decryption
outputs the least significant bit of $\hat w-\langle\hat{\mathbf v},\hat{\mathbf s}\rangle\bmod p$
(BV11's BTS scheme encrypts in the low-order bit), unlike GSW's rounding to the nearer of $0$ and
$\lfloor q/2\rfloor$; the depth argument (iterated addition, then reduction modulo $p$ by parallel
subtraction and a selection tree) is the part the phase-6 plan uses.

## ===== blueprint/src/references/alperin-sheriff-peikert-2014-bootstrapping.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: cecd346d2e879ff865c23fe977e172e1068f20b01c7f555a419d2f3d5ec2c0da -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Faster Bootstrapping with Polynomial Error

Jacob Alperin-Sheriff and Chris Peikert. *CRYPTO 2014*, LNCS 8616, pp. 297–314; IACR ePrint
2014/094, version dated June 13, 2014 (18 pages; tag `AP14`).

**Scope.** Only the passages that the GSW Lean (phase 5) and the phase-6 plan use are
transcribed (DW-7; GSW ruling Q14): §2.2 (symmetric groups and permutation matrices), §3
(the GSW variant: Claim 3.1, Equation (3.1), the scheme, Definitions 3.2–3.3, Claim 3.4,
Lemma 3.5, Corollary 3.6), §4.1–§4.2 (HEPerm, Equation (4.1), Lemma 4.1, Corollary 4.2), and
from §5 the specification, the procedures, Theorem 5.1, the security paragraph and Lemma 5.2
(the phase-6 cross-check). The PDF is not committed. Anchors use the physical PDF page; the
printed page is one less (`p008` is printed page 7). The scoped raw extraction is
`alperin-sheriff-peikert-2014-bootstrapping.raw.md`. Mathematics is set in LaTeX; the
paper's operators are written $\boxplus$ (homomorphic addition), $\boxdot$ (homomorphic
multiplication) and ⧇ (homomorphic composition, printed as a boxed small circle). The wording
is the paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-cecd346d2e87-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Section 2.2, symmetric groups and $\mathbb Z_q$-embeddings (printed p. 6).** Here we recall
some basic facts about symmetric groups, which can be found in most abstract algebra textbooks,
e.g., [Jac12]. Let $S_r$ denote the symmetric group of order $r$, i.e., the group of
permutations (bijections) $\pi:\{1,\dots,r\}\to\{1,\dots,r\}$ with function composition as the
group operation. The group $S_r$ is isomorphic to the multiplicative group of $r$-by-$r$
permutation matrices (i.e., 0-1 matrices with exactly one nonzero element in each row and each
column), via the map that associates $\pi\in S_r$ with the permutation matrix
$\mathbf P_\pi=[\mathbf e_{\pi(1)}\ \mathbf e_{\pi(2)}\ \cdots\ \mathbf e_{\pi(r)}]$, where
$\mathbf e_i\in\{0,1\}^r$ is the $i$th standard basis vector. For the remainder of this work we
identify permutations with their associated permutation matrices.

The additive cyclic group $(\mathbb Z_r,+)$ embeds into the symmetric group $S_r$ via the
injective homomorphism that sends the generator $1\in\mathbb Z_r$ to the "cyclic shift"
permutation $\pi\in S_r$, defined as $\pi(i)=i+1$ for $1\le i<r$ and $\pi(r)=1$.³ Clearly, this
embedding and its inverse can be computed efficiently. Notice also that the permutation matrices
in the image of this embedding can be represented more compactly by just their first column,
because the remaining columns are just the successive cyclic shifts of this column. Similarly,
such permutation matrices can be multiplied in only $O(r^2)$ operations, since we only need to
multiply one matrix by the first column of the other.

For our efficient bootstrapping algorithm, we need to efficiently embed a group
$(\mathbb Z_q,+)$, for some sufficiently large $q$ of our choice, into a symmetric group of order
much smaller than $q$ (e.g., polylogarithmic in $q$). This can be done as follows: suppose that
$q=r_1r_2\cdots r_t$, where the $r_i$ are pairwise coprime. Then by the Chinese Remainder
Theorem, the ring $\mathbb Z_q$ is isomorphic to the direct product of rings
$\mathbb Z_{r_1}\times\mathbb Z_{r_2}\times\cdots\times\mathbb Z_{r_t}$, and hence their additive
groups are isomorphic as well. Combining this with the group embeddings of $(\mathbb Z_{r_i},+)$
into $S_{r_i}$, we have an (efficient) group embedding from $(\mathbb Z_q,+)$ into
$S_{r_1}\times S_{r_2}\times\cdots\times S_{r_t}$.⁴

Importantly for our purposes, $q$ can be exponentially large in terms of $\max_i r_i$ above.
This can be shown using lower bounds on the second Chebyshev function

$$
\psi(x):=\sum_{p^k\le x}\log p=\log\Bigl(\prod_{p\le x}p^{\lfloor\log_p x\rfloor}\Bigr),
$$

where the first summation is over all prime powers $p^k\le x$, and the second is over all
primes $p\le x$; note that $p^{\lfloor\log_p x\rfloor}$ is the largest power of $p$ not exceeding
$x$. Therefore, the product $q$ of all maximal prime powers $r_i=p^{\lfloor\log_p x\rfloor}\le x$
is $\exp(\psi(x))$. Asymptotically, it is known that $\psi(x)=x\pm O(x/\log x)$, and we also have
the nonasymptotic bound $\psi(x)\ge 3x/4$ for all $x\ge 7$ [Sch76, Theorem 11]. In summary:

**Lemma 2.2.** For all $x\ge 7$, the product of all maximal prime powers $r_i\le x$ is at least
$\exp(3x/4)$.

For any given lower bound $q_0\ge 191>\exp(21/4)$, we can therefore efficiently find a
$q\ge q_0$ whose maximal prime-power divisors are all at most $x=\frac43\log q_0\ge 7$.

Footnote 3: This is just a special case of Cayley's theorem, which says that any group $G$
embeds into the symmetric group $S_{|G|}$. Footnote 4: The latter group can be seen as a
subgroup of $S_r$ for $r=\sum_i r_i$, but it will be more efficient to retain the product
structure.

<a id="pdf-cecd346d2e87-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->

## 3 GSW Cryptosystem

**Section 3, opening (printed p. 6).** Here we present a variant of the Gentry-Sahai-Waters
homomorphic encryption scheme [GSW13] (hereafter called GSW), which we believe is simpler to
understand at a technical level. We also give a tighter analysis of its error growth under
homomorphic operations.

<a id="pdf-cecd346d2e87-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Section 3.1, background; Claim 3.1 and Equation (3.1) (printed p. 7).** We first recall some
standard background (see, e.g., [MP12] for further details). For a modulus $q$, let
$\ell=\lceil\log_2 q\rceil$ and define the "gadget" (column) vector
$\mathbf g=(1,2,4,\dots,2^{\ell-1})\in\mathbb Z_q^{\ell}$. Note that the penultimate entry
$2^{\ell-2}$ of $\mathbf g$ is in the interval $[q/4,q/2)$ mod $q$. It will be convenient to use
the following randomized "decomposition" function.

**Claim 3.1 (Adapted from [MP12]).** There is a randomized, efficiently computable function
$\mathbf g^{-1}:\mathbb Z_q\to\mathbb Z^{\ell}$ such that $\mathbf x\leftarrow\mathbf g^{-1}(a)$
is subgaussian with parameter $O(1)$, and always satisfies $\langle\mathbf g,\mathbf x\rangle=a$.

Briefly, the algorithm described in the claim works as follows (though for our application it is
not necessary to understand its internals): let $\mathbf S\in\mathbb Z^{\ell\times\ell}$ be the
basis of the lattice
$\Lambda^\perp(\mathbf g^t)=\{\mathbf z\in\mathbb Z^\ell:\langle\mathbf g,\mathbf z\rangle=0\in\mathbb Z_q\}$
as constructed in [MP12], whose Gram-Schmidt vectors all have Euclidean norm $O(1)$. Given
$a\in\mathbb Z_q$, run a randomized version of the nearest-plane algorithm [Bab85] with basis
$\mathbf S$ to sample from the coset
$\Lambda^\perp_a(\mathbf g^t)=\{\mathbf x:\langle\mathbf g,\mathbf x\rangle=a\}$, where in each
iteration of the algorithm we choose the coefficient of the $i$th basis vector to have
expectation zero over $\{c_i-1,c_i\}$ for an appropriate $c_i\in\frac1q\mathbb Z\cap[0,1)$. In
particular, the coefficient is subgaussian with parameter $\sqrt{2\pi}$ given any fixed values
of the previous coefficients. The final output $\mathbf x$ is the linear combination of the
(orthogonal) Gram-Schmidt vectors of $\mathbf S$ with these coefficients, and is therefore
subgaussian with parameter $O(1)$.

For vectors and matrices over $\mathbb Z_q$, define the randomized function
$\mathbf G^{-1}:\mathbb Z_q^{n\times m}\to\mathbb Z^{n\ell\times m}$ by applying
$\mathbf g^{-1}$ independently to each entry. Notice that for any
$\mathbf A\in\mathbb Z_q^{n\times m}$, if $\mathbf X\leftarrow\mathbf G^{-1}(\mathbf A)$ then
$\mathbf X$ has subgaussian parameter $O(1)$ and

$$
\mathbf G\cdot\mathbf X=\mathbf A,\qquad\text{where }\mathbf G=\mathbf g^t\otimes\mathbf I_n
=\mathrm{diag}(\mathbf g^t,\dots,\mathbf g^t)\in\mathbb Z_q^{n\times n\ell}\tag{3.1}
$$

is the block matrix with $n$ copies of $\mathbf g^t$ as diagonal blocks, and zeros elsewhere.

*Transcription note.* Under the standard Kronecker convention $\mathbf g^t\otimes\mathbf I_n$
and $\mathrm{diag}(\mathbf g^t,\dots,\mathbf g^t)=\mathbf I_n\otimes\mathbf g^t$ differ by a
column permutation; the printed text gives both (Gate 41 audit, roadmap section). The Lean
follows the block-diagonal description.

<a id="pdf-cecd346d2e87-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Section 3.2, cryptosystem and homomorphic operations: parameters and the two differences
(printed pp. 7–8).** The GSW scheme is parameterized by a dimension $n$, a modulus $q$ with
$\ell=\lceil\log_2 q\rceil$, and some error distribution $\chi$ over $\mathbb Z$ which we assume
to be subgaussian. Formally, the message space is the ring of integers $\mathbb Z$, though for
bootstrapping we only work with ciphertexts encrypting messages in
$\{0,1\}\subset\mathbb Z$. The ciphertext space is
$\mathcal C=\mathbb Z_q^{n\times n\ell}$. For simplicity we present just a symmetric-key scheme,
which is sufficient for our purposes (it can be converted to a public-key or even
attribute-based scheme, as described in [GSW13]).

Our GSW variant differs from the original scheme described in [GSW13] in two main ways:

1. In [GSW13], a ciphertext is a square binary matrix $\mathbf C\in\{0,1\}^{n\ell}$, a secret key
   is a "structured" mod-$q$ vector $\mathbf s\in\mathbb Z_q^{n\ell}$ (having large entries), and
   $\mathbf s$ is an "approximate mod-$q$ eigenvector" of $\mathbf C$, in the sense that
   $\mathbf s^t\mathbf C\approx\mu\mathbf s^t\pmod q$, where $\mu\in\mathbb Z$ is the message.

   In our variant, a ciphertext is a rectangular mod-$q$ matrix
   $\mathbf C\in\mathbb Z_q^{n\times n\ell}$, a secret key is some (unstructured, short) integer
   vector $\mathbf s\in\mathbb Z^n$, and
   $\mathbf s^t\mathbf C\approx\mu\cdot\mathbf s^t\mathbf G\pmod q$, i.e., $\mathbf s$ and
   $\mathbf G^t\mathbf s$ are corresponding left- and right- "approximate singular vectors" of
   $\mathbf C$.

   The difference between these two variants turns out to be purely syntactic, in that we can
   efficiently and "losslessly" switch between them (without needing the secret key). However,
   we believe that our variant leads to simpler notation and easier-to-understand operations and
   analysis.
2. The second difference is more substantial: our homomorphic multiplication procedure uses the
   *randomized* $\mathbf G^{-1}(\cdot)$ operation from Claim 3.1. This yields a few important
   advantages, such as a very tight and simple error analysis using subgaussianity (see
   Lemma 3.5), and the ability to *completely re-randomize* the error in a ciphertext (see
   Corollary 3.6).

*Transcription note.* "$\{0,1\}^{n\ell}$" for the square matrix is as printed (an
$n\ell\times n\ell$ matrix is meant).

<a id="pdf-cecd346d2e87-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 3.2, the scheme (printed p. 8).** We now describe the scheme formally.

- $\mathsf{GSW.Gen}()$: choose $\bar{\mathbf s}\leftarrow\chi^{n-1}$ and output secret key
  $\mathbf s=(\bar{\mathbf s},1)\in\mathbb Z^n$.
- $\mathsf{GSW.Enc}((\bar{\mathbf s},1),\mu\in\mathbb Z)$: choose
  $\bar{\mathbf C}\leftarrow\mathbb Z_q^{(n-1)\times n\ell}$ and $\mathbf e\leftarrow\chi^m$, let
  $\mathbf b^t=\mathbf e^t-\bar{\mathbf s}^t\bar{\mathbf C}\pmod q$, and output the ciphertext

  $$
  \mathbf C=\begin{pmatrix}\bar{\mathbf C}\\ \mathbf b^t\end{pmatrix}+\mu\mathbf G\in\mathcal C,
  $$

  where $\mathbf G$ is as defined in Equation (3.1). Notice that
  $\mathbf s^t\mathbf C=\mathbf e^t+\mu\cdot\mathbf s^t\mathbf G\pmod q$.
- $\mathsf{GSW.Dec}(\mathbf s,\mathbf C\in\mathcal C)$: let $\mathbf c$ be the penultimate
  column of $\mathbf C$, and output $\mu=\lfloor\langle\mathbf s,\mathbf c\rangle\rceil_2$, where
  $\lfloor\cdot\rceil_2:\mathbb Z_q\to\{0,1\}$ indicates whether its argument is closer modulo $q$
  to $0$ or to $2^{\ell-2}$ (the penultimate entry of $\mathbf g$).⁵
- **Homomorphic addition** is defined as $\mathbf C_1\boxplus\mathbf C_2=\mathbf C_1+\mathbf C_2$.
- **Homomorphic multiplication** is defined as
  $\mathbf C_1\boxdot\mathbf C_2\leftarrow\mathbf C_1\cdot\mathbf G^{-1}(\mathbf C_2)$, and is
  *right associative*. Notice that this is a randomized procedure, because $\mathbf G^{-1}$ is
  randomized.

The IND-CPA security of the scheme follows immediately from the assumed hardness of
$\mathsf{LWE}_{n-1,q,\chi}$, where the entries of the secret are drawn from the error
distribution $\chi$ (which is no easier than for a uniformly random secret; see [ACPS09,
Lemma 2]). This is because a fresh ciphertext is just $\mu\mathbf G$ plus a matrix of $n\ell$
independent LWE samples under secret $\bar{\mathbf s}$, which are pseudorandom by assumption and
hence hide $\mu\mathbf G$.

Footnote 5: Note that we can decrypt messages in $\mathbb Z\cap[-\frac q2,\frac q2)$, or any
other canonical set of representatives of $\mathbb Z_q$, by "decoding" $\mathbf s^t\mathbf C$ to
the nearest multiple of $\mathbf s^t\mathbf G$. The above decryption algorithm will be
sufficient for our purposes.

*Transcription note.* "$\mathbf e\leftarrow\chi^m$" is as printed; with $n\ell$ columns,
$m=n\ell$ is meant.

<a id="pdf-cecd346d2e87-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Definition 3.2.** We say that a ciphertext $\mathbf C$ is *designed* to encrypt message
$\mu\in\mathbb Z$ (under a secret key $\mathbf s$) if it is a fresh encryption of $\mu$, or if
$\mathbf C=\mathbf C_1\boxplus\mathbf C_2$ where $\mathbf C_1,\mathbf C_2$ are respectively
designed to encrypt $\mu_1,\mu_2\in\mathbb Z$ and $\mu=\mu_1+\mu_2$, or similarly for homomorphic
multiplication.

<a id="pdf-cecd346d2e87-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.95 -->

**Definition 3.3.** We say that a ciphertext $\mathbf C$ that is designed to encrypt
$\mu\in\mathbb Z$ (under $\mathbf s$) has *error* vector $\mathbf e^t\in\mathbb Z^{n\ell}$ if
$\mathbf s^t\mathbf C-\mu\cdot\mathbf s^t\mathbf G=\mathbf e^t\pmod q$.

For convenience later on, we also say the matrix $\mu\mathbf G$ is designed to encrypt $\mu$, and
has error $\mathbf 0$. (This is essentially implied by the above definitions, since $\mu\mathbf G$
is indeed a fresh encryption of $\mu$, assuming that zero is in the support of $\chi$.) The next
claim on the correctness of decryption follows immediately from the fact that
$\mathbf s=(\bar{\mathbf s},1)$ and the penultimate column of $\mathbf G$ is
$(0,\dots,0,2^{\ell-2})$, where $2^{\ell-2}\in[q/4,q/2)\bmod q$.

<a id="pdf-cecd346d2e87-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.95 -->

**Claim 3.4.** If $\mathbf C$ is designed to encrypt some $\mu\in\{0,1\}\subset\mathbb Z$, and has
error vector $\mathbf e^t$ whose penultimate coordinate has magnitude less than $q/8$, then
$\mathsf{GSW.Dec}(\mathbf s,\mathbf C)$ correctly outputs $\mu$.

We now analyze the behavior of the error terms under homomorphic operations.

<a id="pdf-cecd346d2e87-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Lemma 3.5.** Suppose $\mathbf C_1,\mathbf C_2$ are respectively designed to encrypt
$\mu_1,\mu_2\in\mathbb Z$ and have error vectors $\mathbf e_1^t,\mathbf e_2^t$. Then
$\mathbf C_1\boxplus\mathbf C_2$ has error vector $\mathbf e_1^t+\mathbf e_2^t$, and
$\mathbf C_1\boxdot\mathbf C_2$ has error vector $\mathbf e_1^t\mathbf X+\mu_1\mathbf e_2^t$,
where $\mathbf X\leftarrow\mathbf G^{-1}(\mathbf C_2)$ is the matrix used in the evaluation of
$\boxdot$. In particular, for any values of $\mathbf C_i,\mathbf e_i,\mu_i$, the latter error
vector is of the form $\mathbf e^t+\mu_1\mathbf e_2^t$, where the entries of $\mathbf e$ are
independent and subgaussian with parameter $O(\|\mathbf e_1\|)$.

Importantly, the error in $\mathbf C_1\boxdot\mathbf C_2$ is quasi-additive and asymmetric with
respect to the errors in $\mathbf C_1,\mathbf C_2$: while the first error vector
$\mathbf e_1^t$ is multiplied by a short (subgaussian) matrix $\mathbf X$, the second error
vector $\mathbf e_2^t$ is only multiplied by the (scalar) message $\mu_1$, which we will ensure
remains in $\{0,1\}$.

<a id="pdf-cecd346d2e87-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->

**Proof of Lemma 3.5.** The first claim is immediate, by linearity. For the second claim, because
$\mathbf G\cdot\mathbf X=\mathbf C_2$ we have

$$
\begin{aligned}
\mathbf s^t(\mathbf C_1\boxdot\mathbf C_2)&=\mathbf s^t\mathbf C_1\cdot\mathbf X\\
&=(\mathbf e_1^t+\mu_1\cdot\mathbf s^t\mathbf G)\mathbf X\\
&=\mathbf e_1^t\mathbf X+\mu_1(\mathbf e_2^t+\mu_2\cdot\mathbf s^t\mathbf G)\\
&=(\mathbf e_1^t\mathbf X+\mu_1\mathbf e_2^t)+\mu_1\mu_2\cdot\mathbf s^t\mathbf G.
\end{aligned}
$$

<a id="pdf-cecd346d2e87-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.95 -->

**Section 3.3, chains (printed p. 9).** As observed in [BV14], the asymmetric noise growth
allows for performing a long chain of homomorphic multiplications while only incurring a
polynomial-factor error growth, because $\boxdot$ is defined to be right associative. For
convenience of analysis, in such a chain we always include the fixed ciphertext $\mathbf G$,
which is designed to encrypt $\mu=1$ and has zero error, as the rightmost ciphertext in the
chain. This ensures that the error vector of the output ciphertext is subgaussian and essentially
independent of the errors in the input ciphertexts (apart from their lengths), which leads to a
simpler and tighter analysis. (In [BV14] a weaker independence guarantee was achieved by a
separate "partial re-randomization" procedure, which requires additional public key material.)

**Corollary 3.6.** Suppose that $\mathbf C_i$ for $i\in[k]$ are respectively designed to
encrypt $\mu_i\in\{0,\pm1\}$ and have error vectors $\mathbf e_i^t$. Then for any fixed values of
these variables,

$$
\mathbf C\leftarrow\mathop{\boxdot}_{i\in[k]}\mathbf C_i\boxdot\mathbf G
=\mathbf C_1\boxdot(\mathbf C_2\boxdot(\cdots(\mathbf C_k\boxdot\mathbf G)\cdots))
$$

has an error vector whose entries are mutually independent and subgaussian with parameter
$O(\|\mathbf e\|)$, where $\mathbf e^t=(\mathbf e_1^t,\dots,\mathbf e_k^t)\in\mathbb Z^{kn\ell}$
is the concatenation of the individual error vectors.

**Proof.** By Lemma 3.5, the error vector in $\mathbf C$ is $\sum_i\mathbf e_i^t\mathbf X_i$,
where each $\mathbf e_i^t\mathbf X_i$ is a fresh independent vector that has mutually
independent coordinates and is subgaussian with parameter $O(\|\mathbf e_i\|)$. The claim then
follows by Pythagorean additivity.

<a id="pdf-cecd346d2e87-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->

## 4 Homomomorphic Encryption for Symmetric Groups

**Section 4, opening (printed p. 9).** Brakerski and Vaikuntanathan [BV14] showed how to use the
GSW encryption scheme to homomorphically compose permutations of five elements (i.e., to
homomorphically compute the group operation in the symmetric group $S_5$) with small additive
noise growth; the use of $S_5$ comes from its essential role in Barrington's theorem [Bar86]. In
[BV14], the homomorphic composition of permutations is intertwined with the evaluation of a
branching program given by Barrington's theorem. Here we give, as a "first-class object," a
homomorphic cryptosystem for any symmetric group $S_r$. The ability to use several different
small values of $r$, along with a homomorphic equality test that we design, will be central to
our bootstrapping algorithm.

*Transcription note.* The section title is printed "Homomomorphic" (sic).

<a id="pdf-cecd346d2e87-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->

**Section 4.1, HEPerm: encryption, composition (Equation (4.1)) and equality test (printed
p. 10).** We now describe our (symmetric-key) homomorphic encryption scheme for symmetric groups,
called HEPerm. Let $\mathcal C$ denote the ciphertext space for an appropriate instantiation of
the GSW scheme, which we treat as a "black box." A secret key $sk$ for HEPerm is simply a secret
key for the GSW scheme.

- $\mathsf{HEPerm.Enc}(sk,\pi\in S_r)$: let
  $\mathbf P=(p_{i,j})\in\{0,1\}^{r\times r}$ be the permutation matrix associated with $\pi$.
  Output an entry-wise encryption of $\mathbf P$, i.e., the ciphertext

  $$
  \mathbf C=(c_{i,j})\in\mathcal C^{r\times r},\quad\text{where }c_{i,j}\leftarrow\mathsf{Enc}(sk,p_{i,j}).
  $$

(Decryption follows in the obvious manner.) As with the GSW system, we say that a ciphertext
$\mathbf C\in\mathcal C^{r\times r}$ is *designed* to encrypt a permutation $\pi\in S_r$ (or its
permutation matrix $\mathbf P_\pi$) if its $\mathcal C$-entries are designed to encrypt the
corresponding entries of $\mathbf P_\pi$. For convenience, we let
$\mathbf J\in\mathcal C^{r\times r}$ denote the ciphertext that encrypts the identity permutation
with zero noise, which is built in the expected way from the fixed zero-error GSW ciphertexts
that encrypt $0$ and $1$.

We now show how to homomorphically compute two operations: the standard composition operation
for permutations, and an equality test.

**Homomorphic composition $\mathbf C^\pi$ ⧇ $\mathbf C^\sigma$:** on ciphertexts
$\mathbf C^\pi=(c^\pi_{i,j}),\mathbf C^\sigma=(c^\sigma_{i,j})\in\mathcal C^{r\times r}$
encrypting permutations $\pi,\sigma\in S_r$ respectively, we compute one encrypting the
permutation $\pi\circ\sigma$ by homomorphically evaluating the naïve matrix-multiplication
algorithm.⁶ That is, output $\mathbf C=(c_{i,j})\in\mathcal C^{r\times r}$ where

$$
c_{i,j}\leftarrow\mathop{\boxplus}_{\ell\in[r]}\bigl(c^\pi_{i,\ell}\boxdot c^\sigma_{\ell,j}\bigr)\in\mathcal C.\tag{4.1}
$$

Just like $\boxdot$, we define ⧇ to be right associative.

**Homomorphic equality test $\mathsf{Eq?}(\mathbf C^\pi=(c^\pi_{i,j}),\sigma\in S_r)$:** given a
ciphertext encrypting some permutation $\pi\in S_r$ and a permutation $\sigma\in S_r$ (in the
clear), output a ciphertext $c\in\mathcal C$ encrypting $1$ if $\pi=\sigma$ and $0$ otherwise, as

$$
c\leftarrow\mathop{\boxdot}_{i\in[r]}c^\pi_{\sigma(i),i}\boxdot g,
$$

where $g\in\mathcal C$ denotes the fixed zero-error encryption of $1$. (Recall that $\boxdot$ is
right associative.)

Observe that for the above two operations, the GSW ciphertext(s) in the output are designed to
encrypt the appropriate $\{0,1\}$-message. For Compose this is simply by correctness of the
matrix-multiplication algorithm. For Eq? this is because the output ciphertext is designed to
encrypt $1$ if and only if every $c_{\sigma(i),i}$ is designed to encrypt $1$, which is the case
if and only if $\mathbf C^\pi$ is in fact designed to encrypt $\sigma$. All that remains is to
analyze the behavior of the error terms, which we do next.

Footnote 6: Note that asymptotically faster algorithms (e.g., Strassen's) do not appear suitable
here, because the intermediate steps of these algorithms can result in values having magnitude
greater than one, which can cause the error in the ciphertexts to grow much faster. In any case,
this will not matter much in our application, since $r$ will be small.

<a id="pdf-cecd346d2e87-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

**Section 4.2, analysis; Lemma 4.1 (printed p. 11).** Recalling that the GSW scheme is
parameterized by $n$ and $q$, denote its space of error vectors by $\mathcal E=\mathbb Z^m$ where
$m=n\lceil\log_2 q\rceil$. The Euclidean norm on $\mathcal E^r=\mathbb Z^{mr}$ is defined in the
expected way. In what follows it is often convenient to consider vectors and matrices over
$\mathcal E$, i.e., each entry is itself a (row) vector in $\mathcal E=\mathbb Z^m$, and we
switch between $\mathcal E^{h\times w}$ and $\mathbb Z^{h\times wm}$ as is convenient.

The following lemma describes the behavior of errors under the homomorphic composition
operation ⧇. Note that working with vectors and matrices over $\mathcal E$ lets us write a
statement that is syntactically very similar to the one from Lemma 3.5, with a very similar
proof.

**Lemma 4.1.** Let $\mathbf C^\pi,\mathbf C^\sigma\in\mathcal C^{r\times r}$ respectively be
designed to encrypt permutation matrices $\mathbf P_\pi,\mathbf P_\sigma\in\{0,1\}^{r\times r}$
with error matrices $\mathbf E_\pi,\mathbf E_\sigma\in\mathcal E^{r\times r}$. Then for any fixed
values of these variables, $\mathbf C^\pi$ ⧇ $\mathbf C^\sigma$ has error matrix
$\mathbf E+\mathbf P_\pi\cdot\mathbf E_\sigma\in\mathcal E^{r\times r}$, where the
$\mathbb Z$-entries of $\mathbf E$ are mutually independent, and those in its $i$th row are
subgaussian with parameter $O(\|\mathbf e^\pi_i\|)$, where $\mathbf e^\pi_i$ is the $i$th row of
$\mathbf E_\pi$.

**Proof.** Let $\mathbf C\leftarrow\mathbf C^\pi$ ⧇ $\mathbf C^\sigma$. It suffices to show that
for all $i,j$, its $(i,j)$th entry $c_{i,j}\in\mathcal C$ has error

$$
\mathbf e_{i,j}+\mathbf e^\sigma_{\pi^{-1}(i),j}\in\mathcal E=\mathbb Z^m,
$$

where all the $\mathbb Z$-entries of all the $\mathbf e_{i,j}\in\mathbb Z^m$ are mutually
independent and subgaussian with parameter $O(\|\mathbf e^\pi_i\|)$, and $\mathbf e^\sigma_{\ell,j}$
is the $(\ell,j)$th entry of $\mathbf E_\sigma$. This follows directly from Equation (4.1) and
Lemma 3.5: the error in each ciphertext $c^\pi_{i,\ell}\boxdot c^\sigma_{\ell,j}$ is
$p^\pi_{i,\ell}\cdot\mathbf e^\sigma_{\ell,j}$ plus a fresh vector whose entries are independent and
subgaussian with parameter $O(\|\mathbf e^\pi_{i,\ell}\|)$. Since $p^\pi_{i,\ell}=1$ for
$\ell=\pi^{-1}(i)$ and $0$ otherwise, the claim follows by Pythagorean additivity of independent
subgaussians.

<a id="pdf-cecd346d2e87-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->

**Section 4.2, chains of compositions; Corollary 4.2 (printed p. 11).** Similarly to a
multiplication chain of GSW ciphertexts, we can perform a
(right-associative) chain of compositions while incurring only small error growth. For
convenience of analysis, we always include the fixed zero-error ciphertext
$\mathbf J\in\mathcal C^{r\times r}$ (which encrypts the identity permutation) as the rightmost
ciphertext in the chain. The following corollary follows directly from Lemma 4.1 in the same way
that Corollary 3.6 follows from Lemma 3.5.

**Corollary 4.2.** Suppose that $\mathbf C_i\in\mathcal C^{r\times r}$ for $i\in[k]$ are
respectively designed to encrypt permutation matrices $\mathbf P_i\in\{0,1\}^{r\times r}$ and
have error matrices $\mathbf E_i\in\mathcal E^{r\times r}$. Then for any fixed values of these
variables,

$$
\mathbf C\leftarrow\mathop{\text{⧇}}_{i\in[k]}\mathbf C_i\ \text{⧇}\ \mathbf J
=\mathbf C_1\ \text{⧇}\ (\mathbf C_2\ \text{⧇}\ (\cdots(\mathbf C_k\ \text{⧇}\ \mathbf J)\cdots))
$$

has an error matrix whose $\mathbb Z$-entries are mutually independent, and those in its $i$th
row are subgaussian with parameter $O(\|\mathbf e_i\|)$, where
$\mathbf e_i^t\in\mathcal E^{kr}$ is the $i$th row of the concatenated error matrices
$[\mathbf E_1\mid\cdots\mid\mathbf E_k]$.

Finally, since the $\mathsf{Eq?}$ procedure simply performs a chain of (right-associative)
multiplications of GSW ciphertexts, Corollary 3.6 applies.

<a id="pdf-cecd346d2e87-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->

## 5 Bootstrapping

**Section 5 and Section 5.1, specification and usage (printed p. 12).** We now describe our
bootstrapping procedure.

We start by specifying the abstract preconditions and output guarantees of our bootstrapping
algorithm, and describe how to use it (with some additional pre- and post-processing) to
bootstrap known LWE-based encryption schemes.

The scheme to be bootstrapped must have binary ciphertexts in $\{0,1\}^d$ and secret keys in
$\mathbb Z_q^d$ for some dimension $d$ and modulus $q$ that should be made as small as possible
($q,d=\tilde O(\lambda)$ are possible), and a decryption function of the form
$\mathrm{Dec}_{\mathbf s}(\mathbf c)=f(\langle\mathbf s,\mathbf c\rangle)\in\{0,1\}$ for some
arbitrary function $f:\mathbb Z_q\to\{0,1\}$. We rely on an appropriate instantiation of the GSW
cryptosystem, as described in further detail in Section 5.2 below.

- $\mathsf{BootGen}(\mathbf s\in\mathbb Z_q^d,sk)$ takes as input a secret key vector
  $\mathbf s\in\mathbb Z_q^d$ from the scheme to be bootstrapped, and a secret key $sk$ for GSW. It
  outputs a bootstrapping key $bk$, which appropriately encrypts $\mathbf s$ under $sk$.
- $\mathsf{Bootstrap}(bk,\mathbf c\in\{0,1\}^d)$ takes as input the bootstrapping key $bk$ and a
  ciphertext vector $\mathbf c\in\{0,1\}^d$ (which decrypts under the secret key $\mathbf s$). It
  outputs a GSW ciphertext which decrypts (under $sk$) to the same bit as $\mathbf c$ does (under
  $\mathbf s$), but with less error.

<a id="pdf-cecd346d2e87-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->

**Section 5.1, pre- and post-processing (printed p. 13).** We can bootstrap all known LWE-based
bit-encryption schemes using the above algorithms as follows. In all LWE-based encryption
schemes, decryption can be expressed as a "rounded inner product"
$\lfloor\langle\mathbf s,\mathbf c\rangle\rceil_2$ for some appropriate rounding function
$\lfloor\cdot\rceil_2:\mathbb Z_q\to\{0,1\}$, as required. Note that a GSW ciphertext can
trivially be put in this form by just taking its penultimate column (see $\mathsf{GSW.Dec}$ in
Section 3.2). As for the other conditions we need (binary ciphertexts and small $d,q$), LWE
encryption schemes are not always presented in a way that fulfills them, but fortunately there
are standard transformations that do so, as we now describe. (See [BV11, BLP+13] for further
details.)

First, since we do not need to perform any further homomorphic operations on the ciphertext, we
can use dimension- and modulus-reduction [BV11] to get a ciphertext $\bar{\mathbf c}$ (over
$\mathbb Z_q$) of dimension $\tilde O(\lambda)$ and modulus $q=\tilde O(\lambda)$, while
preserving correct decryption. These steps can be implemented with $2^\lambda$ security under
conventional lattice assumptions.⁷ Then, we can obtain a binary ciphertext $\mathbf c$ using
"bit decomposition:" let $\mathbf G$ be as defined in Section 3.1, and for the ciphertext
$\bar{\mathbf c}$ over $\mathbb Z_q$ under secret key $\bar{\mathbf s}$, let $\mathbf c$ be a
$\{0,1\}$-vector such that $\mathbf G\mathbf c=\bar{\mathbf c}$, and let
$\mathbf s=\mathbf G^t\bar{\mathbf s}$ so that
$\langle\mathbf s,\mathbf c\rangle=\langle\bar{\mathbf s},\bar{\mathbf c}\rangle\in\mathbb Z_q$.
(The secret key $\mathbf s$ is therefore the one we need to provide to $\mathsf{BootGen}$.)

After bootstrapping, the output is a GSW ciphertext $\mathbf C$ encrypted under $sk$ (which is
just an integer vector). If desired, we can convert this ciphertext back to one for the original
LWE cryptosystem, simply by taking the penultimate column of $\mathbf C$. We can also key-switch
from $sk$ back to the original secret key $\mathbf s$. (As usual in bootstrapping, going "full
circle" in this way requires an appropriate circular security assumption.)

Footnote 7: To make the modulus quasi-linear, we need to use randomized (subgaussian) rounding in
the modulus-reduction step.

<a id="pdf-cecd346d2e87-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->

**Section 5.2, procedures: parameters and $\mathsf{BootGen}$ (printed p. 13).** Our algorithms
rely on instantiations of GSW and HEPerm with parameters $n,Q,\chi$. Importantly, the ciphertext
modulus $Q$ is not the modulus $q$ of the scheme we are bootstrapping, but rather some $Q\gg q$
that is sufficiently larger than the error in Bootstrap's output ciphertext. Let $\mathcal C$
denote the GSW ciphertext space.

Our procedures need $q$ to be of the form $q=\prod_{i\in[t]}r_i$ where the $r_i$ are small and
powers of distinct primes (and hence pairwise coprime). Specifically, using Lemma 2.2 we can
choose $q=\tilde O(\lambda)$ to be large enough by letting it be the product of all maximal
prime-powers $r_i$ that are bounded by $O(\log\lambda)$, of which there are
$t=O(\log\lambda/\log\log\lambda)$. Let $\phi$ be the group embedding of
$(\mathbb Z_q,+)\cong(\mathbb Z_{r_1}\times\cdots\times\mathbb Z_{r_t},+)$ into
$S=S_{r_1}\times\cdots\times S_{r_t}$ described in Section 2.2, and let $\phi_i$ denote the $i$th
component of this embedding, i.e., the one from $\mathbb Z_q$ into $S_{r_i}$.

- $\mathsf{BootGen}(\mathbf s\in\mathbb Z_q^d,sk)$: given secret key $\mathbf s\in\mathbb Z_q^d$
  for the scheme to be bootstrapped and a secret key $sk$ for HEPerm, embed each coordinate
  $s_j\in\mathbb Z_q$ of $\mathbf s$ as $\phi(s_j)\in S$ and encrypt the components under HEPerm.
  That is, generate and output the bootstrapping key

  $$
  bk=\{\mathbf C_{i,j}\leftarrow\mathsf{HEPerm.Enc}(sk,\phi_i(s_j)):i\in[t],j\in[d]\}.
  $$

  Recalling that we are working with embeddings of $\mathbb Z_{r_i}$, each
  $\mathbf C_{i,j}\in\mathcal C^{r_i}$ can be represented as a tuple of $r_i$ GSW ciphertexts
  encrypting an indicator vector (see Section 4.3). Because $t,r_i=O(\log\lambda)$ and
  $d=\tilde O(\lambda)$, the bootstrapping key consists of $\tilde O(\lambda)$ GSW ciphertexts.

<a id="pdf-cecd346d2e87-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->

**Section 5.2, $\mathsf{Bootstrap}$: Inner Product and Round, Equations (5.1)–(5.2) (printed
pp. 13–14).** $\mathsf{Bootstrap}(bk,\mathbf c\in\{0,1\}^d)$: given a binary ciphertext
$\mathbf c\in\{0,1\}^d$, do the following:

**Inner Product:** Homomorphically compute an encryption of

$$
v=\langle\mathbf s,\mathbf c\rangle=\sum_{j\,:\,c_j=1}s_j\in\mathbb Z_q
$$

using the encryptions of the $s_j\in\mathbb Z_q$ as embedded into the permutation group $S$, via
a chain of compositions. Formally, for each $i\in[t]$ compute (recalling that ⧇ is right
associative, and $\mathbf J$ is the fixed HEPerm encryption of the identity permutation)

$$
\mathbf C_i\leftarrow\mathop{\text{⧇}}_{j\text{ s.t. }c_j=1}\mathbf C_{i,j}\ \text{⧇}\ \mathbf J.\tag{5.1}
$$

Again, because we are working with embeddings of $\mathbb Z_{r_i}$, each
$\mathbf C_i\in\mathcal C^{r_i}$.

**Round:** Homomorphically map $v\in\mathbb Z_q$ to $f(v)\in\mathbb Z_2=\{0,1\}$: for each
$x\in\mathbb Z_q$ such that $f(x)=1$, homomorphically test whether $v\stackrel?=x$ by
homomorphically multiplying the GSW ciphertexts resulting from all the equality tests
$v\stackrel?=x\pmod{r_i}$. Then homomorphically sum the results of all the $v\stackrel?=x$ tests.

Formally, compute and output the GSW ciphertext (recalling that $\boxdot$ is right associative,
and $\mathbf G$ is the fixed GSW encryption of $1$)

$$
\mathbf C\leftarrow\mathop{\boxplus}_{x\in\mathbb Z_q\text{ s.t. }f(x)=1}
\Bigl(\mathop{\boxdot}_{i\in[t]}\mathsf{Eq?}(\mathbf C_i,\phi_i(x))\boxdot\mathbf G\Bigr).\tag{5.2}
$$

Note that since we are working with embeddings of $\mathbb Z_{r_i}$, each
$\mathsf{Eq?}(\mathbf C_i,\phi_i(x))$ is just some GSW ciphertext component of
$\mathbf C_i\in\mathcal C^{r_i}$ (see Section 4.3).

Because $t,r_i=O(\log\lambda)$ and $d=\tilde O(\lambda)$ and by Equations (5.1) and (5.2),
Bootstrap performs $\tilde O(\lambda)$ homomorphic multiplications and additions on GSW
ciphertexts.

<a id="pdf-cecd346d2e87-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->

**Theorem 5.1.** The above bootstrapping scheme can be instantiated to be correct (with
overwhelming probability) and secure assuming that the decisional Shortest Vector Problem
(GapSVP) and Shortest Independent Vectors Problem (SIVP) are (quantumly) hard to approximate in
the worst case to within $\tilde O(n^2\lambda)$ factors on $n$-dimensional lattices.

Because all known (quantum) algorithms for $\mathrm{poly}(n)$-factor approximations to GapSVP
and SIVP on $n$-dimensional lattices take $2^{\Omega(n)}$ time, for $2^\lambda$ hardness we can
take $n=\Theta(\lambda)$, yielding a final approximation factor of $\tilde O(n^3)$. This comes
quite close to the $O(n^{3/2+\epsilon})$ factors obtained in [BV14], but without any expensive
"dimension leveraging:" we use GSW ciphertexts of dimension only $n=O(\lambda)$, rather than
some large polynomial in $\lambda$. Alternatively, at the cost of a larger dimension
$n=\lambda^{1/\epsilon}$, but without using the successive dimension-reduction procedure from
[BV14], we can obtain factors as small as $\tilde O(n^{2+\epsilon})$ for any constant
$\epsilon>0$.

The remainder of this subsection is devoted to proving the above theorem.

<a id="pdf-cecd346d2e87-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->

**Section 5.3, security (printed p. 14).** If the HEPerm key $sk$ is generated independently of
$\mathbf s$, then IND-CPA security of the bootstrapping key follows immediately from the security
of HEPerm, hence from LWE with parameters $n-1,Q,\chi$, and finally from worst-case lattice
problems. (We instantiate these parameters below to obtain the claimed approximation factors.) As
usual, if the keys are not independent, then we need to make an appropriate circular security
assumption. (To date, such an assumption is the only known way to obtain unbounded FHE.)

<a id="pdf-cecd346d2e87-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.95 -->

**Lemma 5.2 (Correctness).** For $bk\leftarrow\mathsf{BootGen}(\mathbf s,sk)$, the GSW ciphertext
$\mathbf C\leftarrow\mathsf{Bootstrap}(bk,\mathbf c)$ is designed to encrypt
$\mathrm{Dec}_{\mathbf s}(\mathbf c)=f(\langle\mathbf s,\mathbf c\rangle)\in\{0,1\}$.

**Proof.** First, by construction the HEPerm ciphertext $\mathbf C_{i,j}$ is designed to encrypt
$\phi_i(s_j)$. Therefore, because $\phi_i:\mathbb Z_q\to S_{r_i}$ is a group homomorphism, the
ciphertext $\mathbf C_i$ as defined in Equation (5.1) is designed to encrypt
$\phi_i(\sum_{j:c_j=1}s_j)=\phi_i(\langle\mathbf s,\mathbf c\rangle)=\phi_i(v)$. By correctness
of Eq? and the isomorphism $\mathbb Z_q\cong\mathbb Z_{r_1}\times\cdots\times\mathbb Z_{r_t}$
given by Chinese Remainder Theorem, the homomorphic product
$\mathop{\boxdot}_{i\in[t]}\mathsf{Eq?}(\mathbf C_i,\phi_i(x))\boxdot\mathbf G$ is designed to
encrypt $1$ if and only if $v=x$. Finally, because the homomorphic sum is taken over every
$x\in\mathbb Z_q$ such that $f(x)=1$, it is designed to encrypt $1$ if and only if $f(v)=1$.

## ===== blueprint/src/references/gentry-sahai-waters-2013-fhe.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: 8edb94cfd852a88a8684adbf81b73e78bd21466514b7bb7000d7df1e4431bf00 -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based

Craig Gentry, Amit Sahai and Brent Waters. *CRYPTO 2013*, LNCS 8042, pp. 75–92; full version
IACR ePrint 2013/340, version dated 8 June 2013 (25 pages; tag `GSW13`).

**Scope.** Only the passages that the GSW Lean (phase 5) and the phase-6 plan cite are
transcribed (DW-7; GSW ruling Q14): the bootstrapping remark of §1.2, §1.3.1–§1.3.4, §2.3, and
§3.1–§3.4. The PDF is not committed. Physical and printed pages coincide. The scoped raw
extraction is `gentry-sahai-waters-2013-fhe.raw.md`. Mathematics is set in LaTeX (the paper's
arrows over vectors are kept as $\vec v$); the wording is the paper's. Notes marked
*Transcription note* are not part of the source.

<a id="pdf-8edb94cfd852-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->

**Section 1.2, bootstrapping and circular security (p. 4).** As with all current FHE schemes
without bootstrapping, the parameters and per-gate complexity of evaluation depend on the
multiplicative depth $L$ of the circuit. "Bootstrapping" [Gen09], together with an assumption
of circular security, remains the only known way of making these performance metrics
independent of $L$, and while the overhead of bootstrapping is high, it becomes an attractive
option once $L$ passes some threshold. However, our scheme loses some of its advantages once
bootstrapping is used. First, to apply bootstrapping, the evaluator needs to obtain the user's
secret key encrypted under its public key – in effect, an evaluation key – and therefore we no
longer achieve identity-based/attribute-based FHE in this context. Second, this encrypted
secret key has quasi-cubic size in our scheme, and while this can be mitigated by public key
compression techniques [CNT12], it eliminates the space complexity advantages of our scheme.
Essentially, bootstrapping returns us to the realm of "unnatural" operations, with all of its
disadvantages. It remains a fascinating open problem to find some "natural" alternative to
bootstrapping, and (relatedly) to achieve "pure" FHE without an assumption of circular
security.

<a id="pdf-8edb94cfd852-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->

## 1.3 An Overview of Our FHE Scheme

**Section 1.3 and Section 1.3.1, homomorphic operations (pp. 4–5).** Our main insight is that we
can achieve LWE-based homomorphic encryption where homomorphic addition and multiplication
correspond directly to matrix addition and multiplication.

Let us skip key generation and encryption for the moment, and jump directly to the homomorphic
operations (and decryption).

In our scheme, for some modulus $q$ and dimension parameter $N$ to be specified later, a
ciphertext $C$ is a $N\times N$ matrix over $\mathbb Z_q$, with "small" entries (much smaller
than $q$) and the secret key $\vec v$ is a $N$-dimensional vector over $\mathbb Z_q$ with at
least one "big" coefficient $v_i$. We restrict the message $\mu$ to be a "small" integer. We
say $C$ encrypts $\mu$ when $C\cdot\vec v=\mu\cdot\vec v+\vec e$, where $\vec e$ is a "small"
error vector. To decrypt, we extract the $i$-th row $C_i$ from $C$, compute
$x\leftarrow\langle C_i,\vec v\rangle=\mu\cdot v_i+e_i$, and output $\mu=\lfloor x/v_i\rceil$.
In a nutshell, the essence of our scheme is that the secret key $\vec v$ is an approximate
eigenvector of the ciphertext matrix $C$, and the message $\mu$ is the eigenvalue.

Now, let us see why matrix addition and multiplication are correct homomorphic operations.
Suppose $C_1$ and $C_2$ encrypt $\mu_1$ and $\mu_2$ in that
$C_i\cdot\vec v=\mu_i\cdot\vec v+\vec e_i$ for small $\vec e_i$. Let $C^+=C_1+C_2$ and
$C^\times=C_1\cdot C_2$. For addition, we have
$C^+\cdot\vec v=(\mu_1+\mu_2)\cdot\vec v+(\vec e_1+\vec e_2)$, where the error likely has grown
a little, as usual in FHE schemes. But assuming the error is still "small", the sum of the
ciphertext matrices encrypts the sum of the messages. For multiplication, we have

$$
\begin{aligned}
C^\times\cdot\vec v&=C_1\cdot(\mu_2\cdot\vec v+\vec e_2)
=\mu_2\cdot(\mu_1\cdot\vec v+\vec e_1)+C_1\cdot\vec e_2
=\mu_1\cdot\mu_2\cdot\vec v+\mu_2\cdot\vec e_1+C_1\cdot\vec e_2\\
&=\mu_1\cdot\mu_2\cdot\vec v+\text{small}
\end{aligned}
$$

where the final error vector is hopefully "small", since $\mu_2$, $C_1$, $\vec e_1$, and
$\vec e_2$ are all small. If so, the product of the ciphertext matrices encrypts the product of
the messages. Interestingly, $C_2\cdot C_1$ is also an encryption of $\mu_1\cdot\mu_2$, even
though matrix multiplication is not commutative.

To simplify further, it might be helpful to imagine an error-free version of the scheme, where
$C_i\cdot\vec v=\mu_i\cdot\vec v$ exactly. In this case, the key $\vec v$ is an (exact)
eigenvector of ciphertext matrices, and the message $\mu_i$ is the eigenvalue. In general, if
matrices $C_1$ and $C_2$ have a common eigenvector $\vec v$ with eigenvalues $\mu_1$ and
$\mu_2$, then $C_1\cdot C_2$ and $C_2\cdot C_1$ have eigenvector $\vec v$ with eigenvalue
$\mu_1\cdot\mu_2$.

<a id="pdf-8edb94cfd852-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->

**Section 1.3.1, end (p. 5).** Of course, in our scheme, the secret key $\vec v$ is only an
approximate eigenvector, not an exact one. Introducing error is necessary to base the security
of our scheme on LWE. The cost of making $\vec v$ only an approximate eigenvector is that
certain terms in our scheme must be "small" to ensure that homomorphic operations do not
disrupt the essential form of the ciphertexts. We call our new approach to LWE-based
(homomorphic) encryption the approximate eigenvector method.

<a id="pdf-8edb94cfd852-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->

**Section 1.3.2, bounding the error and somewhat homomorphic encryption (p. 5).** Although we
have not fully specified the scheme, let us go ahead and estimate how homomorphic it is. The
scheme above works correctly until the coefficients of the error vector begin to approach $q$
in magnitude. How many homomorphic operations can we perform before that happens?

Suppose $C_1$ and $C_2$ are $B$-bounded ciphertexts, in the sense that $\mu_i$ and the
coefficients of $C_i$ and $\vec e_i$ all have magnitude at most some bound $B$. Then, $C^+$ is
$2B$-bounded, and $C^\times$ is $(N+1)B^2$-bounded. In short, the error level grows worse than
$B^{2^L}$, doubly exponentially with the multiplicative depth $L$ of the circuit being
evaluated. Alternatively, if one wants to consider the degree (rather than depth) of functions
that can be evaluated, if we evaluate a multivariate polynomial $P(x_1,\dots,x_t)$ of total
degree $d$, on $B$-bounded ciphertexts as input, the final ciphertext is
$|P|(N+1)^{d-1}B^{d}$-bounded, where $|P|$ is the $\ell_1$-norm of $P$'s coefficient vector.
Taking $q$ to comfortably exceed this bound, we (roughly) can evaluate polynomials of degree
$\log_{NB}q$. Since $q/B$ must be subexponential (at most) in $N$ for security reasons, our
scheme-so-far can only evaluate polynomials of (sublinear) polynomial degree in $N$ (only
logarithmic depth). In short, our scheme-so-far is a somewhat homomorphic encryption (SWHE)
scheme [Gen09] that can evaluate log-depth or polynomial degree. Though not yet fully
homomorphic, it is by far the most homomorphic LWE-based encryption scheme that uses only
"natural" homomorphic operations.

*Transcription note.* The superscripts $(N+1)B^2$ and $B^{2^L}$ are flattened in the
extraction and were checked against the page image (140 dpi); $\log_{NB}q$ is read from the
layout.

<a id="pdf-8edb94cfd852-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.95 -->

**Section 1.3.3, flattening ciphertexts and fully homomorphic encryption (pp. 5–6).** To obtain
a leveled FHE scheme that can evaluate circuits of polynomial depth without bootstrapping or
techniques like relinearization, we need to ensure better bounds on the growth of the error. Let
us say that a ciphertext $C$ is $B$-strongly-bounded if its associated $\mu$ and the
coefficients of $C$ all have magnitude at most $1$, while the coefficients of its $\vec e$ all
have magnitude at most $B$. If we evaluate a NAND gate on $B$-strongly-bounded ciphertexts
$C_1,C_2$ to obtain a new ciphertext $C_3\leftarrow I_N-C_1\cdot C_2$ (where $I_N$ is the
$N$-dimensional identity matrix), then the message remains in $\{0,1\}$, and the coefficients of
$C_3$'s error vector have magnitude at most $(N+1)B$. If we could somehow additionally ensure
that $C_3$'s coefficients have magnitude at most $1$ so that strong-boundedness is preserved,
then we could evaluate a circuit of depth $L$ while keeping the error magnitude at most
$(N+1)^{L}B$. Setting $q/B$ to be subexponential in $N$, we could evaluate a circuit of
polynomial depth rather than merely polynomial degree. In short, we would have a leveled FHE
scheme.

Here we describe a operation called ciphertext flattening that keeps ciphertexts strongly
bounded, so that we obtain leveled FHE.

Flattening uses some simple transformations from [BV11b, BGV12, Bra12] that modify vectors
without affecting dot products. Let $\vec a,\vec b$ be vectors of some dimension $k$ over
$\mathbb Z_q$. Let $\ell=\lfloor\log_2 q\rfloor+1$ and $N=k\cdot\ell$. Let
$\mathrm{BitDecomp}(\vec a)$ be the $N$-dimensional vector
$(a_{1,0},\dots,a_{1,\ell-1},\dots,a_{k,0},\dots,a_{k,\ell-1})$, where $a_{i,j}$ is the $j$-th bit
in $a_i$'s binary representation, bits ordered least significant to most significant. For
$\vec a'=(a_{1,0},\dots,a_{1,\ell-1},\dots,a_{k,0},\dots,a_{k,\ell-1})$, let
$\mathrm{BitDecomp}^{-1}(\vec a')=(\sum 2^j\cdot a_{1,j},\dots,\sum 2^j\cdot a_{k,j})$ be the
inverse of BitDecomp, but well-defined even when the input is not a $0/1$ vector. For
$N$-dimensional $\vec a'$, let
$\mathrm{Flatten}(\vec a')=\mathrm{BitDecomp}(\mathrm{BitDecomp}^{-1}(\vec a'))$, a
$N$-dimensional vector with $0/1$ coefficients. When $A$ is a matrix, let
$\mathrm{BitDecomp}(A)$, $\mathrm{BitDecomp}^{-1}$, or $\mathrm{Flatten}(A)$ be the matrix
formed by applying the operation to each row of $A$ separately. Finally, let
$\mathrm{Powersof2}(\vec b)=(b_1,2b_1,\dots,2^{\ell-1}b_1,\dots,b_k,2b_k,\dots,2^{\ell-1}b_k)$, a
$N$-dimensional vector. Here are some obvious facts:

- $\langle\mathrm{BitDecomp}(\vec a),\mathrm{Powersof2}(\vec b)\rangle=\langle\vec a,\vec b\rangle$.
- For any $N$-dimensional $\vec a'$,
  $\langle\vec a',\mathrm{Powersof2}(\vec b)\rangle
  =\langle\mathrm{BitDecomp}^{-1}(\vec a'),\vec b\rangle
  =\langle\mathrm{Flatten}(\vec a'),\mathrm{Powersof2}(\vec b)\rangle$.

An interesting feature of Flatten is that it makes the coefficients of a vector or matrix
small, without affecting its product with $\mathrm{Powersof2}(\vec b)$, and without knowing
$\vec b$.

To facilitate ciphertext flattening, we give a special form to our secret key $\vec v$.
Specifically, we set $\vec v=\mathrm{Powersof2}(\vec s)$ for some secret vector $\vec s$ (to be
specified later). This form is consistent with our earlier requirement that $\vec v$ have some
big coefficient $v_i$ for decryption; indeed, since $\vec v$'s coefficients go up by
$\lfloor\log_2 q\rfloor$ powers of 2, it must have a big coefficient suitable to recover
$\mu\in\{0,1\}$.

Now, for any $N\times N$ matrix $C$, we have $\mathrm{Flatten}(C)\cdot\vec v=C\cdot\vec v$. So,
after we compute an initial ciphertext $C_3\leftarrow I_N-C_1\cdot C_2$ for the NAND gate, we
set $C^{\mathrm{NAND}}=\mathrm{Flatten}(C_3)$ to obtain a ciphertext that has $0/1$
coefficients and is strongly bounded. Thus, we obtain leveled FHE without relinearization, under
a fixed approximate eigenvector secret key.

*Transcription note.* The page break (p. 5 to p. 6) falls inside the definition of
$\mathrm{Flatten}$; the subsection is kept as one block. The sums in
$\mathrm{BitDecomp}^{-1}$ run over $j$ (the extraction prints the $\sum$ signs on a separate
line).

<a id="pdf-8edb94cfd852-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->

**Section 1.3.4, key generation, encryption, and reduction to LWE (p. 6).** Let us finally
circle back to key generation and encryption. We want to base security on LWE. So, for key
generation, we generate an LWE instance. For suitable parameters $q$, $n$,
$m=O(n\log q)$, an LWE instance over $\mathbb Z_q$ consists of a $m\times(n+1)$ matrix $A$ such
that there exists a $(n+1)$-dimensional vector $\vec s$ whose first coefficient is $1$ where
$\vec e=A\cdot\vec s$ is a "small" error vector. (See Section 2 for a formal definition of LWE.)
In our scheme, $A$ is public and $\vec s$ is secret. We set our approximate eigenvector to be
$\vec v=\mathrm{Powersof2}(\vec s)$, a vector of dimension $N=(n+1)\cdot\ell$ for
$\ell=\lfloor\log_2 q\rfloor+1$.

To encrypt $\mu\in\mathbb Z_q$, the encrypter generates a random $N\times m$ matrix $R$ with
$0/1$ entries, and sets $C=\mathrm{Flatten}(\mu\cdot I_N+\mathrm{BitDecomp}(R\cdot A))$, where
$I_N$ is the $N$-dimensional identity matrix. Since Flatten does not affect the product with
$\vec v$, we have:

$$
C\cdot\vec v=\mu\cdot\vec v+\mathrm{BitDecomp}(R\cdot A)\cdot\vec v
=\mu\cdot\vec v+R\cdot A\cdot\vec s=\mu\cdot\vec v+\text{small}
$$

Flatten ensures that the coefficients of $C$ are small, and therefore that $C$ has the proper
form of a ciphertext that permits our homomorphic operations. Decryption works as mentioned
previously.

To show that security is based on LWE, it is now enough to show that $C$ is statistically
independent of $\mu$ when $A$ is a uniformly random $m\times(n+1)$ matrix over $\mathbb Z_q$.
Let $C'=\mathrm{BitDecomp}^{-1}(C)$. Recall that $C$ is Flatten'd, and so
$C=\mathrm{Flatten}(C)=\mathrm{BitDecomp}(C')$. Therefore, $C$ reveals nothing more than $C'$.
But $C'=\mathrm{BitDecomp}^{-1}(\mu\cdot I_N)+R\cdot A$, and $R\cdot A$ is statistically uniform
by the leftover hash lemma when $m=O(n\log q)$ is chosen appropriately.

<a id="pdf-8edb94cfd852-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Section 2.3, other preliminaries (p. 8).** For $n$, $q$, and
$\ell=\lfloor\log q\rfloor+1$, we define the procedures BitDecomp, $\mathrm{BitDecomp}^{-1}$,
Flatten and Powersof2 as described in the Introduction. $I_N$ denotes the $N$-dimensional
identity matrix.

<a id="pdf-8edb94cfd852-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

## 3 Our LWE-Based FHE Scheme

**Section 3.1, basic encryption scheme: opening and Setup (p. 8).** Here, we formally describe
our basic encryption scheme (without homomorphic operations). This description matches the
description outlined in the Introduction. In our description, we split up KeyGen into three
parts Setup, SecretKeyGen and PublicKeyGen. We provide two decryption algorithms Dec and MPDec.
Dec is sufficient to recover the message $\mu$ when it is in a small space (e.g., $\{0,1\}$).
MPDec is an algorithm by Micciancio and Peikert [MP12] that can recover any
$\mu\in\mathbb Z_q$.

- $\mathrm{Setup}(1^\lambda,1^L)$: Choose a modulus $q$ of $\kappa=\kappa(\lambda,L)$ bits,
  lattice dimension parameter $n=n(\lambda,L)$, and error distribution
  $\chi=\chi(\lambda,L)$ appropriately for LWE that achieves at least $2^\lambda$ security
  against known attacks. Also, choose parameter $m=m(\lambda,L)=O(n\log q)$. Let
  $\textit{params}=(n,q,\chi,m)$. Let $\ell=\lfloor\log q\rfloor+1$ and $N=(n+1)\cdot\ell$.

<a id="pdf-8edb94cfd852-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 3.1, SecretKeyGen, PublicKeyGen, Enc, Dec, MPDec (p. 9).**

- $\mathrm{SecretKeyGen}(\textit{params})$: Sample $\vec t\leftarrow\mathbb Z_q^{n}$. Output
  $sk=\vec s\leftarrow(1,-t_1,\dots,-t_n)\in\mathbb Z_q^{n+1}$. Let
  $\vec v=\mathrm{Powersof2}(\vec s)$.
- $\mathrm{PublicKeyGen}(\textit{params},sk)$: Generate a matrix
  $B\leftarrow\mathbb Z_q^{m\times n}$ uniformly and a vector $\vec e\leftarrow\chi^m$. Set
  $\vec b=B\cdot\vec t+\vec e$. Set $A$ to be the $(n+1)$-column matrix consisting of $\vec b$
  followed by the $n$ columns of $B$. Set the public key $pk=A$. (Remark: Observe that
  $A\cdot\vec s=\vec e$.)
- $\mathrm{Enc}(\textit{params},pk,\mu)$: To encrypt a message $\mu\in\mathbb Z_q$, sample a
  uniform matrix $R\in\{0,1\}^{N\times m}$ and output the ciphertext $C$ given below.

  $$
  C=\mathrm{Flatten}\bigl(\mu\cdot I_N+\mathrm{BitDecomp}(R\cdot A)\bigr)\in\mathbb Z_q^{N\times N}.
  $$
- $\mathrm{Dec}(\textit{params},sk,C)$: Observe that the first $\ell$ coefficients of
  $\vec v$ are $1,2,\dots,2^{\ell-1}$. Among these coefficients, let $v_i=2^i$ be in
  $(q/4,q/2]$. Let $C_i$ be the $i$-th row of $C$. Compute
  $x_i\leftarrow\langle C_i,\vec v\rangle$. Output $\mu'=\lfloor x_i/v_i\rceil$.
- $\mathrm{MPDec}(\textit{params},sk,C)$ (for $q$ a power of 2): Observe that $q=2^{\ell-1}$
  and the first $\ell-1$ coefficients of $\vec v$ are $1,2,\dots,2^{\ell-2}$, and therefore if
  $C\cdot\vec v=\mu\cdot\vec v+\text{small}$, then the first $\ell-1$ coefficients of
  $C\cdot\vec v$ are $\mu\cdot\vec g+\text{small}$, where $\vec g=(1,2,\dots,2^{\ell-2})$.
  Recover $\mathrm{LSB}(\mu)$ from $\mu\cdot 2^{\ell-2}+\text{small}$, then recover the
  next-least-significant-bit from $(\mu-\mathrm{LSB}(\mu))\cdot 2^{\ell-3}+\text{small}$, etc.
  (See [MP12] for the general $q$ case.)

Dec is a BitDecomp'd version of Regev's decryption procedure, applied to one row of the
ciphertext, which is a BitDecomp'd Regev ciphertext. (The extra rows will come into play in the
homomorphic operations). If $C$ is properly generated, then by the elementary properties of
BitDecomp and Powersof2, we have

$$
C\cdot\vec v=\mu\cdot\vec v+R\cdot A\cdot\vec s=\mu\cdot\vec v+R\cdot\vec e.
$$

Dec only uses the $i$-th coefficient of the above expression, which is
$x_i=\mu\cdot v_i+\langle R_i,\vec e\rangle$. The error $\langle R_i,\vec e\rangle$ has
magnitude at most $\|\vec e\|_1$. In general, if $x_i=\mu\cdot v_i+e'$ for some error $e'$ of
magnitude at most $q/8$, and if $v_i\in(q/4,q/2]$, then $x_i/v_i$ differs from $\mu$ by at most
$(q/8)/v_i<1/2$, and Dec uses rounding to output the correct value of $\mu$. (In the basic
scheme, we set $\chi$ to ensure that the error is so bounded with overwhelming probability.)

For the basic scheme (without homomorphic operations), one can take $n$ to be quasi-linear in
the security parameter $\lambda$ and $\kappa=O(\log n)$. When allowing homomorphic operations,
$L$ represents the circuit complexity of the functions that the scheme correctly evaluates
(roughly, $L$ is the multiplicative depth); we provide a detailed analysis later of how $L$
affects the other parameters.

<a id="pdf-8edb94cfd852-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Section 3.2, security (pp. 9–10).** Observe that
$\mathrm{BitDecomp}^{-1}(C)=\mu\cdot G+R\cdot A$, where
$G=\mathrm{BitDecomp}^{-1}(I_N)$ is (the transpose of) the "primitive matrix" used by Micciancio
and Peikert [MP12] in their construction of lattice trapdoors, and the rows of $R\cdot A$ are
simply Regev [Reg05] encryptions of $0$ for dimension $n$. Assuming
$\mathrm{BitDecomp}^{-1}(C)$ hides $\mu$, $C$ does as well, since $C$ can be derived by applying
BitDecomp. Thus, the security of our basic encryption scheme follows directly from the following
lemma, used to prove the security of Regev's encryption scheme [Reg05].

<a id="pdf-8edb94cfd852-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Lemma 1 (Implicit in [Reg05]).** Let $\textit{params}=(n,q,\chi,m)$ be such that the
$\mathrm{LWE}_{n,q,\chi}$ assumption holds. Then, for $m=O(n\log q)$ and $A$, $R$ as generated
above, the joint distribution $(A,R\cdot A)$ is computationally indistinguishable from uniform
over $\mathbb Z_q^{m\times(n+1)}\times\mathbb Z_q^{N\times(n+1)}$.

Concretely, it suffices to take $m>2n\log q$ [Reg05].

Like Brakerski [Bra12], we can also base security on GapSVP via a classical reduction from LWE
[Pei09, BLP+13]. Specifically, Peikert [Pei09] gives a classical reduction of GapSVP to LWE,
with the caveat that $q$ must be exponential in $n$. Brakerski notes that exponential $q$ was
unusable in previous FHE schemes, since the ratio of $q$ to the error level $B$ of "fresh"
ciphertexts cannot be exponential in $n$ for security reasons (since LLL [LLL82] could be used to
break such a scheme), and since $B$ must be very small to permit many homomorphic operations. As
in Brakerski's scheme, we do not have that problem. The error bound $B$ of fresh ciphertexts in
our scheme does not need to be small to permit many homomorphic operations; we only require
$q/B$ to be sub-exponential, and we can therefore permit $q$ to be exponential. Alternatively, we
can use a sub-exponential $q$ and base security on GapSVP via Brakerski et al.'s [BLP+13] recent
classical reduction to LWE that works even for polynomial-size moduli, with the caveat that, in
their reduction, the dimension of the GapSVP instances may be much smaller than the dimension of
the LWE instances.

<a id="pdf-8edb94cfd852-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->

**Section 3.3, homomorphic operations: MultConst, Add, Mult (pp. 10–11).** Recall that we
already described some basic "homomorphic" operations BitDecomp, $\mathrm{BitDecomp}^{-1}$,
Flatten, and Powersof2. These will play an important role in analyzing the homomorphic
operations supported by our scheme. We remark that BitDecomp could alternatively decompose with
respect to bases other than 2, or according to the Chinese Remainder Theorem.

We provide additional homomorphic operations MultConst, Add, Mult, NAND as follows.

- $\mathrm{MultConst}(C,\alpha)$: To multiply a ciphertext $C\in\mathbb Z_q^{N\times N}$ by known
  constant $\alpha\in\mathbb Z_q$, set $M_\alpha\leftarrow\mathrm{Flatten}(\alpha\cdot I_N)$ and
  output $\mathrm{Flatten}(M_\alpha\cdot C)$. Observe that:

  $$
  \begin{aligned}
  \mathrm{MultConst}(C,\alpha)\cdot\vec v&=M_\alpha\cdot C\cdot\vec v
  =M_\alpha\cdot(\mu\cdot\vec v+\vec e)=\mu\cdot(M_\alpha\cdot\vec v)+M_\alpha\cdot\vec e\\
  &=\alpha\cdot\mu\cdot\vec v+M_\alpha\cdot\vec e
  \end{aligned}
  $$

  Thus, the error increases by a factor of at most $N$, regardless of what element
  $\alpha\in\mathbb Z_q$ is used for multiplication. As in "classical" additively homomorphic
  encryption schemes, we could alternatively perform multiplication-by-constant $\alpha$ by
  recursively applying Add. But this multiplies the error size by at least $\alpha$, whereas
  MultConst increases the error by at most a factor of $N$, regardless of $\alpha$. An example
  application of MultConst is that we can perform homomorphic fast Fourier transformations
  (FFTs) natively over $\mathbb Z_q$ without error growth dependent on $q$. Previously, the
  error growth depended on the size of the field underlying the FFT [GHS12a, GHS12b],
  restricting the choice of field.
- $\mathrm{Add}(C_1,C_2)$: To add ciphertexts $C_1,C_2\in\mathbb Z_q^{N\times N}$, output
  $\mathrm{Flatten}(C_1+C_2)$. The correctness of this operation is immediate. Note that the
  addition of messages is over the full base ring $\mathbb Z_q$.
- $\mathrm{Mult}(C_1,C_2)$: To multiply ciphertexts $C_1,C_2\in\mathbb Z_q^{N\times N}$, output
  $\mathrm{Flatten}(C_1\cdot C_2)$. Observe that:

  $$
  \begin{aligned}
  \mathrm{Mult}(C_1,C_2)\cdot\vec v&=C_1\cdot C_2\cdot\vec v
  =C_1\cdot(\mu_2\cdot\vec v+\vec e_2)+\mu_2\cdot(\mu_1\vec v+\vec e_1)+C_1\cdot\vec e_2\\
  &=\mu_1\cdot\mu_2\cdot\vec v+\mu_2\cdot\vec e_1+C_1\cdot\vec e_2
  \end{aligned}
  $$

  As in Add, the multiplication operator is over the full base field $\mathbb Z_q$. In Mult, the
  new error depends on the old errors, the ciphertext $C_1$, and the message $\mu_2$. The
  dependence on the old errors seems unavoidable (and normal for LWE-based HE schemes), and
  observe that $C_1$ contributes at most a factor $N$ blowup of error, since all components of
  $C_1$ are restricted to $\{0,1\}$. The error growth based on the message $\mu_2$, however,
  presents a concern. In general, we must address this concern by using homomorphic operations
  in a way that restricts the message space to small messages. One way to do this is to
  consider Boolean circuits using only NAND operations: this would restrict the message space to
  $\{0,1\}$. We elaborate below.

*Transcription note.* The first line of the Mult display is transcribed as printed (checked
against the page image, 140 dpi): a "$+$" stands where an "$=$" is meant, i.e. the intended
expansion is
$C_1\cdot(\mu_2\cdot\vec v+\vec e_2)=\mu_2\cdot(\mu_1\vec v+\vec e_1)+C_1\cdot\vec e_2$. The
second line is the correct result.

<a id="pdf-8edb94cfd852-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->

**Section 3.3, NAND (p. 11).**

- $\mathrm{NAND}(C_1,C_2)$: To NAND ciphertexts $C_1,C_2\in\mathbb Z_q^{N\times N}$ that are
  known to encrypt messages $\mu_1,\mu_2\in\{0,1\}$, output $\mathrm{Flatten}(I_N-C_1\cdot C_2)$.
  Observe that:

  $$
  \mathrm{NAND}(C_1,C_2)\cdot\vec v=(I_N-C_1\cdot C_2)\cdot\vec v
  =(1-\mu_1\cdot\mu_2)\cdot\vec v-\mu_2\cdot\vec e_1-C_1\cdot\vec e_2
  $$

  Note here that the NAND homomorphic operation maintains the invariant that if the input
  messages are in $\{0,1\}$, then the output ciphertext will also encryption of $\{0,1\}$, thus
  guaranteeing small messages. Note that since $\mu_2\in\{0,1\}$, the error is increased by a
  factor of at most $N+1$.

<a id="pdf-8edb94cfd852-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->

**Section 3.3, "Circuits" (p. 11).** By iteratively applying the homomorphic operations above,
different types of (bounded-depth) circuits may be homomorphically computed while maintaining
correctness of decryption.

The simplest case to analyze is the case of Boolean circuits computed over encryptions of
$\{0,1\}$ values. In this case, the circuit can be converted to use only NAND gates, and through
appropriate leveled application of the NAND homomorphic operation, the final ciphertext's error
will be bounded by $(N+1)^{L}\cdot B$, where $L$ is the NAND-depth of the circuit, and $B$ is the
original bound on the error of a fresh encryption of $\{0,1\}$.

More generally, with more care, we may consider arithmetic circuits over $\mathbb Z_q$ that make
use of gates that perform addition, multiplication, or multiplication by a known constant.
However, as we have seen in the case of multiplication gates, the error growth may depend on the
values being encrypted in intermediate computations. One way to deal with this is to focus on
situations where (1) all input values are known to encrypt values bounded by some value $T$, and
(2) the arithmetic circuit is chosen to guarantee that all intermediate values are also bounded
by $T'$ whenever the circuit inputs are constrained to values bounded by $T$. In such a
situation, the final ciphertext's error will be bounded by $(N+T')^{L}\cdot B$, where $L$ is the
depth of the arithmetic circuit, and $B$ is the original bound on the error of fresh encryptions
of values smaller than $T$. For example, in this way, we can homomorphically evaluate
polynomials of degree $d$ in this large-message-space variant when the initial messages are
bounded by roughly $q^{1/d}$, achieving a scheme that is "somewhat homomorphic" [Gen09]. Another
example application would be to convert encryptions of a polynomially bounded set of small values
to encryptions of binary values, by using an appropriate arithmetic circuit for the conversion.
Once converted to encryptions of binary values, a NAND-based Boolean circuit could be used for
further computations.

<a id="pdf-8edb94cfd852-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.95 -->

**Section 3.4, parameters, performance and optimizations (pp. 11–12).** Suppose that
Flatten'd ciphertexts $C_1,C_2$ encrypt $\mu_1,\mu_2\in\{0,1\}$ under approximate eigenvector
$\vec v$ with $B$-bounded error – that is, $C_i\cdot\vec v=\mu_i\cdot\vec v+\vec e_i$ where
$|\vec e_i|_\infty\le B$. Then $C^{\mathrm{NAND}}\leftarrow\mathrm{NAND}(C_1,C_2)$ encrypts
$\mathrm{NAND}(\mu_1,\mu_2)\in\{0,1\}$ under $\vec v$ with $(N+1)B$-bounded error. As long as
$q/B>8(N+1)^{L}$, we can evaluate a depth-$L$ circuit of NANDs over $B$-bounded ciphertexts to
obtain a $q/8$-bounded ciphertext, which Dec will decrypt correctly.

As in previous LWE-based FHE schemes, $n$ (hence $N$) must increase linearly with $\log(q/B)$ to
maintain fixed $2^\lambda$ security against known attacks, so $q/B$ grows more like
$\exp(L\log L)$. We will brush such issues under the rug and view $n$ as a fixed parameter.
Choosing $\chi$ so that $B$ is not too large, and since in practice there is no reason to have
$\kappa=\log q$ grow super-linearly with $n$, we have
$\kappa=O(L\log N)=O(L(\log n+\log\kappa))=O(L\log n)$, similar to [BGV12, Bra12]. Given that the
NAND procedure is dominated by multiplication of two $N\times N$ matrices for
$N=O(n\kappa)=\tilde O(nL)$, we have the following theorem to characterize the performance of
our FHE scheme.

<a id="pdf-8edb94cfd852-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

**Theorem 3.** For dimension parameter $n$ and depth parameter $L$, our FHE scheme evaluates
depth-$L$ circuits of NAND gates with $\tilde O((nL)^{\omega})$ field operations per gate, where
$\omega<2.3727$ is the matrix multiplication exponent.

This compares favorably with previous LWE-based FHE schemes, which all have at least
$\tilde O(n^3L)$ field operations per gate [BV11b, BGV12, Bra12].

Theorem 3 hides some factors, both good and bad. On the good size, it hides the fact that
ciphertext matrices in our scheme have $0/1$ entries, and therefore can be multiplied faster than
if they were general matrices over $\mathbb Z_q$. In previous LWE-based FHE schemes, the field
operations involve multiplying a small number with a general number of $\mathbb Z_q$, which has
complexity $\tilde O(\kappa)=\tilde O(L)$. So, previous LWE-based FHE schemes have real
complexity $\tilde O(n^3L^2)$ whereas ours remains $\tilde O((nL)^{\omega})$. On the bad side,
Theorem 3 hides logarithmic factors in the dimension of the ciphertext matrices, since
$N=O(n\kappa)=O(nL\log n)$. We note that typically $n$ will dominate $L$, since for very deep
circuits, one would want to use Gentry's bootstrapping technique [Gen09] to make the per-gate
computation independent of $L$.

<a id="pdf-8edb94cfd852-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->

**Section 3.4, bootstrapping (p. 12).** Since bootstrapping involves homomorphically evaluating
the decryption function, and since Dec is essentially Regev decryption [Reg05], bootstrapping
works as in previous LWE-based FHE schemes. In particular, we can use techniques from [BV11b] to
reduce the dimension and modulus-size of the ciphertext before bootstrapping, so that the
complexity of decryption (and hence bootstrapping) is completely independent of the depth $L$ of
the circuit that was evaluated to arrive at that ciphertext. Regev decryption can be evaluated in
$O(\log n)$ depth. Due to the logarithmic depth, one can take $q/B$ to be quasi-polynomial in
$n$, and base security on LWE for quasi-polynomial factors.

## ===== blueprint/src/references/peikert2016-lattice-survey.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

<!-- generated-by: Codex source review of approved excerpts -->
<!-- source-pdf-sha256: 1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488 -->
<!-- validation-status: scoped excerpts for PRs #236 and #237; DW-7 extension (Sections 5.4.3, 6.1.2-6.1.3) awaiting Codex source review -->

# A Decade of Lattice Cryptography

Chris Peikert, author version dated 17 February 2016.

The approved coverage is Definitions 4.1.1, 4.2.1 and 4.2.3, with the
introductory sentence specifying the LWE error law. The anchors refer to
pages 20, 21 and 24 of the original PDF. The added SIS passages cover
the exclusion of trivial modulus multiples and the binary collision argument. The raw extraction retains the
complete document. Footnotes and intervening material are omitted here.

**DW-7 extension (2026-11-16).** The blocks on PDF pages 52–53 and 68–70 were added by the
maintainer for the GSW campaign (GSW ruling Q14; deferred item DW-7). They transcribe, from the
committed raw extraction, the passages the GSW Lean and the phase-6 plan cite: the "Gadgets"
part of §5.4.3 (the vector $\mathbf g$, $\mathbf G=\mathbf I_n\otimes\mathbf g^t$,
Equation (5.4.1) and $\mathbf G\cdot\mathbf G^{-1}(\mathbf u)=\mathbf u$), §6.1.2
(bootstrapping and circular security) and §6.1.3 (Equations (6.1.4)–(6.1.7), decryption, NAND,
bootstrapping by right-associative chains and Barrington's theorem). Unlike the summaries above,
these blocks are transcriptions in the paper's wording, with mathematics in LaTeX; printed page
numbers are two less than the PDF page. The rest of §5.4.3 (trapdoors, Definition 5.4.4 onward)
and of §6.1.3 (fully homomorphic signatures) is not used and is not transcribed. Notes marked
*Transcription note* are not part of the source.

<a id="pdf-1a9802b66031-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.98 -->

**Definition 4.1.1 (Short Integer Solution ($\mathrm{SIS}_{n,q,\beta,m}$)).** Given $m$ uniformly random vectors $\mathbf a_i\in\mathbb Z_q^n$, forming
the columns of a matrix $\mathbf A\in\mathbb Z_q^{n\times m}$, find a nonzero integer vector $\mathbf z\in\mathbb Z^m$ of norm $\|\mathbf z\|\le\beta$ such
that

$$
f_{\mathbf A}(\mathbf z):=\mathbf A\mathbf z=\sum_i\mathbf a_i\cdot z_i=\mathbf0\in\mathbb Z_q^n.\tag{4.1.1}
$$

<a id="pdf-1a9802b66031-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.98 -->

**Observation after Equation (4.1.1).**

Similarly, we
  must take $\beta<q$ because otherwise $\mathbf z=(q,0,\ldots,0)\in\mathbb Z^m$ would always be a legitimate (but trivial)
  solution.

<a id="pdf-1a9802b66031-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.98 -->

* Any solution for a matrix $\mathbf A$ can trivially be converted to one for any extension $[\mathbf A\mid\mathbf A']$, simply by
  appending the solution vector with zeros (which leaves the norm of the solution unchanged). In other
  words, we can ignore columns $\mathbf a_i$ as desired, so the SIS problem can only become easier as $m$ increases.
  Similarly, it can only become harder as $n$ increases.

* The norm bound $\beta$ and the number $m$ of vectors $\mathbf a_i$ must be large enough that a solution is guaranteed
  to exist. This is the case whenever $\beta\ge\sqrt{\bar m}$ and $m\ge\bar m$, where $\bar m$ is the smallest integer greater than
  $n\log q$, by a pigeonhole argument: first, by the previous observation we can assume without loss of
  generality that $m=\bar m$. Then because there are more than $q^n$ vectors $\mathbf x\in\{0,1\}^m$, there must be two
  distinct $\mathbf x,\mathbf x'$ such that $\mathbf A\mathbf x=\mathbf A\mathbf x'\in\mathbb Z_q^n$, so their difference $\mathbf z=\mathbf x-\mathbf x'\in\{0,\pm1\}^m$ is a solution of
  norm at most $\beta$.

* The above pigeonhole argument in fact shows more: the induced function family $\{f_{\mathbf A}:\{0,1\}^m\to\mathbb Z_q^n\}$
  defined in Equation (4.1.1) is *collision resistant*, assuming the hardness of the corresponding SIS
  problem. This is because a collision $\mathbf x,\mathbf x'\in\{0,1\}^m$ for $f_{\mathbf A}$ immediately yields an SIS solution for $\mathbf A$.
  (Of course the domain $\{0,1\}^m$ is somewhat arbitrary here, and can be replaced by essentially any other
  large enough set of sufficiently short integer vectors.)

<a id="pdf-1a9802b66031-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.98 -->

LWE is parameterized by positive integers $n$ and $q$, and an error distribution $\chi$ over $\mathbb Z$.

**Definition 4.2.1 (LWE distribution).** For a vector $\mathbf s\in\mathbb Z_q^n$ called the *secret*, the LWE distribution $A_{\mathbf s,\chi}$
over $\mathbb Z_q^n\times\mathbb Z_q$ is sampled by choosing $\mathbf a\in\mathbb Z_q^n$ uniformly at random, choosing $e\leftarrow\chi$, and outputting
$(\mathbf a,b=\langle\mathbf s,\mathbf a\rangle+e\bmod q)$.

*Definition 4.2.2 omitted.*

**Definition 4.2.3 (Decision-$\mathrm{LWE}_{n,q,\chi,m}$).** Given $m$ independent samples $(\mathbf a_i,b_i)\in\mathbb Z_q^n\times\mathbb Z_q$ where every
sample is distributed according to either: (1) $A_{\mathbf s,\chi}$ for a uniformly random $\mathbf s\in\mathbb Z_q^n$ (fixed for all samples), or
(2) the uniform distribution, distinguish which is the case (with non-negligible advantage).

<a id="pdf-1a9802b66031-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=1.00 -->

**Section 5.1, SIS hashing.** The opening paragraph recalls that the
binary matrix map of Equation (4.1.1) is collision resistant under the
hardness of the corresponding SIS problem. A collision yields the short
nonzero difference described in the earlier section.

<a id="pdf-1a9802b66031-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=1.00 -->

**Section 5.2.1, Regev public-key encryption.** The public key collects
LWE samples under a uniform common secret as columns of an augmented
matrix. Equation (5.2.1) gives the augmented matrix and Equation (5.2.2)
cancels the secret product to expose the errors. Equation (5.2.3) forms
a binary subset sum and adds the message's half-modulus codepoint to its
last coordinate. Decryption cancels the secret contribution and compares
the residual with the two codepoints modulo the modulus.

<a id="pdf-1a9802b66031-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=1.00 -->

**Section 5.2.1, correctness.** The accumulated integer error is the
inner product of the key error vector and the binary subset. The source
uses a quarter-modulus separation and discusses choosing the noise law
and modulus to make decryption correct with overwhelming probability.

<a id="pdf-1a9802b66031-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=1.00 -->

**Section 5.2.1, first security hybrid.** Compare the fixed-bit view
of the public key and ciphertext with the experiment that uses a uniform
public key. A decision-LWE test forms its challenge matrix, encrypts the
fixed bit, and runs the view distinguisher. The simulation is exact for
both challenge laws.

<a id="pdf-1a9802b66031-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=1.00 -->

**Section 5.2.1, second security hybrid.** For a uniform augmented
key matrix and an independent uniform binary subset, the leftover hash
lemma makes the seed-published matrix product close to a uniform independent
ciphertext. Adding a fixed message vector preserves that ideal uniform law.
This hybrid and the first hybrid compare the two fixed-bit views.

<a id="pdf-1a9802b66031-p052-b001"></a>
<!-- pdf-source: page=52; block=1; confidence=0.95 -->

**Section 5.4.3, gadget trapdoors: gadgets (printed p. 50).** We now turn from short bases as
generic lattice trapdoors, to the "gadget"-based trapdoors for $q$-ary SIS/LWE lattices as
developed in [MP12], building on techniques from several related works [Ajt99, AP09, PW08,
ABB10].

*Gadgets.* The first main idea is that there are special, structured matrices $\mathbf G$, called
"gadgets," for which solving SIS and LWE is easy. The simplest gadget is as follows: for a given a
modulus $q$, define the vector

$$
\mathbf g=(1,2,4,\dots,2^{\ell-1})\in\mathbb Z_q^{\ell},
$$

where $\ell=\lceil\log_2 q\rceil$.⁸ Now observe that given any $u\in\mathbb Z_q$, we can find a
short solution $\mathbf x\in\mathbb Z^m$ to

$$
\langle\mathbf g,\mathbf x\rangle=\mathbf g^t\cdot\mathbf x=u\pmod q;
$$

for example, let $\mathbf x$ correspond to the base-two representation of $u$'s canonical
representative in $\{0,\dots,q-1\}$. In other words, it is easy to solve the SIS problem with
respect to the one-row parity-check "matrix" $\mathbf g^t$. Moreover, it is easy to randomly
sample from a discrete Gaussian over the lattice coset $\mathcal L^\perp_u(\mathbf g^t)$ of
solutions.

A bit more thought reveals that solving LWE with respect to $\mathbf g^t$ is also easy. For
simplicity, suppose that $q=2^\ell$; then given any $\mathbf b^t\approx s\cdot\mathbf g^t\pmod q$
with errors in the interval $[-\frac q4,\frac q4)$, we can recover the most-significant bit of
$s\in\mathbb Z_q$ from

$$
b_\ell\approx s\cdot2^{\ell-1}=\mathrm{msb}(s)\cdot\tfrac q2\pmod q.
$$

We can then recover the next-most-significant bit of $s$ from $b_{\ell-1}\approx s\cdot2^{\ell-2}\pmod q$,
etc. (This all generalizes to non-power-of-two moduli as well, but is a bit more technically
involved.)

We extend all of the above to $n$-dimensional SIS and LWE with respect to the block-diagonal
gadget matrix

$$
\mathbf G:=\mathbf I_n\otimes\mathbf g^t=\mathrm{diag}(\mathbf g^t,\dots,\mathbf g^t)\in\mathbb Z_q^{n\times n\ell},
$$

just by working blockwise: for LWE, given $\mathbf b^t\approx\mathbf s^t\mathbf G=(s_1\mathbf g,\dots,s_n\mathbf g)^t$,
just recover each $s_i$ from the corresponding block of $\mathbf b$. For SIS, to find a short
solution to $\mathbf G\mathbf x=\mathbf u$ for a given $\mathbf u\in\mathbb Z_q^n$, just find short
solutions to $\mathbf g^t\cdot\mathbf x_i=u_i$ for each entry $u_i$ and concatenate the results. It
is convenient to express this operation in terms of the "decomposition" function

$$
\begin{aligned}
\mathbf G^{-1}:\ &\mathbb Z_q^n\to\mathbb Z^{n\ell}\\
&\mathbf u\mapsto\text{a short solution }\mathbf x\text{ to }\mathbf G\mathbf x=\mathbf u\pmod q,
\end{aligned}\tag{5.4.1}
$$

Footnote 8: This $\mathbf g$ can be generalized in a variety of ways, e.g., by using a base other
than two, mixed bases, the Chinese Remainder Theorem, etc.

<a id="pdf-1a9802b66031-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=0.95 -->

**Section 5.4.3, the relation $\mathbf G\cdot\mathbf G^{-1}(\mathbf u)=\mathbf u$ (printed p. 51).**
where the choice of notation is explained by the relation

$$
\mathbf G\cdot\mathbf G^{-1}(\mathbf u)=\mathbf u\pmod q.
$$

We stress that $\mathbf G^{-1}$ is not a matrix, but rather a function that maps a mod-$q$ input to
a short integer vector. Depending on the context, the $\mathbf G^{-1}$ operation may even be
randomized, e.g., it could sample a Gaussian-distribution solution.

Finally, observe that given any invertible matrix $\mathbf H\in\mathbb Z_q^{n\times n}$, SIS and LWE
remain easy with respect to the matrix $\mathbf H\mathbf G\in\mathbb Z_q^{n\times n\ell}$.
Specifically, to solve $(\mathbf H\mathbf G)\mathbf x=\mathbf u$, simply output
$\mathbf x=\mathbf G^{-1}(\mathbf H^{-1}\cdot\mathbf u)$, and given
$\mathbf b^t\approx\mathbf s^t\mathbf H\mathbf G$, first recover $\mathbf s^t\mathbf H$ by solving
with respect to $\mathbf G$, then multiply the solution by $\mathbf H^{-1}$.

*Transcription note.* The sentence continues the display (5.4.1) from the previous page.

<a id="pdf-1a9802b66031-p068-b001"></a>
<!-- pdf-source: page=68; block=1; confidence=0.95 -->

**Section 6.1.2, bootstrapping (printed p. 66).** Even with all of the above techniques,
homomorphic operations still always increase the error rate of a ciphertext, by as much as a
polynomial factor per operation. Therefore, the schemes described so far can only homomorphically
evaluate circuits of an a-priori bounded depth; such systems are frequently called "somewhat
homomorphic" or "leveled" (we ignore the precise technical distinction between these terms).

A beautiful idea from Gentry's original work [Gen09b, Gen09a], called *bootstrapping* or sometimes
*refreshing*, makes it possible to reduce the error rate of a ciphertext, thus enabling unbounded
homomorphic computation. Suppose we have a ciphertext $c$ that encrypts some (unknown) message
$\mu$ under a secret key $s$, where the error rate of $c$ is too large to perform further
homomorphic operations on it. The idea behind bootstrapping is to homomorphically evaluate the
*decryption function* on a low-error encryption $c_s=\mathrm{Enc}(s)$ of the secret key $s$, which
is included as part of the public key. More specifically, we homomorphically evaluate the function
$f_c(\cdot)=\mathrm{Dec}(\cdot,c)$ on the ciphertext $c_s$. (Note that the ciphertext $c$ to be
refreshed is "hard-coded" into the function $f_c(\cdot)$, whereas the secret key is treated as the
function argument.) Because $f_c(s)=\mathrm{Dec}(s,c)=\mu$, it follows that homomorphic evaluation
of $f_c$ on an encryption of $s$ (namely, $c_s$) produces an encryption of $\mu$. Moreover, as long
as the circuit depth of $f_c$ and the error rate of $c_s$ are small enough, the error rate of the
output ciphertext will be substantially smaller than that of the input ciphertext $c$, as desired.
In particular, decryption can be performed in $O(\log\lambda)$ depth, so it suffices for $c_s$ to
have some $\lambda^{-O(\log\lambda)}$ error rate.

Because bootstrapping involves the homomorphic evaluation of a somewhat complex function, it is not
very efficient (see, e.g., [GH11b]). However, bootstrapping has been intensively studied and
improved in various ways [GH11a, BGV12], culminating in ring-LWE-based methods that run in only
polylogarithmic $\tilde O(1)$ time per encrypted bit [GHS12a, AP13], where the hidden
$\log^{O(1)}(\lambda)$ factors are not exceedingly large.

We conclude this discussion by noting that, in order to yield unbounded homomorphic operations,
bootstrapping requires a "circular" encryption of the secret key under itself. It is unknown
whether it is provably secure (under a standard assumption) to reveal such an encryption, but nor
are any attacks known. So to date, all unbounded FHE schemes require an additional assumption of
circular security for the secret key.

<a id="pdf-1a9802b66031-p069-b001"></a>
<!-- pdf-source: page=69; block=1; confidence=0.95 -->

**Section 6.1.3, third-generation FHE; homomorphic trapdoors, Equations (6.1.4)–(6.1.6) (printed
p. 67).** In 2013, Gentry, Sahai, and Waters (hereafter GSW) [GSW13] proposed an interesting
LWE-based FHE scheme that has some unique and advantageous properties. For example, homomorphic
multiplication does not require any key-switching step, and the scheme can be made identity-based.
Moreover, as shown in [BV14, AP14], the GSW scheme can be used to bootstrap with only a small
polynomial-factor growth in the error rate, as opposed to quasi-polynomial $\lambda^{\Theta(\log\lambda)}$
growth for the system described above. This yields unbounded FHE based on LWE with just an
inverse-polynomial $n^{-O(1)}$ error rate (plus a circular-security assumption). We describe these
results in some detail next.

*Homomorphic trapdoors.* The GSW scheme is presented most simply in terms of the gadget-based
trapdoors described in Section 5.4.3. (The presentation here has evolved through [BGG+14, AP14,
GVW15b].) At the heart of GSW are the following additive and multiplicative homomorphisms for tags
and trapdoors. Let $\bar{\mathbf A}\in\mathbb Z_q^{n\times\bar m}$ be arbitrary, and for $i=1,2$ let

$$
\mathbf A_i=x_i\mathbf G-\bar{\mathbf A}\mathbf R_i\tag{6.1.4}
$$

for some integer $x_i$ and short integer matrix $\mathbf R_i$. In other words,
$\begin{bmatrix}\mathbf R_i\\ \mathbf I\end{bmatrix}$ is a trapdoor with tag $x_i$ (or more
accurately, tag $x_i\mathbf I$) for the matrix $[\bar{\mathbf A}\mid\mathbf A_i]$.

Applying Equation (6.1.4), it is easy to verify that

$$
\mathbf A_1+\mathbf A_2=(x_1+x_2)\mathbf G-\bar{\mathbf A}(\mathbf R_1+\mathbf R_2),\tag{6.1.5}
$$

and

$$
\begin{aligned}
\mathbf A_1\cdot\mathbf G^{-1}(\mathbf A_2)&=(x_1\mathbf G-\bar{\mathbf A}\mathbf R_1)\cdot\mathbf G^{-1}(\mathbf A_2)\\
&=x_1\mathbf A_2-\bar{\mathbf A}\cdot\mathbf R_1\mathbf G^{-1}(\mathbf A_2)\\
&=x_1x_2\mathbf G-\bar{\mathbf A}\underbrace{\bigl(\mathbf R_1\mathbf G^{-1}(\mathbf A_2)+x_1\mathbf R_2\bigr)}_{\mathbf R}.
\end{aligned}\tag{6.1.6}
$$

In other words, $\begin{bmatrix}\mathbf R_1+\mathbf R_2\\ \mathbf I\end{bmatrix}$ is a trapdoor with
tag $x_1+x_2$ for the matrix $[\bar{\mathbf A}\mid\mathbf A_1+\mathbf A_2]$, and
$\begin{bmatrix}\mathbf R\\ \mathbf I\end{bmatrix}$ is a trapdoor with tag $x_1x_2$ for the matrix
$[\bar{\mathbf A}\mid\mathbf A_1\cdot\mathbf G^{-1}(\mathbf A_2)]$. Note that in the latter case,
we need $x_1$ to be a small integer in order to get a good-quality trapdoor.

One very important property of homomorphic multiplication is that the growth of the resulting
trapdoor matrix $\mathbf R$ is *asymmetric* and *quasi-additive*: while $\mathbf R_1$ is expanded by
some polynomial factor due to the multiplication by $\mathbf G^{-1}(\mathbf A_2)$, the $\mathbf R_2$
term is only multiplied by $x_1$. We discuss the implications of this below.

<a id="pdf-1a9802b66031-p069-b002"></a>
<!-- pdf-source: page=69; block=2; confidence=0.95 -->

**Section 6.1.3, fully homomorphic encryption: the GSW scheme, Equation (6.1.7) (printed
pp. 67–68).** The GSW FHE scheme works as follows. As in prior systems, the public key is a matrix
$\bar{\mathbf A}\in\mathbb Z_q^{n\times\bar m}$ whose columns are LWE samples with some secret
$\bar{\mathbf s}\in\mathbb Z^{n-1}$, i.e.,

$$
\mathbf s^t\bar{\mathbf A}\approx\mathbf 0\tag{6.1.7}
$$

where $\mathbf s=(-\bar{\mathbf s},1)$ is the secret key. An encryption of an integer $x$ is a matrix

$$
\mathbf A=x\mathbf G-\bar{\mathbf A}\mathbf R
$$

for some sufficiently short random $\mathbf R$. As usual, semantic security follows by a lossiness
argument: encrypting under a uniformly random ("malformed") public key $\bar{\mathbf A}$
statistically hides the message, because $[\bar{\mathbf A}\mid\bar{\mathbf A}\mathbf R]$ is very
close to uniformly distributed.

To decrypt a ciphertext $\mathbf A$ using the secret key $\mathbf s$, one just computes

$$
\mathbf s^t\mathbf A\approx x\cdot\mathbf s^t\mathbf G,
$$

where the approximation holds by Equation (6.1.7), and because $\mathbf R$ is short. Since it is
easy to solve LWE with respect to $\mathbf G$, we can recover $x\cdot\mathbf s^t$ and hence $x$
(modulo $q$). In fact, if $x$ is known to be just a bit, then because one of the rightmost entries
of $\mathbf s^t\mathbf G$ is far from zero modulo $q$, we can recover $x$ simply by testing whether
$\mathbf s^t\cdot\mathbf a\approx0$ for an appropriate column $\mathbf a$ of $\mathbf A$.

To homomorphically add or multiply ciphertexts $\mathbf A_1,\mathbf A_2$ that encrypt small
messages, one just computes $\mathbf A_1+\mathbf A_2$ or $\mathbf A_1\cdot\mathbf G^{-1}(\mathbf A_2)$,
respectively. As shown above in Equations (6.1.5) and (6.1.6), the resulting ciphertext is a valid
encryption for the sum or product of the messages, respectively. Because it is important for noise
growth that messages remain small integers, we typically only use operations that maintain the
messages as $\{0,1\}$-values. For example, the binary NAND operation, which is sufficient for
expressing arbitrary computations, can be written as $(x_1\text{ NAND }x_2)=1-x_1x_2$.

*Transcription note.* The block runs onto PDF page 70 (printed 68) from "for some sufficiently
short random $\mathbf R$". "$\bar{\mathbf s}\in\mathbb Z^{n-1}$" is as printed.

<a id="pdf-1a9802b66031-p070-b001"></a>
<!-- pdf-source: page=70; block=1; confidence=0.95 -->

**Section 6.1.3, bootstrapping (printed p. 68).** As first shown by Brakerski and Vaikuntanathan
[BV14], the asymmetric and quasi-additive growth of the trapdoor matrices under homomorphic
multiplication allows certain computations—in particular, decryption for the purpose of
bootstrapping—to be performed with rather small error growth. The first main observation is that
by Equation (6.1.6), any polynomial-length chain of homomorphic bit-multiplications on fresh
ciphertexts, if done in a right-associative manner, incurs only polynomial error growth. The same
also holds when multiplying a sequence of permutation matrices (or more generally, orthonormal
integer matrices), where each matrix is encrypted entry-wise.

The second main idea is that by using Barrington's Theorem [Bar86], any depth-$d$ circuit can be
converted into a length-$4^d$ branching program of permutation matrices. In particular, the
$O(\log\lambda)$-depth decryption circuit can be computed homomorphically in polynomial time and
with polynomial error growth, albeit for rather large polynomials. The subsequent work of
Alperin-Sheriff and Peikert [AP14] significantly improved the runtime and growth to small
polynomials, by avoiding Barrington's Theorem and instead expressing decryption as an arithmetic
function that can be embedded directly into permutation matrices. Ducas and Micciancio [DM15]
devised and implemented a version of this method incorporating additional ideas, yielding a system
that evaluates a complete "bootstrapped NAND gate" in less than a second on standard desktop
hardware.

## ===== blueprint/src/references/barrington-1989-bounded-width-bp.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

<!-- generated-by: maintainer transcription of the passages used (DW-7), read from page images -->
<!-- source-pdf-sha256: 06fd3eeccecf8e3e42c0e33f50356588ea9377b2f7d2642b4d3e0370f4ca7831 -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Bounded-Width Polynomial-Size Branching Programs Recognize Exactly Those Languages in NC¹

David A. Mix Barrington. *Journal of Computer and System Sciences* 38(1):150–164, February 1989
(received 22 August 1986, revised 7 April 1987; preliminary version STOC 1986). Uploaded copy: a
15-page reprint scan with no text layer (tag `Bar89`).

**Scope.** Only the passages that the phase-6 plan uses are transcribed (DW-7; GSW ruling Q13 and
addendum): the abstract, §1 (instructions, width-$w$ branching programs, yields, recognition,
permutation branching programs), and §3 (five-cycle recognition, Theorem 1 with Lemmas 1–3, the
example, the proof of Theorem 1, Theorem 2 with its proof, and the Corollary). §2 and §4–§6 are
not transcribed. The PDF is not committed. Anchors use the physical PDF page; the printed page is
$149+p$ (`p001` is printed page 150). The PDF has no text layer, so the scoped raw file
`barrington-1989-bounded-width-bp.raw.md` is a plain-text reading of the page images (rendered
at 110–170 dpi), not a machine extraction. Mathematics is set in LaTeX; the wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-06fd3eeccecf-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.90 -->

**Abstract (p. 150).** We show that any language recognized by an $NC^1$ circuit (fan-in 2, depth
$O(\log n)$) can be recognized by a width-5 polynomial-size branching program. As any bounded-width
polynomial-size branching program can be simulated by an $NC^1$ circuit, we have that the class of
languages recognized by such programs is exactly nonuniform $NC^1$. Further, following Ruzzo
(*J. Comput. System Sci.* 22 (1981), 365–383) and Cook (*Inform. and Control* 64 (1985) 2–22), if
the branching programs are restricted to be ATIME($\log n$)-uniform, they recognize the same
languages as do ATIME($\log n$)-uniform $NC^1$ circuits, that is, those languages in
ATIME($\log n$). We also extend the method of proof to investigate the complexity of the word
problem for a fixed permutation group and show that polynomial size *circuits* of width 4 also
recognize exactly nonuniform $NC^1$.

<a id="pdf-06fd3eeccecf-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.90 -->

## 1. Definitions

**Section 1, instructions, branching programs and yields (pp. 150–151).** Let
$[w]=\{1,\dots,w\}$. An *instruction* is a triple $\langle j,f,g\rangle$ in which $j$ is the index
of an input variable $x_j$ and $f$ and $g$ are maps from $[w]$ to $[w]$. The meaning of an
instruction $\langle j,f,g\rangle$ is "evaluate to $f$ if $x_j=1$, otherwise evaluate to $g$." A
width-$w$ branching program of length $l$ (a $w$-BP) is a sequence of instructions
$\langle j_i,f_i,g_i\rangle$ for $1\le i\le l$. Given a 0–1 assignment $\mathbf x$ to the input
variables $x_1,\dots,x_n$, a branching program $B$ *yields* the function $B(\mathbf x)$ which is
the composition of the functions produced by each of the instructions. For example, let $w=2$, let
$e$ be the identity function on $w$, and let $(1\,2)$ be the transposition of $w$'s two elements.
Then the program consisting of instructions

$$
\langle 7,(1\,2),e\rangle\langle 4,e,(1\,2)\rangle\langle 8,(1\,2),e\rangle
$$

yields $(1\,2)$ if the exclusive OR of $x_7$, $\bar x_4$, and $x_8$ is one and yields $e$
otherwise.

To recognize a language $L\subseteq\{0,1\}^*$ we need a family of width-$w$ branching programs
$\langle B_n\rangle$, where $B_n$ for each positive integer $n$ takes $n$ Boolean inputs. Length and
size can then be viewed as functions of $n$. We say that $\langle B_n\rangle$ *recognizes* $L$ if
for each $n$ there is a set $F_n$ of functions from $[w]$, such that for all
$\mathbf x\in\{0,1\}^n$, $\mathbf x\in L$ iff $B(\mathbf x)\in F_n$.

$B$ is a *permutation branching program* ($w$-PBP) if each $f_i$ and $g_i$ is a permutation of
$[w]$. In general we will use Greek letters for permutations.

*Transcription note.* The first paragraph is on p. 150 and the rest on p. 151; the block keeps the
definition together. In an instruction the map used when $x_j=1$ comes **first**; BV14's tuples
$(\mathsf{var}(t),\sigma_{t,0},\sigma_{t,1})$ list the map for $x=0$ first.

<a id="pdf-06fd3eeccecf-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->

**Section 1, the traditional model and the main result (p. 151).** The traditional notion (e.g.,
in [10]) of a width-$w$ branching program is of a rectangular $w$ by $l$ array of nodes. Each node
in row $i$ is assigned an input variable and two out-edges leading to nodes in row $i+1$. Our model
can be viewed this way but further requires that each node in a column be assigned the same
variable. This requirement may be enforced at a cost of increasing the length polynomially and
doubling the width. The traditional notion also defines the recognition of a set by a branching
program in a different way, by fixing a start node (a source) and partitioning the sink nodes into
accepting and rejecting. This difference may be dealt with in a similar manner. Thus both models
define the same class BWBP of languages recognized by bounded-width polynomial-size branching
programs. Our main result is that BWBP is equal to (nonuniform) $NC^1$.

In general we will speak of nonuniform circuits and branching programs, so that an $NC^1$ circuit
will be simply a Boolean circuit with fan-in 2 and depth $O(\log n)$ (and hence polynomial size).
Uniformity considerations will be postponed until Section 6, where we will make the appropriate
definitions.

<a id="pdf-06fd3eeccecf-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.90 -->

## 3. The Main Result

**Section 3, five-cycle recognition (p. 152).** We say that a 5-PBP $B$ *five-cycle recognizes* a
set $A\subseteq[2]^n$ if there exists a five-cycle $\sigma$ (called the *output*) in the permutation
group $S_5$ such that $B(\mathbf x)=\sigma$ if $\mathbf x\in A$ and $B(\mathbf x)=e$ if
$\mathbf x\notin A$ ($e$ is the identity permutation). For example, using the usual cycle notation
for elements of $S_5$, the one-instruction program $\langle 1,(12345),e\rangle$ five-cycle
recognizes the set $A=\{\mathbf x:x_1=1\}$ with output $(12345)$.

<a id="pdf-06fd3eeccecf-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.90 -->

**Theorem 1.** Let $A$ be recognized by a depth $d$ fan-in 2 Boolean circuit (we will assume that
the circuit consists of AND and OR gates with a bottom level of inputs and negated inputs). Then
$A$ is five-cycle recognized by a 5-PBP $B$ of length at most $4^d$.

<a id="pdf-06fd3eeccecf-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.90 -->

**Lemma 1.** If $B$ five-cycle recognizes $A$ with output $\sigma$ and $\tau$ is any five-cycle,
then there exists a 5-PBP $B'$, of the same length as $B$, which five-cycle recognizes $A$ with
output $\tau$.

*Proof.* Since $\sigma$ and $\tau$ are both five-cycles there exists some permutation $\theta$ with
$\tau=\theta\sigma\theta^{-1}$. To get $B'$, simply change each instruction of $B$, replacing each
$\sigma_i$ and $\tau_i$ by $\theta\sigma_i\theta^{-1}$ and $\theta\tau_i\theta^{-1}$. $\blacksquare$

*Transcription note.* In this proof $\sigma_i,\tau_i$ name the two permutations of the $i$th
instruction (the $f_i,g_i$ of §1).

<a id="pdf-06fd3eeccecf-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.90 -->

**Lemma 2.** If $A$ can be five-cycle recognized in length $l$, so can its complement.

*Proof.* Let $B$ five-cycle recognize $A$ with output $\sigma$. Call the last instruction of $B$
$\langle i,\mu,\nu\rangle$. Let $B'$ be identical to $B$ except for last instruction
$\langle i,\mu\sigma^{-1},\nu\sigma^{-1}\rangle$. Then $B'(\mathbf x)=e$ if $\mathbf x\in A$ and
$B'(\mathbf x)=\sigma^{-1}$ if $\mathbf x\notin A$. Thus $B'$ five-cycle recognizes the complement
of $A$. $\blacksquare$

<a id="pdf-06fd3eeccecf-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.90 -->

**Lemma 3.** There are two five-cycles $\sigma_1$ and $\sigma_2$ in $S_5$ whose commutator is a
five-cycle. (The commutator of $a$ and $b$ is $aba^{-1}b^{-1}$.)

*Proof* (p. 153). $(12345)(13542)(54321)(24531)=(13254)$. $\blacksquare$

*Transcription note (composition order; checked by computation, not part of the source).* The
displayed identity holds when a product is read left to right, the leftmost permutation acting
first: then $(54321)=(12345)^{-1}$, $(24531)=(13542)^{-1}$, and
$(12345)(13542)(12345)^{-1}(13542)^{-1}=(13254)$. Read right to left (the convention of Mathlib's
`Equiv.Perm` multiplication, which applies the right factor first) the same four factors give
$(14352)$, also a five-cycle. The same left-to-right reading makes Lemma 2's
$B'(\mathbf x)=B(\mathbf x)\sigma^{-1}$ and the yield of a program "the composition of the
functions produced by each of the instructions" in program order. A formalization must fix the
order once; the commutator is a five-cycle in either reading.

<a id="pdf-06fd3eeccecf-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.90 -->

**Example (p. 153).** Consider the 5-PBP

$$
\langle 1,(12345),e\rangle\ \langle 2,(13542),e\rangle\ \langle 1,(54321),e\rangle\ \langle 2,(24531),e\rangle
$$

which yields $(13254)$ as calculated above if $x_1=x_2=1$. If either $x_1$ or $x_2$ is zero, the
yield is $e$ because of cancellation. So this 5-PBP five-cycle recognizes the set
$\{\mathbf x:x_1=x_2=1\}$. We now generalize this construction to prove our theorem.

<a id="pdf-06fd3eeccecf-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.90 -->

**Proof of Theorem 1 (p. 153).** Let $C$ be a depth $d$, fan-in 2 circuit of AND and OR gates, with
a bottom level of inputs and negated inputs. We will show by induction on $d$ that the set
recognized by $C$ can be five-cycle recognized by a 5-PBP. If $d=0$, $C$ has no gates and the set
$A$ can easily be recognized by a one-instruction 5-PBP. Assume without loss of generality that the
output gate of $C$ is an AND gate. If it is an OR gate, appeal to Lemma 2. Then the set $A$
recognized by $C$ is an intersection $A_1\cap A_2$, where $A_1$ and $A_2$ are recognized by circuits
of depth $d-1$ and thus are five-cycle recognized by $B_1$ and $B_2$ of length at most $4^{d-1}$.
Let $B_1$ and $B_2$ have the particular outputs $\sigma_1$ and $\sigma_2$ as defined in Lemma 3, and
$B'_1$ and $B'_2$ have outputs $\sigma_1^{-1}$ and $\sigma_2^{-1}$ (this last is possible by
Lemma 1). Let $B$ be the concatenation $B_1B_2B'_1B'_2$. $B$ yields $e$ unless the input is in both
$A_1$ and $A_2$, but yields the commutator of the two outputs if the input is in $A$. This
commutator is a five-cycle, and so $B$ five-cycle recognizes $A$. $B$ has length at most $4^d$.
Given a circuit and a desired output, this proof gives a deterministic method of constructing the
5-PBP. $\blacksquare$

*Transcription note.* Two steps are left implicit in the source and must be explicit in a
formalization: (i) for an OR gate, "appeal to Lemma 2" means De Morgan — complement the two
sub-programs (Lemma 2), take the AND construction, and complement the result — which keeps the
length bound because Lemma 2 does not change length; (ii) a one-input gate or a constant needs its
own (trivial) case if the circuit model allows them.

<a id="pdf-06fd3eeccecf-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.90 -->

**Theorem 2 (p. 153).** The following result is a nonuniform version of the well-known result that
regular languages can be recognized by $NC^1$ circuits. The proof in the uniform case essentially
appears in [30] and is given explicitly in [22].

*Theorem 2.* If $A\subseteq[2]^n$ is recognized by a $w$-BP $B$ of length $l$, $A$ is recognized by
a fan-in 2 circuit of depth $O(\log l)$, where the constant depends on $w$.

*Proof.* Recall our notion of recognition—we say that $B$ accepts $\mathbf x$ if $B(\mathbf x)$ is
in some arbitrary subset of the functions from $[w]$ to $[w]$. We can represent such a function $f$
by $w^2$ Boolean variables telling whether $f(i)=j$ for each $i$ and $j$. The composition of two
such functions so represented may be computed by a fixed circuit whose size depends only on $w$.
Our circuit for $A$ will have a constant-depth section to find the function yielded by a each
instruction of $B$, a binary tree of composition circuits, and a constant-depth section at the top
to determine acceptance given the function yielded by $B$. $\blacksquare$

<a id="pdf-06fd3eeccecf-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.90 -->

**Corollary (p. 153).** The classes of languages BWBP and nonuniform $NC^1$ are identical. They
equal the class of languages recognized by polynomial-length 5-PBPs.

## ===== blueprint/src/references/gentry-2009-fhe-thesis.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

<!-- generated-by: maintainer transcription of the passages used (DW-8) -->
<!-- source-pdf-sha256: 9e7f32f1b8543416fc6c2fcbfedd5d2d69150226b9bbd2cccac57840a5db7b66 -->
<!-- validation-status: scoped transcription for DW-8; awaiting Codex source review -->

# A Fully Homomorphic Encryption Scheme

Craig Gentry. PhD thesis, Stanford University, September 2009 (tag `Gen09`). Uploaded copy:
`craig-thesis.pdf`, 209 PDF pages.

**Scope.** Only the passages that the leveled scheme uses are transcribed (DW-8; GSW
phase-6 rulings P6-Q14 and P6-Q19 with its refinement): Chapter 4, §4.1 (the overview of
$\mathcal E^{(d)}$ and its chain of encrypted secret keys, Recrypt and $\mathrm{Recrypt}'$,
Definition 4.1.2 of the augmented decryption circuit, Definition 4.1.3 of a bootstrappable
scheme, and the construction $\mathsf{KeyGen}_{\mathcal E^{(d)}}$ /
$\mathsf{Encrypt}$ / $\mathsf{Decrypt}$ / $\mathsf{Evaluate}$ / $\mathsf{Augment}$ /
$\mathsf{Reduce}$ with the high-level review), §4.2 (Theorem 4.2.1, correctness; and
**Theorem 4.2.3 with its proof — the security hybrid**) and the opening of §4.3 with
Remark 4.3.1, which says why the chain is acyclic. Chapters 1–3 and 5–, and §§4.2's
complexity theorem and 4.4, are not transcribed. The PDF is not committed. Anchors use the
**physical** PDF page; the printed page is $p-10$ (`p053` is printed page 43). The scoped
raw extraction is `gentry-2009-fhe-thesis.raw.md`. Mathematics is set in LaTeX; the wording
is the thesis's. Notes marked *Transcription note* are not part of the source.

**Index convention (important when reading the library's leveled scheme).** Gentry numbers
keys $0,\dots,d$ and encrypts $\mathrm{sk}_i$ under $\mathrm{pk}_{i-1}$; a fresh ciphertext
is made under $\mathrm{pk}_d$ and the final decryption is under $\mathrm{sk}_0$, so
evaluation runs *down* the index. He says so explicitly: "in the description below we
encrypt the secret keys in reverse order; the only reason is that this ordering simplifies
our description of the recursion in Evaluate" (p. 46).

<a id="pdf-9e7f32f1b854-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=0.95 -->

**Section 4.1, Leveled Fully Homomorphic Encryption from Bootstrappable Encryption,
Generically (p. 43).** Assume we have an encryption scheme $\mathcal E$ that compactly
evaluates some set of circuits $C_{\mathcal E}$. We want to use $\mathcal E$ to construct a
homomorphic encryption scheme that can handle arbitrary circuits. In this Chapter we prove
a fundamental result: that if $C_{\mathcal E}$ contains (slight augmentations of)
$\mathcal E$'s own decryption circuit $D_{\mathcal E}$ – i.e., if $\mathcal E$ "compactly
evaluates" its (augmented) decryption circuit – then we can use $\mathcal E$ to construct
an efficient scheme that handles circuits of arbitrary depth.

A bit more specifically, for any integer $d$, we use $\mathcal E$ to construct a scheme
$\mathcal E^{(d)}$ that can compactly evaluate circuits of depth up to $d$. The decryption
circuit for $\mathcal E^{(d)}$ is still $D_{\mathcal E}$; the secret key and ciphertexts
are the same size as in $\mathcal E$. **The public key in $\mathcal E^{(d)}$ consists of
$d+1$ public keys from $\mathcal E$, together with a chain of encrypted $\mathcal E$ secret
keys – the first $\mathcal E$ secret key encrypted under the second $\mathcal E$ public key,
and so on.** In short, the family of schemes $\{\mathcal E^{(d)}\}$ is leveled fully
homomorphic. **We base the semantic security of $\mathcal E^{(d)}$ on that of $\mathcal E$
using a hybrid argument; as usual with hybrid arguments, the reduction loses a factor
linear in $d$.**

In Chapter 4.3, we describe how one can obtain a fully homomorphic encryption scheme (where
the public key size does not depend on the maximum number of levels we want to evaluate) by
assuming key-dependent-message (KDM) security, specifically circular-security – i.e., that
one can safely encrypt a $\mathcal E$ secret key under its associated public key.

<a id="pdf-9e7f32f1b854-p054-b001"></a>
<!-- pdf-source: page=54; block=1; confidence=0.95 -->

**Section 4.1, why bootstrappability refreshes along the chain (p. 44).** Since this
critical property of $\mathcal E$ – that it can compactly evaluate (slight augmentations
of) its own decryption circuit – is self-referential and universal, we give it the obvious
name: *bootstrappability*. Why should bootstrappability be such a powerful feature? At a
high level, the reason is that bootstrappability allows us periodically to "refresh"
ciphertexts associated to interior nodes in a circuit; we can refresh for an arbitrary
number of levels in the circuit, and thus can evaluate circuits of arbitrary depth. **To
"refresh" a ciphertext that encrypts a plaintext $\pi$ under $\mathcal E$ public key
$\mathrm{pk}_i$, we re-encrypt it under $\mathrm{pk}_{i+1}$ and then homomorphically apply
the decryption circuit to the result, using the secret key $\mathrm{sk}_i$ that is
encrypted under $\mathrm{pk}_{i+1}$, thereby obtaining an encryption of $\pi$ under
$\mathrm{pk}_{i+1}$.** Homomorphically evaluating the decryption circuit decrypts the inner
ciphertext under $\mathrm{pk}_i$, but within homomorphic encryption under
$\mathrm{pk}_{i+1}$. The implicit decryption "refreshes" the ciphertext, but the plaintext
is never revealed; the plaintext is always covered by at least one layer of encryption. Now
that the ciphertext is refreshed, we can "continue" correctly evaluating the circuit.

<a id="pdf-9e7f32f1b854-p054-b002"></a>
<!-- pdf-source: page=54; block=2; confidence=0.95 -->

**Section 4.1, the Recrypt algorithm (p. 44).** To see how this works mathematically, begin
by considering the following algorithm, called Recrypt. For simplicity, suppose the
plaintext space $\mathcal P$ is $\{0,1\}$ and $D_{\mathcal E}$ is a boolean circuit in
$C_{\mathcal E}$. Let $(\mathrm{sk}_1,\mathrm{pk}_1)$ and
$(\mathrm{sk}_2,\mathrm{pk}_2)$ be two $\mathcal E$ key-pairs. Let $\psi_1$ be an encryption
of $\pi\in\mathcal P$ under $\mathrm{pk}_1$. Let $\overline{\mathrm{sk}_{1j}}$ be an
encryption of the $j$-th bit of the first secret key $\mathrm{sk}_1$ under the second public
key $\mathrm{pk}_2$. Recrypt takes as these things as input, and outputs an encryption of
$\pi$ under $\mathrm{pk}_2$.

$$
\begin{aligned}
&\mathsf{Recrypt}(\mathrm{pk}_2,D_{\mathcal E},
  \langle\overline{\mathrm{sk}_{1j}}\rangle,\psi_1).\\
&\qquad \text{Set }\overline{\psi_{1j}}\xleftarrow{\ R\ }
  \mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_2,\psi_{1j})\text{ where }\psi_{1j}
  \text{ is the }j\text{-th bit of }\psi_1\\
&\qquad \text{Set }\psi_2\leftarrow\mathsf{Evaluate}_{\mathcal E}(\mathrm{pk}_2,
  D_{\mathcal E},\langle\langle\overline{\mathrm{sk}_{1j}}\rangle,
  \langle\overline{\psi_{1j}}\rangle\rangle)\\
&\qquad \text{Output }\psi_2
\end{aligned}
$$

Above, the Evaluate algorithm takes in all of the bits of $\mathrm{sk}_1$ and all of the
bits of $\psi_1$, each encrypted under $\mathrm{pk}_2$. Then, $\mathcal E$ is used to
evaluate the decryption circuit homomorphically. The output $\psi_2$ is thus an encryption
under $\mathrm{pk}_2$ of $\mathsf{Decrypt}_{\mathcal E}(\mathrm{sk}_1,\psi_1)\to\pi$.

*Transcription note.* "Recrypt takes as these things as input" is transcribed as printed.
The `-layout` extraction loses the overbars that mark a value as encrypted (it prints
`sk1j` for $\overline{\mathrm{sk}_{1j}}$ and `ψ1j` for both $\psi_{1j}$ and
$\overline{\psi_{1j}}$); the overbars were read from the page images and are restored here.
The superscript $R$ on the assignment arrow marks a random draw.

<a id="pdf-9e7f32f1b854-p055-b001"></a>
<!-- pdf-source: page=55; block=1; confidence=0.95 -->

**Definition 4.1.2 (Augmented Decryption Circuit) (pp. 45–46).** Let $D_{\mathcal E}$ be
$\mathcal E$'s decryption circuit, which takes a secret key and ciphertext as input, each
formatted as an element of $\mathcal P^{\ell(\lambda)}$, where $\mathcal P$ is the
plaintext space. Let $\Gamma$ be a set of gates with inputs and output in $\mathcal P$,
which includes the trivial gate (input and output are the same). We call a circuit composed
of multiple copies of $D_{\mathcal E}$ connected by a single $g$ gate (the number of copies
equals the number of inputs to $g$) a "$g$-augmented decryption circuit." We denote the set
of $g$-augmented decryption circuits, $g\in\Gamma$, by $D_{\mathcal E}(\Gamma)$.

<a id="pdf-9e7f32f1b854-p056-b001"></a>
<!-- pdf-source: page=56; block=1; confidence=0.95 -->

**Definition 4.1.3 (Bootstrappable Encryption Scheme) (p. 46).** As before, let
$C_{\mathcal E}$ denote the set of circuits that $\mathcal E$ can compactly evaluate. We
say that $\mathcal E$ is *bootstrappable with respect to $\Gamma$* if

$$
D_{\mathcal E}(\Gamma)\subseteq C_{\mathcal E}.
$$

For example, if $\Gamma$ includes the trivial gate and NAND, $\mathcal E$ is bootstrappable
with respect to $\Gamma$ if $C_{\mathcal E}$ contains $D_{\mathcal E}$ and the circuit
formed by joining two copies of $D_{\mathcal E}$ with a NAND gate. Remarkably, as we will
show, if there is a scheme $\mathcal E$ that can compactly evaluate only these two
circuits, then there is a scheme that is leveled fully homomorphic.

<a id="pdf-9e7f32f1b854-p056-b002"></a>
<!-- pdf-source: page=56; block=2; confidence=0.95 -->

**Section 4.1, the construction of $\mathcal E^{(d)}$, and the reverse-order convention
(p. 46).** From the informal description above, it should already be somewhat clear how to
use a bootstrappable encryption scheme to construct a leveled fully homomorphic one; below,
we give a more formal description. Let $\mathcal E$ be bootstrappable with respect to a set
of gates $\Gamma$. For any integer $d\ge 1$, we use $\mathcal E$ to construct a scheme
$\mathcal E^{(d)}=(\mathsf{KeyGen}_{\mathcal E^{(d)}},\mathsf{Encrypt}_{\mathcal E^{(d)}},
\mathsf{Evaluate}_{\mathcal E^{(d)}},\mathsf{Decrypt}_{\mathcal E^{(d)}})$ that can handle
all circuits of depth $d$ with gates in $\Gamma$. **Note that in the description below we
encrypt the secret keys in reverse order; the only reason is that this ordering simplifies
our description of the recursion in Evaluate.** When we refer to the *level* of a wire in
$C$, we mean the level of the gate for which the wire is an input. We use the notation
$D_{\mathcal E}(\Gamma,\delta)$ to refer to the set of circuits that equal a $\delta$-depth
circuit with gates in $\Gamma$ augmented by $D_{\mathcal E}$ (copies of $D_{\mathcal E}$
become inputs to the $\delta$-depth circuit).

<a id="pdf-9e7f32f1b854-p056-b003"></a>
<!-- pdf-source: page=56; block=3; confidence=0.95 -->

**The key chain: $\mathsf{KeyGen}_{\mathcal E^{(d)}}$ (pp. 46–47).**
$\mathsf{KeyGen}_{\mathcal E^{(d)}}(\lambda,d)$. Takes as input a security parameter
$\lambda$ and a positive integer $d$. For $\ell=\ell(\lambda)$ as in Definition 4.1.2, it
sets

$$
\begin{aligned}
(\mathrm{sk}_i,\mathrm{pk}_i)&\xleftarrow{\ R\ }\mathsf{KeyGen}_{\mathcal E}(\lambda)
  &&\text{for } i\in[0,d]\\
\overline{\mathrm{sk}_{ij}}&\xleftarrow{\ R\ }
  \mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_{i-1},\mathrm{sk}_{ij})
  &&\text{for } i\in[1,d],\ j\in[1,\ell]
\end{aligned}
$$

where $\mathrm{sk}_{i1},\dots,\mathrm{sk}_{i\ell}$ is the representation of
$\mathrm{sk}_i$ as elements of $\mathcal P$. It outputs the secret key
$\mathrm{sk}^{(d)}\leftarrow\mathrm{sk}_0$ and the public key
$\mathrm{pk}^{(d)}\leftarrow(\langle\mathrm{pk}_i\rangle,
\langle\overline{\mathrm{sk}_{ij}}\rangle)$. Let $\mathcal E^{(\delta)}$ refer to the
sub-system that uses $\mathrm{sk}^{(\delta)}\leftarrow\mathrm{sk}_0$ and
$\mathrm{pk}^{(\delta)}\leftarrow(\langle\mathrm{pk}_i\rangle_{i\in[0,\delta]},
\langle\overline{\mathrm{sk}_{ij}}\rangle_{i\in[1,\delta]})$ for $\delta\le d$.

*Transcription note.* The second display is the key chain: $\ell$ ciphertexts for each
$i\in[1,d]$, so $\ell\cdot d$ encrypted secret-key elements in all, and only this part of
the public key grows with $d$. The `-layout` extraction prints both sides of that line as
`skij`, losing the overbar on the left; the page image (150 dpi) shows
$\overline{\mathrm{sk}_{ij}}$ on the left and $\mathrm{sk}_{ij}$ inside
$\mathsf{Encrypt}_{\mathcal E}$, as transcribed.

<a id="pdf-9e7f32f1b854-p057-b001"></a>
<!-- pdf-source: page=57; block=1; confidence=0.95 -->

**$\mathsf{Encrypt}$, $\mathsf{Decrypt}$ and $\mathsf{Evaluate}$ for
$\mathcal E^{(d)}$ (p. 47).**

$\mathsf{Encrypt}_{\mathcal E^{(d)}}(\mathrm{pk}^{(d)},\pi)$. Takes as input a public key
$\mathrm{pk}^{(d)}$ and a plaintext $\pi\in\mathcal P$. It outputs a ciphertext
$\psi\xleftarrow{\ R\ }\mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_d,\pi)$.

$\mathsf{Decrypt}_{\mathcal E^{(d)}}(\mathrm{sk}^{(d)},\psi)$. Takes as input a secret key
$\mathrm{sk}^{(d)}$ and a ciphertext $\psi$ (which should be an encryption under
$\mathrm{pk}_0$). It outputs $\mathsf{Decrypt}_{\mathcal E}(\mathrm{sk}_0,\psi)$.

$\mathsf{Evaluate}_{\mathcal E^{(\delta)}}(\mathrm{pk}^{(\delta)},C_\delta,\Psi_\delta)$.
Takes as input a public key $\mathrm{pk}^{(\delta)}$, a circuit $C_\delta$ of depth at most
$\delta$ with gates in $\Gamma$, and a tuple of input ciphertexts $\Psi_\delta$ (where each
input ciphertext should be under $\mathrm{pk}_\delta$). **We assume that each wire in
$C_\delta$ connects gates at consecutive levels; if not, add trivial gates to make it so.**
If $\delta=0$, it outputs $\Psi_0$ and terminates. Otherwise, it does the following:

- Sets $(C^\dagger_{\delta-1},\Psi^\dagger_{\delta-1})\leftarrow
  \mathsf{Augment}_{\mathcal E^{(\delta)}}(\mathrm{pk}^{(\delta)},C_\delta,\Psi_\delta)$.
- Sets $(C_{\delta-1},\Psi_{\delta-1})\leftarrow
  \mathsf{Reduce}_{\mathcal E^{(\delta-1)}}(\mathrm{pk}^{(\delta-1)},
  C^\dagger_{\delta-1},\Psi^\dagger_{\delta-1})$.
- Runs $\mathsf{Evaluate}_{\mathcal E^{(\delta-1)}}(\mathrm{pk}^{(\delta-1)},
  C_{\delta-1},\Psi_{\delta-1})$.

*Transcription note.* The highlighted assumption is the thesis's own layering requirement
on the circuit: every wire joins consecutive levels, padded with trivial gates if not.

<a id="pdf-9e7f32f1b854-p057-b002"></a>
<!-- pdf-source: page=57; block=2; confidence=0.95 -->

**$\mathsf{Augment}$ and $\mathsf{Reduce}$ (p. 47).**

$\mathsf{Augment}_{\mathcal E^{(\delta)}}(\mathrm{pk}^{(\delta)},C_\delta,\Psi_\delta)$.
Takes as input a public key $\mathrm{pk}^{(\delta)}$, a circuit $C_\delta$ of depth at most
$\delta$ with gates in $\Gamma$, and a tuple of input ciphertexts $\Psi_\delta$ (where each
input ciphertext should be under $\mathrm{pk}_\delta$). It augments $C_\delta$ with
$D_{\mathcal E}$; call the resulting circuit $C^\dagger_{\delta-1}$. Let
$\Psi^\dagger_{\delta-1}$ be the tuple of ciphertexts formed by replacing each input
ciphertext $\psi\in\Psi_\delta$ by the tuple
$\langle\langle\overline{\mathrm{sk}_{\delta j}}\rangle,
\langle\overline{\psi_j}\rangle\rangle$, where $\overline{\psi_j}\leftarrow
\mathsf{WeakEncrypt}_{\mathcal E^{(\delta-1)}}(\mathrm{pk}^{(\delta-1)},\psi_j)$ and the
$\psi_j$'s form the properly-formatted representation of $\psi$ as elements of
$\mathcal P$. It outputs $(C^\dagger_{\delta-1},\Psi^\dagger_{\delta-1})$.

$\mathsf{Reduce}_{\mathcal E^{(\delta)}}(\mathrm{pk}^{(\delta)},C^\dagger_\delta,
\Psi^\dagger_\delta)$. Takes as input a public key $\mathrm{pk}^{(\delta)}$, a tuple of
input ciphertexts $\Psi^\dagger_\delta$ (where each input ciphertext should be in the image
of $\mathsf{Encrypt}_{\mathcal E^{(\delta)}}$), and a circuit $C^\dagger_\delta\in
D_{\mathcal E}(\Gamma,\delta+1)$. It sets $C_\delta$ to be the sub-circuit of
$C^\dagger_\delta$ consisting of the first $\delta$ levels. It sets $\Psi_\delta$ to be the
induced input ciphertexts of $C_\delta$, where the ciphertext $\psi^{(w)}_\delta$
associated to wire $w$ at level $\delta$ is set to
$\mathsf{Evaluate}_{\mathcal E}(\mathrm{pk}_\delta,C^{(w)}_\delta,\Psi^{(w)}_\delta)$,
where $C^{(w)}_\delta$ is the sub-circuit of $C^\dagger_\delta$ with output wire $w$, and
$\Psi^{(w)}_\delta$ are the input ciphertexts for $C^{(w)}_\delta$. It outputs
$(C_\delta,\Psi_\delta)$.

<a id="pdf-9e7f32f1b854-p058-b001"></a>
<!-- pdf-source: page=58; block=1; confidence=0.95 -->

**Section 4.1, high-level review of the Evaluate algorithm (p. 48).** In the full scheme
above, the ciphertexts that we associate to the decryption circuit that was attached to
wire $w$ are analogous to the ones we used in $\mathrm{Recrypt}'_{\mathcal E}$: **the
encrypted secret key ($\mathrm{sk}_d$ under $\mathrm{pk}_{d-1}$), and the re-encryption
ciphertexts of $\psi_w$ under $\mathrm{pk}_{d-1}$.** By the correctness of Recrypt, the
ciphertext now associated to $w$ (after performing $\mathsf{Evaluate}_{\mathcal E}$) should
encrypt the same plaintext as $\psi_w$, but now under $\mathrm{pk}_{d-1}$.

The Reduce step simply performs this Evaluate up to the wire $w$, and one level beyond. We
know that Evaluate can correctly continue one level beyond the wire $w$, because (by
assumption) $\mathcal E$ can evaluate not just the decryption circuit attached to $w$, but
can evaluate a circuit containing one $\Gamma$-gate above $w$. Reduce outputs $C_{d-1}$ and
ciphertexts associated to $C_{d-1}$'s input wires. We have made progress, since $C_{d-1}$
is one level shallower than $C_d$. We perform this entire process $d-1$ more times to
obtain the final output ciphertexts.

<a id="pdf-9e7f32f1b854-p059-b001"></a>
<!-- pdf-source: page=59; block=1; confidence=0.95 -->

**Section 4.2, Theorem 4.2.1 (correctness) (p. 49).** Let $\mathcal E$ be bootstrappable
with respect to a set of gates $\Gamma$. Then $\mathcal E^{(d)}$ compactly evaluates all
circuits of depth $d$ with gates in $\Gamma$ – i.e., if $\Gamma$ is a universal set of
gates, the family $\mathcal E^{(d)}$ is leveled fully homomorphic.

*Transcription note.* The proof of Theorem 4.2.1 (pp. 49–50) is not transcribed; only its
statement is, since the citation is for the construction and the security hybrid.

<a id="pdf-9e7f32f1b854-p060-b001"></a>
<!-- pdf-source: page=60; block=1; confidence=0.95 -->

**Section 4.2, Theorem 4.2.3 (the security hybrid) (p. 50).** Finally, assuming the
semantic security of $\mathcal E$, we prove the semantic security of $\mathcal E^{(d)}$.

**Theorem 4.2.3.** Let $\mathcal A$ be an algorithm that $(t,\epsilon)$-breaks the semantic
security of $\mathcal E^{(d)}$. Then, there is an algorithm $\mathcal B$ that
$(t',\epsilon')$-breaks the semantic security of $\mathcal E$ for $t'\approx t\cdot\ell$
and $\epsilon'\ge\epsilon/\ell(d+1)$, for $\ell$ as in Definition 4.1.2.

*Proof.* (Theorem 4.2.3) Let $(\mathcal E)^\ell$ be equivalent to $\mathcal E$, but with
plaintext space $\mathcal P^{\le\ell}$, where $\mathsf{Encrypt}_{(\mathcal E)^\ell}$
involves up to $\ell$ invocations of $\mathcal E$ and a concatenation of the results. We
use a hybrid argument to show that $\mathcal B$ $(t'',\epsilon'')$-breaks the semantic
security of $(\mathcal E)^\ell$ for $t''\approx t$ and $\epsilon''\ge\epsilon/(d+1)$, from
which the result follows.

**For $k\in[0,d]$, let Game $k$ denote a game against $\mathcal E^{(d)}$ in which
everything is exactly as in the real-world game, except that for all $i\in[1,k]$ the
challenger sets**

$$
(\mathrm{sk}'_i,\mathrm{pk}'_i)\xleftarrow{\ R\ }\mathsf{KeyGen}_{\mathcal E}(\lambda)
\quad\text{and}\quad
\overline{\mathrm{sk}_{ij}}\xleftarrow{\ R\ }
\mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_{i-1},\mathrm{sk}'_{ij})
$$

In other words, for $i\in[1,k]$, $\overline{\mathrm{sk}_{ij}}$ is the encryption (under
$\mathrm{pk}_{i-1}$) of the $j$-th bit of a random secret key $\mathrm{sk}'_i$ unrelated to
$\mathrm{sk}_i$. Game $d+1$ is identical to Game $d$, except that the challenger ignores
$b$ and $(\pi_0,\pi_1)$, generates a random plaintext $\pi$ of the appropriate length, and
encrypts $\pi$ to construct the challenge ciphertext. Let $\epsilon_k$ denote the
adversary's advantage in Game $k$.

Since Game $0$ is identical to the real world attack, the adversary's advantage is
$\epsilon$ by assumption. Also, $\epsilon_{d+1}=0$, since the challenge is independent of
$b$. Consequently, for some $k\in[0,d]$, it must hold that
$|\epsilon_k-\epsilon_{k+1}|\ge\epsilon/(d+1)$; fix this value of $k$.

*Transcription note.* The thesis's $\epsilon$ is set in a font that the `-layout`
extraction renders as the character `²`; it is the advantage $\epsilon$ throughout, as the
page image (150 dpi) confirms.

<a id="pdf-9e7f32f1b854-p061-b001"></a>
<!-- pdf-source: page=61; block=1; confidence=0.95 -->

**Section 4.2, Theorem 4.2.3, the reduction (p. 51).** $\mathcal B$ uses $\mathcal A$ to
break $(\mathcal E)^\ell$ as follows. $\mathcal B$ receives from the challenger a public
key $\mathrm{pk}$. $\mathcal B$ generates the secret and public values exactly as in Game
$k$, except that it replaces its original value of $\mathrm{pk}_k$ with $\mathrm{pk}$.
Also, if $k<d$, it generates a dummy key pair
$(\mathrm{sk}'_{k+1},\mathrm{pk}'_{k+1})\xleftarrow{\ R\ }
\mathsf{KeyGen}_{\mathcal E}(\lambda)$, sets $\pi_0\leftarrow\mathrm{sk}_{k+1}$ and
$\pi_1\leftarrow\mathrm{sk}'_{k+1}$, and requests a challenge ciphertext (under
$\mathrm{pk}$) encrypting either $\pi_0,\pi_1\in\mathcal P^\ell$. The challenger generates
$\beta\xleftarrow{\ R\ }\{0,1\}$ and sends a tuple of ciphertexts $\langle\psi_j\rangle$
encrypting the bits $\langle\pi_{\beta j}\rangle$. $\mathcal B$ replaces its original tuple
$\langle\overline{\mathrm{sk}_{(k+1)j}}\rangle$ with the tuple $\langle\psi_j\rangle$. One
can verify that the public values are generated exactly as in Game $k+\beta$. $\mathcal B$
sends the public values to $\mathcal A$.

Eventually, $\mathcal A$ requests a challenge ciphertext on $\pi_0$ or $\pi_1$.
$\mathcal B$ sets $b\xleftarrow{\ R\ }\{0,1\}$. If $k<d$, $\mathcal B$ sends the values
$\psi_j\xleftarrow{\ R\ }\mathsf{Encrypt}_{\mathcal E}(\mathrm{pk}_d,\pi_{bj})$. If $k=d$,
$\mathcal B$ generates random $\pi\xleftarrow{\ R\ }\mathcal P$ and asks the challenger for
a challenge ciphertext on $\pi_b$ or $\pi$. The challenger generates
$\beta\xleftarrow{\ R\ }\{0,1\}$ and encrypts $\pi_b$ or $\pi$ accordingly, and
$\mathcal B$ forwards the challenge to $\mathcal A$. $\mathcal A$ sends a bit $b'$.
$\mathcal B$ sends bit $\beta'\leftarrow b\oplus b'$ to the challenger. One can verify that
the challenge is generated as in Game $k+\beta$.

Since $\mathcal B$'s simulation has the same distribution as Game $k+\beta$, and the
probability that $\mathcal B$ outputs $0$ is $\epsilon_{k+\beta}$. The result follows.
$\square$

*Transcription note.* The last sentence is transcribed as printed; it reads as an
incomplete clause ("Since …, and the probability … is $\epsilon_{k+\beta}$.").

<a id="pdf-9e7f32f1b854-p061-b002"></a>
<!-- pdf-source: page=61; block=2; confidence=0.95 -->

**Section 4.3, why the chain is acyclic (pp. 51–52).** The length of the public key in
$\mathcal E^{(d)}$ is proportional to $d$ (the depth of the circuits that can be evaluated).
It would be preferable to have a construction $\mathcal E^*$ where the public key size is
completely independent of the circuit depth, a construction that is fully homomorphic
rather than merely leveled fully homomorphic. Here is the obvious way to make the public
key $\mathrm{pk}^*$ of $\mathcal E^*$ short: for $\mathcal E$ key pair
$(\mathrm{sk},\mathrm{pk})$, $\mathrm{pk}^*$ includes only $\mathrm{pk}$ and (the "bits"
of) $\mathrm{sk}$ encrypted under $\mathrm{pk}$. In other words, we have a cycle (in fact,
a self-loop in this example) of encrypted secret keys rather than an acyclic chain. It is
clear that $\mathcal E^*$ is correct: the recursive algorithm
$\mathsf{Evaluate}_{\mathcal E^*}$ works as before, except that the implicit recryptions
generate "refreshed" ciphertexts under the same public key.

**Why didn't we present this construction in the first place? Using an acyclic chain of
encrypted secret keys allowed us to base the security of $\mathcal E^{(d)}$ on
$\mathcal E$ using a hybrid argument; this hybrid argument breaks down when there is a
cycle.** In general, a semantically secure encryption scheme is not guaranteed to be
KDM-secure – i.e., secure when the adversary can request the encryptions of key-dependent
messages, such as the secret key itself.

<a id="pdf-9e7f32f1b854-p062-b001"></a>
<!-- pdf-source: page=62; block=1; confidence=0.95 -->

**Remark 4.3.1 (p. 52).** Canetti [27] proposed the acyclic, leveled approach as a way to
remove the need for KDM-security. Our initial approach had actually been to use
$\mathcal E^*$ (with the self-loop), and assume, or try to prove, KDM-security.

## ===== briefs/lattice-gsw/phase6/plan-section.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

# Proposed plan section: GSW phase 6, bootstrapping to FHE with a polynomial modulus-to-noise ratio (BV14 route)

**Revision r3 (2026-11-16): all rulings applied; the 6a statement phase is issued from it.** r1 was drafted overnight,
before Seyoon's rulings (`briefs/pass-shelat-ch5-8/overnight-2026-11-16.md`, item 7). r2 applied P6-Q1 to P6-Q13 and the
location ruling. r3 applies P6-Q14 to P6-Q19 and Seyoon's update to P6-Q19 (Gen09 blocks nothing). All rulings, the Q19
refinement included, are in [rulings.md](rulings.md) and are binding. This is proposed text for
`LatticeCryptographyPlan.md`; the plan itself is not edited. No Lean was written or elaborated, so every statement below
is a sketch for the statement phase. Paths are relative to `TCSlib/` unless stated otherwise. Line references are to the
records head `f6f295a6502b72bbf498bb8c64b63f847e910866`, the 6a issue base, whose Lean equals r2's
`99eae2c1550ee0b0485f115bca76b254dae25064` (the merged #327/#324 state).

Companion files:
- `rulings.md`: the rulings applied here. `questions.md`: the ruled questions P6-Q1 to P6-Q19.
- §H9 below: the questions P6-Q14 to P6-Q19, now ruled, with the option taken.
- Sources: the DW-7 ingests under `blueprint/src/references/` (§H1). Citations use `[TAG, location, anchor]`, where
  the anchor is the ingest's block id without its per-source prefix (§H1 lists the prefixes). For example,
  `[BV14, Thm 3.5, p014-b001]` is `brakerski-vaikuntanathan-2014-fhe.md#pdf-eab2d1667a8e-p014-b001`.

**What r3 changes** (the ruling in brackets):
1. **Consecutive key chain over layered circuits** [P6-Q14 B]. `evk_d` encrypts under `pk_d` the `N` key bits of
   `s_{d−1}`, `N·L` ciphertexts in all (§H3.11). 6a gains the unit U7, a generic **layering conversion**
   `DAGCircuit.layerNAND` in the new `Complexity/CircuitComplexity/NANDLayering.lean`, beside the NAND conversion
   (§H3.13, §H5.6b): double-NAND identity chains, a parity twin for odd gaps, and literal inputs at level 0.
   - **Finding (odd gaps).** A layered NAND circuit whose inputs are positive variables at level 0 computes a
     monotone function at even depth and an antimonotone one at odd depth (induction over the levels: the NAND of
     antimonotone functions is monotone, and conversely). So XOR has no such circuit, and no padding can fix an odd
     gap in general. The conversion therefore reads the `2n` **literals** `x, ¬x` at level 0, which is Bar89's
     "inputs and negated inputs" (§H3.13). In 6b the negative literals are `homNot`, `G − C`: free, under the same
     key and with the same noise.
   - Consequence in 6b: both arguments of a gate now sit under the same key, so the augmented NAND formula has
     **one** key block, BV14's `f_{c₁,c₂}` literally (G7, G9). r2's two-block deviation is withdrawn.
2. **Per-distinguisher concrete `WeakCircularSecure P χ D ε`**, with the asymptotic `WeakCircularSecureFamily` as
   the headline hypothesis [P6-Q15 A] (§H3.12, §H5.12).
3. **NAND form, registry rows and Thm 2's circuit, as ruled** [P6-Q16 A, P6-Q17 A, P6-Q18 A]: the text below states
   them as ruled, not proposed.
4. **Gen09** [P6-Q19 B, with Seyoon's update of 2026-11-16]. The leveled-bootstrapping passage of [Gen09] is to be
   ingested; Seyoon sends the PDF. It blocks nothing: the 6b leveled statements proceed now and cite only ingested
   sources, [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3]. Each such docstring
   states that the key-chain construction and the hybrid order are reconstructed and that the Gen09 passage will be
   cited once ingested. The docstring-only follow-up is recorded in §H10. 6a is unaffected.
5. **Units renumbered.** The layering unit is U7, so r2's U7–U18 are r3's U8–U19 (§H7). Totals, gates and risks are
   updated.

**What r2 changed** (kept for the record; the ruling in brackets):
1. One phase 6 with statement gates **45** (6a) and **46** (6b); the quasi-polynomial route is dropped [P6-Q1].
2. Barrington in both directions, BWBP = NC¹, including Thm 2 with its composition-tree circuit [P6-Q3].
3. The general branching-program model of Bar89 §1 (maps `[w] → [w]`) with an `IsPermutation` predicate [P6-Q4].
4. Bootstrapping is NAND only, literally BV14 Def 2.13, through a new `DAGCircuit`-to-NAND conversion [P6-Q9].
5. Concrete **and** asymptotic `WeakCircularSecure` and IND-CPA, with an explicit reduction-efficiency
   hypothesis [P6-Q10].
6. The full leveled scheme: `L+1` keys, correctness, and IND-CPA by a key hybrid from DLWE [P6-Q11].
7. Branching programs, Barrington and the NAND conversion live in `Complexity/` [location ruling]; the formula
   layer in `Complexity/CircuitComplexity/FormulaArith/` [P6-Q6]; `decode_iff_mem_Ico` in `LWE/BitEncoding.lean` by
   an owner-side PR [P6-Q7].
8. Two path adjustments, with reasons in §H4: a fifth branching-program file `NC1.lean`, and a facade for
   `FormulaArith/`.

Unchanged from r1, as ruled: P6-Q2 (`TreeCircuit` input), Q5 (formula-arithmetic layer), Q7, Q8 (evaluation key),
Q12 (ratio statements) and Q13 (computable `barrington`). r2's item 4 is refined by P6-Q16, its item 5 by P6-Q15,
and its item 6 by P6-Q14 (r3's items 1–3).

---

## H0. Scope, numbering and ownership

**Goal.** Pure (non-leveled) and leveled fully homomorphic encryption from LWE with a **polynomial**
modulus-to-noise ratio, following [BV14, §3] and cross-checked against [AP14, §4–5].

*Complexity layer (6a, Gate 45):*
1. **Barrington, both directions.**
   - Thm 1 with Lemmas 1–3: a fan-in-2 AND/OR formula of depth `d` (negations at the inputs) is five-cycle
     recognized by a width-5 permutation branching program (PBP) of length at most `4^d`
     [Bar89, Thm 1, p003-b002; BV14, Thm 3.5, p014-b001].
   - Thm 2: a width-`w` branching program of length `l` is recognized by a fan-in-2 circuit of depth `O(log l)`,
     the constant depending on `w` [Bar89, Thm 2, p004-b003].
   - Hence BWBP = nonuniform NC¹ = languages of polynomial-length 5-PBPs [Bar89, Corollary, p004-b004].
2. **NAND conversion.** Every `DAGCircuit` with fan-in at most two becomes a NAND-form circuit computing the same
   function, with depth at most twice the original and size linear in the number of gates.
   - **Layering conversion** (P6-Q14). Every NAND-form circuit on `n ≥ 1` inputs becomes a **layered** NAND-form
     circuit on the `2n` literals, of the same depth and function, with every gate exactly one level above each
     vertex it reads. Uneven paths are padded by double-NAND identity chains; odd gaps by a parity twin (§H3.13).
3. **Formula arithmetic.** A shared layer over `TreeCircuit` for the decryption formula: De Morgan negation,
   substitution, `xor3`/`maj3`, carry-save reduction, carry-out comparison, modular interval sum.

*Cryptography layer (6b, Gate 46):*

4. **Homomorphic PBP evaluation.** One selector step per instruction costs an **additive** `2Nβ`
   [BV14, Eq. (4)–(6), Lemma 3.6, p014-b002, p015-b001; AP14, Eq. (4.1), Lemma 4.1, p011-b001, p012-b001].
5. **Decryption formula** of depth `O(log N + log log q)` for public-key GSW
   [BV14, Prop 3.4, p011-b001; BV11, Lemma 4.5, p029-b001].
6. **NAND-only bootstrapping.** Every gate of a NAND-form circuit is evaluated by homomorphically evaluating BV14's
   augmented decryption function `f_{c₁,c₂}` on the evaluation key of P6-Q8
   [BV14, Def 2.13, Thm 2.14, p008-b002, p008-b003; BV11, Defs 3.7–3.8, Thms 3.1–3.2, p014-b002, p015-b001]. The
   output noise is a fixed bound independent of the circuit, so correctness holds for circuits of **every depth**.
7. **Leveled FHE.** `L+1` keys in a consecutive chain (`evk_d` encrypts the bits of `s_{d−1}` under `pk_d`, `N·L`
   ciphertexts; P6-Q14), correctness for layered NAND circuits of depth at most `L`, and IND-CPA by a hybrid over
   the keys from DLWE [BV14, Thm 2.14 first part, Thm 3.7, p008-b003, p016-b001; BV11, Thm 3.1, Def 3.6, p015-b001,
   p014-b001; AP14, §5.3, p015-b002]. It is the FHE statement that needs no circular-security assumption. The key
   chain and hybrid order are reconstructed (§H1 gap 1); [Gen09] is cited once ingested (P6-Q19).
8. **Security.** For pure FHE, statements under an explicit weak-circular-security hypothesis [BV11, Def 3.8; BV14, Thm
   2.14; Pei16, §6.1.2, p068-b001]: the asymptotic `WeakCircularSecureFamily` is the headline, and the concrete form is
   per distinguisher, `WeakCircularSecure P χ D ε` (P6-Q15). Asymptotic IND-CPA of the `evk`-free view and of the
   leveled scheme from `LWE.DLWEAssumption`, under an explicit reduction-efficiency hypothesis.
9. **Polynomial ratio.** The ruled `RatioBounded F B p` (phase-5 Q16) and a family theorem with an explicit
   `PolyExpr` `pBoot` (P6-Q12).

**Numbering** [P6-Q1]. One phase 6 merges the roadmap's phases 6 and 7. It has two statement gates: **Gate 45** for 6a
(branching programs, Barrington in both directions, the NAND and layering conversions, formula arithmetic) and **Gate
46** for 6b. Gates 42–44 are taken; 45 and 46 replace r1's provisional 42 and 43. The quasi-polynomial instantiation
is dropped.

**Assumptions.**
- (A1) Weak circular security of public-key GSW for its own key bits. It is an explicit hypothesis (phase-5 Q15),
  asymptotic as the headline and concrete per distinguisher (P6-Q10, P6-Q15), never derived from LWE, and used only
  by the pure-FHE security statements.
- (A2) DLWE for a family whose ratio `q/B` is polynomially bounded: the existing `LWE.DLWEAssumption`, unchanged
  (phase-5 Q16).
- (A3) Small-secret LWE is **not** needed; the BV14 route uses the uniform-secret `DLWEAssumption` (rulings
  addendum: A3 is assumed only where used; here it is unused).
- (A4) **Reduction efficiency** (new, P6-Q10): an explicit `Prop` per LWE family stating that the encryption
  reductions are realized by non-uniform PPT machines (§H5.16). It is not an LWE variant. It replaces a
  machine-level GSW encryptor, which stays out of scope. Only the asymptotic IND-CPA theorems use it.

**In scope:** items 1–9; the `DAGCircuit` corollary of Thm 1 (length `≤ 4^depth`); the language classes `BWBP`
and `PBP₅` with `BWBP = NC¹ = PBP₅`; the layering conversion (item 2); compactness by typing (docstrings, no
theorem).

**Out of scope:**
- Gaussian or subgaussian noise, the randomization procedure `Rand` [BV14, §2.4], and randomized `G⁻¹`
  [AP14, Claim 3.1].
- Worst-case lattice reductions and approximation factors. [BV14, Thm 1.1, Cor 4.5] and [AP14, Thm 5.1] are context
  only.
- Dimension-modulus reduction [BV14, §4; BV11].
- Machine efficiency of `Eval` and of GSW encryption. There is no `BitPublicKeyScheme` instance, so the
  reduction-efficiency hypothesis (A4) stays a hypothesis.
- The AP14 accumulator route (phase-5 Q12) and the quasi-polynomial instantiation (P6-Q1).
- From Bar89: uniformity (Bar89 §6), width-4 circuits and the word problem (abstract only), and the traditional
  rectangular branching-program model (Bar89 §1, p002-b001).

**Ownership.** The maintainer runs the phase on `cryptography/pass-shelat-ch2-4`. Lean changes go by PR; Seyoon
approves and merges. Codex audits (standing ruling). The 6a statements go to an external Claude session that Seyoon
dispatches (ruling of 2026-11-16, `PassShelatChapter5-8Plan.md`); the maintainer stages the issue package from this
revision, then reviews and lands the delivery.

## H1. Sources (DW-7 ingests)

Each ingest is a scoped raw file (`.raw.md`) plus a LaTeX transcription (`.md`) with proofmatch anchors; the tags
are registered in `blueprint/src/references/sources.json`. PDFs are not committed (DW-7). Matching against the
blueprint waits for an approved proofmatch run.

| Tag | Ingest key | Anchor prefix | SHA-256 of the upload |
|---|---|---|---|
| Bar89 | `barrington-1989-bounded-width-bp` | `pdf-06fd3eeccecf-` | `06fd3eec…7831` |
| BV14 | `brakerski-vaikuntanathan-2014-fhe` | `pdf-eab2d1667a8e-` | `eab2d166…12ca` |
| BV11 | `brakerski-vaikuntanathan-2011-fhe` | `pdf-d3e95f9b9e01-` | `d3e95f9b…0b00` |
| AP14 | `alperin-sheriff-peikert-2014-bootstrapping` | `pdf-cecd346d2e87-` | `cecd346d…c0da` |
| GSW13 | `gentry-sahai-waters-2013-fhe` | `pdf-8edb94cfd852-` | `8edb94cf…bf00` |
| Pei16 | `peikert2016-lattice-survey` (extended) | `pdf-1a9802b66031-` | `1a9802b6…7488` |
| Gen09 | pending (P6-Q19 B): Gentry's leveled-bootstrapping passage (thesis or STOC 2009) | — | PDF pending |

**Gen09** (P6-Q19 B, with Seyoon's update of 2026-11-16). The passage is to be ingested when Seyoon sends the PDF.
It blocks nothing. Until it is ingested no Lean docstring cites `[Gen09]`, because tags must resolve to ingested
sources; the leveled-scheme docstrings cite [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and
[AP14, §5.3] and disclose the reconstruction (gap 1). Adding `[Gen09, loc]` afterwards is a docstring-only
follow-up (§H10).

Passages ingested (unchanged from r1):
- **Bar89** (JCSS 38(1):150–164, 15-page scan, read from page images): abstract, §1, and §3 (five-cycle
  recognition, Thm 1, Lemmas 1–3, example, proof of Thm 1, Thm 2 with its proof, Corollary).
- **BV14** (ePrint 2013/541, 21 pp.): fn. 1, Thm 1.1, §2.3, §2.5 (Defs 2.12–2.13, Thm 2.14), all of §3, Lemma 4.4,
  Cor 4.5.
- **BV11** (FOCS 2011 full version, 39 pp.): §3.1 (Defs 3.1–3.6), §3.2 (Def 3.7, Thms 3.1–3.2, Def 3.8, Lemma
  3.3), §4.5 (Lemma 4.5 with proof, Lemma 4.6, Cor 4.7).
- **AP14** (ePrint 2014/094): §2.2, §3, §4.1–4.2, §5.1–5.3. **GSW13** (ePrint 2013/340): §1.2, §1.3.1–1.3.4,
  §2.3, §3.1–3.4. **Pei16**: extended with §5.4.3, §6.1.2 and §6.1.3.

**Does the Barrington ingest cover Thm 2? Yes.** Block `p004-b003` (printed p. 153) transcribes the statement and
the whole proof. The proof is the paper's single paragraph: represent a map `[w] → [w]` by `w²` Boolean variables
"`f(i) = j`", a constant-depth section per instruction, a binary tree of composition circuits, and a
constant-depth acceptance section at the top. The Corollary (`p004-b004`), the recognition notion (`p001-b002`,
`p002-b001`) and the abstract (`p001-b001`) are also present. Nothing on Thm 2 is missing. Two adjacent items are
not ingested and are not needed for any citation below:
- the bibliography entries [22] and [30], which Thm 2's preamble names for the uniform case (the reference list at
  the end of the paper is not transcribed);
- §2 and §4–§6.

No page needs to be added for Thm 2.

**Gaps found in the sources (no citation is invented for them):**
1. **The leveled key chain.** [BV11, Thm 3.1, p015-b001] and [BV14, Thm 2.14 first part, p008-b003] state the
   leveled theorem. [BV11, Thm 3.1] adds that "only the length of the evaluation key depends on the level L".
   [AP14, §5.3, p015-b002] gives the independent-keys security argument. No ingested passage gives the key-chain
   construction or its hybrid; Gentry's [Gen09] is cited by both papers and is to be ingested (P6-Q19 B). Until
   then the leveled docstrings state that the construction and hybrid order are reconstructed.
2. **NAND conversion.** No ingested passage states that `{NAND}` is a complete basis or gives a conversion. The
   conversion is glue, motivated by [BV14, Def 2.13, Thm 3.5] ("Every Boolean NAND circuit"). AB09's ingest covers
   chapters 7 and 13 only, and nothing there concerns NAND.
3. **AB09 §6** (Defs 6.1, 6.24) is cited by existing docstrings (`DAGCircuit.lean`, `NCAC.lean`) and is not
   ingested. This plan adds no new AB09 citation.
4. **Layering** (new in r3). No ingested passage defines layered circuits or a layering conversion. [BV11, Def 3.6,
   p014-b001] speaks of "depth-`L` binary arithmetic circuits" and [BV11, Thm 3.1, p015-b001] of an evaluation key
   whose length depends on `L`; the conversion is glue motivated by them (§H3.13).

**Record points from r1 (unchanged; nothing here edits them):**
1. BV14's "[BV11, Lemma 4.1]" (Prop 3.4) is **Lemma 4.5** in the BV11 version held. Docstrings cite
   [BV11, Lemma 4.5] and note BV14's numbering.
2. (Pairings) BB04's §3.1 Decision-BDH advantage has an absolute value on the page images;
   `PairingCryptographyPlan.md`, "Where the papers' formulations differ", item 6, says otherwise.

**Anchors used below:**
- **Bar89.** Abstract `p001-b001`; §1 instructions, yield and recognition `p001-b002`; PBP and BWBP `p002-b001`;
  five-cycle recognition `p003-b001`; Thm 1 `p003-b002`; Lemmas 1–3 `p003-b003`, `p003-b004`, `p003-b005`;
  example `p004-b001`; proof of Thm 1 `p004-b002`; Thm 2 with proof `p004-b003`; Corollary `p004-b004`.
- **BV14.**
  - Fn. 1 (leveled vs pure) `p001-b001`; §2.5 ("adversary is given both pk and evk") `p007-b001`;
    Def 2.12 `p008-b001`; Def 2.13 `p008-b002`; Thm 2.14 `p008-b003`.
  - Security of NCCrypt and Prop 3.4 `p011-b001`; PBPs and Eq. (4) `p013-b002`; Thm 3.5 `p014-b001`;
    Eval and Eq. (5)–(6) `p014-b002`.
  - Lemma 3.6 `p015-b001`, its proof `p015-b002`; Thm 3.7 `p016-b001`; Lemma 4.4 `p019-b001`.
- **BV11.** Def 3.1 (CPA with `evk`) `p013-b002`; Def 3.2 (`(t, ε)`-CPA) `p013-b003`; Defs 3.4–3.6 `p014-b001`;
  Def 3.7 `p014-b002`; Thms 3.1–3.2, Def 3.8, Lemma 3.3 `p015-b001`; Lemma 4.5 `p029-b001`, its proof `p029-b002`.
- **AP14.** Lemma 3.5 `p010-b001`; Cor 3.6 `p010-b003`; Eq. (4.1) `p011-b001`; Lemma 4.1 `p012-b001`;
  §5.1 `p013-b001`, `p014-b001`; §5.3 `p015-b002`.
- **GSW13.** §3.2 security `p009-b002`; Lemma 1 `p010-b001`; §3.4 bootstrapping `p012-b002`.
- **Pei16.** §5.4.3 `p052-b001`, `p053-b001`; §6.1.2 `p068-b001`; Eq. (6.1.6) `p069-b001`; §6.1.3 bootstrapping
  `p070-b001`.

## H2. What the existing Lean already provides (reuse findings)

All references are `file:line` at the records head. "Reuse" means cite or consume. "Near-relative" means checked
and not reused, with the reason.

**Phase 5 (`Cryptography/AdvancedEncryption/Homomorphic/GSW/`).** The statements are merged (#332, #333). The fills
#339 (`gsw-core`) and #338 (`gsw-security`) passed Gate 43 (closed CLEAR); their merge waits for the combined build
(GS-01 is ruled). 6b cites the frozen phase-5 statements under the proved-modulo rule and merges after those fills.
- **Noise algebra** (`Noise.lean`): `Encrypts` :97; `Encrypts.mul` :181, whose noise `N·β₁ + |x₁|·β₂` makes a
  selector step additive; `.add` :139, `.sub` :154, `.sum` :164, `encrypts_gadget` :118, `encrypts_zero` :124;
  `nand`/`Encrypts.nand` :73/:210 is the leveled multiplicative NAND, not used by bootstrapping.
- **Scheme** (`Scheme.lean`): `secretVector` :66, `encrypt` :90, `decrypt` :129, `encrypts_encrypt` :147,
  `encrypts_keygen_encrypt` :160, `decrypt_of_encrypts` :181. **Gadget** (`Gadget.lean`): `Parameters` :59,
  `Ciphertext` :78, `gadget` :90, `decomposeVec` :112, `gadget_mulVec_decomposeVec` :163.
- **Circuit evaluation** (`Eval.lean`): `homGate` :96, `eval` :122, `eval_encrypts` :180, on the `runWith` host;
  `fheEval` mirrors it.
- **Security** (`Security.lean`): `view` :58, `realView` :76, `reduction` :112, `distAdv_encrypt_le` :189,
  `distAdv_encrypt_le_of_width` :205. These are the base of G15, of the leveled hybrid and of the asymptotic forms.

**Complexity layer: model, conversions, classes.** No branching-program, Barrington, permutation-program or NAND
material exists. Searches for `branching`, `Barrington`, five-cycle and NAND found only the items below.
- **Formula model** (`CircuitComplexity/Basic.lean`): `Lit` :103, `TreeCircuit` :122, `TreeCircuit.ind` :130,
  `eval` :144, `eval_node_true_iff`/`_false_iff` :155/:163, `depth` :176, `maxFanin` :194,
  `depth_node`/`maxFanin_node` :213/:223, and `size_succ_le_two_pow` :313, which gives polynomial formula size from
  logarithmic depth (used by Thm 2).
- **Name clash, not reusable:** `NAndCircuit` (`Basic.lean:356`) and `TreeCircuit.toNAnd` (:465) are the
  **AND-rooted alternating normal form** of the LMN development, not NAND gates. The new names avoid `NAnd`
  (`IsNANDForm`, `toNANDForm`, `DAGGate.IsNAND`), and the docstrings cross-reference the old ones.
- **DAG model** (`DAGCircuit.lean`): `DAGGate.eval` :123 and `eval_eq` :131. A `¬` gate evaluates to the
  **negated conjunction** of its arguments, so a `¬` gate with two arguments is natively a NAND gate (P6-Q16).
  Also `runWith` :149, `DAGCircuit` :459, `IsWellFormed` :508 (requires `¬` gates of fan-in exactly 1),
  `IsFaninTwo` :512, `runWith_rel` :625, `constGate` :280, `DAGCircuitFamily` :681.
- **Gate-rewriting host** (`DAGTransform.lean`), reused by the NAND conversion: `GadgetSpec` :55,
  `GadgetCorrect` :68, `rewriteGates` :82, `DAGCircuit.rewrite` :246, `rewrite_eval` :263, `rewrite_depth_le` :269,
  `rewrite_new_gates` :273, `rewrite_length_le` :278, `sum_cost_le` :286. Its two instances are the models for the
  NAND gadget (`DAGFanin.lean`): `deMorganGadget` :475 with `deMorganGadget_correct` :499 and `deMorgan_*`
  :603–636; `emitNots` :384; `GateKind.op` :49; `DAGGate.eval_pair` :65; `binarize` :347.
- **Tree ↔ DAG** (`TreeDAG.lean`):
  - `TreeCircuit.toDAG` :349 with `toDAG_eval` :357, `toDAG_size_le` :363, `toDAG_depth_le` :368 and
    `toDAG_isFaninTwo` :378 (the route from Thm 2's formula to NC¹);
  - `DAGCircuit.toTree` :404 with `toTree_eval` :594, `toTree_depth_le` :623 and `toTree_maxFanin_le` :645
    (Barrington's `DAGCircuit` corollary).
  - Near-relative: `unfoldGate` :388 pushes negations by De Morgan, but on DAG input, so it is not a
    tree-to-tree `neg`.
- **Classes** (`NCAC.lean`, `TreeNCAC.lean`): `Language.InNC` NCAC:55, `Language.InTreeNC.inNC` :149,
  `Language.InNC.inTreeNC_one` :194, `Language.inNC_one_iff` :229; `TreeCircuitFamily` TreeNCAC:90,
  `HasPolylogDepth` :121, `Language.InTreeNC` :130. Both Barrington directions go through `inNC_one_iff`.
- **Balanced fan-in-2 gate:** `combine` (**private**, TreeNCAC:252; `pairUp` :175, `combineFuel` :245;
  `combine_eval`/`_maxFanin`/`_depth`/`_size` :332–351, depth `maxDepth + ⌈log₂ k⌉ + 1`). It is promoted by
  owner-side PR O1 (P6-Q6). `TreeCircuit.toBinary` (:353) is public but rebuilds every child, and its depth bound
  `toBinary_depth_le` (:442) is multiplicative, so it cannot replace `combine`.
- **Dual-rail XOR:** `xorNode`/`IsDual` (**private**, `Parity.lean:60/65`). They are re-pointed to the public
  `neg`/`xor2` later, on the dedup queue (P6-Q6).
- **Number semantics** (`Adder.lean`): `bitsVal` :78, `prefixVal` :82, `prefixVal_lt` :101,
  `bitsVal_eq_prefixVal` :136, `carryBit` :377, `sumBit` :382, `prefixVal_add` :397 (ripple-carry correctness).
  F5–F8 state their semantics through these, and F7's carry-out is exactly `carryBit` at position `b`.
  `fullAdderGates`/`adderGates` are linear-depth DAG adders and are not used.
- **Near-relatives checked and not reused:**
  - `Complexity.BinArith.carry`/`sumBit` (`ClassP/BinaryArith/AddSub.lean:49/52`, with `serial_add` :62) are the
    Boolean full-adder functions. They are not imported: that would pull polynomial-time machinery into the formula
    layer. `maj3`/`xor3` state the same functions with Bool operations.
  - `FormulaKit/Gate.lean` (`template` :90, `gate` :142; P6-Q6 asked for this check) builds truth-table CNF
    templates over `Std.Sat.CNF ℕ`. It is a different model, and generic truth-table gadgets over `log q`-bit values
    are excluded by §H3.3.
  - Also: `dnfDAG` (`BookModelBasics.lean:406`, same exclusion); `stdGateOps` (`LayeredCircuit.lean:115`) and
    `SLOp` (`StraightLine.lean:87`), whose bases are `{id, ¬, ∧}` and `{∧, ∨}` (no NAND); `Formulas.lean`'s
    `CNF`/`DNF`.
- **Permutations:** Mathlib `Equiv.Perm (Fin 5)`, `Equiv.Perm.cycleType`, `Equiv.ofBijective`.
- **Layering (r3, P6-Q14).** No layered predicate or depth-preserving layering exists for `DAGCircuit`.
  - Depth readers the conversion uses (`DAGCircuit.lean`): `depths_eq` :601, `depthAt_eq` :605, `depth_eq` :609,
    `depthAt_input` :542, `depthAt_gate` :557, `DAGGate.depth_eq` :571, `DAGGate.getD_lt_depth` :580,
    `values_getD_input` :536, `size_eq` :505; `GatesAcyclic` :395 with `.nil`, `.snoc`, `.append` :399–415.
  - **Near-relative, not reusable, name clash avoided:** `DAGCircuit.toLayered` (`LayeredDAG.lean:208`) and
    `TreeCircuit.toLayered` (:623) map into the other model `LayeredCircuit` (`LayeredCircuit.lean:54`) with one
    DAG vertex per layer, so their depth is the number of gates; they need `IsWellFormed` and no `∨` gate. The new
    conversion keeps the `DAGCircuit` model and its depth, and is named `layerNAND`, not `toLayered`.
  - Near-relative: `StraightLine.dualRail` (`StraightLineDualRail.lean:122`) simulates a DAG by straight-line
    programs with both rails; a different model, not reused. The new literal-input map `litInput` is one line.
  - 6b consumes the negative literals as `homNot P [C] = G − C` (`GSW/Eval.lean:78`, `homNot_eq` :82).
- **Rule 10 readers the 6a fills will need** (the statement phase records them in a reader census; §H5.8, §H8):
  - `TreeCircuit.eval` on nodes: `eval_node_true`/`eval_node_false` (`TreeDAG.lean:126/132`, equation form) and
    `eval_node_true_iff`/`_false_iff` (`Basic.lean:155/163`). The proofs that O1 moves read `TreeCircuit.eval` by
    `simp [TreeCircuit.eval]` at `TreeNCAC.lean:195`, `:199` and `:261`; O1 repairs these three reads through
    those readers, so a moved file passes its seal.
  - `GadgetCorrect` (`DAGTransform.lean:68`) has **no** `_iff` reader, and lint check 8 lists it. N2's proof
    must not unfold it, so a one-line owner-side reader `gadgetCorrect_iff` (`Iff.rfl`) is needed before the N2
    fill. It is a shared-file change for Seyoon's approval (§H8 item 16). `vertexValue`/`vertexDepth`
    (`TreeDAG.lean:53/57`) have readers (`_append`, `_last`, `_input` :63–102).

**Cryptography hooks for the new security statements.**
- `LWE.Family` (`LWE/Assumption.lean`), with `advantageAt` and `DLWEAssumption` (`dlweAssumption_iff`); its fields
  `dimensionBound`, `samplesBound`, `residueBits` and `modulus_le_pow` feed `Parameters.ofFamily`.
- `LWE.encodeChallenge` (`LWE/Encoding.lean:42`); `Encoding.Modular.encodeMatrix`/`encodeVector`
  (`Encoding/Modular.lean:65/51`); `NUPPT.distinguisherL` (`Asymptotic/Adversary.lean:351`).
- `Negligible.add`/`.mono`/`.mul_pow` (`Foundations/Negligible.lean:86/74/126`), `negligible_two_pow_neg` :153,
  `negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`).
- `distAdv_multi_le_sum` with `hybridPlant` (`Encryption/PublicKey/EnsembleSecurity.lean:134/110`) and
  `abs_sub_le_sum_hybrids` (`Foundations/Probability.lean:218`): the multi-ciphertext and key hybrids.
- `BitPublicKeyScheme.SingleBitSecure` (`EnsembleSecurity.lean:164`) is the machine-level bridge. It is **not**
  used: it needs GSW as a machine-level scheme (out of scope; §H8 item 13).
- `LWE/BitEncoding.lean`: `decode` :108 (`decode_eq` :112), `distance` :51, `codepoint` :42. Owner-side PR O2 adds
  the interval reader (P6-Q7).

**Registries.**
- `ComputationalModels.lean` has a **Models** list (each entry's defining file is imported) and a **Conversions**
  list (pointers only). `BoolCircuit.DAGCircuit.binarize`/`deMorgan` are listed there, so the NAND and layering
  conversions belong in Conversions.
- `machine-library-design.md` §14 (line 3037) is the host registry, rows H0–H17. The circuit hosts the phase consumes
  are public but not yet registered: `runWith`/`runWith_rel` (consumed by phase 5 and by `fheEval`) and
  `DAGCircuit.rewrite` (consumed by `binarize`, `deMorgan` and now the NAND conversion). P6-Q17 A rules that they
  are recorded as H19 and H20, beside H18 `BranchingProgram.evalWith` (§H4).

## H3. Design

**H3.1 The pipeline (NAND only).** `N = (n+1)ℓ` is the GSW ciphertext width, and `C₁, C₂` are the ciphertexts on
a NAND gate's two input wires.

```
nandFormula P C₁ C₂ : TreeCircuit N   -- ¬(Dec(C₁) ∧ Dec(C₂)); inputs: the N key bits
barrington (nandFormula …) σ : 5-PBP  -- length ≤ 4^(decDepth P + 1); complexity layer (6a)
homEvalPBP P B evk                    -- selector steps; noise (length)·2N·β_evk
bootNAND P evk C₁ C₂                  -- the coordinate σ 0 of the final state
fheEval P evk Cc cts                  -- Cc in NAND form; runWith over gates, each gate bootNAND evk
fheEvalCircuit P evk Cc hC cts        -- any fan-in-2 DAGCircuit: fheEval on Cc.toNANDForm hC (6a)
leveledEval P lk Cc cts               -- Cc layered NAND form on literals: gate at level d is bootNAND (lk d)
```
The bootstrapped noise `bootNoise P β = 4^(decDepth P + 1) · (2·(N·β))` does not depend on the input noise. So the
single invariant "encrypts its wire value with noise ≤ β*", with `2·(ℓ·β*) < ⌊q/2⌋`, carries through a
circuit of
any depth by `runWith_rel`. The formula reads **one** block of key bits: it is BV14's `f_{c₁,c₂}(x)` literally. r2
gave it two blocks so that the leveled scheme could bootstrap a gate whose arguments sit under different keys (r2's
P6-Q14 A). Under the ruled P6-Q14 B the circuit is layered, so both arguments of a gate at level `d` sit under
`s_{d−1}`, and one block serves
both schemes; the two-block deviation is withdrawn. The bootstrapping lemma keeps its key-switching form: `evk`
encrypts the bits of `s` under `t'`, and pure FHE is the case `t' = t` (G9).
**H3.2 Decryption as a binary modular subset sum** (unchanged). Phase-5 decryption reads the column
`c = C·G⁻¹(⌊q/2⌋·e_{n+1})` and outputs `decode(⟨t, c⟩)` with `t = (−s, 1)`. With
`x = G⁻¹(t) ∈ {0,1}^N`:

```
⟨t, c⟩ = ⟨G x, c⟩ = Σ_{i<N} x_i · a_i (mod q),   a = Gᵀ c  (public: depends only on C).
```

So decryption, as a function of the key bits, is `x ↦ decode((Σ x_i a_i) mod q)` [AP14, §5.1, p014-b001;
BV11, Lemma 4.5, p029-b002]. The key bits `keyBits P s := decomposeVec P (secretVector P s)` are what the
evaluation key encrypts (P6-Q8).

**H3.3 No depth term linear in `ℓ`** (unchanged). The bootstrapped noise is `4^d·2Nβ_evk` and must stay below
about `q/(4ℓ)`. A depth term `c·ℓ` would contribute `4^{cℓ} ≥ q^{2c}`. Hence:
- no Shannon or DNF construction (`dnfDAG`, FormulaKit templates) on `Θ(log q)`-bit values;
- rounding uses that `decode` is an **interval** test, `decode v ↔ v.val ∈ [lo, hi)` (O2);
- `S = Σ x_i a_i < N·q`, so `S mod q ∈ [lo, hi)` iff `⋁_{j<N} (jq + lo ≤ S < jq + hi)`. This is an OR of `N`
  two-sided comparisons with constants, each of depth `O(log b)` with `b = ℓ + ⌈log₂ N⌉ + 1`.

**H3.4 The formula-arithmetic construction** (unchanged; P6-Q5). Numbers are little-endian lists of formulas with
value `bitsVal (U.map (·.eval x))` (`Adder.lean:78`):
1. masked constants `x_i · a_i`, each bit a literal or a constant;
2. a carry-save (3:2) tree down to two numbers `U, W` with `U + W = S`: one `xor3`/`maj3` layer per level (depth
   +4), about `log_{3/2} N` levels;
3. `U + W ≥ c` as the carry-out of `U + W + (2^b − c)`: one more 3:2 layer, then a generate/propagate carry-out
   formula of depth `2⌈log₂(b+2)⌉ + 2`, whose value is `carryBit` (`Adder.lean:377`);
4. the interval and the OR over `j < N`, by balanced fan-in-2 nodes.

Negation is the depth-preserving De Morgan map `TreeCircuit.neg`. Draft depth target, with constants fixed at the
statement phase: `decDepth N ℓ ≤ 9·⌈log₂ N⌉ + 2·⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉ + 21`.

**H3.5 The branching-program model and its host** [P6-Q4].
- **Model.** An instruction is `⟨var, map0, map1⟩` with `map0 map1 : Fin w → Fin w`, applied as `map0` when the
  bit is `0` (BV14's order). Bar89 lists the `x_j = 1` map first; the docstring discloses this. `IsPermutation`
  says every map is a bijection. Recognition follows Bar89 §1: a family with accepting sets
  `F_n ⊆ (Fin w → Fin w)`.
- **Host `evalWith`, push form.** It is generic in the selector `sel : β → α → α → α` and in the value type
  `α` (an additive commutative monoid). One step sends `V` to

  ```
  V'_i = sel (inp var) (Σ_{j : map0 j = i} V_j) (Σ_{j : map1 j = i} V_j).
  ```

  - For **every** map the Boolean semantics hold: with `α = ℕ` and `sel b u v = if b then v else u`, a one-hot
    state stays one-hot at `yield x s` (C8). That is BV14 Eq. (4) generalized.
  - For a **permutation** instruction each sum has exactly one term. The step is then BV14's pull form
    `V'_i = sel x (V_{σ₀⁻¹ i}) (V_{σ₁⁻¹ i})` (C6), which is what GSW's additive noise needs.
  - The fold over instructions carries a step-indexed relational lemma `evalWith_rel` (C7). GSW instantiates it
    with `α = β = Ciphertext P` and `sel = select P`.
- **Why the push form.** A pull form needs inverses, which a general map lacks. The push form keeps the host total
  and computable on the general model (P6-Q13) and confines `IsPermutation` to the consumers that need it.
- **Selector.** With the fresh selector on the left (Gate 41: "fresh ciphertexts belong on the left"),
  `select P C U V := mul P (gadget P − C) U + mul P C V`. If `C` encrypts the bit `b` with noise `β`, and `U, V`
  encrypt bits with noise at most `β_V`, then `select` encrypts `(1−b)·u + b·v` with noise `β_V + 2Nβ`
  (`Encrypts.mul` twice, then `.add`).
- **Start state and growth.** The start state is `Pi.single 0 (gadget P)`: zero noise (AP14's "include `G`").
  After `L` permutation instructions every coordinate has noise `L·2Nβ`, the worst-case form of
  [BV14, Lemma 3.6, p015-b001].
**H3.6 Composition order** (unchanged in substance). Bar89 writes products left to right: the leftmost permutation acts
first. The model fixes **program order**: `yield (B₁ ++ B₂) x = B₂.yield x ∘ B₁.yield x`, which is function
composition on general maps. The AND step's yield, written in Mathlib's `Equiv.Perm` product (right factor first), is
`σ₂⁻¹ * σ₁⁻¹ * σ₂ * σ₁`; this is Bar89's `σ₁σ₂σ₁⁻¹σ₂⁻¹`. Checked by computation
for r2, 0-based:
- with `sigma1 = c[0,1,2,3,4]` and `sigma2 = c[0,2,4,3,1]`, the program-order commutator is `c[0,2,1,4,3]`, which
  is Bar89's `(13254)`;
- the right-to-left reading gives `c[0,3,2,4,1]`, Bar89's `(14352)`, as the ingest's transcription note says;
- the Lemma-1 conjugator `θ(σᵏ 0) = τᵏ 0` satisfies `θσθ⁻¹ = τ` for all 24 × 24 pairs of five-cycles.

**H3.7 Output convention** (unchanged). Five-cycle recognition with start state `0` ends in `σ 0 ≠ 0` on the
accepted set and in `0` off it. The output ciphertext is coordinate `σ 0`. BV14 reads coordinate 1; the deviation is
disclosed and harmless.

**H3.8 Evaluation key** (P6-Q8, as ruled). `evk_i = encrypt P pk (keyBits P s i) R_i`: public-key encryptions under
the user's own `pk` of the `N` bits of `G⁻¹(t)`, with noise `m·B` by `encrypts_encrypt`. This is [BV11, Def 3.8]'s
`{Enc_pk(sk[i])}_i`, and it keeps one `GSW.Parameters` record.

**H3.9 The NAND conversion** (new; P6-Q9, location ruling; representation as ruled by P6-Q16 A).
- **NAND form.** A NAND gate is the model's own `¬` gate of fan-in at most 2 (`DAGGate.eval_eq`: "negated
  conjunction"): `DAGGate.IsNAND g := g.kind = .not ∧ g.args.length ≤ 2`, and `IsNANDForm` holds when every gate
  is one.
  - Fan-in 1 is negation, `NAND(a) = ¬a`. Fan-in 0 is the constant `false`, because `NAND()` is the negation of
    the empty conjunction.
  - NAND-form circuits are **not** `IsWellFormed`, which demands fan-in-1 `¬` gates (disclosed). Lemmas that
    assume well-formedness (`toTree_eval`, `deMorgan_*`) are not needed on this side.
- **Conversion.** An instance of the existing host `DAGCircuit.rewrite`, with a gadget in the style of
  `deMorganGadget`:

  | old gate | NAND gadget | gates | depth added |
  |---|---|---|---|
  | `∧[a,b]` | `t := NAND[a,b]`, `NAND[t]` | 2 | 2 |
  | `∨[a,b]` | `NAND[a]`, `NAND[b]`, `NAND[¬a,¬b]` | 3 | 2 |
  | `∧[a]`, `∨[a]` | `NAND[a]`, `NAND[that]` | 2 | 2 |
  | `∧[]` (true) | `f := NAND[]`, `NAND[f]` | 2 | 2 (absolute) |
  | `∨[]` (false) | `NAND[]` | 1 | 1 (absolute) |
  | `¬[…]` (≤ 2 args) | copied | 1 | 1 |

  - Every gadget costs at most `fan-in + 2` gates and at most 2 levels, so
    `GadgetCorrect n 2 (fun _ l => l ≤ 2) DAGGate.IsNAND (nandGadget n)` holds and
    the pass's lemmas give semantics, depth `≤ 2·depth` and size `≤ n + 4·#gates`.
  - The domain is the phase-5 hypothesis `∀ g ∈ C.gates, g.args.length ≤ 2`, not `IsFaninTwo`. A `¬` gate of
    fan-in 2 is already a NAND gate and is copied.
- **Bootstrapping.** Each NAND gate goes through BV14's binary `f_{c₁,c₂}`. Fan-in 1 is padded to `(a, a)`
  (`NAND(a, a) = ¬a`), and fan-in 0 to `(G, G)`, since `G` encrypts `1` with zero noise and `NAND(1, 1) = 0`.
  Disclosed.

**H3.10 Thm 2: the composition-tree circuit** (new; P6-Q3; circuit model as ruled by P6-Q18 A). Thm 2 is built as
a fan-in-2 **formula** (`TreeCircuit`) that mirrors the proof in [Bar89, Thm 2, p004-b003] section by section:
- *constant-depth section per instruction:* the wire "`ι` sends `i` to `j`" is `true`, `false`, `x_var` or
  `¬x_var` (depth ≤ 1);
- *composition circuit:* from the wires of `f` and `g`, the wire `(g ∘ f)(i) = k` is `⋁_j (f(i)=j ∧ g(j)=k)`, a
  balanced fan-in-2 OR (depth `+⌈log₂ w⌉ + 2`), using the promoted `balanced` (O1);
- *binary tree of composition circuits* over the instruction list (split at the midpoint): depth
  `(⌈log₂ w⌉ + 2)·⌈log₂ l⌉ + 1`;
- *constant-depth acceptance section:* `⋁_{f ∈ F} ⋀_i (B(x)(i) = f(i))`, at most `w^w` terms.

The formula has size `l^{O(log w)}`, polynomial for fixed `w`, by `size_succ_le_two_pow`. The family form then
reaches the book's `DAGCircuit` classes through `Language.InTreeNC.inNC`. A direct DAG construction sharing
composition subcircuits was the alternative, not taken (P6-Q18 B). `toFormula` need not be computable: P6-Q13
covers only `barrington`.

**H3.11 The leveled scheme** (new; P6-Q11; wiring as ruled by P6-Q14 B).
- **Keys.** `L+1` independent honest key pairs `(pk_d, s_d)`, `d ≤ L`.
- **Evaluation key: the consecutive chain.** For `1 ≤ d ≤ L`, `evk_d` holds the encryptions under `pk_d` of the
  `N` key bits of `s_{d−1}` (bits of `G⁻¹(t_{d−1})`, as in P6-Q8). That is `N·L` ciphertexts, and only the
  evaluation key depends on `L` [BV11, Thm 3.1, p015-b001].
- **Circuits are layered.** The scheme evaluates a NAND-form circuit that is layered on the `2k` literals (§H3.13):
  every gate at level `d` reads only vertices at level `d − 1`, and the literals are at level 0.
  - Level 0 holds the fresh encryptions `cts j` under `pk_0` and their negations `homNot P [cts j] = G − cts j`,
    which encrypt `¬x_j` under the same key with the same noise (`Encrypts.sub`, `encrypts_gadget`): no
    bootstrapping and no key change.
  - A gate at level `d` is `bootNAND P (evk_d) C₁ C₂` (§H3.1): both arguments are under `s_{d−1}`, `evk_d`
    encrypts `s_{d−1}`'s bits under `pk_d`, so the output is under `s_d` (G9's key-switching form).
  - A general fan-in-2 `DAGCircuit` of depth `L'` is first converted to NAND form (depth `≤ 2L'`, N5) and then
    layered (depth unchanged, N10), so it needs `L = 2L'` levels, `2L' + 1` keys.
- **Evaluation.** `runWith` over the gates of the layered circuit, with `lk = (evk_d)_d`; the level of a gate is
  `depthAt` (`DAGCircuit.depthAt_gate`), and N8 guarantees that its arguments are one level down.
- **Correctness.** Every vertex at level `d` encrypts its value under `s_d` with noise at most
  `max(m·B, bootNoise P (m·B))`, whatever the circuit, so a layered NAND circuit of depth at most `L` decrypts
  correctly under `s_{depth}`.
  - The output's key index is the circuit depth, which is public. This is disclosed: BV11 Def 3.6's `Dec` is
    level-agnostic.
- **Security** (IND-CPA from DLWE). The hybrid runs from the top level down. At step `d = L, …, 1` the `N`
  encryptions under `pk_d` (the bits of `s_{d−1}`) are replaced by encryptions of `0`. This is legitimate because
  `s_d`'s bits occur only in `evk_{d+1}`, already replaced (and `s_L`'s nowhere). A final phase-5 step handles the
  challenge under `pk_0`, whose secret `s_0` occurs only in `evk_1`. Each step is a multi-ciphertext hybrid over
  `N` positions (`distAdv_multi_le_sum`) over phase-5 `distAdv_encrypt_le`; the independent-keys argument is
  [AP14, §5.3, p015-b002].
- **Sources** (P6-Q19 B, Seyoon's update). The docstrings cite [BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first
  part, Thm 3.7] and [AP14, §5.3], and state that the key-chain construction and the hybrid order are
  reconstructed, with the Gen09 passage cited once ingested (§H1, §H10). The statements do not wait for Gen09.

**H3.12 Security statements: concrete and asymptotic** (new; P6-Q10; concrete form as ruled by P6-Q15 A).
- **Concrete, per distinguisher.** `fheView P χ μ = (pk, evalKey, encrypt pk μ)` [BV14, §2.5, p007-b001: "the
  adversary is given both pk and evk"]. For one distinguisher `D`,
  `WeakCircularSecure P χ D ε := distAdv (fheView P χ false) (fheView P χ true) D ≤ ε` (G14). The `evk`-free view
  inherits phase 5's bound (G15); the leveled view has its key hybrid (L5).
  - Why per distinguisher (P6-Q15): quantified over **all** function-level distinguishers the predicate would hold
    only for `ε` near `1`, since an unbounded distinguisher recovers `s` from `pk` and decrypts. The docstring says
    so, and points to the asymptotic form for content.
- **Asymptotic: the headline.**
  - Over an `LWE.Family F` with `P_κ = Parameters.ofFamily F κ` and canonical bit encodings of the views (built
    from `encodeChallenge` and `Encoding.Modular.encodeMatrix`):
    - `WeakCircularSecureFamily F`: every NUPPT distinguisher has negligible advantage on the encoded FHE views;
      this is [BV11, Def 3.8] with [BV11, Def 3.1], which are asymptotic. It is the headline hypothesis (A1);
    - the explicit hypotheses `ReductionEfficient F` and `LeveledReductionEfficient F L` (A4);
    - A1: asymptotic IND-CPA of public-key GSW (the `evk`-free view) from `DLWEAssumption F`, A4 and the width
      condition;
    - A2: the pure-FHE reading of `WeakCircularSecureFamily`;
    - A3: asymptotic IND-CPA of the leveled scheme from `DLWEAssumption F` and A4.
  - **No NUPPT-bridge extension is needed.** `DLWEAssumption`'s interface (`advantageAt`, `distinguisherL`) and
    the `Negligible` closures (`add`, `mono`, `negligible_two_pow_neg`, `negligible_polyExpr_mul`) suffice once A4
    supplies the reduction machines.
  - A4 is a domination statement (some NUPPT has at least the reduction's DLWE advantage), not a machine
    construction. For the leveled hybrid, "worst level and position" is realizable with non-uniform advice
    (§H8 item 13).

**H3.13 The layering conversion** (new in r3; P6-Q14 B; 6a, Gate 45; `NANDLayering.lean`, §H4).
- **Layered.** `DAGCircuit.IsLayered C`: for every gate `i` and every argument `a` of it,
  `C.depthAt a + 1 = C.depthAt (n + i)`. Inputs have depth 0 and fan-in-0 gates depth 1, so a layered circuit
  evaluates level by level.
- **Why literals at level 0 (the odd-gap finding).** Call a vertex's depth its level. In a layered NAND circuit
  whose only level-0 vertices are the positive inputs, induction on the level shows that every vertex at an even
  level computes a monotone function and every vertex at an odd level an antimonotone one (constants are both; the
  NAND of antimonotone functions is monotone, and conversely). XOR is neither, so no layering of NAND circuits
  over positive inputs exists in general: an odd gap cannot always be padded. With both literals `x_i`, `¬x_i` at
  level 0 every vertex is available at both parities, and the padding below works. Literal inputs are Bar89's
  "inputs and negated inputs" [Bar89, Thm 1, p003-b002] and cost nothing in GSW (§H3.11).
- **Construction** (computable, by columns in topological order; no NAND-form hypothesis). The new circuit has `2n`
  inputs, `litInput x = Fin.append x (fun i => !x i)`. Each old vertex `v` with `depthAt v = δ ≤ D := C.depth` gets
  a column of new vertices `v@k`, one for every level `δ ≤ k ≤ D`, with `v@k` at depth exactly `k`:
  - **base** `v@δ`: an input `x_i` is input vertex `i`; a gate is a NAND gate over its arguments' copies `a@(δ−1)`;
  - **parity twin** `v@(δ+1)` (the care for odd gaps): an input's twin is `NAND(¬x_i)`, reading input vertex
    `n + i`; a gate's twin is the same NAND gate over `a@δ`; a fan-in-0 gate's twin is `NAND(NAND(x₀, ¬x₀))`,
    which needs `n ≥ 1` (`[NeZero n]`, as Barrington's Thm 1);
  - **double-NAND chain** `v@k = NAND(NAND(v@(k−2)))` for `k ≥ δ + 2`, the inner gate at level `k − 1`.

  Every gate is emitted as a NAND gate (`⟨.not, args⟩`), so the definition needs no NAND-form hypothesis; the
  semantics and the NAND-form theorems take `C.IsNANDForm`. Old vertices deeper than `D` are dead and get no
  column. The output is `out@D`. The gate list and output index are definitions; the structure fields of
  `DAGCircuit` (acyclicity, output in range) are the targets N12–N13, as N2 is for `toNANDForm`.
- **Bounds.** `layerNAND C` has depth exactly `D` (N10). The column of `v` has at most `2(D − δ) + 1` gates, so the
  size is at most `2n + (2D + 1)·size C` (N11, *(fix)*).
- **Reuse.** It is not an instance of `DAGCircuit.rewrite`: the input count changes and depth must be exact, not
  bounded. It reuses the depth readers (§H2) and `GatesAcyclic.snoc`/`.append`. The column fold is a construction,
  not a host (its contract does not vary by consumer), so it is not registered in §14.

## H4. Modules, namespaces, registration and definitions

**6a: complexity (Gate 45).** The model type is at the root (registered); its operations live in its namespace.

| File | Content | Namespace |
|---|---|---|
| `Complexity/BranchingPrograms.lean` | facade (new topic) | — |
| `Complexity/BranchingPrograms/Defs.lean` | model, `IsPermutation`, `yield`, families, classes | `BranchingProgram` |
| `Complexity/BranchingPrograms/Eval.lean` | host `evalWith`, `evalWith_rel` | `BranchingProgram` |
| `Complexity/BranchingPrograms/Barrington.lean` | Thm 1, Lemmas 1–3 | `BranchingProgram` |
| `Complexity/BranchingPrograms/BarringtonConverse.lean` | Thm 2 for one program | `BranchingProgram` |
| `Complexity/BranchingPrograms/NC1.lean` | DAG corollary, class inclusions, Corollary | `BranchingProgram` |
| `Complexity/CircuitComplexity/NANDForm.lean` | NAND form and conversion | `BoolCircuit` |
| `Complexity/CircuitComplexity/NANDLayering.lean` | layered predicate, literal input, layering (r3) | `BoolCircuit` |
| `Complexity/CircuitComplexity/FormulaArith.lean` | facade (new sub-folder) | — |
| `…/FormulaArith/{Combinators,CarrySave,Compare,ModSum}.lean` | formula arithmetic | `BoolCircuit` |

**Path adjustments, and why:**
1. **`BranchingPrograms/NC1.lean`** (fifth child). The ruling put "Thm 1, Lemmas 1–3 and the NC¹ corollary" in
   `Barrington.lean` and Thm 2 in `BarringtonConverse.lean`.
   - The two-sided Corollary (BWBP = NC¹ = PBP₅) needs both theorems. `BarringtonConverse` imports `Barrington`, so
     the Corollary can only live downstream of both.
   - The class-level statements also put `Barrington.lean` near 1,000 lines (Thm 1 alone fills to about 550–720).
   - So the `DAGCircuit` corollary, NC¹ ⊆ PBP₅, BWBP ⊆ NC¹ and the Corollary go into `NC1.lean`, following
     `NCAC.lean`'s precedent of classes beside their theorems. `Barrington.lean` keeps Thm 1 with Lemmas 1–3.
2. **`CircuitComplexity/FormulaArith.lean`** (facade). Policy §1 gives every topic folder a facade with a
   `## Contents` list. `CircuitComplexity/` is flat today, so the new sub-folder needs one, imported by
   `CircuitComplexity.lean`.

3. **`CircuitComplexity/NANDLayering.lean`** (r3, P6-Q14), a sibling of `NANDForm.lean` rather than a part of it,
   chosen by file size and layering:
   - `NANDForm.lean` fills to about 300–400 lines (N1–N6). The layering adds a predicate, the column construction
     and N7–N13, about 120–180 statement lines and 150–250 fill lines, which would take one file to 600–800
     lines, past policy §1's 600-line target. Two files stay at about 300–450 each.
   - The layering needs `IsNANDForm`, so it imports `NANDForm.lean`; only 6b's leveled scheme consumes it, while
     pure FHE consumes `NANDForm.lean` alone.
   - The name says what it layers. `Layering.lean` would sit beside `LayeredCircuit.lean` and `LayeredDAG.lean`,
     whose `toLayered` maps into the other model (§H2); `NANDLayering` avoids that confusion.

`NANDForm.lean` and `NANDLayering.lean` sit beside `DAGTransform.lean`/`DAGFanin.lean`, under the location ruling.
Both are imported by `CircuitComplexity.lean`. `BranchingPrograms.lean` is imported by `TCSlib.lean` (policy §1,
Exports).

**Registration** (P6-Q4).
- `ComputationalModels.lean`, **Models:** `BranchingProgram w n` and `BranchingProgramFamily w`, importing
  `Complexity.BranchingPrograms.Defs`.
- **Conversions:**
  - `BranchingProgram.barrington` (formulas → 5-PBPs, `Barrington.lean`);
  - `BranchingProgram.toFormula` (programs → formulas, `BarringtonConverse.lean`);
  - `BoolCircuit.DAGCircuit.toNANDForm` (DAGs → NAND form, `NANDForm.lean`);
  - `BoolCircuit.DAGCircuit.layerNAND` (NAND form → layered NAND form on literals, `NANDLayering.lean`).
- `machine-library-design.md` §14, as ruled by P6-Q17 A: the host `BranchingProgram.evalWith` as row **H18**, and
  the public hosts the phase consumes recorded as **H19** `runWith`/`runWith_rel` (`DAGCircuit.lean:149/625`) and
  **H20** `DAGCircuit.rewrite` (`DAGTransform.lean:246`). Records only; Gate 45 audits their contracts as listed.
  The formula gadgets of F1–F10 become the first rows of a circuit/formula gadget registry (policy §1), in a new
  subsection of the same document.

**6b: cryptography (Gate 46).** Namespace `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW`, except
`LWE/Ratio.lean` (`TCSlib.Cryptography.LWE`). New children of the GSW facade:
`GSW/{Branching,DecryptFormula,Bootstrap,Circular,Leveled,LeveledSecurity,PolyRatio,Asymptotic}.lean`, and
`Cryptography/LWE/Ratio.lean` (`LWE.lean` facade). 6b **imports** the 6a modules and restates none of them.

**Owner-side PRs** (small, maintainer Lean, landing proved, audited as proofs):
- **O1** (P6-Q6, Gate 45). It promotes `TreeNCAC.combine` (and `pairUp`, `combineFuel` and the four lemmas) into
  `FormulaArith/Combinators.lean` as the public `TreeCircuit.balanced`, with the facade `FormulaArith.lean`.
  `TreeNCAC.toBinary` is re-pointed, with its statements unchanged. The proofs move unchanged except the three
  `simp [TreeCircuit.eval]` reads (`TreeNCAC.lean:195/199/261`), which go through `eval_node_true`/`_false`
  (`TreeDAG.lean:126/132`) so that the new owner passes its Rule 10 seal; nothing is duplicated. In r3, O1 is a
  separate small series of the 6a statement job, on its own branch.
- **O2** (P6-Q7, Gate 46). It adds `decodeLo`, `decodeHi` and `decode_iff_mem_Ico` to `LWE/BitEncoding.lean`.

**New definitions** (each lands with its readers: `_eq`/`_apply`/`_iff`, non-simp `simps` for structures):
- **Defs:**
  - instructions: `Instr`, `Instr.eval`, `Instr.IsPermutation`, `Instr.ofPerm`;
  - programs: `BranchingProgram`, `length`, `append`, `yield`, `IsPermutation`, `conj`, `complementLast`;
  - families and classes: `BranchingProgramFamily` (`language`, `IsPolyLength`, `IsPermutation`),
    `Language.InBWBP`, `Language.InPBP`.
- **Eval:** `Instr.stepWith`, `evalWith`.
- **Barrington:** `IsFiveCycle`, `FiveCycleRecognizes`, `sigma1`, `sigma2`, `conjugator`, `barrington`.
- **BarringtonConverse:** `Instr.wire`, `wireComp`, `compTree`, `toFormula`, `topDepth`.
- **NANDForm:** `DAGGate.IsNAND`, `DAGCircuit.IsNANDForm`, `nandGadget`, `DAGCircuit.toNANDForm`.
- **NANDLayering:** `DAGCircuit.IsLayered`, `litInput`, `DAGCircuit.layerNAND` (with its column builder).
- **FormulaArith:**
  - `Combinators`: `TreeCircuit.{neg, subst, rename, const, and2, or2, xor2, xor3, maj3}` (`balanced` from O1);
  - `CarrySave`: `FormulaArith.{val, csaStep, csaReduce, csaLevels}`;
  - `Compare`: `FormulaArith.{bitAt, carryOut, geConst}`;
  - `ModSum`: `FormulaArith.{modSumInterval, modSumDepth}`.
- **GSW:**
  - formulas and bootstrapping: `select`, `homEvalPBP`, `homEvalFormula`, `keyBits`, `decConstants`,
    `decryptFormula`, `nandFormula`, `decDepth`, `bootNoise`, `bootNAND`, `bootGate`, `fheEval`, `fheEvalCircuit`,
    `evalKey`;
  - pure-FHE security: `fheView`, `WeakCircularSecure` (per distinguisher, P6-Q15);
  - leveled scheme: `levelKey`, `literalCts`, `leveledEval`, `leveledEvalCircuit`, `leveledView`,
    `levelReduction`, `levelTerm`;
  - asymptotic: `encodeCiphertext`, `encodeView`, `encodeFheView`, `encodeLeveledView`,
    `WeakCircularSecureFamily`, `ReductionEfficient`, `LeveledReductionEfficient`.
- **LWE:** `Family.RatioBounded`, `decodeLo`, `decodeHi` (O2). **GSW ratio:** `Parameters.ofFamily`, `pBoot`.

## H5. Statements (sketches)

"Target" means a `sorry` statement at the gate. Statements are sketches: names and shapes are fixed at the
statement phase, and constants marked *(fix)* are settled there by hand and by small `decide` checks. Every
docstring opens with a statement in words, then the `[TAG, location, anchor]` tag and any deviation; the proof
sketch follows. Target IDs: the C series is renumbered for the general model; F and G keep their r1 numbers where
the statement survives (F4 became O1, G4 became O2); N, L and A are new. r3 adds N7–N13 (the layering, §H5.6b) and
reshapes G7, G9, G14, L1–L5 and A3 under P6-Q14 and P6-Q15.

### H5.1 `Complexity/BranchingPrograms/Defs.lean` (C1–C4)

```lean
/-- An instruction `⟨j, f₀, f₁⟩` of width `w` over `n` inputs: read input `j`; apply `f₀` if it is `0`,
`f₁` if it is `1` [Bar89, §1, p001-b002]. Deviation: Bar89 lists the `x_j = 1` map first; the fields follow
BV14's `(var(t), σ_{t,0}, σ_{t,1})` [BV14, §3.3, p013-b002]. -/
structure BranchingProgram.Instr (w n : ℕ) where
  var : Fin n
  map0 : Fin w → Fin w
  map1 : Fin w → Fin w

/-- A width-`w` branching program on `n` inputs: a finite sequence of instructions [Bar89, §1, p001-b002]. -/
structure BranchingProgram (w n : ℕ) where
  instrs : List (BranchingProgram.Instr w n)

/-- The map `B` yields on `x`: the composition, in program order, of the maps its instructions produce;
`yield ⟨[]⟩ x = id` [Bar89, §1, p001-b002]. -/
def BranchingProgram.yield (B : BranchingProgram w n) (x : Fin n → Bool) : Fin w → Fin w

/-- `B` is a permutation branching program: every map of every instruction is a bijection
[Bar89, §1, p002-b001]. -/
def BranchingProgram.IsPermutation (B : BranchingProgram w n) : Prop

/-- A family of width-`w` programs with accepting sets: `u ∈ language ↔ (program |u|).yield u.get ∈ accept |u|`
[Bar89, §1, p002-b001: "x ∈ L iff B(x) ∈ F_n"]. Registered model. -/
structure BranchingProgramFamily (w : ℕ) where
  program : (n : ℕ) → BranchingProgram w n
  accept : (n : ℕ) → Finset (Fin w → Fin w)

/-- `L ∈ BWBP`: some width and some polynomial-length family (`length ≤ a·(n+1)^k`) recognize `L`
[Bar89, §1, p002-b001]. `L ∈ PBP_w`: the same with a permutation family of width `w`. -/
def Language.InBWBP (L : Language Bool) : Prop
def Language.InPBP (w : ℕ) (L : Language Bool) : Prop

-- C1. Yield in program order [Bar89, §1, p001-b002, "the composition of the functions produced by each of
-- the instructions"]; the Mathlib translation of §H3.6 is in the docstring.
theorem yield_append (B₁ B₂ : BranchingProgram w n) (x : Fin n → Bool) :
    (B₁ ++ B₂).yield x = B₂.yield x ∘ B₁.yield x
theorem yield_nil (x : Fin n → Bool) : (⟨[]⟩ : BranchingProgram w n).yield x = id

-- C2. Conjugating every map by `θ` conjugates the yield; length is unchanged [Bar89, Lemma 1 proof, p003-b003].
theorem yield_conj (B : BranchingProgram w n) (θ : Equiv.Perm (Fin w)) (x : Fin n → Bool) :
    (B.conj θ).yield x = θ ∘ B.yield x ∘ θ.symm
theorem length_conj : (B.conj θ).length = B.length
theorem length_append : (B₁ ++ B₂).length = B₁.length + B₂.length

-- C3. Post-composing the last instruction's two maps with `σ⁻¹` post-composes the yield
-- [Bar89, Lemma 2 proof, p003-b004: "B'(x) = e if x ∈ A and B'(x) = σ⁻¹ if x ∉ A"].
theorem yield_complementLast (B : BranchingProgram w n) (σ : Equiv.Perm (Fin w)) (hB : 0 < B.length)
    (x : Fin n → Bool) : (B.complementLast σ).yield x = σ.symm ∘ B.yield x
theorem length_complementLast : (B.complementLast σ).length = B.length

-- C4. Permutation programs [Bar89, §1, p002-b001]: closure and bijective yields (glue).
theorem isPermutation_iff :
    B.IsPermutation ↔ ∀ ι ∈ B.instrs, Function.Bijective ι.map0 ∧ Function.Bijective ι.map1
theorem IsPermutation.append; IsPermutation.conj; IsPermutation.complementLast
theorem IsPermutation.bijective_yield (h : B.IsPermutation) (x : Fin n → Bool) : Function.Bijective (B.yield x)
```

### H5.2 `Complexity/BranchingPrograms/Eval.lean` (C5–C8): the host

```lean
/-- One instruction on a state vector, push form: coordinate `i` receives, through `sel` applied to the
instruction's input, the sums of the entries that the `0`-branch and the `1`-branch send to `i`. Host step;
glue generalizing [BV14, Eq. (4), p013-b002]. -/
def Instr.stepWith [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β) (ι : Instr w n)
    (V : Fin w → α) : Fin w → α :=
  fun i => sel (inp ι.var) (∑ j ∈ univ.filter (ι.map0 · = i), V j)
    (∑ j ∈ univ.filter (ι.map1 · = i), V j)

/-- **The branching-program host**: fold `stepWith` over the instructions in program order. Generic in the
selector and the value type; consumers are the Boolean semantics (C8) and GSW (G2). -/
def evalWith [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β) (B : BranchingProgram w n)
    (V : Fin w → α) : Fin w → α

-- C5. Readers of the fold (glue).
theorem evalWith_nil : (⟨[]⟩ : BranchingProgram w n).evalWith sel inp V = V
theorem evalWith_append : (B₁ ++ B₂).evalWith sel inp V = B₂.evalWith sel inp (B₁.evalWith sel inp V)

-- C6. For a permutation instruction each sum has one term: BV14's pull form
-- `V'_i = sel x (V (σ₀⁻¹ i)) (V (σ₁⁻¹ i))` [BV14, Eq. (4), p013-b002].
theorem Instr.stepWith_of_isPermutation (hι : ι.IsPermutation) (i : Fin w) :
    ι.stepWith sel inp V i =
      sel (inp ι.var) (V ((Equiv.ofBijective _ hι.1).symm i)) (V ((Equiv.ofBijective _ hι.2).symm i))

-- C7. **Step-indexed relational host lemma** (glue): two runs related at step 0 and preserved by every step
-- stay related after `B.length` steps; GSW carries its noise `t·2Nβ` in the index.
theorem evalWith_rel [AddCommMonoid α] [AddCommMonoid α'] (sel : β → α → α → α)
    (sel' : β' → α' → α' → α') (inp : Fin n → β) (inp' : Fin n → β') (B : BranchingProgram w n)
    (R : ℕ → (Fin w → α) → (Fin w → α') → Prop) (V : Fin w → α) (V' : Fin w → α') (h0 : R 0 V V')
    (hstep : ∀ t (ht : t < B.length) U U', R t U U' →
      R (t + 1) ((B.instrs[t]).stepWith sel inp U) ((B.instrs[t]).stepWith sel' inp' U')) :
    R B.length (B.evalWith sel inp V) (B.evalWith sel' inp' V')

-- C8. Boolean semantics for **general** maps: a one-hot state stays one-hot at the yield
-- [BV14, Eq. (4), p013-b002, generalized from permutations; Bar89, §1].
theorem evalWith_single (B : BranchingProgram w n) (x : Fin n → Bool) (s : Fin w) :
    B.evalWith (fun b (u v : ℕ) => if b then v else u) x (Pi.single s 1) = Pi.single (B.yield x s) 1
```

### H5.3 `Complexity/BranchingPrograms/Barrington.lean` (C9–C16)

```lean
/-- `σ` is a five-cycle: `σ.cycleType = {5}` (decidable) [Bar89, §3, p003-b001]. -/
def IsFiveCycle (σ : Equiv.Perm (Fin 5)) : Prop

/-- `B` five-cycle recognizes `A` with output `σ`: `σ` is a five-cycle, and `B.yield x` is `σ` on `A` and `id`
off `A` [Bar89, §3, p003-b001]. -/
def FiveCycleRecognizes (B : BranchingProgram 5 n) (A : (Fin n → Bool) → Prop) (σ : Equiv.Perm (Fin 5)) : Prop

/-- Bar89's `(12345)` and `(13542)`, 0-based: `c[0,1,2,3,4]`, `c[0,2,4,3,1]` [Bar89, Lemma 3, p003-b005]. -/
def sigma1 : Equiv.Perm (Fin 5);  def sigma2 : Equiv.Perm (Fin 5)

/-- The explicit conjugator of two five-cycles, `θ (σ^k 0) = τ^k 0` for `k < 5` [Bar89, Lemma 1 proof,
p003-b003]; computable (P6-Q13). -/
def conjugator (σ τ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 5)

/-- Barrington's program for a formula with output `σ` [Bar89, Thm 1 proof, p004-b002]:
- literal `x_i` gives `⟨i, 1, σ⟩` and `¬x_i` gives `⟨i, σ, 1⟩` (BV14's order);
- a constant node gives `⟨0, σ, σ⟩` (`true`) or `⟨0, 1, 1⟩` (`false`), hence `[NeZero n]`;
- a fan-in-1 node gives its child;
- `∧` gives the children with outputs `τ₁, τ₂, τ₁⁻¹, τ₂⁻¹`, where `τᵢ = θ σᵢ θ⁻¹`
  and `θ` conjugates the commutator of `sigma1` and `sigma2` to `σ`;
- `∨` uses De Morgan through `complementLast` (Lemma 2), the step the ingest's transcription note makes explicit.
Computable (P6-Q13). Fan-in above 2 is never used: the theorems assume `c.maxFanin ≤ 2`. -/
def barrington [NeZero n] : BoolCircuit.TreeCircuit n → Equiv.Perm (Fin 5) → BranchingProgram 5 n

-- C9. Lemma 3 in program order: the commutator of the two five-cycles is a five-cycle, `c[0,2,1,4,3]`
-- (Bar89's (13254)) [Bar89, Lemma 3, p003-b005]; kernel `decide`, no `native_decide`.
theorem isFiveCycle_sigma1 : IsFiveCycle sigma1;  theorem isFiveCycle_sigma2 : IsFiveCycle sigma2
theorem isFiveCycle_commutator : IsFiveCycle (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1)

-- C10. The conjugator conjugates [Bar89, Lemma 1 proof, p003-b003] (checked for all 24 × 24 pairs, §H3.6).
theorem conjugator_conj (hσ : IsFiveCycle σ) (hτ : IsFiveCycle τ) :
    conjugator σ τ * σ * (conjugator σ τ)⁻¹ = τ

-- C11. **Lemma 1**: change the output to any five-cycle at the same length [Bar89, Lemma 1, p003-b003].
theorem FiveCycleRecognizes.conj (h : FiveCycleRecognizes B A σ) (hτ : IsFiveCycle τ) :
    FiveCycleRecognizes (B.conj (conjugator σ τ)) A τ

-- C12. **Lemma 2**: the complement, same length, output `σ⁻¹` [Bar89, Lemma 2, p003-b004].
theorem FiveCycleRecognizes.complementLast (h : FiveCycleRecognizes B A σ) (hB : 0 < B.length) :
    FiveCycleRecognizes (B.complementLast σ) (fun x => ¬ A x) σ⁻¹

-- C13. **Barrington's Theorem 1**, recognition [Bar89, Thm 1, p003-b002, proof p004-b002;
-- BV14, Thm 3.5, p014-b001].
theorem barrington_recognizes [NeZero n] (c : BoolCircuit.TreeCircuit n) (hc : c.maxFanin ≤ 2)
    (hσ : IsFiveCycle σ) : FiveCycleRecognizes (barrington c σ) (fun x => c.eval x = true) σ

-- C14. **Theorem 1**, length [Bar89, Thm 1, p003-b002].
theorem barrington_length_le [NeZero n] (hc : c.maxFanin ≤ 2) (σ) : (barrington c σ).length ≤ 4 ^ c.depth
theorem barrington_length_pos [NeZero n] (c) (σ) : 0 < (barrington c σ).length          -- glue for Lemma 2

-- C15. The program is a permutation program (glue; [Bar89, Thm 1]: "a 5-PBP").
theorem isPermutation_barrington [NeZero n] (c) (σ) : (barrington c σ).IsPermutation

-- C16. BV14's reading from start state `0` (§H3.7) [BV14, Thm 3.5, p014-b001].
theorem barrington_yield_zero [NeZero n] (hc : c.maxFanin ≤ 2) (hσ : IsFiveCycle σ) (x : Fin n → Bool) :
    (barrington c σ).yield x 0 = if c.eval x then σ 0 else 0
```

### H5.4 `Complexity/BranchingPrograms/BarringtonConverse.lean` (C17–C21): Thm 2

```lean
-- C17. The constant-depth section per instruction [Bar89, Thm 2 proof, p004-b003]: the wire "ι sends i to j".
def Instr.wire (ι : Instr w n) (i j : Fin w) : BoolCircuit.TreeCircuit n
theorem Instr.wire_eval : (ι.wire i j).eval x = decide (ι.eval x i = j)
theorem Instr.depth_wire_le : (ι.wire i j).depth ≤ 1;  theorem Instr.maxFanin_wire_le : (ι.wire i j).maxFanin ≤ 2

-- C18. One composition circuit, `(wireComp F G) i k = ⋁_j (F i j ∧ G j k)` by `balanced`
-- [Bar89, Thm 2 proof: "may be computed by a fixed circuit whose size depends only on w"].
def wireComp (F G : Fin w → Fin w → BoolCircuit.TreeCircuit n) : Fin w → Fin w → BoolCircuit.TreeCircuit n
theorem wireComp_eval (hF : ∀ x i j, (F i j).eval x = decide (f x i = j))
    (hG : ∀ x i j, (G i j).eval x = decide (g x i = j)) : (wireComp F G i k).eval x = decide (g x (f x i) = k)
theorem depth_wireComp_le (hF : ∀ i j, (F i j).depth ≤ d) (hG : ∀ i j, (G i j).depth ≤ d) :
    (wireComp F G i k).depth ≤ d + Nat.clog 2 w + 2

-- C19. The binary tree of composition circuits over the instruction list, split at the midpoint
-- [Bar89, Thm 2 proof, p004-b003]; the empty list gives the identity wires.
def compTree : List (Instr w n) → Fin w → Fin w → BoolCircuit.TreeCircuit n
theorem compTree_eval (B : BranchingProgram w n) : (compTree B.instrs i j).eval x = decide (B.yield x i = j)
theorem depth_compTree_le : (compTree B.instrs i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + 1   -- (fix)
theorem maxFanin_compTree_le : (compTree B.instrs i j).maxFanin ≤ 2

/-- **Barrington's Theorem 2, one program** [Bar89, Thm 2, p004-b003]: the formula
`⋁_{f ∈ F} ⋀_i compTree B i (f i)` (the constant-depth acceptance section on top) decides `B.yield x ∈ F`.
Deviation: built as a formula (fan-out one), not a DAG (P6-Q18); `noncomputable` is allowed. -/
noncomputable def toFormula (B : BranchingProgram w n) (F : Finset (Fin w → Fin w)) : BoolCircuit.TreeCircuit n

-- C20. Semantics [Bar89, Thm 2, p004-b003].
theorem toFormula_eval (B) (F) (x : Fin n → Bool) : (B.toFormula F).eval x = decide (B.yield x ∈ F)

-- C21. Depth `O(log l)` with a constant depending on `w` [Bar89, Thm 2, p004-b003], fan-in two.
theorem depth_toFormula_le : (B.toFormula F).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + topDepth w
theorem maxFanin_toFormula_le : (B.toFormula F).maxFanin ≤ 2
--   with `topDepth w := w * Nat.clog 2 w + Nat.clog 2 w + 4`                                               (fix)
```

### H5.5 `Complexity/BranchingPrograms/NC1.lean` (C22–C25)

```lean
-- C22. **`DAGCircuit` corollary** [BV14, Thm 3.5, p014-b001; Bar89, Thm 1, p003-b002]: a fan-in-two circuit
-- on `n ≥ 1` inputs is five-cycle recognized at length `≤ 4^depth`, through `toTree` (depth-preserving).
theorem exists_fiveCycleRecognizes_of_dagCircuit [NeZero n] (C : BoolCircuit.DAGCircuit n) (hC : C.IsFaninTwo)
    (hσ : IsFiveCycle σ) : ∃ B : BranchingProgram 5 n, B.IsPermutation ∧ B.length ≤ 4 ^ C.depth ∧
      FiveCycleRecognizes B (fun x => C.eval x = true) σ

-- C23. **NC¹ ⊆ polynomial-length width-5 PBPs** [Bar89, Corollary, p004-b004; abstract, p001-b001], through
-- `Language.InNC.inTreeNC_one`; length `4^{b(log₂ n + 1)} ≤ 4^b (n+1)^{2b}`; `n = 0` by the accepting set.
theorem Language.InNC.inPBP_five {L : Language Bool} (h : L.InNC 1) : L.InPBP 5

-- C24. **BWBP ⊆ NC¹**, Theorem 2 for families [Bar89, Thm 2, p004-b003; abstract, p001-b001]: `toFormula` per
-- length gives a fan-in-2 formula family of depth `O(log n)` and size `≤ 2^(depth+1)` (`size_succ_le_two_pow`),
-- so `L.InTreeNC 1`, then `Language.InTreeNC.inNC`.
theorem Language.InBWBP.inNC_one {L : Language Bool} (h : L.InBWBP) : L.InNC 1

-- C25. **Barrington's Corollary** [Bar89, Corollary, p004-b004]: BWBP = nonuniform NC¹ = PBP₅.
theorem Language.inNC_one_iff_inBWBP (L : Language Bool) : L.InNC 1 ↔ L.InBWBP
theorem Language.inNC_one_iff_inPBP_five (L : Language Bool) : L.InNC 1 ↔ L.InPBP 5
```

### H5.6 `Complexity/CircuitComplexity/NANDForm.lean` (N1–N6)

```lean
/-- A NAND gate: a `¬` gate (negated conjunction, `DAGGate.eval_eq`) reading at most two vertices; fan-in 1 is
negation, fan-in 0 the constant `false`. Not `NAndCircuit` (`Basic.lean:356`, an AND-rooted normal form).
Glue; motivated by [BV14, Def 2.13, p008-b002; Thm 3.5, p014-b001]. -/
def DAGGate.IsNAND (g : DAGGate) : Prop := g.kind = .not ∧ g.args.length ≤ 2
/-- Every gate is a NAND gate. Such circuits are not `IsWellFormed` (fan-in-2 `¬` gates). -/
def DAGCircuit.IsNANDForm (C : DAGCircuit n) : Prop := ∀ g ∈ C.gates, g.IsNAND

-- N1. NAND semantics (reader; glue).
theorem DAGGate.eval_of_isNAND (hg : g.IsNAND) (vals : List Bool) :
    g.eval vals = !(g.args.all fun a => vals.getD a false)

-- N2. The gadget of §H3.9 is correct in the sense of `GadgetCorrect` (`DAGTransform.lean:68`), with depth
-- factor 2 and domain "fan-in ≤ 2" (glue; proof as `deMorganGadget_correct`, `DAGFanin.lean:499`).
theorem nandGadget_correct : GadgetCorrect n 2 (fun _ l => l ≤ 2) DAGGate.IsNAND (nandGadget n)

/-- The NAND form of a circuit with fan-in at most two: `C.rewrite (nandGadget n) nandGadget_correct hC`. -/
def DAGCircuit.toNANDForm (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) : DAGCircuit n

-- N3–N6: semantics, form, depth, size (from `rewrite_eval`, `rewrite_new_gates`, `rewrite_depth_le`,
-- `rewrite_length_le`; glue).
theorem toNANDForm_eval (x : Fin n → Bool) : (C.toNANDForm hC).eval x = C.eval x            -- N3
theorem toNANDForm_isNANDForm : (C.toNANDForm hC).IsNANDForm                                -- N4
theorem toNANDForm_depth_le : (C.toNANDForm hC).depth ≤ 2 * C.depth                         -- N5
theorem toNANDForm_size_le : (C.toNANDForm hC).size ≤ n + 4 * C.gates.length                -- N6
```

`toNANDForm`'s body passes the proof `nandGadget_correct` to `rewrite`. While N2 is admitted, `sorryAx` therefore
reaches `toNANDForm` and its consumers through N2 alone; the statement phase's axiom report says so, and the N2 fill
removes it. N2's fill needs the owner-side reader `gadgetCorrect_iff` (§H2).

### H5.6b `Complexity/CircuitComplexity/NANDLayering.lean` (N7–N13; P6-Q14 B; new in r3)

```lean
/-- `C` is layered: every gate sits exactly one level above each vertex it reads,
`C.depthAt a + 1 = C.depthAt (n + i)` for every argument `a` of gate `i` (inputs at level 0). Glue, motivated by
the level-by-level evaluation of [BV11, Thm 3.1, Def 3.6, p015-b001, p014-b001]; `_iff` reader. -/
def DAGCircuit.IsLayered (C : DAGCircuit n) : Prop :=
  ∀ (i : ℕ) (hi : i < C.gates.length), ∀ a ∈ (C.gates[i]).args, C.depthAt a + 1 = C.depthAt (n + i)

/-- The literal input of `x`: the `2n` literals, `litInput x = Fin.append x (fun i => !x i)` (Bar89's "inputs and
negated inputs" [Bar89, Thm 1, p003-b002]); `_apply` readers for both halves. -/
def litInput (x : Fin n → Bool) : Fin (n + n) → Bool

/-- The gate list and output vertex of the layering (§H3.13): every old vertex `v` is realized at each level
`depthAt v ≤ k ≤ C.depth` (base, parity twin, double-NAND chain), every gate emitted as a NAND gate, columns in
topological order; the output is `out@(C.depth)`. Computable; glue (§H1 gap 4); `_eq` readers. -/
def DAGCircuit.layerGates [NeZero n] (C : DAGCircuit n) : List DAGGate
def DAGCircuit.layerOutput [NeZero n] (C : DAGCircuit n) : ℕ
-- N12–N13. The structure fields: acyclicity and the output's range (targets, like N2 for `toNANDForm`).
theorem layerGates_acyclic [NeZero n] : GatesAcyclic (n + n) C.layerGates
theorem layerOutput_lt [NeZero n] : C.layerOutput < (n + n) + C.layerGates.length

/-- **The layering conversion**: `⟨C.layerGates, C.layerOutput, N12, N13⟩` (readers `layerNAND_gates`,
`layerNAND_output`). While N12 and N13 are admitted, `sorryAx` reaches it through them only. -/
def DAGCircuit.layerNAND [NeZero n] (C : DAGCircuit n) : DAGCircuit (n + n)

-- N7. Semantics on the literal input.
theorem layerNAND_eval [NeZero n] (hC : C.IsNANDForm) (x : Fin n → Bool) :
    C.layerNAND.eval (litInput x) = C.eval x
-- N8. Layered (no hypothesis: every new gate reads only copies one level down).
theorem layerNAND_isLayered [NeZero n] : C.layerNAND.IsLayered
-- N9. NAND form (the copies keep the old fan-in, so `hC` is needed for `≤ 2`).
theorem layerNAND_isNANDForm [NeZero n] (hC : C.IsNANDForm) : C.layerNAND.IsNANDForm
-- N10. Depth is preserved exactly.
theorem layerNAND_depth [NeZero n] : C.layerNAND.depth = C.depth
-- N11. Size: each column has at most `2(D − δ) + 1` gates.                                         (fix)
theorem layerNAND_size_le [NeZero n] : C.layerNAND.size ≤ 2 * n + (2 * C.depth + 1) * C.size
```

The proof sketch is the column invariant: for every old vertex `v` and level `depthAt v ≤ k ≤ C.depth`, the new
vertex `v@k` exists, has depth exactly `k`, and on `litInput x` has the value of `v` on `x`. It is proved by
induction along the fold (old vertices in topological order), with `GatesAcyclic.snoc` for acyclicity,
`depthAt_gate`/`DAGGate.depth_eq` for the depths and `DAGGate.eval_of_isNAND` (N1) for the values; N7–N13 read it
off at the output, at every gate and at the column lengths.

### H5.7 `Complexity/CircuitComplexity/FormulaArith/` (F1–F3, F5–F10; P6-Q5, P6-Q6)

`Combinators.lean` (`balanced` and its four lemmas arrive proved with O1, §H5.8):

```lean
-- F1. De Morgan negation (literals flip sign, nodes flip kind): depth- and fan-in-preserving (glue).
theorem TreeCircuit.neg_eval : c.neg.eval x = !c.eval x
theorem TreeCircuit.depth_neg : c.neg.depth = c.depth;  theorem TreeCircuit.maxFanin_neg : c.neg.maxFanin = c.maxFanin
-- F2. Substitution of formulas for variables (a negative literal becomes `(f i).neg`); `rename` is the
-- literal case and preserves depth (glue).
theorem subst_eval : (c.subst f).eval x = c.eval (fun i => (f i).eval x)
theorem depth_subst_le : (c.subst f).depth ≤ c.depth + ⨆ i, (f i).depth;  theorem maxFanin_subst_le
theorem rename_eval : (c.rename e).eval x = c.eval (x ∘ e);  theorem depth_rename : (c.rename e).depth = c.depth
-- F3. Gadgets `and2/or2/xor2/xor3/maj3`: value, depth (+1, +1, +2, +4, +3) (fix), fan-in ≤ 2 (glue).
theorem xor3_eval : (xor3 a b c).eval x = (a.eval x ^^ b.eval x ^^ c.eval x)
theorem maj3_eval : (maj3 a b c).eval x = (a.eval x && b.eval x || c.eval x && (a.eval x ^^ b.eval x))
```

`CarrySave.lean`, `Compare.lean`, `ModSum.lean`:

```lean
/-- The value of a little-endian formula number: `val x U = bitsVal (U.map (·.eval x))` (`Adder.lean:78`). -/
def FormulaArith.val (x : Fin n → Bool) (U : List (TreeCircuit n)) : ℕ

-- F5. One 3:2 layer: `val A + val B + val C = val S + val K` (`S` bitwise `xor3`, `K` shifted `maj3`), depth +4
-- [BV11, Lemma 4.5 proof, p029-b002: "the summation … can be done in depth O(log k + log log p)"].
-- Deviation: carry-save tree.
theorem csaStep_val; theorem depth_csaStep_le
-- F6. The reduction to two numbers: value preserved; depth ≤ 4·csaLevels k + d₀;
-- csaLevels k ≤ 2⌈log₂ k⌉ + 3.
theorem csaReduce_val; theorem depth_csaReduce_le; theorem csaLevels_le                                  -- (fix)
-- F7. Carry-out of `U + W` at position `b` (generate/propagate, depth `2⌈log₂(b+1)⌉ + 2`): its value is
-- `carryBit` (`Adder.lean:377`), hence `decide (2^b ≤ val U + val W)` by `prefixVal_add` (`Adder.lean:397`).
theorem carryOut_eval : (carryOut U W).eval x = carryBit (bitAt x U) (bitAt x W) b
theorem carryOut_eval_le (hU : U.length ≤ b) (hW : W.length ≤ b) :
    (carryOut U W).eval x = decide (2 ^ b ≤ FormulaArith.val x U + FormulaArith.val x W)
-- F8. Comparison with a constant: `(geConst U W c).eval x = decide (c ≤ val x U + val x W)`; depth.
theorem geConst_eval; theorem depth_geConst_le
-- F9. **The modular interval sum** [BV11, Lemma 4.5, p029-b001; BV14, Prop 3.4, p011-b001]:
theorem modSumInterval_eval (ha : ∀ i, a i < q) (hlh : lo ≤ hi) (hhq : hi ≤ q) :
    (modSumInterval a q lo hi).eval x =
      decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi)
-- F10. Depth `O(log M + log log q)` with no term linear in `log q` (§H3.3), fan-in two:
theorem depth_modSumInterval_le : (modSumInterval a q lo hi).depth ≤ modSumDepth M q
theorem modSumDepth_le : modSumDepth M q ≤ 9 * Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 q + Nat.clog 2 M + 3) + 21
theorem maxFanin_modSumInterval_le : (modSumInterval a q lo hi).maxFanin ≤ 2                             -- (fix)
```

### H5.8 The owner-side PRs (O1, O2): proved, not fill units

```lean
-- O1 (P6-Q6; `FormulaArith/Combinators.lean` with the facade `FormulaArith.lean`, moved from
-- TreeNCAC.lean:172–351; TreeNCAC re-pointed). Proofs move byte-identical except the three Rule-10 repairs of
-- `simp [TreeCircuit.eval]` at TreeNCAC.lean:195/199/261 (readers `eval_node_true`/`_false`, TreeDAG.lean:126/132).
/-- A balanced binary tree of `b`-gates over `cs`, computing the unbounded `b`-gate (the former private
`TreeNCAC.combine`; its existing docstring tag is kept). -/
def TreeCircuit.balanced (b : Bool) (cs : List (TreeCircuit n)) : TreeCircuit n
theorem balanced_eval : (balanced b cs).eval x = (TreeCircuit.node b cs).eval x
theorem maxFanin_balanced_le : (balanced b cs).maxFanin ≤ max 2 (TreeCircuit.maxFaninL cs)
theorem depth_balanced_le : (balanced b cs).depth ≤ TreeCircuit.maxDepth cs + Nat.clog 2 cs.length + 1
theorem size_balanced_le : (balanced b cs).size ≤ TreeCircuit.sumSize cs + cs.length + 1

-- O2 (P6-Q7; `LWE/BitEncoding.lean`). With h = ⌊q/2⌋: lo = ⌊h/2⌋ + 1, hi = ⌈(q + h)/2⌉. Checked by
-- computation for 2 ≤ q < 300 against Mathlib's `valMinAbs` convention (r2). Glue for the file's `decode`.
def decodeLo (P : LWE.Parameters) : ℕ;  theorem decodeLo_eq : decodeLo P = P.modulus / 2 / 2 + 1
def decodeHi (P : LWE.Parameters) : ℕ;  theorem decodeHi_eq : decodeHi P = (P.modulus + P.modulus / 2 + 1) / 2
theorem decode_iff_mem_Ico (P : LWE.Parameters) (v : ZMod P.modulus) :
    decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P
```

### H5.9 `GSW/Branching.lean` (G1–G3)

```lean
-- G1. **The selector step** [BV14, Eq. (5)–(6), p014-b002; Lemma 3.6 proof, p015-b002, mirrored;
-- AP14, Eq. (4.1), p011-b001; Lemma 4.1, p012-b001].
theorem Encrypts.select (hC : Encrypts P t b β C) (hU : Encrypts P t u βV U) (hV : Encrypts P t v βV V)
    (hb : b = 0 ∨ b = 1) : Encrypts P t ((1 - b) * u + b * v) (βV + 2 * (P.columns * β)) (select P C U V)

-- G2. **Homomorphic PBP evaluation**: `homEvalPBP P B cts V := B.evalWith (select P) cts V` (C7 with
-- C6), for a permutation program [BV14, Lemma 3.6, p015-b001, worst-case form].
theorem encrypts_homEvalPBP (hB : B.IsPermutation) (hin : ∀ j, Encrypts P t (x j).toNat β (cts j)) (s₀ i) :
    Encrypts P t (decide (B.yield x s₀ = i)).toNat (B.length * (2 * (P.columns * β)))
      (homEvalPBP P B cts (Pi.single s₀ (gadget P)) i)

-- G3. **Homomorphic formula evaluation**: Barrington (C13–C16), then G2; output coordinate `σ 0` (§H3.7)
-- [BV14, Thm 3.5 with Lemma 3.6; Pei16, §6.1.3 bootstrapping, p070-b001].
theorem encrypts_homEvalFormula [NeZero k] (c : TreeCircuit k) (hc : c.maxFanin ≤ 2)
    (hin : ∀ j, Encrypts P t (x j).toNat β (cts j)) :
    Encrypts P t (c.eval x).toNat (4 ^ c.depth * (2 * (P.columns * β))) (homEvalFormula P c cts)
```

### H5.10 `GSW/DecryptFormula.lean` (G5–G8; G4 is O2)

```lean
-- G5. Decryption is a binary subset sum of public constants `Gᵀc` [AP14, §5.1, p014-b001; Pei16, §5.4.3].
theorem vecMul_secretVector_eq_sum :
    secretVector P s ⬝ᵥ c = ∑ i, ((keyBits P s i).toNat : ZMod q) * (decConstants P C i)
-- G6. **The decryption formula** [BV14, Prop 3.4, p011-b001; BV11, Lemma 4.5, p029-b001]: built from F9 and O2.
theorem decryptFormula_eval : (decryptFormula P C).eval (keyBits P s) = decrypt P s C
-- G7. **The augmented NAND formula** [BV14, Def 2.13, p008-b002; BV11, Def 3.7, p014-b002]: BV14's `f_{c₁,c₂}`
-- literally, one key block (r3: under P6-Q14 B both arguments share a key, so r2's two blocks are withdrawn).
--   nandFormula P C₁ C₂ := (and2 (decryptFormula P C₁) (decryptFormula P C₂)).neg
theorem nandFormula_eval : (nandFormula P C₁ C₂).eval (keyBits P s) = !(decrypt P s C₁ && decrypt P s C₂)
-- G8. Depth and fan-in [BV14, Lemma 4.4, p019-b001: "depth c_dec·log(k log q(k)) + 1"].
theorem depth_nandFormula_le : (nandFormula P C₁ C₂).depth ≤ decDepth P + 1
theorem maxFanin_nandFormula_le : (nandFormula P C₁ C₂).maxFanin ≤ 2
theorem decDepth_le : decDepth P ≤ 9 * Nat.clog 2 P.columns + 2 * Nat.clog 2 (P.width + …) + 21          -- (fix)
```

### H5.11 `GSW/Bootstrap.lean` (G9–G13, G18)

```lean
-- G9. **Bootstrapped NAND, key-switching form** [BV14, Thm 2.14, p008-b003; Lemma 4.4, p019-b001;
-- BV11, Thm 3.1, p015-b001]. No hypothesis on `C₁, C₂`: the output encrypts, under `t'`, the NAND of their
-- decryptions under `s`. Pure FHE takes `t' = secretVector P s`; the leveled scheme `s = s_{d−1}`, `t' = t_d`.
--   bootNAND P evk C₁ C₂ := homEvalFormula P (nandFormula P C₁ C₂) evk
theorem encrypts_bootNAND (hk : ∀ i, Encrypts P t' (keyBits P s i).toNat βk (evk i)) :
    Encrypts P t' (!(decrypt P s C₁ && decrypt P s C₂)).toNat (bootNoise P βk) (bootNAND P evk C₁ C₂)

-- G10. **Pure-FHE correctness for NAND-form circuits of every depth** [BV14, Thm 2.14 second part, p008-b003;
-- BV11, Thm 3.2, Def 3.5, p015-b001, p014-b001]. `bootGate` pads fan-in 1 to (a, a), 0 to (G, G) (§H3.9).
theorem decrypt_fheEval (hNAND : Cc.IsNANDForm)
    (hevk : ∀ i, Encrypts P (secretVector P s) (keyBits P s i).toNat βk (evk i))
    (hin : ∀ j, Encrypts P (secretVector P s) (x j).toNat βin (cts j)) (hβin : 2 * (P.width * βin) < q / 2)
    (hboot : 2 * (P.width * bootNoise P βk) < q / 2) : decrypt P s (fheEval P evk Cc cts) = Cc.eval x

-- G18. **Every fan-in-2 circuit**, through the NAND conversion (N3, N4) [BV14, Thm 2.14; BV11, Def 3.5].
theorem decrypt_fheEvalCircuit (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) … :
    decrypt P s (fheEvalCircuit P evk Cc hC cts) = Cc.eval x

-- G11. The evaluation key of P6-Q8 [BV11, Def 3.8, p015-b001; BV14, Lemma 4.4, p019-b001].
theorem encrypts_evalKey :
    Encrypts P (secretVector P s) (keyBits P s i).toNat (P.lwe.samples * B) (evalKey P pk s R i)
-- G12. **Honest keys, every circuit** [BV14, Thm 3.7, p016-b001, worst-case and any depth].
theorem decrypt_keygen_fheEvalCircuit (hχ : χ.Bounded B)
    (hsep : 2 * (P.width * bootNoise P (P.lwe.samples * B)) < q / 2) … : … = Cc.eval x
-- G13. Closed form of the bootstrapped noise from `decDepth_le` (glue).
theorem bootNoise_le :                                                                             -- (fix)
    bootNoise P β ≤ 4 ^ c₀ * N ^ (2 * c₁ + 1) * (ℓ + Nat.clog 2 N + 3) ^ (2 * c₂) * (2 * β)
```

Compactness [BV14, Def 2.12, p008-b001; BV11, Def 3.4, p014-b001; Lemma 3.3, p015-b001] holds by typing:
`fheEval`, `fheEvalCircuit` and `leveledEval` return a `Ciphertext P` whatever the circuit. Each docstring records
this; there is no separate theorem (P6-Q10).

### H5.12 `GSW/Circular.lean` (G14–G15): concrete, per distinguisher (P6-Q15 A)

```lean
/-- The FHE view `(pk, evk, Enc_pk(μ))` from honest key generation [BV14, §2.5, p007-b001: "the adversary is
given both pk and evk"; BV11, Def 3.1, p013-b002]. -/
def fheView (P) (χ) (μ : Bool) : Seeds P χ → FheView P

/-- **Weak circular security, concrete, for one distinguisher** (P6-Q15 A) [BV11, Def 3.8, p015-b001;
BV14, Thm 2.14, p008-b003; Pei16, §6.1.2, p068-b001]: `D`'s advantage between the FHE views of `0` and `1` is at
most `ε`. A hypothesis, never derived from LWE (phase-5 Q15); `_iff` reader. Deviation: BV11's definition is
asymptotic, and `WeakCircularSecureFamily` (§H5.16) is the headline form. Quantified over every function-level
distinguisher it would hold only for `ε` near `1` (an unbounded distinguisher recovers `s`), so it is stated per
distinguisher. -/
def WeakCircularSecure (P) (χ) {ρ : Type} [Fintype ρ] [Nonempty ρ] (D : FheView P → ρ → Bool) (ε : ℝ) :
    Prop :=
  distAdv (fheView P χ false) (fheView P χ true) D ≤ ε

-- G14. The security half of [BV11, Thm 3.2, p015-b001], deliberately thin: pure-FHE security *is* (A1).
theorem distAdv_fheView_le (h : WeakCircularSecure P χ D ε) :
    distAdv (fheView P χ false) (fheView P χ true) D ≤ ε
-- G15. Without `evk` the view is phase 5's and inherits `distAdv_encrypt_le` (two DLWE + 2Nε)
-- [GSW13, §3.2, p009-b002; AP14, §5.3, p015-b002: "if … generated independently"].
theorem distAdv_fheView_noEvk_le …
```

### H5.13 `GSW/Leveled.lean` (L1–L3): the leveled scheme (P6-Q14 B)

Every docstring of this file and of §H5.14 cites only ingested sources and carries the disclosure of P6-Q19 B:
"The key-chain construction and the hybrid order are reconstructed: no ingested passage gives them. BV11 and BV14
attribute leveled bootstrapping to Gentry's work; that passage will be cited here once it is ingested." The
disclosure names no `[Gen09]` tag, which would not resolve until the ingest.

```lean
/-- The level-`d` evaluation key, `1 ≤ d ≤ L`, of the consecutive chain: the encryptions under `pk_d` of the `N`
key bits of `s_{d−1}` [BV11, Thm 3.1, p015-b001: "only the length of the evaluation key depends on the level L";
BV14, Thm 2.14 first part, p008-b003]. In all `N·L` ciphertexts. Reconstruction disclosed (above). -/
def levelKey (P) (pks : Fin (L+1) → PublicKey P) (ss : Fin (L+1) → Secret P) (R : LevelCoins P L)
    (d : Fin L) : Fin P.columns → Ciphertext P      -- encrypts `keyBits P (ss d.castSucc)` under `pks d.succ`

/-- The level-0 literal ciphertexts: `cts` followed by their negations `homNot P [cts j] = G − cts j`
(`litInput`'s order, §H3.13). -/
def literalCts (P) (cts : Fin k → Ciphertext P) : Fin (k + k) → Ciphertext P

/-- Leveled evaluation of a layered NAND-form circuit on the `2k` literals: `runWith` over its gates; a gate at
level `d ≥ 1` is `bootGate` with `levelKey ⟨d − 1, _⟩` (§H3.9's padding). -/
def leveledEval (P) (lk) (Cc : DAGCircuit (k + k)) (cts : Fin (k + k) → Ciphertext P) : Ciphertext P
/-- Any fan-in-2 circuit: `leveledEval` of `(Cc.toNANDForm hC).layerNAND` on `literalCts P cts` (N3–N13). -/
def leveledEvalCircuit (P) (lk) [NeZero k] (Cc : DAGCircuit k) (hC) (cts : Fin k → Ciphertext P) : Ciphertext P

-- L1. Evaluation-key noise `m·B` (glue; `encrypts_encrypt`).
theorem encrypts_levelKey (hχ : χ.Bounded B) … :
    Encrypts P (secretVector P (ss d.succ)) (keyBits P (ss d.castSucc) j).toNat (P.lwe.samples * B)
      (levelKey P pks ss R d j)
-- L2. **Leveled correctness, noise form** [BV14, Thm 2.14 first part; BV11, Thm 3.1, Def 3.6, p014-b001]: every
-- vertex at level `d` encrypts its value under `s_d` with noise ≤ max βin (bootNoise P βk); hence the output.
theorem encrypts_leveledEval (hNAND : Cc.IsNANDForm) (hlay : Cc.IsLayered) (hdepth : Cc.depth ≤ L) … :
    Encrypts P (secretVector P (ss ⟨Cc.depth, _⟩)) (Cc.eval y).toNat (max βin (bootNoise P βk)) (leveledEval …)
-- L3. **Honest keys, every fan-in-2 circuit of NAND depth ≤ L** [BV14, Thm 3.7, p016-b001: "a leveled FHE
-- scheme, without additional assumptions"]. Deviation: decryption uses the public output level (§H3.11).
theorem decrypt_keygen_leveledEvalCircuit (hχ : χ.Bounded B)
    (hsep : 2 * (P.width * bootNoise P (P.lwe.samples * B)) < q / 2)
    (hin : 2 * (P.width * (P.lwe.samples * B)) < q / 2)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (hdepth : (Cc.toNANDForm hC).depth ≤ L) … :
    decrypt P (ss ⟨(Cc.toNANDForm hC).depth, _⟩)
      (leveledEvalCircuit P lk Cc hC fun j => encrypt P (pks 0) (x j) (R' j)) = Cc.eval x
```

### H5.14 `GSW/LeveledSecurity.lean` (L4–L5): IND-CPA by a key hybrid from DLWE

```lean
/-- The leveled FHE view: the `L+1` public keys, the `L` level keys and `Enc_{pk_0}(μ)`, from independent honest
key generations [BV11, Def 3.1, p013-b002, for the leveled scheme]. Reconstruction disclosed (§H5.13). -/
def leveledView (P) (χ) (L : ℕ) (μ : Bool) : LeveledSeeds P χ L → LeveledView P L

/-- The explicit level-`d`, position-`j` reduction (`1 ≤ d ≤ L`, `j < N`): it samples the other keys itself,
plants the DLWE challenge key as `pk_d`, encrypts the other positions of `evk_d` under it, and runs `D`
(composition of `hybridPlant` and phase-5 `reduction`). `levelTerm` is its two DLWE advantages plus
`2·(N·ε_LHL)` (`Regev.extractionError`). -/
def levelReduction (P) (χ) (L d : ℕ) (j : ℕ) (μ : Bool) (D) : … → Bool
def levelTerm (P) (χ) (L d j) (D) : ℝ

-- L4. **One level**: replacing the `N` encryptions under `pk_d` (the bits of `s_{d−1}`) by encryptions of `0`
-- costs at most `∑_{j < N} levelTerm P χ L d j D` [AP14, §5.3, p015-b002 (independent keys); GSW13, §3.2,
-- Lemma 1, p009-b002, p010-b001]; by `distAdv_multi_le_sum` over phase-5 `distAdv_encrypt_le`. Legitimate
-- because `s_d` occurs only in `evk_{d+1}`, replaced earlier (top-down order).
theorem distAdv_levelHybrid_le …

-- L5. **IND-CPA of leveled GSW-FHE from DLWE** [BV14, Thm 2.14 first part, p008-b003, and Thm 3.7, p016-b001;
-- BV11, Thm 3.1, p015-b001]: hybrids from level `L` down to `1` on both sides, then the phase-5 challenge step.
theorem distAdv_leveledView_le (D) :
    distAdv (leveledView P χ L μ₀) (leveledView P χ L μ₁) D ≤
      2 * ∑ d ∈ Finset.Icc 1 L, ∑ j ∈ Finset.range P.columns, levelTerm P χ L d j D + challengeTerm P χ L D
```

### H5.15 `Cryptography/LWE/Ratio.lean` and `GSW/PolyRatio.lean` (G16–G17; P6-Q12, as ruled)

```lean
/-- The ratio predicate (phase-5 Q16): `B`-bounded noise and `q ≤ p(κ)·B(κ)` at every `κ`; `_iff` reader. -/
def LWE.Family.RatioBounded (F : LWE.Family) (B : ℕ → ℕ) (p : PolyExpr) : Prop
/-- GSW parameters of a family: `lwe := F.parameters κ`, `width := F.residueBits.eval κ`,
`modulus_le := F.modulus_le_pow κ`; non-simp `simps` [GSW13, §3.1; phase-5 §G4]. -/
def Parameters.ofFamily (F : LWE.Family) (κ : ℕ) : Parameters
-- G16. An explicit `PolyExpr` `pBoot` with `4·ℓ·bootNoise (ofFamily F κ) (m·B κ) ≤ pBoot.eval κ · B κ`
-- [BV14, Thm 3.7, p016-b001, worst-case analogue].
theorem bootRatio_le_poly …
-- G17. **Polynomial-ratio correctness**: `pBoot.eval κ · B κ < q κ` and `B`-bounded noise ⇒ pure and leveled
-- bootstrapped GSW at `κ` are correct on every circuit (G12, L3); with `RatioBounded F B p` this is (A2)'s regime
-- [BV14, §3.4, p016-b001].
theorem decrypt_fheEval_of_ratio …
```

### H5.16 `GSW/Asymptotic.lean` (A1–A3): asymptotic forms (P6-Q10)

```lean
/-- Canonical bit encodings: a ciphertext by `Encoding.Modular.encodeMatrix P.width`; the views by
`LWE.encodeChallenge P.lwe P.width` for each public key followed by the ciphertexts (`_eq`, `_length` readers). -/
def encodeCiphertext (P) (C : Ciphertext P) : List Bool
def encodeView (P) : View P → List Bool;  def encodeFheView (P) : FheView P → List Bool
def encodeLeveledView (P) (L) : LeveledView P L → List Bool

/-- **Weak circular security, asymptotic: the headline hypothesis** (P6-Q15 A) [BV11, Def 3.8 with Def 3.1,
p015-b001, p013-b002; BV14, Thm 2.14]: every non-uniform PPT distinguisher has negligible advantage on the encoded
FHE views at `P_κ = ofFamily F κ`; equivalently, each one satisfies the concrete `WeakCircularSecure` at every `κ`
with a negligible `ε` (docstring remark). -/
def WeakCircularSecureFamily (F : LWE.Family) : Prop :=
  ∀ D : NUPPT, Negligible fun κ => distAdv (fheView (ofFamily F κ) (F.noise κ) false)
    (fheView (ofFamily F κ) (F.noise κ) true) (fun v r => D.distinguisherL κ (encodeFheView (ofFamily F κ) v) r)

/-- **(A4) Reduction efficiency, explicit hypothesis** (P6-Q10). For every non-uniform PPT distinguisher `D` of
encoded GSW views and every bit `μ`, some non-uniform PPT `D'` has, at every `κ`, DLWE advantage at least that of
phase 5's encryption reduction run on `D`:
`decisionAdvantage P_κ.lwe χ_κ (reduction P_κ μ D_κ) ≤ F.advantageAt D' κ`, where `P_κ = ofFamily F κ` and
`D_κ v r = D.distinguisherL κ (encodeView P_κ v) r`. It says that encrypting a fixed bit under the challenge key
with fresh binary coins, re-encoding and running `D` is polynomial-time. The library does not prove it: there is
no machine-level GSW encryptor, which is out of scope as for phase 5 (Q8). Real-valued on both sides, so no
transport between `(ofFamily F κ).lwe` and `F.parameters κ` is needed. -/
def ReductionEfficient (F : LWE.Family) : Prop :=
  ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
    LWE.decisionAdvantage (ofFamily F κ).lwe (F.noise κ)
        (reduction (ofFamily F κ) μ fun v r => D.distinguisherL κ (encodeView (ofFamily F κ) v) r) ≤
      F.advantageAt D' κ

/-- **(A4) for the leveled hybrid**: as `ReductionEfficient`, for the level reductions of L4. One `D'` dominates
every level `d ≤ L.eval κ` and position `j` at each `κ`; non-uniform advice can select the worst `(d, j)`. -/
def LeveledReductionEfficient (F : LWE.Family) (L : PolyExpr) : Prop :=
  ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ, ∀ d ≤ L.eval κ, ∀ j < (ofFamily F κ).columns,
    levelDLWEAdvantage F L κ d j μ D ≤ F.advantageAt D' κ
--   where `levelDLWEAdvantage F L κ d j μ D` is `LWE.decisionAdvantage (ofFamily F κ).lwe (F.noise κ)` of
--   `levelReduction (ofFamily F κ) (F.noise κ) (L.eval κ) d j μ D_κ` (L4), with `D_κ` reading
--   `encodeLeveledView`.

-- A1. **Asymptotic IND-CPA of public-key GSW** (the evk-free view) [GSW13, §3.2, p009-b002; BV11, Def 3.1]:
-- phase-5 `distAdv_encrypt_le_of_width` at each κ, (A4), `Negligible.add`, `negligible_polyExpr_mul`,
-- `negligible_two_pow_neg`.
theorem indCPA_of_dlweAssumption (F : LWE.Family) (hF : LWE.DLWEAssumption F) (heff : ReductionEfficient F)
    (hm : ∀ κ, ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤ (F.parameters κ).samples)
    (D : NUPPT) : Negligible fun κ => distAdv (realView (ofFamily F κ) (F.noise κ) false)
      (realView (ofFamily F κ) (F.noise κ) true) (fun v r => D.distinguisherL κ (encodeView (ofFamily F κ) v) r)
-- A2. **Pure FHE**: IND-CPA of the bootstrapped scheme is (A1) [BV11, Thm 3.2; BV14, Thm 2.14 second part]. Thin.
theorem fheView_negligible (h : WeakCircularSecureFamily F) (D : NUPPT) : Negligible fun κ => …
-- A3. **Asymptotic IND-CPA of leveled GSW-FHE from DLWE** [BV14, Thm 3.7, p016-b001; BV11, Thm 3.1]: L5 at
-- each κ, `N·L` level terms per side (polynomial), each `≤ 2·advantageAt D' κ + 2N·2^{-κ}`. Reconstruction
-- disclosed (§H5.13).
theorem leveledINDCPA_of_dlweAssumption (L : PolyExpr) (hF : LWE.DLWEAssumption F)
    (heff : LeveledReductionEfficient F L) (hm : …) (D : NUPPT) : Negligible fun κ => …
```

## H6. Noise and ratio ledger

| Quantity | Value | From |
|---|---|---|
| fresh public-key ciphertext (inputs, `evk`, level keys) | `m·B` | `encrypts_encrypt`, G11, L1 |
| negative literal at level 0 (leveled), `G − C` | unchanged, `m·B` | `Encrypts.sub`, `encrypts_gadget` |
| selector step (permutation instruction) | `β_V + 2N·β` | G1 (`Encrypts.mul` ×2, `.add`), C6 |
| PBP of length `L` | `L·2N·β_evk` | G2 (C7) |
| formula of depth `d` | `4^d·2N·β_evk` | G3, C14 |
| bootstrapped NAND gate (pure and leveled) | `bootNoise = 4^{decDepth+1}·2N·m·B` | G8, G9 |
| decryption condition | `2·(ℓ·bootNoise) < ⌊q/2⌋` and `2·(ℓ·m·B) < ⌊q/2⌋` | `decrypt_of_encrypts` |
| draft depth target | `decDepth ≤ 9⌈log₂N⌉ + 2⌈log₂(ℓ+⌈log₂N⌉+3)⌉ + 21` | §H3.4, F10 |
| resulting ratio | `q/B > c·ℓ·m·N^{19}·(ℓ+⌈log₂N⌉+3)^4`, `c < 2^{70}` (draft): polynomial | G13, G16 |

G7 has one key block again (r3), so the formula's input count is `N`, as in r1; r2's two blocks changed only the
input count, never the depth, so the ledger is unchanged. The leveled scheme has the same per-gate bound, and its
literal inputs add no noise, so one separation condition serves both schemes. The exponents are
large (BV14 says only "`c > c_dec` large enough"); they are polynomial, which is the claim.

## H7. Sequence, gates and units

**Order** (P6-Q1, location ruling):
1. **O1** (owner-side PR, proved): `TreeCircuit.balanced` into `FormulaArith/Combinators.lean`, `TreeNCAC`
   re-pointed. It lands first, like #332 before #333. In r3 the 6a statement job writes it as a separate small
   series on its own branch; the maintainer opens it as its own PR.
2. **6a statements**: an external Claude job (ruling of 2026-11-16) staged as an issue package from r3
   (`issued-6a-r1/`).
   - Drafts at the ruled paths, including the layering conversion (U7), each module compiled with
     `scripts/lean_check_tree.sh`.
   - It also carries the registration in `ComputationalModels.lean`, the facades and the §14 rows H18–H20
     (P6-Q17 A).
   - One statement PR stacked on O1. Nothing of 6b (O2 included) is in it.
3. **Gate 45** (Codex): the 6a statements and O1.
4. **6a fills** (proved-modulo): U1–U11 in parallel.
   - Before the N2 fill (U6), the owner-side reader `gadgetCorrect_iff` lands, if Seyoon approves it (§H2).
   - The **6b statements may overlap** Gate 45 and the 6a fills. They are drafted against the 6a statement PR,
     re-checked if Gate 45 changes a 6a signature, and frozen only after Gate 45 closes. O2 lands with or before
     the 6b statement PR.
5. **Gate 46** (Codex): the 6b statements and O2.
6. **6b fills**: U12–U19 in parallel, after Gate 46 and the merge of the phase-5 fills (#339, #338). The leveled
   units cite only ingested sources; the Gen09 citation is a later docstring-only edit (§H10).

**Merge order:** phase-5 fills (combined build) → O1 → 6a statements → 6a fills → O2 → 6b statements →
6b fills.

**Gate 45 audits** (6a and O1):
- **The model.** General maps, `IsPermutation`, `yield` in program order (`yield_append`'s direction), BV14's
  instruction order against Bar89's (disclosed), and recognition by accepting sets (`BranchingProgramFamily`,
  `InBWBP`, `InPBP`) against Bar89 §1 (`p001-b002`, `p002-b001`).
- **The host contract.** Push-form `evalWith`, generic in selector and value type; the step-indexed `evalWith_rel`;
  C8 for general maps; C6 under `IsPermutation`. Also the §14 rows of P6-Q17.
- **Barrington Thm 1.**
  - The composition-order translation and Lemma 3 by kernel `decide`; the explicit conjugator (P6-Q13).
  - Lemma 2's last-instruction form, the OR case by De Morgan, and constants with `[NeZero n]`.
  - `length ≤ 4^depth`, and the `n = 0` case of C23 through the accepting set.
- **Thm 2.** The composition-tree formula against [Bar89, Thm 2 proof] section by section, the depth constants of
  C19 and C21, and the class route through `InTreeNC` (P6-Q18). The Corollary C25 against `p004-b004`.
- **NAND conversion.** `IsNAND`/`IsNANDForm` (P6-Q16 A), `nandGadget_correct` against `GadgetCorrect`'s cost and
  depth budget, the factor 2, the size bound, the not-`IsWellFormed` disclosure, and the `NAndCircuit` name clash;
  `sorryAx` reaching `toNANDForm` only through N2.
- **Layering conversion** (P6-Q14 B). `IsLayered` against level-by-level evaluation; the odd-gap finding and the
  literal inputs (`litInput`, `[NeZero n]`); the column construction (base, parity twin, double-NAND chain) against
  §H3.13; N7–N13, with depth preserved exactly and the size constant; the name `layerNAND` against the existing
  `toLayered` (`LayeredDAG.lean:208`); `sorryAx` reaching `layerNAND` only through N12–N13.
- **Formula arithmetic.** Depth targets F5–F10 with no `Θ(ℓ)` term (§H3.3) and closed forms; F7's semantics
  through `carryBit`/`prefixVal_add`.
- **O1.** Byte comparison of the moved proofs, the only differences being the three Rule-10 repairs (§H5.8);
  `toBinary`'s statements unchanged; no duplicate left behind; the new owner `Combinators.lean` sealed.
- **Rule 10 seals.**
  - Circuits: `TreeCircuit.eval`/`depth`/`maxFanin` (through `eval_node_*_iff`, `depth_node`, `maxFanin_node`);
    `DAGGate.eval` (`eval_eq`); `DAGCircuit.eval`/`depth`; `runWith`; `rewrite` (its four lemmas);
    `toTree`/`toDAG` (their lemmas).
  - Classes and numbers: `Language.InNC`/`InTreeNC`; `bitsVal`/`prefixVal`/`carryBit`.
  - The statement job's reader census (§H2): every foreign definition a 6a sketch reads, with its reader or the
    missing one (`GadgetCorrect`).
- **Registration and attribution.** `ComputationalModels.lean` entries and facades; the §14 rows H18–H20 as ruled
  (P6-Q17 A); every `[Bar89, …]` against the ingest anchors; glue tags for the NAND and layering conversions and
  the host.

**Gate 46 audits** (6b and O2):
- **Noise ledger** re-derived by hand (§H6): the selector's `2Nβ` under `IsPermutation`, `4^d`, `bootNoise`, and
  `decDepth`'s closed form.
- **NAND-only bootstrapping** against [BV14, Def 2.13]: one key block (r3), the key-switching form of G9, the
  `(a, a)` and `(G, G)` padding, the output coordinate `σ 0`, and the evaluation key of P6-Q8.
- **O2** as a proof: `decodeLo`/`decodeHi` and the interval reader.
- **Correctness.** Pure FHE for every depth (G10, G12), the conversion route (G18), and compactness by typing.
- **The leveled scheme** (P6-Q14 B). The consecutive chain (`N·L` ciphertexts), the level-0 literal ciphertexts
  (`G − C`), correctness for layered NAND circuits of depth `≤ L` and for every fan-in-2 circuit through N3–N13,
  and the output level as public information (disclosed). The key hybrid's top-down order and sum structure
  (L4 over `N` positions, L5), with `distAdv_multi_le_sum`/`hybridPlant` and `abs_sub_le_sum_hybrids` reused.
  Citations of ingested sources only, and the reconstruction disclosure (P6-Q19 B).
- **Security hypotheses.**
  - `WeakCircularSecure`'s per-distinguisher form (P6-Q15 A) and the headline `WeakCircularSecureFamily` against
    [BV11, Defs 3.1, 3.8].
  - The A4 hypotheses: the exact quantifier structure, domination rather than construction, and the advice
    remark.
  - A1 and A3 from the unchanged `DLWEAssumption`.
- **Ratio** (P6-Q12). `RatioBounded`, `ofFamily` (type-level Rule 10: `(ofFamily F κ).lwe` against
  `F.parameters κ`), and `pBoot` explicit.
- **Rule 10 seals.**
  - Phase 5: `Encrypts`, `encrypt`, `decrypt`, `decomposeVec`, `reduction`, `realView`.
  - LWE and asymptotics: `decode`, `advantageAt`, `encodeChallenge`, `encodeMatrix`, `distinguisherL`.
  - 6a: `barrington`, `evalWith`, `toNANDForm`, `layerNAND`, `litInput`, `IsLayered`, `FormulaArith.*`.
- **No restatement:** 6b imports the 6a modules and restates none of them.

**Units.** Each fill unit owns its file(s), so units never share a file. Dependencies are on frozen statements only,
so under the proved-modulo rule every 6a unit can start once Gate 45 closes, and every 6b unit once Gate 46 closes.
Estimates are fill (proof) lines. r3 inserts the layering unit as U7, so r2's U7–U18 are r3's U8–U19. In the "vs r2"
column, *new* means new in r3, *changed* means re-scoped by r3, and *r2* means unchanged from r2 (r2's number in
brackets where it moved).

| Unit | File | Targets | Statements needed | Est. fill | vs r2 |
|---|---|---|---|---|---|
| O1 | owner PR: `FormulaArith/Combinators` (`balanced`), `TreeNCAC` | 4 (moved, proved) | — | ~170 moved | changed |
| U1 | `BranchingPrograms/Defs` | C1–C4 | — | 120–180 | r2 |
| U2 | `BranchingPrograms/Eval` | C5–C8 | U1 | 150–230 | r2 |
| U3 | `BranchingPrograms/Barrington` | C9–C16 | U1 | 360–520 | r2 |
| U4 | `BranchingPrograms/BarringtonConverse` | C17–C21 | U1, O1, U8 | 250–400 | r2 |
| U5 | `BranchingPrograms/NC1` | C22–C25 | U1, U3, U4 | 180–320 | r2 |
| U6 | `CircuitComplexity/NANDForm` | N1–N6 | `gadgetCorrect_iff` | 150–250 | r2 |
| U7 | `CircuitComplexity/NANDLayering` | N7–N13 | U6 | 150–250 | **new** |
| U8 | `FormulaArith/Combinators` | F1–F3 | O1 | 150–220 | r2 (U7) |
| U9 | `FormulaArith/CarrySave` | F5–F6 | U8 | 250–400 | r2 (U8) |
| U10 | `FormulaArith/Compare` | F7–F8 | U8 | 150–250 | r2 (U9) |
| U11 | `FormulaArith/ModSum` | F9–F10 | U8–U10 | 150–250 | r2 (U10) |
| O2 | owner PR: `LWE/BitEncoding` | G4 → `decode_iff_mem_Ico` | — | 60–90 (proved) | r2 |
| U12 | `GSW/Branching` | G1–G3 | U2, U3 | 150–250 | r2 (U11) |
| U13 | `GSW/DecryptFormula` | G5–G8 | U8–U11, O2 | 200–330 | changed (U12; one block) |
| U14 | `GSW/Bootstrap` | G9–G13, G18 | U6, U12, U13 | 280–440 | changed (U13; one block) |
| U15 | `GSW/Circular` | G14–G15 | U14 | 60–120 | changed (U14; per distinguisher) |
| U16 | `GSW/Leveled` | L1–L3 | U7, U14 | 180–300 | changed (U15; chain, layered) |
| U17 | `GSW/LeveledSecurity` | L4–L5 | U16 | 230–370 | changed (U16; `N` per level) |
| U18 | `LWE/Ratio`, `GSW/PolyRatio` | G16–G17 | U14, U16 | 140–220 | r2 (U17) |
| U19 | `GSW/Asymptotic` | A1–A3 | U15, U17, U18 | 150–280 | changed (U18) |

The layering estimate is the ruling's (+150–250). The column invariant with exact depths is the bulk; §H8 item 19
records the risk of its upper end. U16 and U17 shrink a little: under the consecutive chain both arguments of a gate
share a key, and each hybrid step has `N` positions instead of `N·d`.

**Totals.**

| | r2 | r3 |
|---|---|---|
| fill units | 18 (6a: 10, 6b: 8) + owner PRs O1, O2 | 19 (6a: 11, 6b: 8) + owner PRs O1, O2 |
| target rows (lemmas) | 65 rows (about 95 lemmas) | 72 rows (about 102 lemmas): C 25, N 13, F 9, G 17, L 5, A 3 |
| fill lines, 6a | 1,910–3,020 | **2,060–3,270** |
| fill lines, 6b | 1,430–2,370 | **1,390–2,310** |
| fill lines, total | 3,340–5,390 | **3,450–5,580**, plus O1 (~170 moved) and O2 (60–90), both proved |
| statement surface | about 2,800–3,300 lines; 19 files, 2 facades | about 2,950–3,500 lines; 20 files, 2 facades |

The r3 change is +110 to +190 fill lines: the layering conversion (U7) +150–250, the leveled units U16–U17 −40 to
−60. The r2 growth over r1 (+1,190 to +1,990) was:
- Thm 2 (U4, part of U5): +300–520, the ruling's +300–500;
- the leveled scheme (now U16, U17): +450–730, the ruling's +400–700;
- the NAND conversion (U6, G18): +180–290;
- the general model and host (U1, U2): +120–190;
- the asymptotic forms (now U19): +150–280.

Every math file stays below the 1,000-line split threshold. `Barrington.lean` is the largest, at about 550–720
lines filled; it exceeds the 600-line target only at the top of the range, for one structural induction whose cases
share local lemmas. `NANDForm.lean` and `NANDLayering.lean` stay at about 300–450 lines each (§H4).

**The 6a statement job** (`issued-6a-r1/`): every 6a module above (11 files and 2 facades), O1 as its own series,
the registrations and the §14 rows; about 1,600–2,100 statement lines, including the definitions with bodies
(`barrington`, `compTree`, `toFormula`, `nandGadget`, `layerGates`, the formula arithmetic). It contains nothing
of 6b and does not depend on Gen09.

## H8. Risks

1. **Depth constants** (r1). A single `Θ(ℓ)` term in the decryption depth makes the ratio condition unsatisfiable
   (§H3.3). Gate 45 checks the closed forms, and no fill may introduce Shannon or DNF steps over `log q`-bit values.
2. **`decode` is an interval** (r1, now settled). `lo`/`hi` are fixed by O2 and checked by computation for
   `2 ≤ q < 300` against Mathlib's `valMinAbs` convention. O2's proof is the remaining work.
3. **Composition order** (r1). A wrong order still yields a five-cycle in Lemma 3, so C9 alone cannot catch it;
   C13's statement is the check, and §H3.6's computation is recorded for the gate.
4. **NAND form is not well-formed** (P6-Q16 A, disclosed). `¬` gates of fan-in 2 violate `IsWellFormed`.
   Lemmas assuming it (`toTree_eval`, `deMorgan_*`, `binarize_*`) do not apply to NAND-form circuits;
   bootstrapping does not need them.
   The size bound `n + 4·#gates` is the generic `rewrite` bound, not the tight `3·#gates`.
5. **Name clash.** `BoolCircuit.NAndCircuit`/`TreeCircuit.toNAnd` (`Basic.lean:356/465`) are AND-rooted normal
   forms. The new names avoid `NAnd`, and the docstrings say so.
6. **Thm 2's circuit model** (P6-Q18 A). A formula has size `l^{O(log w)}`, polynomial for fixed `w`, which is all
   NC¹ needs. A gate-efficient DAG form would need relocation ledgers like `Adder.lean`'s. Reaching `DAGCircuit` adds
   one level (`toDAG_depth_le`).
7. **Constants and `n = 0`.** Thm 1 needs `[NeZero n]` (constant nodes read variable 0), and so does the layering
   (a fan-in-0 gate's twin reads `x₀, ¬x₀`). The family statements handle `n = 0` through the accepting set. The
   decryption formula has `N ≥ 1` inputs.
8. **Kernel `decide` on `Equiv.Perm (Fin 5)`.** Lemma 3 is cheap. The conjugator over all 24 × 24 pairs may be
   slow; the fallback states C10 over the explicit cycle structure. No `native_decide` (none remains in the
   library).
9. **Computability** (P6-Q13). `barrington` is defined by well-founded recursion on a nested inductive: computable,
   but not kernel-reducible, so `decide` is used only on closed `Fin 5` facts. `evalWith`'s `Finset` sums are
   computable. `toFormula` may be `noncomputable`.
10. **Worst case against probabilistic** (r1). BV14's Lemma 3.6 and Thm 3.7 are probabilistic; the formal versions
    are worst-case and lose polynomial factors. The public-key evaluation key costs one factor `m` (P6-Q8).
11. **Circular security** (r1, extended). Its truth for GSW is open [Pei16, §6.1.2]. Over all function-level
    distinguishers a concrete predicate would hold only for `ε` near `1`; P6-Q15 A therefore states it per
    distinguisher, and the asymptotic family predicate is the headline.
12. **Leveled scheme** (P6-Q14 B, P6-Q19 B).
    - Wires of unequal depth are resolved by the layering conversion (U7); the evaluation key is the consecutive
      chain (`N·L` ciphertexts).
    - **Odd gaps** (finding, §H3.13): over positive inputs at level 0 no layering exists in general (layered NAND
      circuits compute monotone or antimonotone functions only). The literal inputs fix it at no cost in GSW
      (`G − C`); a statement over positive inputs only would be false, and the probes of the 6a job check it.
    - The output level is public information.
    - Each hybrid step's messages (the bits of `s_{d−1}`) are random. The multi-ciphertext lemma takes fixed
      messages, so the step conditions on `s_{d−1}` inside the reduction's coins. This is the longest proof of 6b,
      hence U17's estimate.
    - Gen09 is not ingested yet; the statements cite ingested sources only and disclose the reconstruction, and
      nothing waits for it (§H10).
13. **Asymptotic statements.**
    - No `NUPPT`-bridge extension is needed (§H3.12). `BitPublicKeyScheme.SingleBitSecure` stays out of scope
      because it needs a machine-level GSW.
    - (A4) is a domination hypothesis. For the leveled form, one machine must dominate every `(d, j)`, which holds
      with advice (NUPPT advice picks the worst pair per `κ`); the docstring says so.
    - The view encodings are new definitions over `Encoding.Modular`. `ofFamily` raises the type-level Rule-10
      transport between `(ofFamily F κ).lwe` and `F.parameters κ`; the hypotheses are real-valued to avoid it, and
      `hm` is read through `ofFamily`'s `simps` readers.
14. **Unregistered hosts** (P6-Q17 A). The phase consumes `runWith` and `DAGCircuit.rewrite`, both public but
    missing from §14; the 6a statement job records them as H19 and H20, and Gate 45 audits their contracts.
15. **Private helpers** (r1). `combine` is promoted by O1. `Parity`'s dual-rail XOR stays private until the dedup
    queue; copying it would be duplication needing approval.
16. **Shared-file changes.** Each needs Seyoon's approval:
    - Lean: `ComputationalModels.lean` (models and conversions), `TreeNCAC.lean` (O1), `LWE/BitEncoding.lean` (O2),
      `TCSlib.lean`, and the `CircuitComplexity`, `LWE` and GSW facades; proposed in r3, the one-line reader
      `gadgetCorrect_iff` in `DAGTransform.lean` (before the N2 fill; §H2).
    - Records: `machine-library-design.md` §14 and the gadget registry subsection.
17. **Source fidelity.** Disclosed deviations:
    - BV14's coordinate 1 against our `σ 0` (§H3.7);
    - fan-in padding (§H3.9);
    - literal inputs and layering for the leveled scheme (§H3.13);
    - the carry-save tree (F5);
    - the reconstructed key chain and hybrid order (§H1 gap 1, P6-Q19 B).

    r2's two key blocks in the augmented formula are withdrawn (G7).
18. **Scope and schedule.** Fill grows from 2.2–3.4k (r1) to 3.3–5.4k (r2) and 3.5–5.6k lines (r3). 6a is
    independent of GSW and can land while 6b is drafted.
19. **Layering estimate** (r3). The ruling's +150–250 assumes the column invariant goes through in one induction.
    Exact depths (`depthAt` of every copy) through `runWith` are the bulk; if they need their own ledger, U7 may
    reach about 300 lines. The file stays well under 600.
20. **Rule 10 and the moved O1 proofs.** Three moved proofs read `TreeCircuit.eval` by `simp` (§H2); O1 repairs
    them through published readers, so the byte comparison of O1 shows exactly those three hunks.

## H9. Questions P6-Q14 to P6-Q19 (ruled 2026-11-16)

r2 raised these six questions; Seyoon ruled them the same day. The options as asked are in `questions.md`, and the
rulings in `rulings.md`. r3 applies them as follows.

- **P6-Q14, wires of unequal depth: B (changed).** Consecutive keys (`N·L` ciphertexts) over layered circuits; a
  generic layering conversion in 6a (Gate 45), double-NAND chains with care for odd gaps, +150–250 lines.
  Applied in §H3.11, §H3.13, §H5.6b, §H5.13–H5.14, U7, U16–U17.
- **P6-Q15, the concrete `WeakCircularSecure`: A.** Per distinguisher, `WeakCircularSecure P χ D ε`;
  `WeakCircularSecureFamily` is the headline. Applied in §H3.12, §H5.12, §H5.16.
- **P6-Q16, representation of NAND form: A.** A predicate on `DAGCircuit` (`¬` gates of fan-in `≤ 2`), an instance
  of `rewrite` with depth factor 2, padding `(a, a)` and `(G, G)`, not `IsWellFormed` (disclosed). Applied in
  §H3.9, §H5.6.
- **P6-Q17, host registry rows: A.** H18 `BranchingProgram.evalWith`; H19 `runWith`/`runWith_rel`; H20
  `DAGCircuit.rewrite`; records only, audited at Gate 45. Applied in §H2, §H4, §H7.
- **P6-Q18, Thm 2's circuit model: A.** A fan-in-2 `TreeCircuit` formula in Bar89's three sections, reaching
  `InNC 1` through `InTreeNC.inNC`. Applied in §H3.10, §H5.4.
- **P6-Q19, source for the leveled key chain: B (changed), with Seyoon's update.** Ingest Gen09 (PDF pending);
  nothing waits for it; cite ingested sources only and disclose the reconstruction; a docstring-only follow-up.
  Applied in §H1, §H3.11, §H5.13–H5.14, §H10.

**No new question in r3.** The odd-gap finding (§H3.13) is resolved inside P6-Q14 B by literal inputs at level 0,
which Bar89's model already has and GSW provides for free; Gate 45 audits it. If Seyoon prefers another treatment
(for example inputs encrypted under every key), only N7–N13 and L2–L3 change.

## H10. Not in this phase (recorded)

- Uniform `NC¹`/BWBP (Bar89 §6), width-4 circuits and the word problem (Bar89 abstract).
- A machine-level GSW (`BitPublicKeyScheme` instance) and a proof of (A4).
- The AP14 accumulator route, small-secret LWE and its ACPS09 equivalence (DW-6), modulus switching.
- Worst-case lattice approximation factors.
- Re-pointing `Parity.lean`'s dual-rail XOR (dedup queue).

**Deferred follow-ups** (recorded, not scheduled):
- **After the Gen09 ingest, add `[Gen09, loc]` to the leveled-scheme docstrings** (P6-Q19 B, Seyoon's update of
  2026-11-16). Docstring-only: `GSW/Leveled.lean`, `GSW/LeveledSecurity.lean` and A3 in `GSW/Asymptotic.lean`, plus
  §H1's source table. No statement changes, and nothing waits for it; the reconstruction disclosure stays, now
  pointing to the ingested passage.
- The owner-side reader `gadgetCorrect_iff` (§H2), before the N2 fill, if Seyoon approves it.

## H11. Proposed plan rows (for the maintainer)

Phase table:

| Phase | Frozen surface to prepare | Fill starts only after |
|---|---|---|
| 6a | BP model and host; Barrington Thm 1, Thm 2; BWBP = NC¹; NAND form; layering; formula arithmetic | Gate 45; O1 |
| 6b | PBP evaluation; decryption formula; NAND bootstrapping; pure/leveled FHE; security; ratio | Gate 46; O2; ph. 5 |

In the 6b row, "ph. 5" means that the phase-5 fills (#339, #338) are merged.

Decision-log row:

| Date | Decision/evidence | Status |
|---|---|---|
| 2026-11-16 | Phase-6 plan section r2, under rulings P6-Q1–Q13 and the location ruling. Records. | Q14–Q19 open |
| 2026-11-16 | Phase-6 plan section r3, under P6-Q14–Q19 (Gen09 blocks nothing). 6a statement job staged. | ruled |

Detail for the r3 row: gates 45 (6a) and 46 (6b); units U1–U19 plus owner PRs O1 and O2; fill 3.5–5.6k lines
(r2: 3.3–5.4k; r1: 2.2–3.4k). New: the layering conversion U7 (N7–N13) and the odd-gap finding; the
consecutive key chain; the per-distinguisher concrete `WeakCircularSecure`; one key block in G7; Gen09 to be
ingested, cited later by a docstring-only follow-up. The 6a statement job is issued from r3 (`issued-6a-r1/`).

## ===== policy.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/lattice-gsw/gates/50-gsw-6a-fills/findings-r1.md (records, at 9ae6b909305f868f51f5cc05787c66e4d336bf74; equal at the pin) =====

# Gate 50 · round 1 findings (Codex), filed verbatim

Received from Seyoon as an upload, 2026-11-18 (`gate50-gsw-6a-fills-findings.md`).

---

# Gate 50 — GSW 6a fills, round 1

**#366: CLEAR. #368: CLEAR. Overall: CLEAR.**

Counts below are unresolved findings at the audited pins. The historical findings graded later are not counted again.

| Scope | Blockers | Majors | Minors | Notes | Verdict |
|---|---:|---:|---:|---:|---|
| #366 | 0 | 0 | 1 | 1 | CLEAR |
| #368 | 0 | 0 | 3 | 0 | CLEAR |
| Overall | 0 | 0 | 4 | 1 | CLEAR |

## Audited pins

| Material | Pin |
|---|---|
| #366 head | `597fb736e545706a058cc212243a13f6dadfeceb` |
| #366 tree / merge base | `df05652d512a702fa8e379fe3f16258f0e1d20d5` / `555f0fe1b10a20d1be72386a97c6fe7a2f39c204` |
| #368 head | `1953898b18a33ab2cd533820c5754a1aacffeb44` |
| #368 tree / base | `89952a4a153c1183e0345f88a10568a936762a7d` / `55f553715f280be36827ad86a94c93db39ec56c3` |
| Campaign records | `b1392d065d0a8f496db8e01b6bdad746bc847ffe` |
| Exchange | `b14712e545ce9a6e08d0070ef134358cc5c8d952` |
| Gate-45 freeze | `d154c8830fc8ffc52671b41992e7dbef61e30959` |

The live PR heads match these pins. Scope follows the dispatch: #360, its addendum, all fills, LE-gf1–4, both records-tip merges, LE-g50, and all of #368. The previously audited #358/#359 content, 6b statements, cleanup Stage 1, #365, snapshot adoption and merge order are excluded.

## Findings

| ID | Severity | PR · location | Finding and evidence | Proposed fix |
|---|---|---|---|---|
| **G50-01** | **minor** | #366 · `BranchingPrograms/{Defs,Eval,Barrington}.lean`; `CircuitComplexity/{NANDForm,FormulaArith/Combinators}.lean` | Documentation still describes the admitted state: module sentences at Defs:32, Eval:35 and Barrington:32; the N2/`sorryAx` sentences at NANDForm:61 and :455. Combinators:303 and :329 still say the literal readers are missing. These disagree with the proved head and published readers. Also, the new `barrington_length_pos_aux` at Barrington:613 has a formula and sketch but lacks the glue classification promised by pack question 5. These are documentation defects, not proof or statement defects. | Correct the sketches and helper classification; make the frozen statement/module-prose corrections through a recorded documentation exception. |
| **G50-02** | **minor** | #368 · `GSW/Scheme.lean`; `Encryption/PublicKey/EnsembleSecurity.lean:116` | `hybridPlant_eq` has an accurate verbal description but omits the explicit equation and glue classification requested for the reader API. The retained sketches of `decrypt_eq_decode_errorSum` and `decrypt_of_encrypts` describe the residual calculation without identifying the newly extracted public lemma. The formal statements and proofs are correct. | Add the reader equation and glue note; identify `decrypt_eq_decode_dotProduct` in the affected sketches. |
| **G50-03** | **minor** | #368 · `evidence-s8.zip`, `owner-prereqs-6b-s8/SHA256SUMS` | The manifest includes itself with the empty-file hash. That entry fails verification. All other **184 entries pass**, and the containing ZIP is independently bound by the outer manifest and the pinned records blob. Necessary evidence remains verifiable, so this is not a major binding failure. | Issue a replacement evidence archive whose manifest excludes itself, with an appended records correction and new archive hash. |
| **G50-04** | **minor** | #368 · PR description, “Gating” and replay report | The description still assigns gating to the 6b fills or a small-items gate and reports only the snapshot-7 replay. The recorded ruling instead assigns Gate 50, and the snapshot-8 replay is present and valid. | Update the description to name Gate 50 and link the snapshot-8 replay record. |
| **G50-05** | **note** | #366 · phase-1 duplication disposition and phase-2 sweep | The phase-1 review deferred U1/U2 without filing the required disposition; the later name/body sweep missed U1–U3. Disclosure and a search returning no matches did not establish acceptance or absence of semantic duplication. LE-g50 now repairs all three, so no duplicate debt remains from these items. The retained “on #6 … No duplicate was found” PR sentence describes that limited historical scan, not a clean semantic census. | Record duplication dispositions when discovered and distinguish name/body scans from statement-shape review. No further code repair is required for U1–U3. |

## Historical findings and sweep grades

These grades apply to the original defects. “Closed” means repaired in the audited head.

| Item | Audit grade | Disposition / reason |
|---|---|---|
| GF-F01 | **major**, agree | Closed by LE-gf1: both logarithm bounds cite `Nat.pow_log_le_add_one`. |
| GF-F02 | **major**, agree | Closed by LE-gf3: four owner-side promotions, two visibility promotions, fourteen private-copy deletions and qualified consumers. |
| GF-F03 | **major**, regraded from minor | The old bound is a direct instance of `Finset.sum_le_card_nsmul`. Rebuilding it from `sum_le_sum` and `sum_const` is still an inline re-derivation under the dispatched rule. Closed by LE-gf4. |
| GF-F04 | **minor**, agree | Closed by the expressly ruled, one-sentence LE-gf2 exception. |
| GF-F05 | **note** | Size accepted by GF-W3; 948 lines after the documented rewrap, below 1,000. |
| GF-F06 | **note** | Landing dependency resolved: U8 retains LE-g45’s `const_eval` proof. |
| GF-F07 | **minor**, regraded from info | The REPORT recount exceptions are factual documentation defects; the pack reconciles them. GF-F01’s duplication omission retains its separate major grade. |
| GF-F08 | **note** | The job name in NC1’s permitted module sentence is cosmetic, not a fidelity defect. |
| GF-F09 | **note** | Process weakness; the resulting code defects are graded separately. See G50-05. |
| Sweep U1 | **major** | The substitution bounds repeated the promoted list-bound argument. Closed by LE-g50’s public-lemma calls. |
| Sweep U2 | **major** | The private mapped-list bounds became instances of the new public lemmas. Closed by deletion and redirected consumers; TreeNCAC’s two seal failures also disappear. |
| Sweep U3 | **major**, not merely borderline | The orbit equality is the full-support case of the existing Mathlib cycle-on lemma. Closed by LE-g50’s citation-based proof and attribution. |

## Verification and audit conclusions

**Integrity and provenance.** All 16 outer-manifest entries and all 89 entries inside `verification-r1.zip` verify. The seven nested archives verify except G50-03. All 58 source-file hashes verify; the copied TCSlib/reference files and 70 manifest-listed records/evidence/snapshot files match their pinned git blobs. All **53 bundle sections** match their source material. I additionally retrieved the worker delivery at `60703442`: its **955-entry outer** and **939-entry evidence** manifests pass. The deterministic base and all **seven worker commits reproduce hash for hash**, and all six delivered source files match that reproduced head.

**Freeze and proofs.** Independent comparison against `d154c883` finds **zero changed declaration headers**, no changed existing definition bodies, 78 additions and the two disclosed private removals. Exactly **36 public docstring changes are sketch-only**; `layerNAND` is the sole outside-sketch change and matches LE-gf2. The named-public declaration delta against the tip is **289 ADDED / 1 REMOVED / 0 CHANGED**; the removal is `eval_node_nil` leaving `Hierarchy`, with its destination in `Combinators`. #368 adds two declarations and changes only the disclosed private proof body.

All **98 targets**, independently identified from the frozen admissions plus `const_eval`, occur uniquely in the axiom evidence. The final census contains **853 constants**, only standard axioms, **zero TRACE lines**, and no `sorryAx`. The six promoted lemmas and the structural definitions are also covered. Source review found no hidden restriction or weakening in the conjugator argument, commutator/De Morgan cases, length bound, converse/NC¹ proofs, NAND gadgets, layering invariants, carry-save reduction, comparison or modular interval sum. The fixed permutations use kernel `decide`; C10’s general conjugacy proof uses orbit matching for arbitrary five-cycles.

**API, sources and reuse.** The fifteen #360 readers have the appropriate owners, binders and equations, with no added simp attributes. The three literal readers legitimately use their owner’s well-founded equations. The six public promotions have suitable homes and formula docstrings. #368’s decryption identity holds for every stated `P`, `s`, `C`: splitting the last coordinate gives exactly the Regev residual. Its result-level source tags are supported by the supplied GSW13/BV14 passages and the module’s documented representation deviations. `hybridPlant_eq` repeats the definition’s body exactly. The Barrington reference is supported. Documentation exceptions are recorded above.

LE-gf1/3/4 and LE-g50 consume the public results they replace; LE-gf2 is limited to the ruled sentence. I found no additional unaccepted re-proof in the reviewed declarations or inline arguments. The disclosed padded-value pair uses different representation interfaces and shared public arithmetic lemmas; the negation bounds retain equality statements, rather than the promoted upper-bound statements. Neither supplies a further instance of U1–U3.

**Rule 10.** I checked **74 owner/root seal records** against reconstructed owner bytes, git blobs, insertion hashes, probe hashes, resolved names/homes, raw logs, and installation/EOF counts. The final 22-owner run has no new failures; inherited failures remain Adder 3, DAGTransform 11, Hierarchy 2 and TreeDAG 25. TreeNCAC improves **2 → 0**. The final root run verifies **14,105 requests**, rc 0, zero errors. Attempt-2 controls have six failing sealed negatives, six passing sealed positives, and passing unsealed counterparts. The explicit-unfold comparison introduces no new foreign read. #368’s seals retain Scheme **101/0** and EnsembleSecurity **1268/6**, with the same inherited failing declarations. Together with source inspection, this suffices for the in-scope changes; it does not clear the inherited failures. Carrying the controls and scan across LE-g50 is justified by its deletion/citation-only delta and renewed owner seals.

**Replay binding.** Every per-module build source hash matches the claimed git revision, and raw log hashes and state/output-map hashes reconcile:

| Evidence | Bound revision/tree | Rebuilt modules | Result |
|---|---|---:|---|
| #366 phase 2, snapshot 6 | `ccca6f80` | 564 | rc 0; state 1,445 |
| #366 snapshot 7, then #365 merge | `e4d77a5e`, `93ae671e` | 564 + 22 | rc 0; state 1,447 |
| LE-g50 | `597fb736` | 16 | rc 0; state 1,447; zero warnings |
| #368 snapshot 7 | `1953898b` | 67 | rc 0; state 1,434 |
| #368 snapshot 8 | tree `ab098201a13ad10829914bfbc6bedcbb2fe52e9e` | 67 | rc 0; state 1,434 |

The records-tip merges preserve #366’s earlier change exactly. LE-g50 changes precisely its three declared source modules and their three output hashes. All 67 #368 rebuilt objects and logs equal the snapshot-7 run. I independently reproduced the claimed merge trees and verified their Lean equality to the respective replay trees. No necessary evidence-binding gap remains. Adoption and the second PR’s combined-tree replay remain maintainer merge conditions, outside this verdict.

This audit used independent git/source checks, patch reproduction and the recorded verification evidence. I did not run Lean or independently rehash the maintainer-hosted olean files. SSH signature blocks are present on #366’s 22 first-parent commits and #368’s commit; their signatures were not cryptographically verified.
