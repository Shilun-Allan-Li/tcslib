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