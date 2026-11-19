# GSW 6b U14+U16 `gsw-6b-u14-u16` · final r1 · maintainer review (phase 1 static, phase 2 Lean replay)

**Verdict after phase 2: ACCEPT. No landing edit.** All seven targets are proved as stated: G9, G10, G18, G12 and G13
of `GSW/Bootstrap.lean`, and L2 and L3 of `GSW/Leveled.lean`. So is the one ruled public helper `encrypts_bootGate`,
whose statement is the brief's, byte for byte. Phase 2 passed with no new finding, both at B6 and stacked on the records
tip with U12 and U13. The details are in [`phase2.md`](phase2.md).

- **Findings:** 0 blockers, 0 majors, 1 minor, 4 infos.
  - The minor is **on our side**, not the worker's. U1416-F01: the pre-dispatch sweep missed a fact that two units
    need, `m·B ≤ bootNoise P (m·B)`. This unit's G12 and U18-U19's G17 now each derive it inline. There is no change to
    this delivery.
  - The infos:
    - U1416-F02: G12's `hs` is the third inline copy of the LWE seed identity, and no published lemma states it (W1).
    - U1416-F03: the private `four_pow_clog_le` has no Mathlib or TCSlib equivalent.
    - U1416-F04: proof text shared with phase 5 (`eval_encrypts`, `homGate_encrypts`'s `¬` step); within the allowance.
    - U1416-F05: count slips in `REPORT.md`, the seal-count method, and the worker's host housekeeping.
- **Phase 2 (2026-11-19, 01:16–01:36 UTC).** There were two replay trees: B6 + unit, and records tip + unit.
  - **Build:**
    - B6: 10/10 rc 0, including the root `TCSlib`, with 0 errors. Admissions are **35 in 14**, the brief's C2 count.
    - Stacked: 12/12 rc 0, including the root, with 0 errors. Admissions are **26 in 12**.
    - No `audits/*/Checks` imports a changed module. Both owners' oleans are byte-identical between the two trees.
  - **Axioms:** 65/65 stored constants censused.
    - At B6, 8 constants reach `sorryAx`, each only through the allowed U12/U13 targets (0 disallowed, no owner
      declaration in any trace).
    - **On the stack, 0 `sorryAx`**: all eight are `[propext, Classical.choice, Quot.sound]`.
  - **Seals:** canonical coe-A and seal B give 0 errors on both owners and both heads. Bootstrap has 444 requests and
    Leveled 479, all verified.
  - **Controls:** 6 liveness pairs, two of them for `encrypts_bootGate`, ALL_OK.
  - **Unfold scan:** 0 foreign definitions.
  - **Lint:** unchanged.
  - **Snapshot #11:** rehashes 0/0/0 before, after, at the end, and after the trees were deleted.

## What was reviewed

- **Delivery.** `inbox/fills/gsw-6b-u14-u16/` on `exchange/pass-shelat-ch5-8`, at
  `b614ee7774e7b29f5f68f5d0df01c05ea932e3f1`. The folder's final commit is `90b4c3a1549008f93ae35a0395bca88f0f557f73`
  ("fill gsw-6b-u14-u16: final"); its checkpoint is `e727c64dd02c0219f6f4c4588638ebea946d14cc`.
  - **The two folder commits.** Both are unsigned (0 `gpgsig`) and touch only `inbox/fills/gsw-6b-u14-u16/`. The final
    changes only `REPORT.md` and `SHA256SUMS`, so the checkpoint already delivered the same head, `src/`, patches and
    evidence. `b614ee77` itself is another campaign's commit (Arora–Barak `outbox/`) and touches nothing of this unit.
  - **Extraction.** With `git archive`, the delivery has 271 files: `REPORT.md`, `SHA256SUMS`, 2 patches with
    `COMMITS.tsv`, `src/` (2 files) and `evidence/` (264 files).
- **Contract.** The issued pack at the records pin `27e53754d28703907571cacbaf905b441e03c393`:
  - `README.md`, `COMMON.md`, `U14-U16/brief.md`, `U14-U16/dispatch-prompt.md`, `dup-sweep.md` (§0, §U14-U16),
    `targets.txt`, `closures.txt`, `base-sorries.txt` and **`rulings.md`** (`855ea62b…`; Q-6BF-1..7 all A). The pack's
    `SHA256SUMS` verifies at the pin (52 files).
  - Since the pin, only the three U14–U19 dispatch prompts changed, by `f5dade19` ("prompts pinned"): the pin hash was
    filled in, 4 lines each. That is why they no longer match the pack's own `SHA256SUMS`. The brief, `COMMON.md`,
    `dup-sweep.md` and `rulings.md` are unchanged.
  - Also read: handoff §2 (rules 10 and 15, the duplication rule) and `policy.md` §1–§3.
- **Rulings in force.**
  - **Q-6BF-2 A** (one unit for U14 and U16).
  - **Q-6BF-3 A**: exactly one public helper here, `encrypts_bootGate`, as a pure insertion, decls2 ADDED = 1, sealed
    with its own controls. Any other new public declaration is E-SCOPE.
  - Gate 46 and the 6b rulings, none of which bears on these proofs otherwise.
  - Gate 53's G53-01 lesson: every duplication probe below carries its use's hypotheses.
- **Base.** B6 = `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`, tree `845bdc98…`, checked with `git rev-parse`.
- **Records tip.**
  - At the replay it was `c63ee44f47c72a09545235fddccaa765efd64568`, `TCSlib` tree `745bf4b4…`: U12 and U13 merged as
    #392. Against B6 it changes only `GSW/Branching.lean` and `GSW/DecryptFormula.lean` under the Lean paths.
  - At the end of the review it was `c87eb40365e8ccd44f02ca54f6e5e4f0e50de633`, with records-only changes since (the
    same `TCSlib` tree).
- **Precedent for format and method:** `U12/final-r1/` and `U13/final-r1/`, with Gate 53's findings.
- **Tools.**
  - Phase 1 used `git` and `python3 -I` only.
  - Scratch work is under
    `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g6b-u1416/`.
  - Nothing was committed or pushed. The main checkout was only read, apart from this folder.

## Checks

| Check | Result |
|---|---|
| **Integrity** | **PASS.**<br>• Both manifests pass `sha256sum -c`: 270 top-level rows and 263 evidence rows.<br>• No duplicates, no leading `./`, and neither manifest lists itself.<br>• Each manifest equals its tree exactly.<br>• The top level binds `evidence/SHA256SUMS`. |
| **Reproduction (C13)** | **PASS: 2/2 hashes reproduced.**<br>• `git am` on B6 in a scratch sparse worktree, unsigned, with committer data from `COMMITS.tsv`, gives `e09ce69861010e646fa22cdd212b219ed7acf94d` and then **`9852429ef14ce063fcf11ff860e7262f92063d55`**, REPORT's head.<br>• 0 `gpgsig`.<br>• `src/…/Bootstrap.lean` and `src/…/Leveled.lean` equal the head byte for byte. |
| **Scope** | **PASS.**<br>• `git diff --stat bff0567b 9852429e` shows only the two owned files: Bootstrap +189/−20, Leveled +102/−9.<br>• Commit 1 touches only `Bootstrap.lean`, and commit 2 only `Leveled.lean`.<br>• `git merge-tree --write-tree` with the records tip is clean: tree `b3a0ad09…`, `TCSlib` tree `8dc09446…`. |
| **Statements (C3), independently** | **PASS.**<br>• decls2 (records copy `fa81981a…`) at the head against B6: **ADDED exactly `encrypts_bootGate`, 0 CHANGED, 0 REMOVED**. Leveled is 0/0/0.<br>• The helper's statement (`Bootstrap.lean:270`) is **byte-identical to the brief's proposed statement**, so no refinement was needed or made.<br>• **Headers compared exactly** (my `frozen2.py`): all seven targets have headers (3–12 lines, keyword through `:= by`) and statement prose before `**Proof sketch.**` byte-identical to B6. |
| **Frozen regions (C4), independently** | **PASS.**<br>• Each head normalizes **byte-identically** to B6 after six steps:<br>&nbsp;&nbsp;1. the seven bodies are set back to `sorry`;<br>&nbsp;&nbsp;2. the three refreshed sketches (G10, G13, L2) are set back to B6's;<br>&nbsp;&nbsp;3. the private `four_pow_clog_le` (19 lines) is deleted;<br>&nbsp;&nbsp;4. `encrypts_bootGate` (53 lines with its docstring) is deleted. The tool requires it to sit directly after G9 and directly before G10, and it does;<br>&nbsp;&nbsp;5. its two `## Main results` lines are deleted. They sit directly after G9's entry;<br>&nbsp;&nbsp;6. the two admission sentences are set back ("… are proved, as is G11/L1" → "… are admitted; … is proved").<br>• So no definition, reader, instance, `set_option`, import, namespace or other text changed.<br>• Controls each FAIL (13): a one-character header change (×2), a definition body (`bootNoise`, `levelGate`), statement prose (×2), a reader body, an unpermitted import (×2), an extra public declaration, the helper moved after G10, another Main-results edit, and a deleted target.<br>• Base against itself and a sketch-only edit PASS. |
| **Public declarations** | **PASS.** Exactly one is new, `encrypts_bootGate`, as Q-6BF-3 A rules. The only other new name is `private theorem four_pow_clog_le`. |
| **Admissions** | **PASS.**<br>• 0 `sorry`, `admit`, `native_decide`, `axiom` or `opaque` in either file (comments stripped).<br>• No new `set_option`, `attribute` or `@[simp]`. No `decide` or `Classical` in the new code.<br>• Base→head: 5 + 2 `sorry` → 0. |
| **Axioms (C5)** | The worker gives 65 constants with 8 `sorryAx` traces, all through allowed names, and 0 on its information merge with the records tip. **Phase 2 reproduces this independently, with its own trace:**<br>• the same 65 constants;<br>• G13 traces through `[decDepth_le]`;<br>• the other six targets and the helper trace through `[depth_nandFormula_le, encrypts_homEvalFormula, maxFanin_nandFormula_le, nandFormula_eval]`;<br>• 0 disallowed names, and no owner declaration in any trace;<br>• **on the stacked tree, 0 `sorryAx`**: all eight are `[propext, Classical.choice, Quot.sound]`. |
| **Rule 10 (C6)** | The worker ran whole-file seals A/B × strict/coe on both owners at the head and the base copies: all 0 errors. Its 7 liveness pairs include one for the helper. **Phase 2:**<br>• canonical coe-A and seal B give 0 errors on both owners. Requests are 444 for Bootstrap and 479 for Leveled, all verified. This holds at B6 and again on the stacked tree;<br>• my 6 liveness pairs are ALL_OK. Two are for the helper, in `Leveled`'s sealed copy where `bootGate` is foreign: `rfl` at a fan-in-0 gate against `bootGate_of_args_eq_nil`, and `rfl` at a fan-in-1 gate against a sealed application of `encrypts_bootGate`;<br>• the explicit-unfold scan finds 0 foreign definitions. The only definitions it finds are the frozen own case readers' `unfold bootGate`/`levelGate`, the same as at B6. |
| **Duplication** | **PASS.** No restatement, no re-proof of a published lemma, and no cross-file private copy. Every must-reuse item is used or rightly not needed (below). U1416-F01–F04 record the overlaps. |
| **Hygiene (C8, C9)** | **PASS.**<br>• **Sizes.** Bootstrap 349 → 518 lines, Leveled 291 → 384. That is 291 added lines in all, under the brief's 460–740 estimate (the must-reuse list and `runWith_rel` carry the inductions), and far under the 1,000-line cap and G6B-F07's 791 projection. Maximum width is 99; there are no tabs, no trailing spaces and no micro sign.<br>• **Sketches.** Every proof of 20 or more lines has one: the helper 31, G10 35, G12 26, G13 24, L2 60, L3 34. Each describes the delivered proof. The four kept sketches (G9, G18, G12, L3) already did, and the three refreshed ones changed only below `**Proof sketch.**`. Step comments sit at the major `have`s.<br>• **Docstrings.** The helper's has words, the formula, "Glue." (no source tag, as the brief says) and a sketch. The private helper's has its formula and "Glue for G13.". |
| **Lint (C7)** | **PASS.** `campaign_style_lint --check8b` gives 92 FAIL / 103 WARN over 540 files at B6, at `9852429e`, at the records tip and at the stack. The line sets are identical. `style_lint` gives 0 findings on both files at B6 and at the head. |
| **Clashes (C10)** | **PASS.** `encrypts_bootGate` and `four_pow_clog_le` occur in no `TCSlib/` or `audits/` file of any of the **342** local and remote heads (`git grep -w`), including `iO/phase-a-base` `5ed465f6` and `cleanup/stage2-s2a` `9f7f409c`. They also occur nowhere in Mathlib, Batteries or core. The new public short name occurs only in the two owned files at the head, so no resolution can change. |
| **Build (C1)** | The worker reports a 224-module bootstrap, rc 0 with census 42 in 16, and a head sweep of 9/9. It did not build the root. **Phase 2:** B6 10/10 rc 0 with the root, and stacked 12/12 rc 0 with the root. |

## The proofs, target by target

- **G9 `encrypts_bootNAND`.**
  - **Route.** `bootNAND_eq`, then G3 `encrypts_homEvalFormula` on `nandFormula P C₁ C₂`, with fan-in from G8
    `maxFanin_nandFormula_le` and the inputs `keyBits P s`/`evk` (`hk`).
  - **Message:** G7 `nandFormula_eval`, by `rw … at h`.
  - **Noise:** `Encrypts.mono`, `bootNoise_eq`, `Nat.mul_le_mul_right` and `Nat.pow_le_pow_right` on G8
    `depth_nandFormula_le`.
  - It is exactly the sketch's route, with no hypothesis on `C₁`, `C₂`.
- **`encrypts_bootGate`** (public, statement as briefed).
  - **Length and value.** `g.args.length ≤ 2` comes from `DAGGate.isNAND_iff`. `DAGGate.eval_of_isNAND` (N1) rewrites
    the value to `!(g.args.all …)`.
  - **`hG`.** The padded `G` decrypts to `true` by `decrypt_of_encrypts` on `encrypts_gadget`. At noise `0` the
    separation `2·(ℓ·0) < ⌊q/2⌋` follows from `modulus_ge_two` and `omega`.
  - **Cases.** `rcases` on `g.args` gives `[]`, `[a]` and `a :: b :: l`, and the tail is empty by the length bound.
    Each case uses its frozen reader (`bootGate_of_args_eq_nil`/`_singleton`/`_cons_cons`), then G9 on `(G, G)`,
    `(a, a)` or `(a, b)`, rewritten by `hG`/`hargs`. `simpa` closes it.
  - **Rule 10.** The case split is never read by unfolding (the scan and the helper's pairs confirm this).
- **G10 `decrypt_fheEval`.**
  - **Route.** The host `runWith_rel` (H19) on `DAGGate.eval`/`List.ofFn x` and `bootGate P evk`/`List.ofFn cts`. The
    relation is "`Encrypts P t b.toNat (if v < k then βin else bootNoise P βk) C`". A local `hsep` discharges both
    separation cases.
  - **Inputs:** `List.getD_eq_getElem`, `List.getElem_ofFn`, `if_pos` and `hin`.
  - **Acyclicity:** `Cc.args_lt`.
  - **Gate step:** `if_neg`, then **`encrypts_bootGate`** (`t' = t`) for the gate's NAND property
    (`isNANDForm_iff`, `List.getElem_mem`), with argument decryptions by `decrypt_of_encrypts` and `hsep a`.
  - **Output:** `Cc.output_lt`, `fheEval_eq`, `Cc.eval_eq`, `Cc.values_eq` and `decrypt_of_encrypts`.
  - The host induction is not re-proved.
- **G18 `decrypt_fheEvalCircuit`.** `fheEvalCircuit_eq`, `← toNANDForm_eval` (N3), then G10 on `Cc.toNANDForm hC` with
  `toNANDForm_isNANDForm` (N4). Three lines.
- **G12 `decrypt_keygen_fheEvalCircuit`.**
  - **The honest key.** `hs : LWE.sample P.lwe χ rg = (rg.1, noisyValues …)` is `Prod.ext` of `LWE.sample_fst`/`_snd`
    (U1416-F02). The errors are bounded by `LWE.Noise.bounded_iff`.
  - **The evaluation key:** `Regev.keygen_fst`/`_snd`, `hs`, then **G11 `encrypts_evalKey`**.
  - **The inputs:** `encrypts_keygen_encrypt`.
  - **`hle : m·B ≤ bootNoise P (m·B)`:** `bootNoise_eq`, `N ≥ 1` (`NeZero`), and three `Nat.le_mul_of_pos_left` in a
    `calc` (U1416-F01).
  - **Close:** G18, with the input condition from `hsep` through `hle`.
- **G13 `bootNoise_le`.**
  - **Exponent.** `bootNoise_eq`, `N ≥ 1` and `X ≥ 1`. G8 `decDepth_le` with `Nat.pow_le_pow_right` and `omega`
    bounds the exponent by `9a + 2b + 22`.
  - **Split.** `← pow_mul`, `← pow_add` and `omega` on the exponent split it into `4^22·(4^a)^9·(4^b)^2`. This is
    written out because `ring` does not match `4^(9a)` with `(4^a)^9`.
  - **Bound.** The private `four_pow_clog_le` and `Nat.pow_le_pow_left` give `4^22·(4N²)^9·(4X²)^2`, which `ring`
    turns into `4^33·N^18·X^4`. Then `Nat.mul_le_mul_right` and `ring`.
  - **Constants.** `c₀ = 33`, `c₁ = 9`, `c₂ = 2`, as frozen. The sketch's old "`N = 0`" case is correctly dropped,
    since `N ≥ 1` holds by the instance.
  - **`four_pow_clog_le`.** `y = 1` uses `Nat.clog_one_right`. `y ≥ 2` uses `Nat.pow_pred_clog_lt_self`,
    `Nat.clog_pos`, `pow_succ` and `omega` to get `2^⌈log₂ y⌉ ≤ 2y`. Squaring then uses `pow_mul` and
    `Nat.pow_le_pow_left`.
- **L2 `encrypts_leveledEval`.**
  - **Route.** `runWith_rel` with the gate function `levelGate P lk (Cc.depthAt vs.length)` and the dependent relation
    "`∀ hv : depthAt v < L + 1, Encrypts P (t_{depthAt v}) b.toNat (max βin (bootNoise P βk)) C`".
  - **Inputs:** level `0` by `depthAt_input` and `Fin.ext`, then `hin` and `Encrypts.mono` with `le_max_left`.
  - **Gate `i`.**
    - The data length comes from `runWith_rel`'s own hypothesis `hB`, so `length_runWith` is not needed.
    - `δ ≥ 1` by `depthAt_gate` and `DAGGate.depth_eq`. Then `levelGate_of_lt` at `δ − 1 < L`.
    - `hsucc` (`Fin.ext`, `Fin.val_succ`) moves `hk` at `δ − 1` to the key under `t_δ`.
    - **`encrypts_bootGate`** with `s = s_{δ−1}`, then `Encrypts.mono` with `le_max_right`.
    - Each argument is at level `δ − 1` by `isLayered_iff`. Its cast is matched by `Fin.ext`/`Fin.coe_castSucc`, and it
      decrypts by `decrypt_of_encrypts` with the `max` separation.
  - **Output:** `Cc.output_lt`, the level by `Fin.ext Cc.depth_eq`, then `leveledEval_eq`, `Cc.eval_eq` and
    `Cc.values_eq`.
  - Gates above `L` are never constrained or read. The relation's hypothesis excludes them, so `levelGate_of_le` is not
    needed.
- **L3 `decrypt_keygen_leveledEvalCircuit`.**
  - **Start:** `leveledEvalCircuit_eq`.
  - **Literal ciphertexts** (`induction j using Fin.addCases`):
    - left: `literalCts_castAdd`, `litInput_castAdd` and `encrypts_keygen_encrypt`;
    - right: `literalCts_natAdd`, `litInput_natAdd`, `homNot_eq`, `homAnd_singleton`, and `Encrypts.sub` of
      `encrypts_gadget` and the input. The message is `(!b).toNat = 1 − b.toNat` by cases, and the noise
      `0 + m·B ≤ m·B` (U1416-F04).
  - **L2** on `(Cc.toNANDForm hC).layerNAND`, with `layerNAND_isNANDForm` + `toNANDForm_isNANDForm`,
    `layerNAND_isLayered`, `layerNAND_depth`, and L1 `encrypts_levelKey` for the keys (`βk = βin = m·B`).
  - **Value:** `layerNAND_eval` and `toNANDForm_eval`.
  - **Output level:** `Fin.ext` of `layerNAND_depth`.
  - **Close:** `decrypt_of_encrypts` with `hin`/`hsep` by `max_cases`.

## Duplication sweep (binding)

- **`dup-sweep.md` §U14-U16 must-reuse list.** Every item is used, or has a reason I accept. I checked each name
  against the added lines.
  - **Used:**
    - G3 `encrypts_homEvalFormula`; G7 `nandFormula_eval`; G8 `depth_nandFormula_le`, `maxFanin_nandFormula_le`,
      `decDepth_le`;
    - the in-unit chain G9 → helper → G10 → G18 → G12, and helper → L2 → L3;
    - `runWith_rel`, `values_eq`, `DAGCircuit.eval_eq`, `depth_eq`, `depthAt_input`, `depthAt_gate`,
      `DAGGate.depth_eq`, and the fields `args_lt`, `output_lt`;
    - `DAGGate.isNAND_iff`, `isNANDForm_iff`, `DAGGate.eval_of_isNAND`, `toNANDForm_eval`, `toNANDForm_isNANDForm`,
      `isLayered_iff`;
    - `litInput_castAdd`/`_natAdd`, `layerNAND_eval`/`_isLayered`/`_isNANDForm`/`_depth`;
    - `decrypt_of_encrypts`, `encrypts_keygen_encrypt`, `encrypts_gadget`, `Encrypts.sub`, `Encrypts.mono`,
      `homNot_eq`, `homAnd_singleton`, `Regev.keygen_fst`/`_snd`, `LWE.sample_fst`/`_snd`, `LWE.Noise.bounded_iff`;
    - the own readers `bootNAND_eq`, the three `bootGate_of_args_eq_*`, `bootNoise_eq`, `fheEval_eq`,
      `fheEvalCircuit_eq`, `literalCts_castAdd`/`_natAdd`, `levelGate_of_lt`, `leveledEval_eq`,
      `leveledEvalCircuit_eq`;
    - G11 `encrypts_evalKey`, L1 `encrypts_levelKey`, the instance `Parameters.neZero_columns` (through `NeZero`);
    - `Nat.pow_pred_clog_lt_self`, `Nat.clog_one_right`, `Nat.pow_le_pow_right`, `Nat.pow_le_pow_left`, `pow_mul`.
  - **Not needed:**
    - `length_runWith`: `runWith_rel` supplies the length, and uses it internally;
    - `DAGGate.getD_lt_depth`: `isLayered_iff` gives the exact level, which is stronger;
    - `encrypts_encrypt`, `evalKey_eq` and `levelKey_eq`: they are used through G11 and L1;
    - `levelGate_of_le`: gates above `L` are excluded by the relation.
- **My searches.** These were static (`logs/dup-searches.txt`, S1–S14, at B6, on all heads, and in Mathlib, Batteries
  and core) and by `exact?` (phase 2, D1–D7, each with its use's hypotheses).
  - **The helper.** No per-gate bootstrapping lemma exists at B6 (S3, S4). Its phase-5 relative `homGate_encrypts`
    (`Eval.lean:181`) cannot serve: it takes encryptions, not decryptions, and its noise grows to `(N+1)·β`. The
    worker disclosed this. `hG` (the gadget decrypts to `true`) has no lemma (S5, D6).
  - **`four_pow_clog_le`.** See U1416-F03.
  - **G12's `hs` and `hle`.** See U1416-F02 and F01.
  - **L3's `hm`.** No Mathlib, Batteries or core lemma states `(!b).toNat = 1 − b.toNat` (S11, D4). See U1416-F04.
  - **`runWith_rel`.** At B6 it has one use, `eval_encrypts` (S13). G10 and L2 follow it; see U1416-F04.
- **Near relatives, as disclosed:**
  - `eval_encrypts` and `homGate_encrypts` (`GSW/Eval.lean:250`, `:181`);
  - `decrypt_keygen_eval` (`:300`, G12's leveled phase-5 analogue);
  - `two_pow_clog_le` (`ClassP/BinaryArith/PrimeFind.lean:119`).

  None is restated.

## Findings

**Blockers: none. Majors: none.**

- **U1416-F01 (minor; records side, no change to the delivery). A fact two units need, `m·B ≤ bootNoise P (m·B)`, was
  not identified as shared, and it is now derived inline twice.**
  - **Where.**
    - This unit's G12 proves it as a local `have hle` (`Bootstrap.lean:448–454`, a 7-line `have` with a `calc` from
      `bootNoise_eq`, `N ≥ 1` and `Nat.le_mul_of_pos_left`).
    - U18-U19's final (exchange `c414248e`, received 01:26Z) proves the same fact again as a local `have hin` in
      `decrypt_leveledEval_of_ratio` (`PolyRatio.lean`, a 10-line `have` with a `calc`).
  - **Why it was foreseeable.** Both frozen sketches name the fact at B6: `Bootstrap.lean:320` ("`m·B ≤ bootNoise P
    (m·B)` (`bootNoise_eq`)") and `PolyRatio.lean:160`. Yet `dup-sweep.md` §0 item 6 lists only two cross-unit helpers,
    `encrypts_bootGate` and `Parameters.ofFamily_columns_le`. Q-6BF-3 A then allows exactly those two public helpers,
    so neither worker could publish it without an E-SCOPE request.
  - **Status.** Neither copy re-proves a published lemma (none exists: S14, D7), and neither is a private declaration,
    so COMMON §5.2 is not breached. It is the kind of near-duplicate the sweep exists to prevent, and the gap is ours.
  - **Fix.** None to this delivery. Q-U1416-2 records the follow-up. The U18-U19 review should cite this finding
    rather than charge its worker.
- **U1416-F02 (info; = W1). G12's `hs` is the third inline copy of the LWE seed identity.**
  - **The fact.** `LWE.sample P χ r = (r.1, noisyValues P r.1 r.2.1 (χ.sample ∘ r.2.2))` by `Prod.ext` of
    `LWE.sample_fst`/`_snd`. It appears at `Bootstrap.lean:432–434`, and also at `GSW/Scheme.lean:214–216` and
    `Encryption/PublicKey/Regev/Basic.lean:168–170`. The worker disclosed the `Scheme` copy but not the Regev one.
  - **No published lemma** (S10). `exact?` offers only `rfl`, a defeq read of the foreign `LWE.sample` (D5). So the
    two-reader composition is the right Rule-10 form, and G11's frozen statement (`(A, noisyValues A s e)`) forces it.
  - **Fix.** None to the delivery. See Q-U1416-1.
- **U1416-F03 (info). The private `four_pow_clog_le` is new content.**
  - **Searches.** `exact?` finds no lemma for its statement or its inner step `2^⌈log₂ y⌉ ≤ 2y`, nor for the general
    `b^clog b y ≤ b·y` (D1–D3, each with `1 ≤ y`; the claims fail at `y = 0`). Mathlib's `Nat/Log.lean` has
    `pow_pred_clog_lt_self` and `le_pow_clog` only (S6).
  - **TCSlib's `two_pow_clog_le`** (`PrimeFind.lean:119`, `2^⌈log₂ 2n⌉ ≤ 4n+1`) has a different shape and is not in
    this unit's closure.
  - The brief asked for this search first and allowed a private helper. It is one use, with a formula and "Glue for
    G13.". Accept.
- **U1416-F04 (info). Proof text shared with phase 5, within the allowance.**
  - **G10 and L2.** Both repeat `eval_encrypts`' `runWith_rel` call shape. That includes its input-vertex block (the
    four `List.getD_eq_getElem`/`List.getElem_ofFn` rewrites under `List.length_ofFn`, `Eval.lean:260–264`) and the
    3-line `args_lt` obligation. These are the obligations of the call shape that `dup-sweep.md` allows, and the worker
    disclosed them.
  - **L3's NOT-literal step.** `Encrypts.sub` of `encrypts_gadget`, with `(!b).toNat = 1 − b.toNat` by `cases … <;>
    rfl`, mirrors the `¬` case inside `homGate_encrypts` (`Eval.lean:226–231`). No lemma states it (D4).
    `homGate_encrypts` cannot be used: its noise `(N+1)·β` exceeds L2's `βin = m·B`.
  - The worker disclosed `homGate_encrypts` only as the helper's analogue, not this step.
  - **Fix.** None. A future `Encrypts.not` (`G − C`, message `1 − b`, noise `0 + β`) would serve both; it is not a
    request now.
- **U1416-F05 (info). Report slips and host notes.**
  - **Line counts.** `REPORT.md` gives the public helper as "64 lines with its docstring" (it is 53, plus 2
    `## Main results` lines) and the private helper as "21 lines" (it is 19).
  - **Seal counts.** The worker's "298–330 definitions" sealed come from its own whole-file method. The canonical
    request sets are 444 and 479, and they pass.
  - **Records tip.** The tip "seen at delivery" (`f46a2ae4`) has since moved on records only. The merge's `TCSlib`
    tree is the same.
  - **No sub-agent.** The lead used none, which the brief allows ("up to 1"). So the `lev` split did not apply.
  - **Host housekeeping.** On its own host, the worker removed its landed U13 worktree and sparsified its exchange
    worktree to pass the disk preflight. Nothing of ours was touched.
  - None of these affects the delivery.

## Questions for Seyoon (recommended option first)

- **Q-U1416-1 · G12's honest-key rewriting (U14-U16-W1; U1416-F02).**
  - **A (rec.)** Accept it as delivered. The local two-reader `hs` is the brief's route and cites only published
    readers.
  - **B** Also queue a cleanup item: publish `LWE.sample_eq` in `LWE/Basic.lean` and use it at the three sites
    (Regev `Basic`, GSW `Scheme`, `Bootstrap`). It would be an owner edit outside every 6b unit.
  - **C** Ask for a revision now. Not recommended: there is no lemma to cite, and the fix belongs to a cleanup.
- **Q-U1416-2 · the shared `m·B ≤ bootNoise P (m·B)` (U1416-F01).**
  - **A (rec.)** Accept both inline derivations: this unit's G12, and U18-U19's G17 when that review reaches it.
    Record a cleanup item to publish `le_bootNoise : β ≤ bootNoise P β` in `Bootstrap.lean` after the 6b fills land,
    and use it at both sites. Note the sweep gap in the decision log.
  - **B** Rule a third public helper now (a Q-6BF-3 amendment) and ask this unit for a revision that adds
    `le_bootNoise`. U18-U19 would then be revised to cite it. Not recommended: it costs two re-deliveries for a 7-line
    fact.
- **Q-U1416-3 · landing order.**
  - **A (rec.)** Land U14+U16 now as one PR with the two worker commits, as delivered (no landing edit), on the records
    tip. It merges cleanly (`TCSlib` tree `8dc09446…`), and that exact stack is Lean-tested (12/12 with the root,
    0 `sorryAx`). U15-U17 and U18-U19 are replayed on top when their reviews run.
  - **B** Hold it and land it together with U15-U17 and U18-U19 in one stacked PR. This would only delay: the units
    are disjoint in files, and U18-U19 cites this unit's G13.

## Landing

- **Landing.** One PR with the two worker commits `e09ce698`, `9852429e` on B6, as delivered (no landing edit).
  - The prospective records tree has `TCSlib` tree `8dc094469b996283c47c3bb5e56587ed1cdd7160`. This is
    `git merge-tree --write-tree 9852429e <tip>` against both `c63ee44f` and `c87eb403`.
  - Its stacked build is phase 2's P2-3.
- **Snapshot.** The replay trees were deleted. Rebuilding the stack takes about a minute (12 modules, about 35 s of
  Lean). Snapshot #12 can be adopted from a fresh replay of whatever merges.

## Evidence

`gsw-6b-u14-u16-final-r1-evidence.zip` sits beside this file; its SHA-256 is in `evidence-SHA256SUMS`.

- It holds `PROVENANCE.txt` and an inner `SHA256SUMS` (264 files), which does not list itself.
- It contains the reproduction and stack-head logs, decls2 and the helper-statement check, the frozen check with its
  controls, the static scans, and the B6 and stacked replays (plans, runner records, per-module logs, permod,
  admissions, state checks).
- It also contains the axiom censuses with traces, the collectors, the coe-A and seal-B records with their sealed
  copies and raw logs on both heads, the controls, the duplication probes and searches, the unfold scans, lint, and
  every tool and probe source.
