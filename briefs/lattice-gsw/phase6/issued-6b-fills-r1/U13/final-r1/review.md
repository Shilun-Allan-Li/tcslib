# GSW 6b U13 `gsw-6b-u13` · final r1 · maintainer review (phase 1 static, phase 2 Lean replay)

**Verdict after phase 2: ACCEPT. No landing edit.** The six targets G5–G8 of
`GSW/DecryptFormula.lean` are proved as stated, `decDepth_le` among them. The file gains no helper,
no import and no statement change. Phase 2 passed with no new finding. The details are in
[`phase2.md`](phase2.md).

- **Findings:** 0 blockers, 0 majors, 1 minor, 2 info.
  - The minor is **on our side**: U13-F01, the never-filed `rulings.md` (shared with U12-F01).
  - The infos:
    - U13-F02: proving `decDepth_le` is what ruling F2 provided for, not a conflict with it.
    - U13-F03: a disclosed pool slip and housekeeping on the worker's own host.
- **Phase 2 (2026-11-18, 22:28–22:42 UTC; one replay tree, U12 and U13 stacked).**
  - **Build:** 12/12 rc 0, including the root `TCSlib`. No `audits/*/Checks` imports the changed
    modules. U13 **alone** also passes: 11/11 rc 0, admissions 36 in 15.
  - **Axioms:** the census covers all 23 stored constants, all standard, with 0 `sorryAx`.
  - **Seals:** canonical coe-A and seal B both give 0 errors, with 380 requests verified.
  - **Controls:** 2 liveness pairs, ALL_OK.
  - **Unfold scan:** 0 foreign definitions.
  - **Lint:** unchanged.
  - **Snapshot #11:** rehashes 0/0/0 before, after and at the end.

## What was reviewed

- **Delivery.** `inbox/fills/gsw-6b-u13/` on `exchange/pass-shelat-ch5-8`, at
  `87012e786e70134018a22156d3a299c2c55b943a` ("fill gsw-6b-u13: final"). The tip
  `9b4ab065f58581ac93ba6641f29a0d4051482dfa` (U12's final) does not change the folder.
  - Both U13 commits (checkpoint `ab9d1ec3`, final `87012e78`) are unsigned and touch only
    `inbox/fills/gsw-6b-u13/`.
  - Extracted with `git archive`, the delivery has 173 files: `REPORT.md`, 1 patch with
    `COMMITS.tsv`, `src/` (1 file) and `evidence/` (168 files).
- **Contract.**
  - The issued pack at the pin `bbc930b3853adb29ba96324568e984d521abd257`: `README.md`,
    `COMMON.md`, `U13/brief.md`, `U13/dispatch-prompt.md`, `dup-sweep.md` (§0, §U13),
    `targets.txt` and `base-sorries.txt`.
  - Since the pin, only the U12/U13 dispatch prompts changed (the pin hash was filled in).
  - Handoff §2: rules 10 and 15, and the duplication rule; `policy.md` §1–§3.
- **Rulings in force.**
  - Gate 46 (CLEAR).
  - Q-6B-F2 ("`decDepth_le` stays an admitted target", below).
  - Q-C1: the owner-side `decrypt_eq_decode_dotProduct`, which G6 must use.
  - G6B-F05 and sweep note N1: `decDepth_le` is a disclosed weakening of F10.
- **Base and records tip** as in U12's review: B6 = `bff0567b…` (tree `845bdc98…`). The records
  tip `31247fe7…` is Lean-equal to B6.

## Checks

| Check | Result |
|---|---|
| **Integrity** | **PASS.**<br>• Both manifests pass `sha256sum -c`: 172 top-level rows and 167 evidence rows.<br>• No duplicates, no leading `./`, and neither manifest lists itself.<br>• Each manifest equals its tree exactly.<br>• The top level binds `evidence/SHA256SUMS`. |
| **Reproduction (C13)** | **PASS: 1/1.**<br>• `git am` on B6 with the committer data from `COMMITS.tsv` gives **`74fb355a17a47076d7de44a0f691ea03572cb170`**, REPORT's head.<br>• 0 `gpgsig`.<br>• `src/…/DecryptFormula.lean` equals the head byte for byte.<br>• Checkpoint 1 delivered the same head (`src/` and `patches/` are unchanged since `ab9d1ec3`). |
| **Scope** | **PASS.**<br>• `git diff --stat bff0567b 74fb355a` shows only `GSW/DecryptFormula.lean`, +55/−7.<br>• `git merge-tree --write-tree` with the records tip is clean (tree `62e193f2…`). |
| **Statements (C3), independently** | **PASS.**<br>• decls2 at the head: **0 ADDED, 0 CHANGED, 0 REMOVED**.<br>• **Headers compared exactly:** all six targets have headers (2–4 lines) and statement prose byte-identical to B6. `decDepth_le`'s header is identical to B6's, keyword through `:= by` (below). |
| **Frozen regions (C4), independently** | **PASS.**<br>• The head normalizes **byte-identically** to B6 after two steps: the six bodies are set back to `sorry`, and the module sentence "All are proved, as are the definitions and the instance" is set back to "All are statement-phase targets (admitted); …".<br>• So no sketch changed, no helper was added, and the instance `neZero_columns`, every definition and every reader are untouched.<br>• Controls each FAIL: a header change on `decDepth_le`, a definition-body change on `decDepth`, and a reader-docstring change. |
| **Public declarations** | **PASS.** None was added, as the brief requires, and no private one either. |
| **Admissions** | **PASS.**<br>• 0 `sorry`, `admit`, `native_decide`, `axiom` or `opaque` in the code.<br>• No new `set_option`, `attribute` or `@[simp]`.<br>• Base→head: 6 `sorry` → 0. |
| **Axioms (C5)** | The worker's census of 23 constants is standard, with an empty trace and a base control. **Phase 2 reproduces it:** 23/23 with the same sets, and the six targets `[propext, Classical.choice, Quot.sound]`. |
| **Rule 10 (C6)** | The worker ran a whole-closure seal at the head and the base, 8/8 runs with 0 errors, plus controls on `decConstants` (own) and `decrypt` (Scheme). **Phase 2:** canonical coe-A and seal B both give 0 errors with 380 requested and 380 verified, my 2 liveness pairs are ALL_OK, and the unfold scan finds 0 definitions. |
| **Duplication** | **PASS** (below). |
| **Hygiene (C8, C9)** | **PASS.**<br>• 216 → 264 lines (+48 net, under the 200–330 estimate and the 550 cap); maximum width 98; no micro sign.<br>• The longest body is G6 at 20 lines, with step comments at its `have`s and the frozen G6 sketch, which describes the delivered proof step for step (the reader `decrypt_eq_decode_dotProduct`, G5, the representative, O2's interval test, F9 with `ZMod.val_lt` and `decodeLo ≤ decodeHi ≤ q`).<br>• The other sketches also match: G5 `ht` + `dotProduct_mulVec` + `decConstants_eq`; G7; G8 `max_le`/`omega`; `decDepth_le` as below.<br>• So "no sketch refreshed" is right. |
| **Lint (C7)** | **PASS.** 92 FAIL / 103 WARN over 540 files at B6, `74fb355a` and the stack, with identical line sets. `style_lint` gives 0 findings. |
| **Clashes (C10)** | **PASS.** No new name. The only new stored constants are 6 `_proof_` auxiliaries under the targets' own names. |
| **Build (C1)** | The worker reports a 224-module bootstrap and a 10-module head sweep, rc 0. **Phase 2:** 12/12 rc 0 in the stack (with root `TCSlib`) and 11/11 alone. |

## The proofs, target by target

- **G5 `vecMul_secretVector_eq_sum`.**
  - `ht : t = G·x`, by `keyBits_eq` and `gadget_mulVec_decomposeVec`.
  - Then `dotProduct_comm`, `Matrix.dotProduct_mulVec`, `← decConstants_eq` and
    `dotProduct_comm`, closed by `rfl`. Mathlib's `dotProduct` is the stated `∑`; this is a
    Mathlib definition in a `rfl` step, which is allowed.
- **G6 `decryptFormula_eval`.**
  - **The reader.** `rw [decrypt_eq_decode_dotProduct, …]`: the owner-side reader, used and not
    re-derived (Q-C1).
  - **`hval`:** `(t ⬝ᵥ c).val = (∑ xᵢ·aᵢ.val) % q`, by G5, `Nat.cast_sum`, `Nat.cast_mul`,
    `ZMod.natCast_zmod_val` and `ZMod.val_natCast`.
  - **The interval.** `hlh`/`hhq` (`decodeLo ≤ decodeHi ≤ q`): one `omega` each after
    `decodeLo_eq`/`decodeHi_eq` and `modulus_ge_two`.
  - **Closing.** `FormulaArith.modSumInterval_eval` with `ZMod.val_lt`. `Bool.eq_iff_iff` and
    `decide_eq_true_iff` then reach `decode_iff_mem_Ico`.
  - **Rule 10.** `decode`, `modSumInterval`, `decomposeVec`, `gadget` and `decrypt` are never
    unfolded. The seals confirm it.
- **G7 `nandFormula_eval`.** One `rw`: `nandFormula_eq`, `neg_eval`, `and2_eval`, then G6 twice.
- **G8 `depth_nandFormula_le`, `maxFanin_nandFormula_le`.**
  - `depth_modSumInterval_le`/`maxFanin_modSumInterval_le` for both operands, read back through
    `← decryptFormula_eq` and `← decDepth_eq`.
  - Then `depth_and2_le`/`maxFanin_and2_le`, `max_le`, `depth_neg`/`maxFanin_neg`, and `omega`.
- **G8 `decDepth_le`.**
  - `⌈log₂ q⌉ ≤ ℓ` by `(Nat.clog_le_iff_le_pow _).mpr P.modulus_le`.
  - `Nat.clog_mono_right` on `⌈log₂ q⌉ + ⌈log₂ N⌉ + 3 ≤ ℓ + ⌈log₂ N⌉ + 3`.
  - `FormulaArith.modSumDepth_le P.columns q`, `decDepth_eq`, then `omega`.
  - 9 lines, exactly the frozen sketch. No term linear in `ℓ` is introduced (r3 §H3.3).

## `decDepth_le` and ruling Q-6B-F2

- **The ruling's text.** The decision log, 2026-11-18, "6b statements rulings (Seyoon), all as
  recommended", says: **"Q-6B-F2: `decDepth_le` stays an admitted target."**
- **The question it answered** (`phase6/final-6b-r1/review.md`, *Q-6B-F2*):
  - **"A (rec.)** Keep it an admitted target, as `targets.txt` makes it. **The U13 fill proves it
    from F10.**"
  - "**B** Prove it at landing as a citation (admissions 24 → 23; a new proof in a statement PR)."
- **The surrounding records agree:**
  - G6B-F05: "Once #366 lands, F10 is proved and the U13 fill is about 3 lines";
  - Gate 46 `dup-sweep.md` N1: "ruled Q-6B-F2 A (it stays an admitted target; the U13 fill is
    about 3 lines)";
  - Gate 46 `findings-r1.md`: "Valid weakening of F10 … admitted as ruled".
- **What F2 was protecting.** Only the shape of the **statement PR (#377)**: no new proof in a
  statement PR, and 24 admitted targets.
  - It was never a claim that the statement is false.
  - It was never a claim that a restatement is planned.
  - Gate 46 judged the statement a valid weakening, and the closed form `(9, 2, 21)` was settled.
- **The fill side.** This pack lists `decDepth_le` as a U13 target. U13's brief gives the proof
  route (about 3 lines, citing F10, disclosing the specialization). The README expects 0
  admissions in the 6b modules after all five units.
- **The statement as proved equals B6 exactly.** The header is `theorem decDepth_le (P : Parameters)
  :` / `decDepth P ≤` / `9 * Nat.clog 2 P.columns + 2 * Nat.clog 2 (P.width + Nat.clog 2 P.columns
  + 3) + 21 := by`, byte-identical. The prose and the sketch are unchanged too, and decls2 gives
  CHANGED 0.
- **Duplication.** The proof **cites** `FormulaArith.modSumDepth_le` (`FormulaArith/ModSum.lean:365`)
  and re-proves nothing. It is the disclosed specialization G6B-F05/N1, disclosed again in
  REPORT §5.

**Conclusion: proving it is fine.** It is the outcome F2 A provided for. It conflicts with nothing
F2 protected, and it is strictly better than leaving it admitted. Decision-log row 609's wording
("which Gate 46 F2 had left admitted") is accurate, but it could be read as a conflict. U13-F02
records the reading.

## Duplication sweep (binding)

- **`dup-sweep.md` §U13 must-reuse list.**
  - **Used:**
    - `gadget_mulVec_decomposeVec` (G5);
    - `decrypt_eq_decode_dotProduct` (G6);
    - the own readers `keyBits_eq`, `decConstants_eq`, `decryptFormula_eq`, `nandFormula_eq` and
      `decDepth_eq`;
    - O2's `decode_iff_mem_Ico`, `decodeLo_eq` and `decodeHi_eq`;
    - F9/F10's `modSumInterval_eval`, `depth_modSumInterval_le`, `modSumDepth_le` and
      `maxFanin_modSumInterval_le`;
    - F1/F3's `neg_eval`, `depth_neg`, `maxFanin_neg`, `and2_eval`, `depth_and2_le` and
      `maxFanin_and2_le`;
    - all eight Mathlib items.
  - **Not needed:** `secretVector_eq` and `vecMul_secretVector_augmented`. They are "only if
    needed", since `t` is read only through `gadget_mulVec_decomposeVec`.
- **My searches:**
  - **D3, `hval` in general form:** `(∑ ((b i).toNat : ZMod q) * a i).val = (∑ (b i).toNat *
    (a i).val) % q`. `exact?` finds nothing.
    - A Mathlib grep for `ZMod.val_sum`/`natCast_sum`-style lemmas finds none.
    - At B6, `git grep` for `.val) % ` in TCSlib finds only unrelated arithmetic
      (`DyadicLinearAlgebra.lean:225` uses `ZMod.val_add`).
    - It is assembled from the four cited Mathlib lemmas.
  - **D4, `decodeLo ≤ decodeHi` and `decodeHi ≤ q`:** `exact?` finds nothing.
    `LWE/BitEncoding.lean` has no such lemma; its theorems are the `_eq` readers,
    `decode_iff_mem_Ico` and the distance lemmas.
  - **Not a duplicate:** `TrapdoorFunctions/Lossy.gadget`'s decomposition lemmas. G5 is over
    `decomposeVec`.
- **No restatement, no inline re-derivation of a published lemma, no cross-file copy.**

## Findings

**Blockers: none. Majors: none.**

- **U13-F01 (minor; records side, no change to the delivery). The pack's `rulings.md` was never
  filed.** This is the same defect as U12-F01, and the full text is there.
  - The README (*Blocking* 1, *Maintainer steps* 1), `COMMON.md`'s preamble and both dispatch
    prompts name `issued-6b-fills-r1/rulings.md`.
  - The pin `bbc930b3` was cut without it (decision-log row 607), and no ref has ever carried it.
  - **Impact on U13: none.**
    - No Q-6BF question bears on U13. It is one file with no public helper under every grouping
      option, and Q-6BF-1 and Q-6BF-4..7 are EF-R1's.
    - The worker's only ruling-dependent choices rest on rulings that **are** recorded: Q-C1
      (the reader) and Q-6B-F2 (above).
    - The worker checked every input hash at the pin and raised the gap at once (U13-W1).
  - **Fix:** Q-U13-1.
- **U13-F02 (info). `decDepth_le` was proved although Q-6B-F2 said it "stays admitted".**
  - **Consistent; see the section above.** F2 kept it an admitted target **of the statement PR**
    so that the U13 fill would prove it.
  - The statement is byte-identical, and the proof cites F10.
  - **Records note.** When the landing is logged, say "F2 discharged by the U13 fill as
    planned", so that row 609 is not read as a deviation.
- **U13-F03 (info). Pool slip and host housekeeping, both on the worker's own host.**
  - **The slip.** At 21:56:18Z, five two-second control probes started at once, which is above the
    local cap of 3. It was a scripting error, disclosed. Everything else kept 3.
  - **The housekeeping.** To pass its 12 GiB disk preflight, the worker removed its own
    delivered `sc-ot` worktree (`/workspace/scot`, branch kept).
  - Neither touches this machine or the records. They are recorded so that the cap is restated
    to future workers.

## Questions for Seyoon (recommended option first)

- **Q-U13-1 · the missing `rulings.md` (U13-W1; the same as Q-U12-1).**
  - **A (rec.)** Confirm that no ruling applies to U13 (or U12) and accept the delivery as it is.
    Record it in the decision log, and file `issued-6b-fills-r1/rulings.md` with the Q-6BF-1..7
    answers before any further unit of the folder is dispatched.
  - **B** File `rulings.md` first and have this delivery re-checked against it. Not needed.

No other question: the `decDepth_le` point needs no ruling (U13-F02).

## Landing

- **Landing.** One PR with the one worker commit, as delivered (no landing edit), after U12's
  (README order).
  - The two files are disjoint and neither imports the other.
  - The stack U12 + U13 (`fb6884d1`) and U13 alone are both Lean-tested on snapshot #11.
- **The prospective trees:**
  - U13 alone on the records tip: `62e193f2…`;
  - U12 + U13: `fb6884d1…`.
- **After landing.** The 6b admissions fall from 24 to 15. The base order's 42 falls to 33.

## Evidence

`gsw-6b-u12-u13-final-r1-evidence.zip` sits beside this file; its SHA-256 is in
`evidence-SHA256SUMS`. It is the same zip as under `U12/final-r1/`; its layout is in that review
and in `PROVENANCE.txt`.
