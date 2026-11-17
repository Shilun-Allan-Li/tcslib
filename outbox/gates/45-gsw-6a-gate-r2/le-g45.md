# Gate 45 · landing edit LE-g45 (G45-01..03): `eval_node_nil` moved into `Combinators`, `const_eval` proved from it

**Verdict: PASS, pushed.** `land/gsw-6a-statements` (PR #359) is now
**`ad9c4fc701ed145cbc96acceefaad447398c8321`** (parent `73aedcdaaaffef7e69ab012d9b9195f150bae68d`), a fast-forward.
Its tree is **`c3608d4621b3c722db76654f9310715ca192787f`**.
- The edit touches 3 files, +15/−14, and nothing else:
  - **G45-01:** `BoolCircuit.eval_node_nil` moves from `Hierarchy` to `Combinators`, with the same name, binders,
    statement and docstring. `TreeCircuit.const_eval` becomes a proved citation of it.
  - **G45-03:** Barrington's cycle-notation prose is corrected.
  - **G45-02:** the "promoted unchanged" sentence in `Combinators` is reworded.
- **Admissions 98 → 97.** `const_eval` is the only name that leaves the list. The exact-target check gives
  `RESULT EXACT`.
- **Replay:** 16/16 modules rebuilt with rc 0, 0 errors, and `sorry` warnings exactly on the 97 targets.
  - The state check gives **1440/1440 OK**, and the 16 rebuilt oleans have link count 1.
  - Snapshot #5 and `olean-replay-6a-stmt` rehash **0/0/0** at the start, after the build and at the end.
- **Axioms:** `eval_node_nil` and `const_eval` use `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
  The census has 545 constants, of which 102 use `sorryAx`: the 97 targets plus the same 5 dependents as before.
- **Rule 10, canonical coe-A seals, base against head:**
  - `Combinators`: 174 requests, 0 errors.
  - `Barrington`: 119 requests, 0 errors.
  - `Hierarchy`: 355 requests, 2 errors in `Language.InTreeSize.inSIZE`. The same 2 errors occur at the base, so they
    are not introduced by this edit (see the notes).
  - In all three, the request sets are equal at base and head.
  - The explicit-unfold scan finds 0 new foreign unfolds. One foreign unfold is removed: the old proof's
    `simp [TreeCircuit.eval]`.
- Lint is unchanged.
- **decls2:** `eval_node_nil` moved with its statement unchanged. Nothing else is CHANGED, ADDED or REMOVED.
- **Merge-tree:** clean with #360, #357, #347 and #355. None of them touches LE-g45's three files.
- **New replay tree:** `$SP/olean-replay-6a-stmt-g45`. Its output map (Mathlib excluded) has SHA-256
  **`3cb140cbf20939e61b67eed47e5cd27b73478cf76e993db0129a23b1d81e7d89`** and 1471 entries.

Run on 2026-11-17, about 11:08–11:30 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`;
the job's directory is `$SP/le-g45-work`.
- **Evidence:** `le-g45-evidence.zip`, beside this file. It holds `PROVENANCE.txt`, `SHA256SUMS` (227 files) and
  `tools/TOOLS.txt`. Its SHA-256 is `983e42386bbf09c835979cbdbba9985029a31ca4e39d1318f1dccc6be9d8677e`; the zip does
  not contain this file.
- **Diff:** `le-g45.diff.txt` = `git diff 73aedcda ad9c4fc7`, SHA-256
  `c8edd59aaced56f2340e316e132439f72ee5216729c3b4c4422ed5b07346346c`.
- **Builds:** no `lake build` and no cache get. One Lean process of this job ran at a time. Before each of the 29 Lean
  processes, the job read the host's slot count: it saw 0–1 `lean` processes and never had to wait.
- **Records:** nothing was committed to the records branch. This file, the diff and the zip are left uncommitted.

## The edit (`git diff --numstat`: Barrington 5/3, Combinators 10/6, Hierarchy 0/5)
- **G45-01, the move.** The lemma's three lines and its docstring were deleted from `Hierarchy.lean` (old `:104–108`).
  They are inserted into `Combinators.lean` at `:411–414` (declaration at `:412`), inside `namespace BoolCircuit`, just before
  `TreeCircuit.const`:
  - The name is the same, `BoolCircuit.eval_node_nil`.
  - The binders and statement are the same. The ambient binder is `{n : ℕ}` in both files, and `#check` prints the
    same type at base and head.
  - The docstring is the same.
  - **Deviation (Rule 10, disclosed):** the old proof `cases b <;> simp [TreeCircuit.eval]` unfolds
    `TreeCircuit.eval`, which `Basic` owns. The new proof is
    `cases b <;> simp [TreeCircuit.eval_node_true, TreeCircuit.eval_node_false]`. It uses `TreeDAG`'s public readers
    (`Combinators` imports `TreeDAG`).
- **Users:** `git grep` over `TCSlib/` at the head finds only the two in `Hierarchy`:
  - `:146`, `restrictCircuit_eval`;
  - `:192`, `Language.zero_inTreeSize`.
  - `Hierarchy` imports `TreeNCAC`, which imports `Combinators`, so both resolve. The probe gives the home of both
    users as `Hierarchy` and the home of `eval_node_nil` as `Combinators`.
  - Elsewhere, `eval_node_nil` appears only in prose in `ch6/CRITIQUE_LOG.md`, which was not changed.
- **`const_eval`:** the statement is byte-identical. The proof `sorry` becomes
  `rw [TreeCircuit.const_eq]; exact eval_node_nil b x`.
  - The docstring keeps `**F3, constant: value.**` and the formula. It replaces "Glue." and the case-split sketch with
    "This is `BoolCircuit.eval_node_nil` read through `const_eq`."
  - There is no "Proof sketch" block, because the proof is a one-line citation.
- **Module docstrings:**
  - `Hierarchy`'s docstring does not list `eval_node_nil`, and `Combinators` has `## Main definitions` / `## Main
    results` but no `## Contents`. So neither changed.
- **G45-03 (prose only):**
  - `Barrington.lean:43–45`, the Orders convention, now reads: "… `sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1`. That is
    `(13254)` in Bar89's one-based cycle notation, whose zero-based form `(0 2 1 4 3)`, the cycle
    `0 ↦ 2 ↦ 1 ↦ 4 ↦ 3 ↦ 0`, is what the code implements; …"
  - The C9 docstring, `:339–341`, now reads: "the product is `(13254)` in Bar89's one-based cycle notation, whose
    zero-based form `(0 2 1 4 3)` is what the code implements, `List.formPerm [0, 2, 1, 4, 3]`". The Bar89 anchor and
    quotation lines are unchanged.
- **G45-02 (prose only):** `Combinators.lean:16–18` now reads: "promoted with its computation unchanged; its proofs
  carry the five Q2-approved Rule 10 repairs."
- Every new line is at most 96 characters. `Combinators` grows 629 → 633 lines (the existing G6A-F06 size watch),
  `Hierarchy` shrinks 343 → 338, and `Barrington` grows 463 → 465.

## Commit and push
- **Worktree:** a sparse worktree of the three files at `$SP/le-g45-work/wt`, on `land/gsw-6a-statements`. The branch
  was not checked out anywhere else, so no detached head was needed. The worktree was removed afterwards. The local
  branch is at `ad9c4fc7`.
- **The edits** were made by `tools/edit.py`, which asserts that each old string occurs exactly once.
- **Commit:** `git commit -S -F <msg> -- <3 paths>`.
  - The subject is "LE-g45: move eval_node_nil into Combinators and prove const_eval from it; Barrington cycle-notation
    and Combinators wording (Gate 45 G45-01..03)".
  - The message ends with the two required trailers.
  - Author and committer are `Claude <noreply@anthropic.com>`.
  - The SSHSIG key is `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`, the same as `73aedcda`. This is key
    identity only (`sigkey.py`).
- **Push**, after the replay and every check below:
  - Before: `ls-remote` gave `73aedcda`.
  - `git push origin HEAD:land/gsw-6a-statements` gave `73aedcdaa..ad9c4fc70`, with no force.
  - After: `ls-remote` gives `ad9c4fc7…`.

## Replay (snapshots.md job recipe, on #359's replay tree)
- **Copy:** `cp -al $SP/olean-replay-6a-stmt $SP/olean-replay-6a-stmt-g45`.
  - It has 1472 files, all hard links, and 3346 Mathlib symlinks.
  - The overlay and the NthRootLemmas olean `c0a9cff0…` came with the copy.
  - `olean-replay-6a-stmt` was never written.
- **Export:** a `git archive` of `ad9c4fc7` with `.lake/packages` symlinked: 1592 files, all blob-exact.
- **State:** the re-replay's R2 `state.json` at `73aedcda` (`e492d0b3…`) was used. It checks **1440/1440 OK** against
  both `olean-replay-6a-stmt` and the copy.
- **Plan:**
  - `downorder.py ad9c4fc7 73aedcda` gives changed 3 and **down 16**.
  - `fullorder.py` gives 1440 modules, byte-identical to R2's order (`516473…`).
  - `stateplan plan` gives **16 to build and 1424 reused**, and the queue equals `down.txt`.
  - **The 16:** `Combinators`, `TreeNCAC`, `NCAC`, `CarrySave`, `Compare`, `ModSum`, the `FormulaArith` facade,
    `Parity`, `Hierarchy`, the `CircuitComplexity` facade, `Barrington`, `BarringtonConverse`, `NC1`, the
    `BranchingPrograms` facade, `ComputationalModels` and `TCSlib`.
  - `Defs`, `Eval`, `NANDForm` and `NANDLayering` are not downstream and are reused.
- **Build** (`tools/run-build-g45.sh`, 11:15:18–11:16:55): the recipe's `runner.py`, unmodified, one module per call.
  - **16/16 rc 0.** `permod.py` gives `error:` 0, `error(` 0, substring 0, and no log/record mismatch.
  - There are 68 warnings, all `declaration uses 'sorry'`: Combinators 23, CarrySave 7, Compare 7, ModSum 4,
    Barrington 11, BarringtonConverse 11, NC1 5.
  - `warncmp` against the R2 logs gives 13 SAME. The 3 NEWSRC are the edited files, and their warnings are only the
    `sorry` lines.
- **Accept:**
  - `stateplan update` took 16 modules and left none out.
  - `check` at `ad9c4fc7` gives **1440/1440 RESULT OK**, and again at the end. The resulting `state.json` is
    `0a56622f…`.
  - **Link count 1** holds for exactly the 16 rebuilt oleans, whose object hash equals the record.
- **Rehash:**
  - Snapshot #5: `snapmap.py verify` against `map-3f540c22` (`fca1b6a3…1ef9`) gives **1458 files, 0/0/0** at the start,
    after the build and at the end.
  - `olean-replay-6a-stmt`: it has no registered map, so its map was taken at the start with `mapnoml.py`: 1471 entries,
    `4ae688be8db0fb1a1d2965dfa58296d26cabaf631cf7abe29123e165c85410b7`.
  - The state check above binds every olean of that map to R2's recorded hashes.
  - `replayverify.py` then gives **0/0/0, RESULT OK** after the build and at the end, and the state check at `73aedcda`
    gives 1440/1440 OK at the start, after the build and at the end.

## Output map and adoptability
- **`$SP/olean-replay-6a-stmt-g45`** (REV `ad9c4fc7`, tree `c3608d46`):
  - **Map:** `mapnoml.py`, Mathlib excluded, 1471 entries, SHA-256
    **`3cb140cbf20939e61b67eed47e5cd27b73478cf76e993db0129a23b1d81e7d89`**. `replayverify` at the end gives OK, and
    the map file is `run/output-map/olean-replay-6a-stmt-g45.map-ad9c4fc7.noMathlib.tsv`.
  - **Against `olean-replay-6a-stmt`:** 1468 equal, **3 changed** (`Combinators`, `Barrington`, `Hierarchy`), 0 added
    and 0 removed. The other 13 rebuilt oleans are byte-identical.
  - **Against snapshot #5:** 1453 equal, 5 changed (`TCSlib`, `CircuitComplexity`, `Hierarchy`, `TreeNCAC`,
    `ComputationalModels`) and 13 added (the new modules). Nothing is removed.
  - **Method deviation:** phase 2 of 6a recorded no output map. This map uses the method of the pairing landings
    (`mapnoml.py`, as in LE-g48).
- **Adoptable** in place of `olean-replay-6a-stmt` on the statement merge, under three conditions:
  - the merge follows O1 (#358) directly, with the records tip otherwise Lean-equal to snapshot #5;
  - `git diff --name-only <merge> c3608d4621b3c722db76654f9310715ca192787f -- '*.lean' lean-toolchain
    lake-manifest.json` is empty;
  - the recipe's step-6 checks are run at adoption.
- `olean-replay-6a-stmt` (REV `73aedcda`) is no longer adoptable for #359. It is kept: this job never writes or
  deletes it.
- If #360 (or anything else touching its closure) merges first, re-replay instead.

## Checks
- **Admissions** (`admcheck.py` against `e1d39836`, using R2's logs with this run's 16 on top; `touched.json`
  regenerated against `e1d39836` over the 16 series files plus `Hierarchy`):
  - head 97: Defs 11, Eval 5, Barrington 11, BarringtonConverse 11, NC1 5, NANDForm 6, NANDLayering 7,
    Combinators **23**, CarrySave 7, Compare 7, ModSum 4.
  - **Exact-target check:** the delivered `rowmap.txt` (`b3ac759e…`) minus `rename_eval`, `depth_rename` and
    `const_eval` gives 97 targets, 97 admitted, 97 matched, 0 extra, 0 twice and 0 missing: **EXACT**.
  - **Against the snapshot-#5 re-replay's `r2-delta.txt`:** the admitted (file, name) sets differ in exactly one row,
    `Combinators … BoolCircuit.TreeCircuit.const_eval`, which is removed.
- **decls2** (phase 1's unmodified `decls2.py`, `73aedcda` against the head, on the three files):
  - Two rows: `REMOVED Hierarchy.lean:105 BoolCircuit.eval_node_nil` and `ADDED Combinators.lean:412
    BoolCircuit.eval_node_nil`. Their normalized statements are identical, which makes this a move.
  - There is no CHANGED row and no other row. `decls2` is per file, so the move shows as one REMOVED and one ADDED.
  - The `.err` file is empty.
- **Axioms:**
  - **`AxiomsStmt.lean`** (phase 2's probe, source byte-identical) on the new tree: rc 0. Against the re-replay's log,
    the diff is exactly 3 lines:
    - `const_eval` loses `sorryAx`;
    - a new `DECL Combinators BoolCircuit.eval_node_nil [Classical.choice, Quot.sound, propext]` appears;
    - the `TRACE const_eval` line is gone.
  - **`axtrace`:** 545 constants (DECL 383, AUX 162). There is no non-standard axiom other than `sorryAx`. `sorryAx` is
    in 102 constants: the 97 targets and the 5 N2/N12–N13 dependents, as before. No AUX constant has it.
  - **`AxiomsG45.lean`** (new): `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for:
    - `eval_node_nil` and `const_eval`;
    - Hierarchy's users `restrictCircuit_eval` and `zero_inTreeSize`.
  - On the base, the same probe gives `const_eval` `[propext, sorryAx, Classical.choice, Quot.sound]` and the same
    types.
- **Rule 10, canonical coe-A** (collector and `mkseals_coe.py` as in the re-replay's `rule10_g6a5.sh`;
  `SEAL_CHUNK=1000`; owners `Combinators`, `Barrington`, `Hierarchy`):
  - The base is the `73aedcda` export on `olean-replay-6a-stmt`, read only (no `-o`). The head is `ad9c4fc7` on the
    new tree.

    | Owner | Requests (base / head) | Errors (base / head) | Request names | Closure modules |
    |---|---|---|---|---|
    | `Combinators` | 174 / 174 | 0 / 0 | equal | 3 / 3 |
    | `Barrington` | 119 / 119 | 0 / 0 | equal | 2 / 2 |
    | `Hierarchy` | 355 / 355 | 2 / 2, both in `Language.InTreeSize.inSIZE` | equal | 12 / 12 |

  - Every probe has its install and EOF records.
  - `Hierarchy`'s two error messages are identical at base and head, apart from line numbers: "Invalid `⟨...⟩`
    notation" and "No goals".
  - The base's `Combinators` and `Barrington` records equal the snapshot-#5 re-replay's: same requests, names, probe
    SHA-256, source SHA-256 and outcome.
  - **The moved lemma introduces no seal failure.** `eval_node_nil` is a theorem, so no request changes.
- **Explicit-unfold scan** of the three files (`scan1_g40.py`/`scan2.py`):
  - Head: 159 items, 14 foreign, all in `Hierarchy`.
  - Base: 157 items, 15 foreign, all in `Hierarchy`.
  - **0 new foreign items.** The only one removed is base `Hierarchy`'s `eval_node_nil` `simp TreeCircuit.eval`
    (`Basic`).
  - The head adds 3 `LOCAL_OR_UNRESOLVED` theorem names: `TreeCircuit.eval_node_true`/`_false` in `eval_node_nil`,
    and `TreeCircuit.const_eq` in `const_eval`. These are theorems, not definitions.
  - The two users in `Hierarchy` now resolve to the `Combinators` home.
  - `Combinators` and `Barrington` have 0 foreign items.
- **Lint** (each run from its own export):
  - `campaign_style_lint TCSlib/Complexity --check8b` gives 25 FAIL / 390 WARN over 513 files at both base and head.
    The FAIL/WARN line sets are identical (0 diff lines), and the base output equals the re-replay's
    `campaign-stmt.txt`.
  - Only 3 INFO lines change: the line and declaration counts of the three files.
  - `style_lint` on the three files gives 2 findings, identical at base and head. Both are pre-existing `Hierarchy:17`
    false positives on the docstring phrase "theorem below".
- **`git diff`:** limited to the three files.
- **Merge-tree of `ad9c4fc7`** (`run/cross/merge-tree.txt`), every one rc 0 (clean):

  | PR | Head | Tree | Shared paths |
  |---|---|---|---|
  | #360 | `cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25` | `8743591a` | `TreeNCAC.lean` (from O1, #358; not an LE-g45 file) |
  | #357 | `dfdc56f2` | `c2e6fab3` | none |
  | #347 | `daa6e173` | `6b71a6e4` | none |
  | #355 | `d3c7cb00` | `c15c1bbf` | `TCSlib/Cryptography/Games.lean` (from the records history since the old base `2da7e0f3`, not LE-g45) |

  - None of the four touches `Combinators`, `Hierarchy` or `Barrington` since its merge base.
  - Each merged tree has exactly one declaration of `eval_node_nil`, at `Combinators.lean:412`.
  - #360's head is the one the coordinator gave (`cc05f76c`), which is also the remote head.

## Deviations and notes
- **Proof of the moved lemma** (Rule 10, disclosed above): it reads `TreeDAG`'s `eval_node_true`/`eval_node_false`
  instead of unfolding `Basic`'s `TreeCircuit.eval`.
- **Not changed, as briefed ("nothing else changes"):**
  - The `Combinators` `## Main results` line `const_eval, xor3_eval, maj3_eval, … (F3; targets)` still says
    "targets", although `const_eval` is now proved.
  - `Barrington.lean:23`, `:108` and `:116` still write "Bar89's `(12345)`, 0-based: the five-cycle …" and
    "`(12345)`, `(13542)`, 0-based". These lines name the one-based Bar89 cycle and then give its zero-based reading, so
    they are less wrong than `:43`/`:339` were, but they use the same loose phrasing.
  - Both can go into a later wording pass if wanted.
- **Pre-existing seal failure, new to the records:** `Hierarchy`'s coe-A seal fails twice, in
  `Language.InTreeSize.inSIZE`, at both `73aedcda` and the head.
  - `Hierarchy` is unchanged by the series apart from this edit, and phase 2 did not seal it.
  - The failure is not introduced here. It is a Rule 10 item for the clean-up track, like G6A-F05.
- **Output map method:** see the adoptability section.
- **Not touched:** `olean-snapshot` and `olean-replay-6a-stmt` (read and hard-linked only), other agents' directories,
  every other records file, and the fill branches.
- **Cleanup:**
  - Removed: the worktree, both exports and this job's temporary extract of the re-replay zip.
  - Kept: `$SP/olean-replay-6a-stmt-g45` and `$SP/le-g45-work/run` (8.6 MB).
  - Disk: 2542 MB free at the start, 2349 MB at the lowest point, about 2.5 GB at the end.
