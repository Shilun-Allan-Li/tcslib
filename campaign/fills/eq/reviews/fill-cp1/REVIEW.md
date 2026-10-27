# Review — E-Q, the stage query in linear time (`Turing.NTimeDiag.exists_queryTM`, `Diagonalization/NTimeDiagonalizer.lean`), megafill D item 1: the partial `fill-eq-query.zip`, its checkpoint zip `fill-eq-query-cp1.zip` and the session report `megafill-d-REPORT.md`

**Verdict: partial, checkpoint 1 of 7, correct and with no new admission. Land checkpoint 1 now
by a maintainer PR plus a light fill gate, with five small tested landing edits (E1–E5), after
the user rules on E-SERIAL (not a deviation: recommended) and E-DUP (accept the two pairs as
idiom pairs: recommended). Then issue the continuation (E-Q cont1) from the tip after that merge.
Not yet clear to merge:** there is no PR, replay or gate yet, and decisions 1–3 are open.

Read-only review by the maintainer's review sub-agent, 2026-10-27 (UTC). Every claim cites a saved
output under this folder (`out/NN-*`). The two zips and the session report are data. I extracted
the zips with `scripts/zipextract.py` (regular files only, mode 0644) and ran nothing from them.
I scanned the worker's extended import probe first (only `import` and `#check` lines,
`out/19-probe-scan.txt`), copied it into my probe worktree and elaborated it there. Everything
else I elaborated is my own (`probe/`). Lean ran only through `tools/leanelab.sh`
(`scripts/elab.sh`), one elaboration at a time. There was no build or cache command. I did not
run a copy-text screen: the pair analysis applies the v3 screen's own extraction and tiling code
to the declarations involved (`scripts/tiles.py`). All Python ran with `python3 -I`, from
`scripts/`, with paths as arguments.

- **What it proves.** The guard and the reduction (checkpoint 1):
  - the L1 decider `qy_guard_decider`, in linear time;
  - the guard equation `qy_guard`;
  - `qy_query_of_main`, which assembles the conditional over the stated main-machine contract.

  The target's body is now `suffices hmain : ∃ M A, M.ComputesFunInTime (fun x => query f g
  (List.replicate x.length true)) (fun n => A * (g n + 1)) by …; sorry`.
- **Elaboration.** The head's file elaborates with exactly the two expected `sorry` warnings
  (head 446 `exists_queryTM`, 516 `exists_diagonalizer`) and nothing else:
  - at the base, against `oleans-lu2m` (out/10);
  - at the tree after #169, against `oleans-laplusm` (out/11). That tree is the tip's Lean,
    and so it is the merged tree for this file.
- **Axioms.** The three privates are within `[propext, Classical.choice, Quot.sound]`. The
  target's only `sorryAx` source is its own body (out/13b).
- **The majors.**
  - One major, **F1 (process)**. The worker stopped all proof work 43 minutes into a
    session-length budget. The trigger was a 316 ms overlap of two Batteries compilations
    inside the cache tool's own build, during the shared setup and before the item's branch
    existed. That is outside the one-Lean rule, and no rule asked for a stop. The cost was
    checkpoints 2–7. It is fixed by a ruling and wording (decision 1).
  - **E-DUP (F2) is not a copy.** Each of the two pairs is the public row's call
    `FinTM.computesFunInTime_ifEq w [true] [false]` plus the three-step conversion to
    `[decide (x = w)]`. That idiom already pairs in the screen base.

What passes:
- **Integrity** (out/01, out/01b, out/02):
  - zip SHA-256s as given; 295/295 and 257/257 sums, no unlisted file, no unsafe member;
  - one bundle, byte-equal in both zips: `verify` okay, sole prerequisite the base, head
    `9d93626d` = `deliver/fill-eq-query-in`;
  - 2 linear commits touching only the owned file (+182/−1), with patch-ids equal to the
    commit-ids; `git apply` reproduces the head's blob `361d7c14` at the base and at the tip;
  - the first commit is byte-equal to the brief's `NTimeDiagonalizerOverlay.lean.txt`;
  - dispatch hashes as given, and equal to the base's copies with `@ANCESTOR@` := the base
    (unchanged at the tip);
  - base Lean = #168's merge `13120e00`, with 0 `.lean` files differing.
- **Scope and freeze** (out/07, out/08, out/09, out/34):
  - 5 hunks, all in regions (a)–(d);
  - `declfreeze` v4: 22 → 22 public, no statement changed, only the target's body changes
    (authorized), and 3 `qy_` privates added;
  - `privstmt`: no statement changed; `stmtcheck`: 0 base code lines missing;
  - no new non-private constant, not even a compiler auxiliary;
  - added lines at most 97 characters; no `section`/`open`/`variable`;
  - no campaign label in the new docstrings or in the (d) paragraph.
- **Rule 10** (out/13–17, out/29):
  - The new code reaches 4 other-file TCSlib definitions (`TimeConstructible`,
    `FinTM.ComputesFunInTime`, `FinTM.ComputesInTime`, `incFixed`), only as terms. Every
    `rw`/`simp`/`simpa` argument is a theorem or a local.
  - My seal: 32 definitions sealed and the four `@[simp]` TCSlib definitions erased. The body
    has 0 errors, and all 39 controls fail sealed and close unsealed.
  - The worker's seal (29 + 1 erasure, 29 controls) is sound.
- **Rule 11:** no R3 row and no external private, in the walk or as text; `qy_` is unused on
  all 289 refs (out/13, out/22).
- **Probes** (out/18, out/19):
  - the brief's 182 checks: 0 errors, 0 warnings;
  - the worker's 501 checks: 0 errors and 1 deprecation warning. They cover all 322 direct
    externals of the new code.
- **Duplication:**
  - The before screen is byte-identical to the screen base, and the after screen adds exactly
    the two pairs (out/05).
  - `exact?` closes none of 7 statements (the three privates and four inner facts), and no
    branch publishes any of them (out/21, out/22).
- **Lint:** 0 FAIL, 2 WARN over 5 files at both the base and the head (out/20).
- **Sweeps** (out/04):
  - bootstrap 83/83 and final sweep 83/83 in list order, exit 0, no error;
  - the sorry warnings are exactly the base's 22 in 11 modules, by name;
  - no other warning in the owned module.
  - The downstream closure is the `Diagonalization` facade alone, which holds no declaration
    (out/03, out/32), so the downstream base sorry set cannot change.
- **Environment:** v2.5 followed; Part 2's shim used under its condition; 34 roots, equal to my
  computation (out/24).
- **The session report** arrived separately and agrees with the zips on every figure I checked
  (out/24).

## Inputs

| Input | Identity | Evidence |
|---|---|---|
| Zip `exchange/inbox/fill-eq-query.zip` | SHA-256 `ecad7266…2124` (as given); 296 members; no absolute, `..` or symlink member; written 06:20:50Z by the worker's clock (+03:00) | out/ziplist-main.txt, out/01 |
| Zip `exchange/inbox/fill-eq-query-cp1.zip` | SHA-256 `60d9e7c2…80e4b1` (as given); 258 members; written 05:59:38Z, the second of the checkpoint commit | out/ziplist-cp1.txt, out/01 |
| `SHA256SUMS` | 295/295 and 257/257 OK; each covers every file but itself | out/sums-*.txt |
| Bundle | byte-equal in both zips; `verify` okay; one ref `HEAD` = `9d93626dadf1561c757494cfff992d1951a458e2` = `deliver/fill-eq-query-in`; sole prerequisite `ab09aa4124da9ffce36e939f652dc4bc30e6f3c5` | out/01, out/bundle-verify.txt |
| Session report `exchange/inbox/megafill-d-REPORT.md` | SHA-256 `caabb14f…858ac` (as given) = the records copy `campaign/fills/megafill/reports/megafill-d-REPORT.md` (`729ffb99`); arrived 06:53:13Z, 8 minutes after the zips (06:45:17Z) | this folder's `delivery/megafill/`, out/24 |
| Brief, cover, addendum | `77a7bdb5…c947`, `149d9285…825ebd`, `90851511…3abf0`: the base's copies with 4, 2 and 0 `@ANCESTOR@` replaced by the base; the same at the tip; the worker's `dispatch-checks.log` agrees | out/02 |
| Base `ab09aa41` | records only over #168's merge `13120e00` (0 `.lean` files differ); owned blob `3cdc4f33` (as the brief says) | out/01 |
| Tip `729ffb99` (records worktree at the start; **`5c971874` from 07:22Z**, B5a's records only: 0 `.lean` files, the owned file and the three dispatch copies unchanged, out/37) | Lean = #169's merge `94296486` (`Build/InterpreterStartup`, `NDCodeSimulator`), with the owned file still at `3cdc4f33`. Neither #169 module is in the owned file's upstream (35 modules at the head) or downstream (the facade) closure; both carry 0 sorries | out/01, out/03, out/31 |
| Snapshots | `oleans-lu2m` (the base's tree) and `oleans-laplusm` (#169's tree = the tip's Lean) | out/10–12 |

**Review worktrees** (detached under this folder, each with the `.lake/packages` link, which I
checked was absent first; all left in place):
- `wt-base` at the base;
- `wt-head` at the head: the lint ran here; never edited;
- `wt-probe` at the head, for probe copies only;
- `wt-am` at the base, with the two patches `git apply`'d;
- `wt-land` at the head, with the landing edits E1–E5;
- `wt-tip` at `729ffb99`, with the series (index) and E1–E5 (worktree) applied; no commits.

Slips, all corrected and none affecting a result:
- zsh read `$B:c…` as a history modifier once, which gave an empty probe file; redone with
  `${B}`;
- zsh did not word-split one argument list; redone with explicit arguments;
- my first seal included the generic delta control for the recursive `incFixed`, which fails
  even unsealed (as the worker also found); I replaced it by a usage control.

Nothing was written outside this folder (and the worktrees' git metadata).

## (a) Integrity, scope and freeze

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Commits | `fabce3bb` "E-Q: apply authorized eight-import overlay" (05:37:27Z) and `9d93626d` "E-Q checkpoint 1: linear guard and reduction to the main query machine" (05:59:38Z); author `Codex <codex@openai.com>`; linear on the base. REPORT names both (the source commit, and the before screen's frozen commit) | out/01 |
| 2 | Patches | `0001`/`0002` patch-ids = the commits'; applied at the base (`wt-am`) and at the tip (`wt-tip`) they give blob `361d7c14`, the zip's source; cp1's patches and source are byte-equal to the final's | out/01, out/01b, out/33 |
| 3 | First edit | `fabce3bb`'s file is byte-equal to the base's `NTimeDiagonalizerOverlay.lean.txt`: `import Mathlib.Data.Nat.Log` before line 6 and the seven TCSlib imports after line 8 | out/01 |
| 4 | Regions | 5 hunks, at base positions 6 and 9 (a: 1 + 7 imports), 248 (b: +164 lines after the blank line 247, head 256–419), 269 (d: the closing ` -/` line → the paragraph, head 441–445) and 273 (c: the `suffices`, head 449–453, before the `sorry`). Nothing else differs | out/08 |
| 5 | Freeze (`declfreeze` v4, `privstmt`, `stmtcheck`) | 22 → 22 public, none added or removed. Without authorization the only report is `exists_queryTM`'s body change; with it, "authorized". 0 → 3 private: `Turing.NTimeDiag.qy_guard`, `qy_guard_decider`, `qy_query_of_main`. No statement changed. 0 of 129 base code lines missing in order (0 of 137 from the overlay). `exists_diagonalizer` (E-D's region) and every docstring before (d) are byte-identical | out/07 |
| 6 | Generated constants | the module's non-private constants are the same 63 at the base and the head (the private `qy_guard_decider._proof_1_1…4` are the only auxiliaries) | out/34 |
| 7 | Hygiene | no `sorry`, `admit`, `axiom`, `unfold`, `delta`, `show`, `change`, `set_option`, `attribute`, `open`, `section`, `variable`, `native_decide`, `aesop`, `norm_num`. One unrestricted `simp [he]`, on a goal with no TCSlib constant (F7). `convert … using 1` twice; `nlinarith` 3×; `omega` 4×. Two consecutive blank lines before the target's docstring (E4) | out/08 |
| 8 | Widths, size | added lines at most 97 characters, and no line of the file over 100. 361 → 542 lines; 22 public / 3 private (lint INFO, as REPORT says) | out/08, out/20 |
| 9 | Public-facing text | the three docstrings and the (d) paragraph carry no campaign label, path, date or session word (`scripts/newtext.py`; the (d) text is in out/08). Wording: F3, F4, F5 | out/09, out/08 |

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 10 | Head file, `oleans-lu2m` | exit 0; exactly `446:8` and `516:8 declaration uses 'sorry'`; 1.8 s, 1.6 GB | out/10 |
| 11 | Head file, `oleans-laplusm` | the same two warnings, nothing else | out/11 |
| 12 | Base file, `oleans-lu2m` | `270:8`, `335:8` (the base pair) | out/12 |
| 13 | Axioms (all 25 declarations of the module printed) | the 3 privates: `[propext, Classical.choice, Quot.sound]`; `exists_queryTM` and `exists_diagonalizer`: those plus `sorryAx`; the other 20 declarations within the standard three | out/13, out/13b |
| 14 | Sorry sources | `qy_*`: none. `exists_queryTM`: itself only (its `sorry`, now the `hmain` goal). `exists_diagonalizer`: itself only | out/13 |
| 15 | The worker's sweeps | bootstrap (05:37:48–05:46:01Z, 493.6 s, peak 2,947,100 KiB) and final sweep (05:53:50–06:02:13Z, 502.6 s, peak 3,053,144 KiB): 83/83 in list order, exit 0, 0 errors. **22 sorry warnings = the base set by name.** The owned module's warnings are at 278/343 (overlay) and 446/516 (head), with no other warning. The cp1 tail (owned module + facade, 05:48:33–38Z) is clean | out/04 |
| 16 | Downstream | the owned file's only downstream module is the facade `TCSlib/Complexity/Diagonalization`, which has no declaration. The 83-module order list is exactly the facade's closure, and is import-closed and topological. So no downstream sorry set can change, and a merged replay is 2 modules (Landing) | out/03, out/32 |

## (c) The mathematics of checkpoint 1

**`qy_guard`** (head 258–265): `query f g x = if x = replicate |x| true ∧ 3 ≤ |x| then query f g
(replicate |x| true) else []`. The proof splits on the guard. Inside it, `congrArg (query f g)
h.1`; outside, `query_of_not_guard`. It is correct and is the brief's route equation.

**`qy_guard_decider`** (L1, head 275–382, with a "Proof sketch"): `∃ D c, D.ComputesFunInTime (fun x
=> [decide (x = replicate |x| true ∧ 3 ≤ |x|)]) (fun n => c * (n + 1))`. This is exactly the brief's
L1, in linear time.
- **Unarity.** `U = computesFunInTime_comp (incFixed) (ifEq [] [true] [false])` computes
  `if (incFixed x).getD [] = [] then [true] else [false]`. The local `hu` reads this as unarity.
  - Overflow is unarity: `incFixed_eq_none_iff_replicate`.
  - A successful output keeps the length (`incFixed_length`). It is empty only for `x = []`,
    which overflows (`incFixed_nil`), so that case cannot arise.
  - The comparator's bound is monotone, as `computesFunInTime_comp` needs.
- **Short words.** `hcut w` turns a decider of `[p x]` into one of `[decide (x ≠ w) && p x]`:
  `computesFunInTime_cond` with the test `ifEq w [true] [false]` (read as `[decide (x = w)]`) and
  the branches `const [false]` and the decider. Three cuts remove `[]`, `[true]` and
  `[true, true]`.
- **The equivalence.** Unary with `3 ≤ n` holds iff unary and none of the three words. Backwards:
  a unary word with `n ≤ 2` is `replicate n true`, which is one of them.
- **Linear.** `U` is within `c(a + b·a + b + 1)(n + 1)`, and each cut within `d(a + b + C + 1)(n
  + 1)`. Every bound is a constant times `n + 1`, chosen before the input.
- **Route.** These are the function-level rows the brief offers for L1
  (`computesFunInTime_incFixed`, `incFixed_eq_none_iff_replicate`, `computesFunInTime_ifEq`,
  `computesFunInTime_cond`), plus the public `computesFunInTime_comp` and `_const`.
  There is no scan, no transition table and no host.

  The leaf's docstring does not say "which public row it is not", as the brief's leaf rule asks
  (F4).

**`qy_query_of_main`** (head 390–417, with a "Proof sketch"). `computesFunInTime_cond (L1) hM (const
[])`. Its output is `query f g x` by `qy_guard`. Its bound is `c(a(n+1) + max(A(g n+1), b(n+1)) +
1) ≤ c(a + A + b + 1)(g n + 1)`, by `n ≤ g n` (`timeConstructible_iff`'s first conjunct). This is
the brief's checkpoint-7 arithmetic, done early. `C = c(a + A + b + 1)` is uniform, as gate 39
requires.

**Is the main-machine contract the right interface for checkpoints 2–7?** Yes, exactly.
- **The function.** `computesFunInTime_cond` needs `M₁` total, so the contract quantifies over
  every word. `F x = query f g (replicate |x| true)` depends only on `|x|`:
  - it is `[]` for `|x| ≤ 2` (`query_of_not_guard`, since `3 ≤ |x|` fails);
  - it is `query_eq`'s word for `|x| ≥ 3` (`query_eq f g hn`).
- **The route's `M₁` meets it on non-unary and short inputs.**
  - `bits n` comes from the input call of `computesFunInTime_lengthBits`, which serves any word.
  - `g`'s witness runs on the native input. `TimeConstructible g` gives a machine computing
    `(g |x|).bits` on **every** word (`timeConstructible_iff`; definition at
    `ClassP/TimeConstructible.lean:74`), so the input call serves non-unary words too.
  - `f`'s witness runs through the install call on `1^a`, never on `x`.
  - The setup's `n ≥ 3` scan outputs `[]` for `n ≤ 2`, which is `F x`.
- **The bound.** `A(g n + 1)` holds for every `n`: constant for `n ≤ 2`; the linear ledger plus
  `O(g n + 1)` otherwise.
- **Recommendation.** Keep `hmain`'s statement verbatim as the continuation's target, and keep
  the `suffices` until it is proved. Checkpoint 7 then closes it with `qy_query_of_main` already
  in place.

**Edge cases covered at this checkpoint** (all instances of what the kernel checked; none of the
statements carries an extra hypothesis):
- non-unary words, and lengths 0, 1, 2 (rejected by the guard);
- a unary word of length 3 (the main branch);
- `g n = n` (the absorption needs only `n ≤ g n`).

The top, first-stage, timeout and large-output cases belong to `M₁` (checkpoints 2–7), as REPORT
says.

## (d) Rule 10 and rule 11

| # | Check | Result | Evidence |
|---|---|---|---|
| 17 | Elaborated walk (the three privates and the target, stopping at the 21 frozen declarations) | 8 local constants (the 3 privates, `qy_guard_decider._proof_1_1…4`, the target). **16 direct TCSlib constants**, 4 of them definitions: `Complexity.TimeConstructible`, `FinTM.ComputesFunInTime`, `FinTM.ComputesInTime`, `Turing.incFixed`. Plus 306 core/Mathlib constants (322 in all, = the worker's `external-constants.tsv`). The cited statements reach no further TCSlib definition. No external private, no R3 row; only core `eq_*` aux names (`eq_self`, `eq_false`, …) | out/13 |
| 18 | Tactic arguments | 105 identifiers classified in the environment (out/15): every `rw`/`simp only`/`simpa only` argument is a core theorem (`if_pos`, `Option.getD_some`, `decide_eq_true_eq`, …), a TCSlib theorem (`incFixed_eq_none_iff_replicate`, `incFixed_nil`) or a local. Definitions occur only as terms: `FinTM.ComputesFunInTime`, `incFixed` (in `cases hi : incFixed x`), `List.replicate`, `decide`, `max`, the owned `query`, and the core `List.singleton` (F6). There is no `unfold`, `dsimp`, `show` or `change`. The worker's `rule10-inspection.md` lists the same arguments | out/14, out/15 |
| 19 | My seal (`scripts/mkseal.py`) | `attribute [local irreducible]` on 32 definitions: the worker's 29 (the brief's list, `counterValue`, `incFixed`), plus `Action.apply`, `Cfg.init` and `NDTM.initCfg`. `attribute [-simp]` on all four `@[simp]` TCSlib definitions of the environment (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`; out/15's listing). Placed at the top of region (b). **Body: 0 errors.** Controls, inside the namespace so the local seal applies: 31 delta `rfl` controls, 4 `simp` erasure controls and 4 usage-shaped controls, the last for the four reached definitions (`h x` for `ComputesFunInTime`, `ComputesInTime` as its `∃ s`, `h.1` for `TimeConstructible`, `incFixed [false, true] = some [true, true]`). **All 39 fail sealed** (74 errors = 35 × 2 + 4; no PASS message) **and close unsealed** (35 PASS, 0 errors) | out/16 |
| 20 | `List.singleton` experiment | with the core `List.singleton` also sealed, exactly one error: `apply congrArg List.singleton` (head 354) cannot unify. The step closes only by reducing a core definition, outside the `rfl`/`decide`/`show` steps the 2026-10-23 scope names (F6). With E3 (`refine congrArg (fun b => [b]) ?_`) the body has 0 errors even with `List.singleton` sealed | out/17, out/27 |
| 21 | The worker's seal and controls | `OwnedSealed.lean` = the head file plus the block (29 definitions, `[-simp] MultiTapeTM.initCfg`) before region (b): 0 errors (`seal-final`). Controls: 28 generated plus `incFixed [] = none`. Unsealed 28 PASS and 0 errors; sealed 0 PASS and 58 errors. Sound; it erases one of the four `@[simp]` definitions (F7) | out/29, delivery `evidence/` |
| 22 | Probes | The brief's `EQImportProbe` (182 checks; 9 imports + `#check` only): 0 errors, 0 warnings. The worker's `ImportProbeExtended` (501 checks): 0 errors, 1 warning (`Int.ofNat_nonneg` deprecated, reached through arithmetic tactics; its own log shows it too, and REPORT says "zero errors and warnings": F8). It covers all 16 TCSlib and all 306 core/Mathlib direct externals. Seven of the 16 TCSlib names were outside the brief's 182 (`FinTM`, `ComputesFunInTime`, `ComputesInTime`, `computesFunInTime_ifEq`, `incFixed`, `incFixed_length`, `incFixed_nil`), so extending the probe was needed and done | out/18, out/19 |
| 23 | Rule 11 | no R3 row, no other file's private (walk; the kinds table has no private name but the owned `qy_`s). `qy_`/`Qy` appears in no TCSlib file on any of the 289 local and remote refs except the delivery | out/13, out/15, out/22 |

## (e) Duplication

**The screens** (out/05):
- The worker's before screen (`fabce3bb`, 1,734 declarations, 2,162 pairs, 758,806 chars) is
  **byte-identical** to the base's `eq-fill-query-screen-base.txt`.
- The after screen (`9d93626d`; 1,738 / 2,164 / 758,958) differs by exactly two new pairs
  (`pairdiff.py`), none gone:
  - `qy_guard_decider` reproduces `Nondeterminism.lean::a3n_poly_fixed_eq`: 76/114 = 67%;
  - `qy_guard_decider` reproduces `TMSAT.lean::tmsat_pt_eq`: 76/127 = 60%.
- There is no in-file pair and no measurement changed. Both runs used the population's 29
  files. The declaration count rises by 4: the three privates, and the target, whose body now
  passes the screen's 60-character minimum.

**What the pairs are** (out/06, the screen's own tiling):
- **Each pair is exactly two tiles:**
  - `FinTM.computesFunInTime_ifEq w [true] [false]` (42 characters), the invocation of the
    public fixed-word row;
  - `using 1 funext x by_cases hx : x = w <;> simp` (34), the conversion of
    `if x = w then [true] else [false]` into `[decide (x = w)]`.
- **The two sources** are a pair of colleagues' private lemmas: `a3n_poly_fixed_eq` and
  `tmsat_pt_eq`, each three lines, the same conversion lifted to `PolyTimeComputable`.
- **The same idiom already pairs in the screen base:** `TMSAT_NPHard` reproduces `tmsat_pt_eq`
  at 65% and `a3n_poly_fixed_eq` at 53%, and the two sources pair with each other at 76% and
  85%.
- **It is an idiom pair:** the same public row, composed with the same three-step conversion.
  Nothing published is re-derived, and the guard does not copy either lemma's argument (each is
  only the conversion).
- **The overlap is wider than the screen shows.** `qy_guard_decider` also reproduces 49% of
  `a3n_poly_unary` and 48% of `tmsat_pt_unary`, just under the screen's half threshold. These
  are the neighbours' private polynomial-time unary deciders (increment ∘ empty test, with
  their own `getD [] = []` criterion). `EXPCOM.lean`'s private `expcom_all_true` is a third
  home of that criterion. The guard is the fourth.
- **The new copy is the least derived of the four:** it cites the public
  `incFixed_eq_none_iff_replicate` and `incFixed_length`. The neighbours re-prove
  `a3n_inc_none`/`tmsat_inc_none` (= the public criterion) and `*_inc_nonempty`.

**Is there a published decider all three should cite?** The public fixed-word decider is
`FinTM.computesFunInTime_ifEq`, and all three already cite it. What is not published is:
- its Boolean-singleton reading `[decide (x = w)]`, which the conditional's test argument needs;
- the linear unary decider `[decide (x = replicate |x| true)]`;
- the criterion in `getD` form.

`exact?` closes none of these (out/21, statements 3–6). The search found no statement or
generalization of them on any of the 289 local and remote refs, including `origin/main` and every
fetched PR branch (out/22). Rule 11 forbids citing the neighbours' privates.

**Disposition (decision 2).** Accept both as idiom pairs (recommended).
- They meet the campaign's idiom criterion: the shared text is a public row and its standard
  conversion, as with the accepted `Cfg.mapState_mapState` pairs.
- Nothing citable exists.
- The alternatives cost far more than they remove:
  - a public lemma in `Composition`/`Primitives`/`Convention` would replay most of the library;
  - one in a new leaf module needs a ninth import and a gate cycle before E-Q can continue;
  - a refactor of the guard (for example the framed input fold) to dodge 76 characters would
    hide the same idiom, and the brief offered the function-level rows by name.

Record the promotion (F11) for the maintainer's dedup window instead.

**Semantic duplication per private** (`exact?` in out/21; text search in out/22):

| New private | Published candidates checked | Result |
|---|---|---|
| `qy_guard` | `query_eq`, `query_of_not_guard` (cited) | `exact?` fails; the brief's route equation (`qy_guard` in the route probe) |
| `qy_guard_decider` | `computesFunInTime_ifEq`, `_incFixed`, `_cond`, `_comp`, `_const`, `incFixed_eq_none_iff_replicate`, `incFixed_length`, `incFixed_nil` (cited); the neighbours' privates `a3n_poly_unary`/`tmsat_pt_unary`, `*_fixed_eq`/`*_pt_eq`, `*_inc_none`, `*_inc_nonempty`, `expcom_all_true` (not citable) | `exact?` fails on the statement and on the inner facts (Boolean fixed-word decider, linear unary decider, `getD` criterion, nonempty increment); not published on any ref |
| `qy_query_of_main` | `computesFunInTime_cond`, `timeConstructible_iff` (cited) | `exact?` fails; specific to `query` |

`ClassP/BinaryArith` (#135, on `main`) is not relevant at this checkpoint: there is no L2 or L3
yet.

## (f) Process

**E-SERIAL (decision 1; F1).**

What happened (out/23, out/35):
- The narrowed `lake exe cache get` compiled the cache executable first. That is 20 Lake jobs,
  among them `Batteries.Data.String.Basic` (316 ms) and `Batteries.Data.Array.Match` (684 ms).
- By the worker's reconstruction from trace mtimes and Lake's timing semantics, those two ran
  together for about 316 ms, at 05:35:46Z. That is during the shared session setup (Part 3,
  item 2), **before the item's branch existed** (05:37:27Z).
- The worker noticed it at 06:13Z, after checkpoint 1's commit. It named it E-SERIAL and
  stopped all proof work ("No further proof construction follows that finding"). The after
  screen finished and the item ended at 06:20:49Z, 43 minutes after the branch was created.
  The cp1 REPORT, at 05:59Z, already called it a "process limitation".

Was the bootstrap within the one-Lean rule's scope? **No.**
- **The rule's own text scopes it to the agent's checks.** The cover: "One Lean process at a
  time and one screen at a time, under `nice -n 10`. Every check through
  `scripts/lean_check_tree.sh`." Part 3, item 5 carries the same rule across the queue. Its
  purpose (Part 1's "Why") is the memory of concurrent module checks on 8 GiB hosts.
- **Part 1, item 2 classifies this exact work** as "expected and allowed": the cache tool's
  internal validation, and (v2.4) "on its first use, `lake exe cache` also compiles the cache
  executable itself … not a `lake build` of the project".
- **The prescribed command cannot be serialized.** Lake 4.25's help lists no job-count option
  (`Lake/CLI/Help.lean` in the pinned toolchain, read, not run; out/23). A rule that the
  addendum's own command cannot satisfy was not meant to cover it.
- **The worker's own checks were serial.** I confirm the worker's count: 182 Lean records, 0
  overlaps (out/35). Memory was never short: 6.5–7.8 GiB headroom at every reading, 0 `oom`
  (`runtime-memory.log`).

Was stopping required? **No.**
- No rule turns a process deviation into a stop. Ground rule 4 stops "on anything unprovable
  as stated", item by item. The cover ends an item early only "if nothing is left that its
  escalations allow". Megafill C's E-CHK was a disclosed deviation, with no stop.
- A past event cannot be cured by stopping.
- The cost: the session's remaining budget, and with it checkpoints 2–7. Checkpoint 1's proof
  work took about 6 minutes (the guard drafts 05:46–05:47Z, sealed by 05:52Z), so the session
  was productive while it ran.

**Proposed wording** (decision 1). For the addendum, as v2.6:
- Part 1, item 2 (the cache tool's own work):
  > - **The cache tool's own work is outside the one-Lean rule.** `lake exe cache get` may first
  >   compile the cache executable (on a fresh clone, about 20 Lake jobs, among them a few
  >   Batteries modules) and runs `lake build --no-build proofwidgets:release`. Lake schedules
  >   these jobs itself, and at this pin it has no option to serialize them. They are expected
  >   and allowed. They are not a `lake build` of the project, and they are not "a Lean process"
  >   in the sense of Part 3, item 5. Run the command alone: start no check of your own until it
  >   has exited. Do not reconstruct, measure or certify Lake's internal scheduling, and do not
  >   report it as a deviation.
- Part 3, item 5:
  > 5. **One Lean process at a time** across the whole queue, and one screen at a time. A Lean
  >    process is one that you start: a module check, a probe, a bootstrap or sweep step (each
  >    through `scripts/lean_check_tree.sh`), or one `lake exe cache get`. Never run two of them
  >    at once. One text screen (Python, `nice -n 10`) may run beside one of them. Processes that
  >    Lake or the cache tool start inside `lake exe cache get` are not counted.
- A new Part 3, item 7:
  > 7. **A process deviation never ends an item.** A deviation from these rules, yours or a
  >    tool's, is disclosed in `REPORT.md` with its evidence, and the work continues: stopping
  >    does not undo it. Only E-RES (Part 1) or an item brief's own escalation (its ground rules)
  >    ends an item early.

For the continuation brief (its environment section):
> - **E-SERIAL (megafill D) is not a deviation** (the user's ruling): the cache tool's own
>   compilation inside `lake exe cache get` is outside the one-Lean rule. Do not stop, or open an
>   escalation, for it or anything like it. Your own checks stay strictly one at a time: never two
>   `lean_check_tree.sh` runs, probes or sweeps at once, and none while `lake exe cache get` runs.
>   A screen may run beside one of them.

**Checkpoint zip** (cover: "one checkpoint, one commit, one zip … deliver it as soon as it is
written"; F8, F9):
- Met: one checkpoint, one commit (`9d93626d`), one zip `fill-eq-query-cp1.zip`, written at the
  commit's second.
- The commit came 11 minutes after the source was final (05:48:32Z). In between ran the
  per-checkpoint seal, controls, axioms, probe, lint and freeze. That is reasonable.
- The cp1 zip carries a partial `final-sweep.log`, copied while the sweep was still running (to
  module 61; no `.json` or `.exit`). Its REPORT discloses the sweep as "pending" and ships the
  tail check instead, which the brief allows.
- Both zips reached the inbox together (06:45:17/19Z). That they were delivered "immediately"
  cannot be checked from here.

**The session report** (F9: resolved):
- `megafill-d-REPORT.md` was not in the intake. It arrived separately at 06:53:13Z. That is
  correct in form: the cover asks for it as its own deliverable "at the end", and it must carry
  both zips' SHA-256s, which no zip can hold.
- It matches the zips on every checked fact: the two zip hashes; the branch start and item end;
  the dispatch hashes; the preflight (31,103,799,296 B free; headroom 8,390,078,464 B); the
  pre-cache disk (26,974,597,120 B); the empty store; 34 roots and 1,003/1,003 files; the
  manifest; the sweep sums (493.631 s and 502.596 s, with their peaks); and the screens
  (1,158.702 s and 1,144.766 s, peak about 0.5 GB). Out/24 has the 23-item check.
- The zip's `evidence/runtime/write_megafill_report.py` was not run, and needs no review.

**Environment (v2.5)** (out/24, delivery logs):
- Preflight: 9 CPUs; 28.97 GiB free (floor 12); headroom `8,589,934,592 − (100,954,112 +
  98,902,016 + 0)` = 7.81 GiB (floor 4); overlay filesystem, not tmpfs.
- Part 2: the condition occurred (`failed to locate application`), and the shim's SHA-256 is
  the addendum's.
- Store logged first (absent, 0 files); 1,003 files fetched, exit 0.
- **34 roots = my computation from the overlay**, against 33 at the shared base. The cover
  says 34; Part 3's literal command "at the shared base" gives 33, because the overlay's
  `Mathlib.Data.Nat.Log` is applied only on the item branch. The worker added it and logged
  the adjustment, correctly (F13).
- Manifest PASS (11 present, 4 doc packages absent); 0 empty oleans; per-module time and memory
  through `os.wait4`, since `/usr/bin/time` is absent.

**Screens and budget figures** (for the continuation; F10):
- Each screen took **1,159 s and 1,145 s** (about 19 minutes; peak 0.5 GB). The brief's "about
  14 minutes" is the maintainer's host.
- The before screen ran beside 137 Lean records (the whole bootstrap among them), yet took no
  longer than the after screen, which ran nearly alone (out/35). Running a screen beside Lean costs
  nothing here.
- The bootstrap took 494 s and the final sweep 503 s; a tail re-check is about 5 s.

## Findings

| # | Severity | Location | Claim | Evidence | Proposed resolution |
|---|---|---|---|---|---|
| F1 | **major** (process: an unnecessary stop) | the session (E-SERIAL) | The worker ended all proof work after checkpoint 1, 43 minutes into a session-length budget, over a 316 ms overlap inside the cache tool's own build. The overlap happened during the shared setup, before the item began. That build is outside the one-Lean rule (the rule's text and purpose; Part 1, item 2; no Lake job option at this pin), and no rule asks for a stop. Checkpoints 2–7 were not attempted. No effect on the delivered content | out/23, out/35; REPORT "Environment"; `cache-bootstrap-concurrency.log` | Decision 1: rule it not a deviation; adopt the v2.6 wording above (scope, "a Lean process", "a process deviation never ends an item") and the continuation-brief paragraph |
| F2 | minor (governance; decision) | `qy_guard_decider` (`hcut`, head 280–308) | Two new cross-file pairs, which the brief's "No new cross-file pair … Nothing is pre-disclosed" forbids. Each is the public `computesFunInTime_ifEq` call plus the `[decide (x = w)]` conversion: an idiom pair, already present in the screen base as a class. No published statement exists to cite | out/05, out/06, out/21, out/22 | Decision 2: accept as idiom pairs (recommended). If checkpoint 1 travels, pre-disclose both in cont1. Replace the absolute ban with the disposition rule in "The continuation" below |
| F3 | minor (docs) | `qy_guard`'s docstring (head 256–257) | "agrees with its unary-input version exactly on unary words of length at least three" is false as an "exactly": every word of length at most 2 also agrees (both sides `[]`) | head 256; `query_of_not_guard` | E1: "The query of a word is the query of the unary word of the same length when the word is unary of length at least three, and is empty otherwise." |
| F4 | minor (brief's leaf rule) | `qy_guard_decider`'s docstring (head 267–274) | Leaves need "a docstring saying which public row it is not"; this one only lists the rows it uses | brief, "Leaves you may write" | E2 adds: "No public row decides this guard: the fixed-word test `Turing.FinTM.computesFunInTime_ifEq` decides one word, and the increment `Turing.FinTM.computesFunInTime_incFixed` signals an all-true word only by an empty output." |
| F5 | note (docs) | the (d) paragraph (head 443–445) | Accurate and public-facing, but it omits one obligation the frozen sketch names, "the ledger" | head 424–445 | E5: "…budget computation, output writer and linear ledger remain open." |
| F6 | note (rule 10) | `qy_guard_decider`, head 354 | `apply congrArg List.singleton` closes only by reducing the core `List.singleton` during unification. That is not a `simp`/`rw`/`unfold` use, and REPORT calls it permitted, but it is outside the `rfl`/`decide`/`show` steps the 2026-10-23 scope names. Harmless | out/17 | E3: `refine congrArg (fun b => [b]) ?_`; tested, with `List.singleton` sealed (out/27) |
| F7 | note (rule-10 records) | the worker's seal | It erases one of the environment's four `@[simp]` TCSlib definitions (`MultiTapeTM.initCfg`, not `Action.apply`, `Cfg.init`, `NDTM.initCfg`). The one unrestricted `simp [he]` has a goal with no TCSlib constant, so nothing is affected | out/15, out/16, out/29 | None. Mine covers all four with erasure controls. For cont1: erase all four, and seal every definition the walk reaches |
| F8 | note (records) | REPORT, cp1 zip, commits | REPORT says the 501-check probe has "zero … warnings" (it has one deprecation warning). REPORT is 564 KB because it inlines both 274 KB screens (the brief asked to "quote both outputs"). The cp1 zip ships an in-progress `final-sweep.log`. Commit subjects carry the campaign label "E-Q". The file has a double blank line (head 418–419) | out/19, out/ziplist-*.txt, out/08 | E4 removes the blank line. Reword the subjects in the PR if wanted. For cont1: quote the screens' summary and new pairs, ship the outputs as files; logs in a cp zip are finished runs or marked partial |
| F9 | note (resolved) | `megafill-d-REPORT.md` | Not in the intake; delivered separately afterwards, as the cover's form requires, and consistent with the zips | out/24 | None. For later covers: deliver the session report with the final zip, in the same message |
| F10 | note (budget) | the brief's timing | A screen takes about 19 minutes a run on the fill host (1,159 s; 1,145 s), not 14. Bootstrap and final sweep about 8.4 minutes each | out/24, out/35 | Use the measured figures in cont1 (below) |
| F11 | note (promotion; the maintainer's dedup window) | `Nondeterminism`, `TMSAT`, `EXPCOM`, this file | The linear unary decider and the Boolean fixed-word decider are argued privately in four files: `a3n_poly_fixed_eq`/`_unary`/`_inc_none`/`_inc_nonempty`, their `tmsat_` twins, `expcom_all_true`, `qy_guard_decider`. `Savitch`'s `hD'` uses the same conversion inline. REPORT proposes no promotion for it | out/06, out/22 | Promotion requests: `FinTM.computesFunInTime_decideEq (w)` beside `computesFunInTime_ifEq`; a linear `FinTM.computesFunInTime_allTrue` beside `computesFunInTime_incFixed`; `incFixed_getD_eq_nil_iff` beside `incFixed_eq_none_iff_replicate`. Then re-point the customers (dedup owned by the maintainer, the 12.2c window). Not this landing |
| F12 | note (landing order) | H's pre-ship (`campaign/fills/h/drafts/h-fill-hierarchy/preship-9d0af8cb/`) | H's overlay imports `NTimeDiagonalizer`, and its 11-file screen population includes it. If checkpoint 1 lands first, H's order list goes 81 → 83 (`Build/Contract/Catalog`, `Build/Contract/Seam`), its roots 33 → 34 (`Mathlib.Data.Nat.Log`), and its screen base gains the three privates (a 4-second screen). B5a's 57-file population does not include the owned file | out/30 | Land checkpoint 1 before H issues, and re-take H's lists at that tree (decision 3) |
| F13 | note (brief accuracy) | cover / Part 3, item 2 | Part 3's root command runs "at the shared base", where an overlay's Mathlib import is not yet present (33), while the cover expects 34 | `roots-extraction.log`, out/24 | After the landing the base has 34 directly. For overlays with a Mathlib import, say "the shared base plus the overlays' imports" |

## Decisions for the user

1. **E-SERIAL (F1).**
   - (a) Rule that the cache tool's own build is outside the one-Lean rule, and that process
     deviations never end an item. Adopt the v2.6 wording and the continuation paragraph
     above. **Recommended.**
   - (b) Record it as a disclosed process deviation, as megafill C's E-CHK was. This leaves
     the rule's scope ambiguous for the next agent.
2. **E-DUP (F2).**
   - (a) Accept both pairs as idiom pairs: the public row and its standard conversion. Record
     F11's promotion for the dedup window, and use the disposition rule from now on.
     **Recommended.**
   - (b) A public-lemma API PR first (`computesFunInTime_decideEq`, `_allTrue`), in a new leaf
     module to avoid a library-wide replay, then a ninth import for E-Q. This costs a gate
     cycle before cont1.
   - (c) A refactor of the guard. Not recommended: it would only rephrase the idiom.
3. **Landing.**
   - (a) Land checkpoint 1 now by a maintainer PR and a light fill gate, with E1–E5, before H
     issues. Then base cont1 at the tip after the merge. **Recommended**:
     - the campaign's partials have landed this way (`lean/g4-cont2-partial`,
       `lean/g4-cont3-partial`, `lean/b6-f3-partial`, `lean/c1-un-partial` are all merged into the
       campaign branch; out/36);
     - the continuation then starts from a campaign commit, with an ordinary pre-ship and no
       patch inputs;
     - the replay is 2 modules;
     - the work and the eight imports are secured for E-D as well.
   - (b) The same, as delivered (no edits).
   - (c) Let checkpoint 1 travel with cont1, which carries the two patches as inputs (Part 3,
     item 3.1). One gate for E-Q later, but a heavier cont1 brief, and the pairs pre-disclosed.
4. **The landing edits E1–E5** (out/25; all tested): two docstring corrections (F3, F4), the
   status paragraph's ledger (F5), the `List.singleton` step (F6) and the blank line (F8).
   **Recommended: all five.** They change no statement and no axiom, and leave the pairs' text
   unchanged.
5. **The continuation's agent** (a soft suggestion). Codex again: its progress was fast
   (checkpoint 1 in about 6 minutes of proof work), and the stop came from a rule's reading,
   which the wording fixes.

## The continuation (E-Q cont1): what its brief must change

- **Base.** After decision 3(a): the campaign tip after the landing PR merges, plus the records
  commit that issues cont1.
  - Its Lean = #169's tree + checkpoint 1 (+ E1–E5).
  - No overlay: the eight imports are in the file, so the first edit is a proof edit.
  - Re-take every list at that tree. The order list is the facade's closure, 83 modules,
    computed there. The base sorries are still 22 in 11 modules (checkpoint 1 adds none; #169's
    files have none, out/31), or 21 in 10 if B5a's `exists_uniformSimulator` lands first
    (`CodeSimulator` is in the order list, out/37). The roots are 34. Re-take the screen base
    too: it then contains the two pairs.
  - After 3(c) instead: the current tip, with the two patches (and E1–E5) as prescribed inputs.
    The screen base is the delivery's after screen, with the two pairs pre-disclosed by name.
- **Numbering.** Keep the brief's checkpoints 2–7, and name the zips
  `fill-eq-query-cont1-cp<N>.zip` (N = 2…7) and `fill-eq-query-cont1.zip`, so that records and
  the route note line up.
- **Regions.**
  - (b) the home after `qy_query_of_main`. The three privates stay frozen, unless a change is
    authorized and reported.
  - (c) the `sorry` under the `suffices`: prove `hmain`, verbatim.
  - (d) the status paragraph, updated.
- **The target.** State `hmain` verbatim, with the facts above:
  - `F x = []` for `|x| ≤ 2` (`query_of_not_guard`), and `query_eq`'s word for `|x| ≥ 3`;
  - `g`'s witness from `timeConstructible_iff` computes `(g |x|).bits` on every word, so the
    input call on the native input serves non-unary words;
  - `n ≤ g n` is already absorbed by `qy_query_of_main`.
- **Duplication governance.** Replace "No new cross-file pair … Nothing is pre-disclosed" by:
  > A new cross-file pair with an owned-file declaration on one side is listed in `REPORT.md` with
  > its shared tiles and one disposition:
  > - **idiom**: the shared text is a public row's invocation and the standard conversion around
  >   it (for example `FinTM.computesFunInTime_ifEq w [true] [false]` with `convert … using 1;
  >   funext x; by_cases hx : x = w <;> simp …`), and no lemma, public or private, is re-derived.
  >   Justify it in one line and go on.
  > - **re-derivation of a published lemma**: cite the lemma instead, before the zip.
  > - **re-derivation of another file's private**: keep yours, and list it as a promotion
  >   request.
  >
  > A pair at 90% or more is a copy. None of these ends the item.
- **Pre-disclosures.**
  - The accepted idiom classes: the `Cfg.mapState_mapState` field equations, and the
    `[decide (x = w)]` conversion of `computesFunInTime_ifEq`.
  - If 3(c): the two pairs by name.
- **E-SERIAL.** The ruling paragraph above, and the no-stop rule.
- **Lessons for L2, L3, L5, L6.**
  - Each leaf's docstring says which public row it is not, and why.
  - No core or Mathlib definition is reduced outside `rfl`/`decide`/`show`: write
    `congrArg (fun b => [b])`, not `congrArg List.singleton`.
  - The seal erases all four `@[simp]` TCSlib definitions (`Action.apply`, `Cfg.init`,
    `MultiTapeTM.initCfg`, `NDTM.initCfg`) and seals every definition the walk reaches.
  - Recursive definitions (`incFixed`) get usage controls, not delta controls.
- **REPORT.** Quote each screen's summary and new pairs, and ship the full outputs as files. A
  cp zip's logs are finished runs, or marked partial.
- **Budget** (measured on this fill host).
  - Fetch about 2 minutes; bootstrap 8.2 minutes.
  - Screens about 19 minutes each (1,159 s; 1,145 s).
  - Final sweep 8.4 minutes; a tail re-check about 5 s.
  - Start the before screen right after branching, beside the bootstrap: it costs nothing here
    (out/35).
  - Run the after screen once, at the end, beside the final sweep. Checkpoint zips carry the
    tail check, the seal and the axiom prints, not a screen.
  - Reserve about 25 minutes for the finishing sequence: the final sweep with the after screen
    beside it, then the REPORT and the zip. Use the rest of the session for proofs.
  - A cheaper screen mode for the maintainer's tools: only pairs with a changed-file
    declaration on one side. That would make a continuation's screen a minute or two.
- **Promotion requests carried.** The brief's own (the clocked install call, L2, L3, L6), plus
  F11's three.
- **H** (F12): re-take H's pre-ship lists at the landing tree before H issues.

## Landing

**Recommendation: land checkpoint 1 by a maintainer PR into `complexity/arora-barak-ch3-4`, with
a light fill gate.**

**Not yet clear to merge.** It becomes clear when all of these hold:
- the PR is open and based on the campaign branch, not stacked;
- decisions 1–3 are taken;
- the replay below has passed;
- the fill gate is recorded with zero blockers and zero majors. F1 is a process finding, closed
  by decision 1; it does not concern the landed content.

**Commits.**
- Cherry-pick `fabce3bb` and `9d93626d` from `deliver/fill-eq-query-in` (sole prerequisite
  `ab09aa41`, a records-only ancestor of the tip), or squash them. They touch only
  `NTimeDiagonalizer.lean`, which is unchanged at the tip (blob `3cdc4f33`). They apply cleanly
  at `729ffb99` (out/33).
- Reword the "E-Q" subjects if the PR wants library-only wording.
- One maintainer commit with out/25-landing-edits.diff (E1–E5). It is tested at the head, against
  `oleans-lu2m` and `oleans-laplusm`:
  - exactly the two `sorry` warnings (447/517; out/26);
  - axioms unchanged (out/28);
  - the 39-control seal, also with `List.singleton` sealed (out/27);
  - freeze: no statement changed; only `qy_guard`'s and `qy_guard_decider`'s text and the
    target's docstring change (out/28, out/28b);
  - lint 0 FAIL, 2 WARN; widths at most 97; no double blank line; 543 lines;
  - the pairs' measurements unchanged (67%, 60%).
- No module-header edit is needed: its entry "(sorried; C1-E's first fill)" stays true for a
  partial. Its labels belong to the deferred docstring cleanup.
- Link `.lake/packages` in the PR worktree.

**Replay.**
- The downstream closure is 2 modules, the same at the head and with the edits (out/03):
  1. `TCSlib/Complexity/Diagonalization/NTimeDiagonalizer`;
  2. `TCSlib/Complexity/Diagonalization` (the facade; never the root `TCSlib`).
- The upstream closure grows from 17 to 35 modules, all present in `oleans-laplusm`.
- Chain from the snapshot that is exactly the tree the PR merges into: `oleans-laplusm` now (the
  tip's Lean = #169's merge, out/31). If B5a, H or anything else merges first, use the snapshot
  its merged-tree replay leaves. Never compose snapshots.
- Expected: 0 errors; `NTimeDiagonalizer` with exactly `exists_queryTM`'s and
  `exists_diagonalizer`'s warnings; the facade with none.

**Order against the in-flight work.**
- **H** (draft; its pre-ship is on #169's tree; F12): land checkpoint 1 first, then re-take H's
  order list (+2 modules), roots (+1) and 11-file screen base. Its import probe and route probe
  need no change, since H cites statements only.
- **B5a** (pre-ship on #169's tree; its assembly is prepared locally, `5c971874`): its population
  excludes the owned file, and `CodeSimulator` is in the order list but not upstream of the owned
  file (out/37). Independent, except that whichever lands second replays the facade at the merged
  tree, and that cont1's base sorry set is 21 in 10 modules if B5a's `exists_uniformSimulator`
  lands first.
- **E-D** (`exists_diagonalizer`, the same file): it follows E-Q and cites only the target's
  statement. It must not run in parallel with cont1 in this file.

**What the fill gate's pack should ask.** Attach:
- `campaign/standards/TEMPLATE.md`, `policy.md` and `workflow.md`;
- the brief, the cover and addendum v2.5;
- the delivery's REPORT and evidence, and `megafill-d-REPORT.md`;
- this review with `out/`, and the landing diff.

It should ask:
1. **Correctness:** the three privates and the reduction; is the `hmain` contract the right
   interface (section c)?
2. **Route conformance:** L1 from the function-level rows, and F4's docstring rule.
3. **E-DUP:** the idiom disposition and F11's promotion; any further semantic overlap with the
   neighbours' `*_unary` deciders.
4. **Rule 10:** the seal sets (mine: 32 plus 4 erasures, 39 controls; the worker's: 29 plus 1,
   29 controls); F6 and E3. Rule 11.
5. **The duplication screen at the landing head,** against the tip's screen base.
6. **The public-facing text** of the three docstrings, (d), and E1–E5.
7. **Process:** the E-SERIAL ruling, the cp zip and the session report.
8. **The replay** (2 modules) and the order against H.
9. **Deliverable:** a downloadable `eq-query-cp1-fill-findings.md` with the findings table and
   the verdict line.

**Review table for the PR body:**
- integrity: 295/295 sums; one bundle; 2 commits; patches = bundle = file;
- scope: regions (a)–(d); statements and frozen docstrings byte-identical; 3 `qy_` privates;
  the eight authorized imports;
- elaboration at the base and at #169's tree: exactly the two expected sorry warnings;
- axioms: the standard three for the privates; the target's `sorryAx` only from its own body;
- rule 10: a 39-control seal (32 definitions, 4 erasures); rule 11 clean;
- probes: 182 and 501 checks, 0 errors;
- screen: 1,734 → 1,738 declarations, 2,162 → 2,164 pairs (two idiom pairs, decision 2);
- lint: 0 FAIL, 2 WARN; sweeps: 22 sorries = the base;
- edits E1–E5; replay: 2 modules.
