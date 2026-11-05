# Gate 03l: review of the auditor's findings, with resolution proposals

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03l-findings.md`: 1 major, 3 minors and 210 notes (rows 5–214).
- **Code:** worktree `wt-g03r` at `af91d53a`. `git diff --stat a3c5fa8b HEAD -- TCSlib/Complexity/Randomized/Build` is empty, so the six `Build/*` files are byte-identical to the pinned `a3c5fa8b`. The 26-module closure listed in `evidence/l/replay.log` is unchanged too. Line numbers below refer to those files. Unless a path says otherwise, a Lean file is under `TCSlib/Complexity/Randomized/Build/`.
- **Also read:** `Repetition.lean` (pack 03a), main's `ClassNP/SAT.lean`, `ClassNP/PolyTimeBlockLoop.lean`, `ClassP/BinaryArith/Basic.lean` and `TuringMachine/Build/EmitIterBody.lean`, `briefs/pass-shelat/DESIGN.md` §2.4 and §2.6, `policy.md` §1–§3, `machine-library-design.md` §14, the duplication ledger, and `QUEUE.md` (G3-5, G3-6).
- **Downstream:** `wt-s2b-fix` (`243598b7`), `wt-prong-a` (`2d7b5441`), `wt-prong-b` (`587843c7`), `wt-prong-c` (`9e6f08bb`) and `wt-prong-d` (`6ea900ae`). All five carry the same six `Build/*` files.
- **Method:**
  - I did not build Lean.
  - I ran `scripts/campaign_style_lint.py --check8b` (read-only) on the six files.
  - I grepped for the users of every touched declaration, using scripts in `scratchpad/g03l-tools/` (`users.py`, `clash.py`, `simcheck.py`). All were run with `python3 -I`.

## Summary

- **No finding is false.** I agree with every severity: Major 1 stays major, and Minors 2–4 stay minor. The auditor's per-declaration readings hold. I found no wrong statement, and the two adversarial counterexamples check.
- **Major 1 (`axioms.log` is empty): true.**
  - The file holds only its heading line (139 bytes). Pack attestation 2's "0 use only the standard axioms, and 0 depend on `sorryAx`" counts over an empty selection.
  - The maintainer's full print of every public theorem in the six files closes it.
  - The gate's existing print log (`scratchpad/g03-checks.log`, at `a3c5fa8b`) already shows standard axioms for the nine consumers built on these files (lines 15–16 and 25–31). So the new print is expected to be clean.
- **Minor 2 (DESIGN §2.6 tests the old length): true.**
  - `DESIGN.md:384` guards on `|pairSndD w| ≤ P|x|`. The auditor's `R = 0, P = var, g = true :: ·, x = []` instance breaks the claimed closure at `:387–390`.
  - **Missed:** the same stale design is copied into pack 03a's `Repetition.lean`: the construction plan at `:68–95` and the proof sketch of `polyTimeComputable_iterateFind` at `:199–215`. Policy §3 says such a sketch "is worse than no sketch".
  - **Fix:** a dated as-built erratum to DESIGN §2.6, and a rewrite of the two `Repetition.lean` passages.
- **Minor 3 (32 public definitions without reading lemmas): true, with a part the auditor missed.**
  - **The missed part:** two files already read these definitions by unfolding them, against policy §1's no-unfolding rule. There are about 16 sites:
    - `IterateFind.lean`: `rfl` on `hostRet` ×5, `simp [copyTM]` ×2, and `hostTM`'s `q₀`/`k` read by definitional equality;
    - `Repetition.lean` (03a): `IterateFind.step … := rfl`, `simp [IterLoop.acc]` ×4, `simp [IterLoop.out]`, `simp [EmitLoop.out]`, and `unfold XorLoop.rounds` ×2.
  - **The pack's lint attestation understates the gap.** It ran the presence-only `scripts/style_lint.py`. The `campaign_style_lint.py` check 8/8b reports 7 definitions and 2 machines.
  - **Fix:** 39 one-line lemmas (`rfl`/`Iff.rfl`), about 150–190 lines in 4 files; re-point the 16 sites; run the rule-10 seal check. Only `BlockLoop.blk` is a reasonable candidate for `private`. For `copyTM` and `hostTM`, use `simps` with `isSimp := false`.
  - No ruling is needed: policy §1 and the R-04-2 precedent (every equation lemma) settle the scope.
- **Minor 4 (13 public docstrings are labels): true.** Rewrite them as statements.
  - **Missed:** `Clean`'s docstring (`IterateFindHost.lean:182–185`) omits the conjunct `0 < M.k`, which is part of the formal definition.
- **Notes: 210 rows.**
  - 153 need no action: 17 general notes, 67 private declarations and 69 public declarations. Two of the 153 have optional fixes: note 6 (design record) and note 65 (wording).
  - 1 is the same as Minor 2, 32 are Minor 3's rows and 13 are Minor 4's.
  - 11 public rows not in any minor need action: `copyTM`, `hostTM`, the 7 FP-toolkit lemmas, and `orbit_zero`/`orbit_succ`. Three Minor 3 rows (`step`, `Clean`, `BlockLoop.*`) and the private copy rows carry extra items.
  - **Missed items that should have been raised:**
    - **(a) Duplication, unledgered.** This is major under policy §1 until the user accepts the debt.
      - `IterateFindHost.lean` reproduces 26 declarations of main's private module layer in `ClassNP/SAT.lean:3785–4202` (148 of 216 code lines of `:79–335` match). Ten of the copies are public: `Clean`, `clean_install`, `clean_emit`, `HostState`, `hostEntry`, `hostRet`, `hostTM`, `host_call`, `guard_add`, `host_clean`.
      - The `StateLoop` FP toolkit (`headBit_poly`, `tail_poly`, `isNil_poly`, `not_poly`, `or_poly`, `xor_poly`) restates lemmas that main has had since 2026-10-09/14 (`PolyTimeBlockLoop.lean`, `BinaryArith/Basic.lean`). They arrived together with the #186 merge, like DL-3.
      - `UnaryMul` copies `PairSplit`'s parser privately.
      - The new public host is missing from the host registry (`machine-library-design.md` §14).
    - **(b) A latent namespace clash.** `Complexity.StateLoop.BlockLoop` (03l) and main's `Complexity.BlockLoop` share the short names `step` and `orbit`. Ten modules see both namespaces; none uses `BlockLoop.` yet.
    - **(c) Two unlisted `@[simp]` attributes.** `orbit_zero` and `orbit_succ` (`StateLoop.lean:186`, `:190`) carry `@[simp]`. G3-6 approved only the attributes listed in packs 03a, 03b, 03c and 03e, and these two are in none of them (§6.6).
- **User rulings needed:**
  - **R-03l-1:** the duplication in (a) (§6.1).
  - **R-03l-2:** the two `@[simp]` attributes in (c), probably a one-line extension of G3-6 (§6.6).
  - Everything else is a maintainer fix.
- **Effect on other packs and on ch. 5–8:**
  - **Ch. 5–8:** no new ch. 5–8 file uses any of the 35 definitions or 13 theorems touched here. The user sets are identical in all five sibling worktrees, and the 13 theorems are used only inside 03l's own files.
  - **03a:** `Repetition.lean` changes in its proofs (9 re-pointed sites) and its prose (Minor 2). No statement changes.
  - **Additive only:** 03g, 03i, 03j and 03k use `orbit`, `gstep` and `gstepBound` only through lemmas, so they see only new lemmas.
  - **G3-5 clean-up:** the queued fix to the `stateFind` prose at `StringLoops.lean:36–38` touches the same file. Land both in one PR.

---

## 1. Major 1: `evidence/l/axioms.log` is empty

### Verdict: **true**. Severity: **major (agree)**.

**Evidence.**
- `evidence/l/axioms.log` is 139 bytes, one heading line: "headline axiom prints (audits/pass-shelat/Checks.lean) for declarations in pack 03l's files, at a3c5fa8b…". It has no result lines.
- `audits/pass-shelat/Checks.lean` names no declaration in the six files. A grep for `exists_pairSplitTM`, `polyTimeComputable_find`, `clean_install` and `Build.` finds nothing. So the selection is empty by construction.
- Pack attestation 2 still reads "0 use only the standard axioms, and 0 depend on `sorryAx`". This is a count over nothing, and specific question 3 cannot be answered from the packet.

**Severity.**
- I agree with major, as the closing condition. The pack's own question 3 asks about main's five `Loop.lean` admissions, and only a print answers it.
- It is an evidence defect, not a statement defect, and it needs no Lean change.

**Supporting evidence the maintainer can reuse.** The gate 03 print log `scratchpad/g03-checks.log` was taken at `a3c5fa8b`, and the closure is unchanged at `af91d53a`. It already shows `[propext, Classical.choice, Quot.sound]` for:
- `Turing.FinTM.computesFunInTime_pairSplitAt` and `computesFunInTime_unaryMul` (lines 15–16), which consume `exists_pairSplitTM` and `exists_unaryMulTM`;
- `polyTimeComputable_iterateFind` and the six derived lemmas (lines 25–31), which consume `IterateFind.polyTimeComputable_find`, `clean_install`, `clean_emit`, `copy_clean`, the `host_*` lemmas and the `StateLoop`/`StringLoops` lemmas.

So the auditor's note 10 (no use of the five `Loop.lean` admissions) is already borne out for every consumer. The fresh print adds the 90 public theorems themselves.

**Fix (maintainer, as agreed).**
- Print every public theorem of the six files at the pinned head (90 declarations), plus the 9 consumers above, into `evidence/l/axioms.log`.
- Reword attestation 2 so that an empty selection reads "not applicable (no declaration selected)", never "0 of 0".

**Ruling:** none.

---

## 2. Minor 2: DESIGN §2.6 tests the old length

### Verdict: **true**. Severity: **minor (agree)**.

**Evidence.** The auditor cites `DESIGN.md:381`. The exact lines are:
- `:384`: "`stepF x w := if |pairSndD w| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`". The guard tests the **old** state.
- `:386`: "`Inv x w := pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length`".
- `:387–390`: "`|g s| ≤ …` is **not** needed … so `Inv` is closed under `stepF` for every `w`".

**The counterexample checks.**
- Take `x = []`, `P = var` (so `P|x| = 0`), `g s = true :: s`, `R = const 0`.
- The orbit hypothesis needs only `i = 0`: `|x| ≤ 0`, which holds.
- `w = pairEncode [] [] = [false, true]` satisfies `Inv`. The old guard `0 ≤ 0` passes and installs `pairEncode [] [true]`, whose second component has length 1 > 0, so `Inv` fails.
- `exists_loopFindTM` asks for closure of `Inv` under the step on every admissible word, not only on the orbit. So the design route cannot discharge that hypothesis.
- The implementation guards on the **new** point (`IterateFind.lean:98–99`: "`if (g (pairSndD w)).length ≤ P.eval x.length then …`"), and its private `Inv` asserts an actual pair (`:104–105`). `inv_step` (`:114–121`) closes it.

**Other departures from §2.6, all confirmed.**

| §2.6 says | Built |
|---|---|
| step 3 (`:401–410`): body `Unit ⊕ (C₁ ⊕ C₂ ⊕ C₃) ⊕ Fin 3`, `leftAction`/`leftCfg_run`, transitions into `exit` **redirected** | `IterateFindHost.lean:85–95` (`stopTM`, a release flag that halts one silent step after the first positive exit), `:273–292` (`padTM`), `:531` (`HostState M := Fin 3 ⊕ Σ i, (M i).State`), five modules |
| step 4 (`:411–415`): a one-state copy scan plus `timed_rewind` | `copyTM`, two states (`:343–355`) |
| step 5 (`:421–423`): `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` | `IterateFind.lean:329–332`: `T n = A·(2n + 2 + P n + 5)^D` |

**Missed by the auditor: the same stale text sits in pack 03a's file.**
- `Repetition.lean:47–99` (module docstring, "Construction plan of `iterateFind`"):
  - step 1 (`:50–58`) has the right guard, but names `LoopInv` as the machine's invariant. The machine uses the private actual-pair `Inv`, and `LoopInv`, `loopInv_init` and `loopInv_guardedStep` are used by no proof (grep over all six worktrees);
  - steps 3–5 (`:68–89`) repeat the redirected gluing, the `inl ()` anchor, the one-state copy scan with `timed_rewind`, and the old budget;
  - step 7 (`:95`) says `acc := lenEq cnt 1^{R|x|}`, whereas `IterLoop.acc` is a `≤` test.
- `Repetition.lean:199–215`, the proof sketch of `polyTimeComputable_iterateFind`:
  - items (1) and (3)–(5) describe that construction;
  - the proof (`:226–244`) is in fact a `convert` from `IterateFind.polyTimeComputable_find`, via `iterate_guardedStep_eq`, `acc_guardedStep_eq` and `find?_congr_of_mem`.
- Policy §3 ("Synchronization") applies: "A sketch that describes a proof the code no longer performs is worse than no sketch."
- The citations "(DESIGN.md §2.6, step 1)" in `IterateFind.lean:95` and in `Repetition.lean`'s `guardedStep` docstring (`:135`) point at the wrong guard.

**Fix (maintainer).**
1. Append a dated **as-built erratum** to DESIGN §2.6; do not rewrite the frozen text. It records:
   - the new-output guard, and the actual-pair invariant (needed for the length bound `2|x| + 2 + P|x|`);
   - the release-flag stop, the padding and the five-module `Fin 3 ⊕ Σ` host;
   - the two-state copier;
   - the budget `A·(2n + 7 + P n)^D`.
   Optionally, add to §2.4 that `PairSplit` uses one work tape, not two (auditor note 6).
2. Rewrite `Repetition.lean:47–99` and `:199–215` to describe the built route, and point them at `Build/IterateFind{,Host}`. This touches 03a's prose only, not its statements.
3. Keep the "§2.6, step 1" pointers. They are right once the erratum exists.

**Ruling:** none. The erratum leaves the frozen decisions and signatures alone.

---

## 3. Minor 3: public definitions without reading lemmas

### Verdict: **true, and understated**. Severity: **minor (agree)**.

**Count confirmed.**
- The six files have 35 public `def`/`abbrev`s: IterateFind 1, IterateFindHost 6, StateLoop 10, StringLoops 18.
- `orbit` has `orbit_zero`/`orbit_succ` (`StateLoop.lean:186–191`; their `@[simp]` is not yet approved, see §6.6). `copyTM` has `copy_clean`; `hostTM` has `host_call`, `host_clean`, `host_dispatch`, `host_branch` and `host_halt`.
- The other 32 have no defining equation, case lemmas or `_iff`. The closed forms (`orbit_eq`, `acc_orbit_*`, `out_orbit`) and the `_poly` lemmas read them only on the orbit, or not at all.

**Policy.** `policy.md` §1, "Definitions land with their lemmas" (user, 2026-10-16): "any other definition: an equation lemma `<name>_eq` … or case lemmas that together cover every input … a predicate: an `_iff` characterization … Consumers never unfold another file's definition." Run 3b wrote these files on 2026-10-28, after the rule. So the clause "Definitions that predate the rule … are covered as consumers need them" does not apply.

**Missed by the auditor: consumers already unfold these definitions.** Scan: `scratchpad/g03l-tools/users.py`.

| Site | Reads | How |
|---|---|---|
| `IterateFind.lean:338–342` | `hostRet M 0..4` (IterateFindHost) | `:= rfl` ×5 |
| `IterateFind.lean:326`, `:348` | `copyTM.k = 1` | `simp [M, K, copyTM]`, `simp [M, copyTM]` |
| `IterateFind.lean:350–353` | `(hostTM …).tm.q₀ = hostEntry M 0` | `Cfg.ext rfl …` on the state field |
| `IterateFind.lean:343–345`, `:375–385` vs the `host_*` outputs | `(hostTM …).k = K + 1` | definitional equality between `stateWord H.k` and `stateWord (K + 1)` |
| `IterateFind.lean:416`, `:446` | possibly `hostEntry … ≠ .inl 0` | `simp [Cfg.ofWords, anchor]`; the seal run decides |
| `Repetition.lean:229` (03a) | `IterateFind.step` | `IterateFind.step g P x = guardedStep g P x := rfl` |
| `Repetition.lean:322`, `:327`, `:378`, `:383` | `IterLoop.acc` | `simp [IterLoop.acc, …]` |
| `Repetition.lean:334` | `IterLoop.out` | `simp [IterLoop.out]` |
| `Repetition.lean:390` | `EmitLoop.out` | `simp [EmitLoop.out, …]` |
| `Repetition.lean:434`, `:464` | `XorLoop.rounds` | `unfold XorLoop.rounds` |

**The lint attestation understates this.**
- `evidence/l/lint.log` comes from `scripts/style_lint.py`, which checks presence only.
- `scripts/campaign_style_lint.py --check8b`, run on the six files, gives 5 WARN:
  - check 8: `step`, `hostEntry`, `hostRet`, `gstepBound`, `blk`, `rounds` ×2;
  - check 8b: `copyTM`, `hostTM`.
- Check 8's name heuristic accepts the `_poly` lemmas as "coverage" for the other 25 names. So a clean check 8 does not prove compliance either.

**Severity.**
- I keep **minor**. Gate 04 rated the same pattern (F02) major, but here:
  - the readers are two ch. 2–4 files of the same layer;
  - no ch. 5–8 file reads these definitions (§7);
  - no statement depends on the missing lemmas.
- Still, the fix is mechanical and should land in the gate 03 repair PR, not be deferred.

**Fix: lemmas to add.** None carries `@[simp]`. Each docstring states its formula, and each is proved by `rfl` or `Iff.rfl` unless marked.

| Definition | File:line | Lemmas |
|---|---|---|
| `IterateFind.step` | `IterateFind.lean:98` | `step_eq : step g P x w = if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w`; optional cases `step_of_le`, `step_of_lt` |
| `Clean` | `IterateFindHost.lean:186` | `clean_iff : Clean M result emit B ↔ 0 < M.k ∧ ∀ x arg, ∃ t, 0 < t ∧ t ≤ B arg.length ∧ … ∧ …`. Name it in lower case, as in policy's `recordAt_iff` |
| `HostState` (abbrev) | `:531` | `hostState_eq : HostState M = (Fin 3 ⊕ Σ i, (M i).State)`. A reducible type abbreviation is notation, but policy still asks for one `_eq` |
| `hostEntry` | `:534` | `hostEntry_eq : hostEntry M i = .inr ⟨i, (M i).tm.q₀⟩` |
| `hostRet` | `:539` | five cases covering `Fin 5`: `hostRet_zero : hostRet M 0 = hostEntry M 1`, `hostRet_one : … 1 = .inl 0`, `hostRet_two : … 2 = .inl 1`, `hostRet_three : … 3 = .inl 0`, `hostRet_four : … 4 = .inl 2` |
| `copyTM` (machine) | `:343` | `@[simps (config := { isSimp := false }) k]`, giving `copyTM_k : copyTM.k = 1`. Its consumer needs this, and it clears check 8b |
| `hostTM` (machine) | `:547` | `@[simps (config := { isSimp := false }) k tm_q₀]`, giving `hostTM_k : (hostTM M K hk).k = K + 1` and `hostTM_tm_q₀ : … = hostEntry M 0` (or two explicit `rfl` lemmas) |
| `gstep` | `StateLoop.lean:195` | `gstep_eq : gstep step B w = if (step w).length ≤ B.eval (pairFstD w).length then pairEncode (pairFstD w) (step w) else w` |
| `gstepBound` | `:199` | `gstepBound_eval : (gstepBound B).eval n = 3 * n + 2 + B.eval n` (by `simp`, in its own file); optional literal `gstepBound_eq` |
| `IterLoop.start` / `step` / `acc` / `out` | `:280–292` | `start_eq : start x = pairEncode [] x`; `step_eq : step g w = pairEncode (true :: pairFstD (pairSndD w)) (g (pairSndD (pairSndD w)))`; `acc_eq : acc R w = decide (R.eval (pairFstD w).length ≤ (pairFstD (pairSndD w)).length)`; `out_eq : out w = pairSndD (pairSndD w)` |
| `EmitLoop.start` / `step` / `out` | `:329–338` | `start_eq`, `step_eq`, `out_eq` (the bodies at `:329`, `:333–335`, `:339`) |
| `MajLoop.start` / `step` / `acc` / `out` | `StringLoops.lean:68–84` | `start_eq`, `step_eq`, `acc_eq`, `out_eq` |
| `XorLoop.start` / `step` / `acc` / `out` / `rounds` | `:175–193` | `start_eq`, `step_eq`, `acc_eq`, `out_eq`, `rounds_eq : rounds z = min (pairFstD z).length (pairSndD z).length` |
| `EqLoop.step` / `out` / `flag` | `:298–311` | `step_eq`, `out_eq`, `flag_eq` (or cases `flag_of_eq`, `flag_of_ne`) |
| `BlockLoop.start` / `blk` / `step` / `acc` / `out` / `rounds` | `:430–449` | `start_eq`, `step_eq`, `acc_eq`, `out_eq`, `rounds_eq : rounds b z = (pairSndD z).length / b.eval (pairFstD z).length`; `blk_eq`, unless `blk` becomes private (below) |

**Size.**
- 39 required lemmas: IterateFind 1, IterateFindHost 11, StateLoop 9, StringLoops 18 (17 if `blk` becomes private). Up to 3 optional: `step_of_le`, `step_of_lt` and `gstepBound_eq`.
- At about 3–5 lines each, that is 150–190 lines. `IterateFindHost.lean` goes from 695 to about 740 lines; no file approaches 1000.
- Re-pointing the 16 sites:
  - `IterateFind.lean`: `copyTM_k` at `:326` and `:348`, `hostRet_*` at `:338–342`, `hostTM_tm_q₀` at `:353`, `hostTM_k` where the seal shows it;
  - `Repetition.lean`: `funext w; rw [IterateFind.step_eq]; rfl` at `:229` (`guardedStep` is its own definition), `IterLoop.acc_eq` and `out_eq`, `EmitLoop.out_eq`, and `rw [XorLoop.rounds_eq]`.
- Then a rule-10 seal check (`attribute [local irreducible]` on the consumed definitions, with controls), as in gate 04 round 2.
- Re-run attestation 4 with `campaign_style_lint.py --check8b`. Its check 8 and 8b lists for the six files should come out empty.

**Private, or `simps`?**
- **`BlockLoop.blk` → private.** No statement or consumer names it; only the bodies of `step` and `acc` use it. If it is private, state `step_eq` and `acc_eq` with `b.eval (pairFstD (pairFstD v)).length` written out. This saves one lemma.
- **Everything else stays public:**
  - `IterateFind.step` is in `polyTimeComputable_find`'s statement and is read by `Repetition`;
  - `HostState`, `hostEntry` and `hostRet` are in the public types of `host_call` and `host_clean`;
  - `Clean` is in `clean_install`, `clean_emit` and `host_clean`;
  - `gstepBound` is passed by 5 files;
  - the loop data are the instance data of `polyTimeComputable_stateFind`, which G3-5 makes public, and they appear in public `orbit_eq` statements;
  - `XorLoop.rounds` and `BlockLoop.rounds` are named in `Repetition.lean`;
  - `EqLoop.flag` is in `EqLoop.orbit_eq`.
- **`simps`:** only for the two `FinTM` literals, `copyTM` and `hostTM`. This follows policy §1's rule for structure-valued definitions (`isSimp := false`, explicit projections). The others are functions into `List Bool`, `Bool`, `ℕ` or `Prop`, where `simps` does not apply.

**Ruling:** none. Policy §1 fixes the scope, and the user's R-04-2 (every equation lemma) is the precedent.

---

## 4. Minor 4: public theorem docstrings that are labels

### Verdict: **true**. Severity: **minor (agree)**.

**Evidence.** All 13 cited lines check.
- `StateLoop.lean:341` "The orbit point of the state word." (`point_poly`) and `:345` "The accumulator of the state word." (`accum_poly`).
- `StringLoops.lean`:
  - `:86`, `:90`, `:94` (`MajLoop.rest_poly`, `trues_poly`, `falses_poly`);
  - `:195`, `:199`, `:203`, `:207` (`XorLoop.fstRest_poly`, `sndRest_poly`, `accum_poly`, `xorBit_poly`: "The xor of the two head bits …, as a one-bit output.");
  - `:451`, `:455`, `:459` (`BlockLoop.param_poly`: "The unary parameter `fst z` of the state word."; `rest_poly`; `accum_poly`).
- `IterateFindHost.lean:645` "Specialize a clean module to one call site in the host." (`host_clean`).

Each formal statement asserts `PolyTimeComputable …`, or the bounded host-call contract, so the formal side is correct. Policy §2: "A bare label … is not a statement."

**Missed by the auditor (note 81): `Clean`'s docstring omits a conjunct.**
- `IterateFindHost.lean:182–185` describes the seam, the first halt, the budget, the result and the emission. It never mentions `0 < M.k`, which is the first conjunct of the definition (`:187`), nor that the first halt is at a positive time.
- The auditor's restatement includes `0 < M.k`, but the docstring does not, so a blind restatement from the docstring would miss it.

**Fix (maintainer, prose only).**
- For the 12 projection/test lemmas, write "The map `v ↦ …` (the … of the state word) is polynomial-time computable."
- For `param_poly`, add "any first component works: only its length is used as the parameter".
- For `host_clean`, write: "If module `i` is `Clean` with budget `B`, then from the host seam at its entry, with output prefix `pre`, the host reaches the seam at `hostRet M i` holding `f arg`, with output `pre ++ g arg`, at some time `0 < t ≤ B |arg|`, and does not visit the anchor before `t`."
- For `Clean`, add "the module has at least one work tape (`0 < M.k`), and the first halt is at a positive time".
- Optional: the five `orbit_eq` docstrings ("The closed form of the orbit: …") read better as "After `i` rounds the state is …".

**Ruling:** none.

---

## 5. The 210 notes

### Classification

| Group | Rows | Count | Action |
|---|---|---:|---|
| General: source comparison, budget arithmetic, fresh coins, `Loop.lean` dependency, inventory, run-3 record, adversarial instantiations, finite checks | 5–20, 22 | 17 | none. Note 6 → optional DESIGN §2.4 erratum (one work tape), with Minor 2 |
| Same as Minor 2 | 21 | 1 | with Minor 2 |
| Private declarations, "agrees with the docstring" | 23–37, 39–53, 56–71, 73, 75–80, 82–83, 86–91, 93–97, 103 | 67 | none on statements. Note 65 → optional wording. The copy rows → §6.1 |
| Public declarations, agree, no action | 38, 54, 72, 74, 84, 85, 98, 104, 105, 107–111, 114, 120–122, 127–130, 135–139, 145–148, 156–164, 174–182, 186–196, 206–214 | 69 | none (84, 85, 104 → §6.1 ledger only) |
| Same as Minor 3 | 55, 81, 99–101, 125, 126, 131–134, 140–142, 149–152, 165–169, 183–185, 197–202 | 32 | Minor 3. Extra items: 55 → §6.4, 81 → Minor 4, 197–202 → §6.3 |
| Same as Minor 4 | 106, 143, 144, 153–155, 170–173, 203–205 | 13 | Minor 4 |
| Public, needing action that the auditor missed | 92, 102, 112, 113, 115–119, 123, 124 | 11 | below |

The totals check: 17 + 1 + 67 + 69 + 32 + 13 + 11 = 210. They match the auditor's census: 35 public definitions, 90 public theorems, 16 private definitions and 51 private theorems.

### Notes that need action (one line each)

- **55 (`IterateFind.step`):** add `step_eq` (Minor 3). The definition repeats `Complexity.guardedStep`'s body (`Repetition.lean:139`); the docstring discloses this. Bridge the two through `step_eq` (§6.4).
- **65 (`stepWord_verdictWord`, private), optional:** the docstring says "an admissible pair", but the identity holds for every pair. Drop "admissible".
- **81 (`Clean`):** add `clean_iff` (Minor 3), and add `0 < M.k` and the positive first halt to the docstring (Minor 4).
- **92 (`copyTM`):** add `simps … k` (`copyTM_k`). `IterateFind.lean:326,348` unfolds `copyTM` to get it.
- **102 (`hostTM`):** add `simps … k tm_q₀`. `IterateFind.lean:350–353` and the `H.k` steps read them by definitional equality.
- **112, 113, 115–118 (`headBit_poly`, `tail_poly`, `isNil_poly`, `not_poly`, `or_poly`, `xor_poly`):** these restate main lemmas; ledger them (§6.1).
- **119 (`length_pairFstD_add_pairSndD_le`):** it is implied by main's `length_pair_components_le` (`PolyTimeBlockLoop.lean:207`, `2|fst y| + |snd y| ≤ |y|`). Ledger it with the toolkit (§6.1).
- **123, 124 (`orbit_zero`, `orbit_succ`):** their `@[simp]` attributes are outside G3-6's list. Get them approved (R-03l-2, §6.6).
- **197–202 (`BlockLoop.*`):** add the reading lemmas (Minor 3), and record the latent name clash with main's `Complexity.BlockLoop` (§6.3).
- **75–91, 103, 104, 106 and 41–46 (copied machine layers):** the docstrings disclose the copies, but they are not ledgered (§6.1).

### Notes that should have been raised

- **Duplication (rows 75–91, 103, 104, 106, 41–46, 112, 113, 115–119):** this should have been a **major**. Policy §1 says: "the audit template treats accumulated duplication as a major finding that a gate cannot close over without the human maintainer explicitly accepting the debt and naming where and when it is paid back". The 03a review raised #8 to major on the same rule. It closes by ledger (R-03l-1), with no Lean change needed now.
- **Rows 81 and 92/102:** each should have been part of a minor, Minor 4 and Minor 3 respectively. They are folded in above.
- **Rows 123/124:** the unapproved `@[simp]`s should have been a minor, as they were in 03a, 03b, 03c and 03e. They go to R-03l-2.

---

## 6. Missed by the auditor

### 6.1 Unledgered duplication (major until ruled; R-03l-1)

**(a) The clean-module host is a copy of `ClassNP/SAT.lean`'s private module layer.**
- `IterateFindHost.lean:47–49`: "The clean-module layer is a private copy of the module-gluing layer of `TCSlib.Complexity.ClassNP.SAT` (`satStopTM`, `satClean_install`, `satHost_call`, …), a template only, never a dependency." `DESIGN.md:433–434` planned it: "private copies, not edits".
- The correspondence is declaration by declaration:

  | SAT (`SAT.lean`) | 03l copy |
  |---|---|
  | `sat_call_first_halt` :3785 | `call_first_halt` |
  | `satPad*` :3843–3893 | `padAction`, `padTM`, `padCfg`, `pad_apply`, `pad_run`, `pad_seam` |
  | `satStopTM` / `satStopCfg` / `satStop_step` / `sat_live_prefix` / `satStop_clean` :3908–3950 | `stopTM`, `stopCfg`, `stop_step`, `live_prefix`, `stop_clean` |
  | `SatHostState` / `satHostEntry` / `satHostRet` / `satHostTM` / `satHost_seam` / `satHost_call` :3982–4033 | `HostState` (`Fin 3` for `Unit`, `Fin 5` modules for `Fin 6`), `hostEntry`, `hostRet`, `hostTM`, `host_seam`, `host_call` |
  | `sat_guard_add` :4076 | `guard_add` |
  | `SatClean` / `satClean_stop` / `sat_bridge_bound` / `satClean_install` / `satClean_emit` :4091–4161 | `Clean`, `clean_stop`, `bridge_bound`, `clean_install`, `clean_emit` |
  | `sat_request_budget` :4183 | `IterateFind.request_budget` |
  | `satHost_clean` :4191 | `host_clean` |

- That is 26 declarations. 148 of the 216 code lines of `IterateFindHost.lean:79–335` occur verbatim in `SAT.lean:3770–4210` once the `sat` prefix is dropped (`simcheck.py`).
- Ten of the copies are **public** here: `Clean`, `clean_install`, `clean_emit`, `HostState`, `hostEntry`, `hostRet`, `hostTM`, `host_call`, `guard_add`, `host_clean`.
- Policy §1 ("Hosts come first", binding, 2026-10-12) says "A private host already in the tree is harvested into the shared layer before a second consumer is briefed against it". This host is the second consumer, built against a copy. It is also missing from the host registry (`machine-library-design.md` §14, rows H1–H13).

**(b) `UnaryMul` copies `PairSplit`'s parser.**
- `UnaryMul.lean:28–29`: "in the idiom of the coin-splitting machine … (whose parser is copied privately)".
- `mulCfg`, `mulCfg_read`, `mulCfg_congr`, `mul_first`, `mul_block` and `mul_back` (`UnaryMul.lean:129–240`) match `splitCfg` through `split_rewind` (`PairSplit.lean:129–243`) line for line, apart from renames. That is about 80 lines.
- `PairSplit.lean:26–27` in turn takes "the idiom of the private buffered extractor of `TuringMachine.Build.Primitives` (copied privately, never edited)".

**(c) The `StateLoop` FP toolkit restates main's lemmas.**
- They arrived on this branch with the #186 merge, the same way DL-3 did:

  | 03l (`StateLoop.lean`) | main |
  |---|---|
  | `headBit_poly` :95 | `Complexity.polyTimeComputable_headD` (`ClassNP/PolyTimeBlockLoop.lean:308`), same statement |
  | `tail_poly` :105 (`List.tail`) | `polyTimeComputable_tail` (:143, `w.drop 1`) |
  | `isNil_poly` :117 | `polyTimeComputable_isNil` (:156), same |
  | `not_poly` :123 | `polyTimeComputable_not` (:175), same statement and proof |
  | `or_poly` :131 | `polyTimeComputable_or` (:167), same statement and proof |
  | `xor_poly` :138 | `BinArith.polyTimeComputable_xor` (`ClassP/BinaryArith/Basic.lean:208`), same |
  | `length_pairFstD_add_pairSndD_le` :146 | implied by `length_pair_components_le` (:207) |

- Main's files date from 2026-10-09/14; run 3b wrote `StateLoop` on 2026-10-28, on a branch without them.
- `cons_poly` is defined as `polyTimeComputable_prepend [b]`, an alias with no duplicated proof, so it needs no action.

**(d) Lesser: the copier is a re-derivation, not a copy.** `copyTM` with `copy_step` … `copy_clean` (`IterateFindHost.lean:338–524`) re-derives the input copier of main's private emit-iteration body (`TuringMachine/Build/EmitIterBody.lean:392–650`). The line overlap is 16%, so it is not a copy, but it is a parallel routine. List it in the same ledger entry as (a).

**R-03l-1, options (recommended first):**
- **(A) Ledger now, pay back at the `main` landing.**
  - Four DL entries, (a)–(d), plus a §14 registry row for the clean-module host that names both copies.
  - Payback: one public clean-module host in `TuringMachine/Build/`, generic in the number of modules and consumed by SAT and IterateFind; one copy of the FP toolkit, in `ClassNP/PolyTimePairing.lean` (already in `StateLoop`'s closure); `UnaryMul` reads `PairSplit`'s parser from a shared private-to-the-area file.
  - **Cost:** the gate closes on recorded debt; roughly 400–500 copied lines stay until the landing; no Lean change now.
- **(B) Clean up in the gate 03 repair PR,** as G3-5 does for ch. 2–4's own copies.
  - **Cost:**
    - it edits main-owned `ClassNP/SAT.lean` (around 420 lines), `PolyTimeBlockLoop.lean` and `BinaryArith/Basic.lean` on the ch. 2–4 branch, with merge-conflict risk against main;
    - it generalizes the host from `Fin 5`/`Fin 6`;
    - it re-points the toolkit's users: about 23 files in 03a, 03c, 03e, 03f2 and 03g–03k, including S2b-touched `PRFLemmas`, `MultiMessageLemmas` and `GraphIsomorphism/Efficiency*`;
    - 03g–03k re-pin again.
- **(C) Accept permanently** (a ledger entry with "no payback"). **Cost:** it contradicts "Hosts come first" and leaves three parallel module layers, two private on main and one public here.

### 6.2 `Repetition.lean`'s stale construction text (03a)

See §2. It belongs with Minor 2's fix: 03a's prose only.

### 6.3 Latent namespace clash: `Complexity.StateLoop.BlockLoop` vs main's `Complexity.BlockLoop`

- Main's `ClassNP/PolyTimeBlockLoop.lean` declares `Complexity.BlockLoop.step`, `orbit`, `length_flag_le`, … 03l declares `Complexity.StateLoop.BlockLoop.step`, and `Complexity.StateLoop.orbit`.
- In a module inside `namespace Complexity` (or with `open Complexity`) that also opens `Complexity.StateLoop`, `BlockLoop.step` is ambiguous.
- Ten modules import both and open `Complexity.StateLoop` (`clash.py`): HardCoreGL, HardCoreLoops, GI-ZK Simulator, ThreeColoring Parties, Machines, SimulatorNumeric and SimulatorMachine, and GI Efficiency, EfficiencyRep and EfficiencyRepGI. None writes `BlockLoop.` today. The same holds in all five sibling worktrees.
- **Fix (no ruling):** record it with R-03l-1's toolkit entry. If a consumer ever needs both, rename 03l's namespace to `StateLoop.BlockMapLoop`. That rename touches `StringLoops.lean` and 9 references in `Repetition.lean`.

### 6.4 `IterateFind.step` restates `guardedStep`

- `IterateFind.lean:94–99` defines the same function as `Repetition.lean:139–140`. Its docstring says why: "restated here because this file is imported by the file defining `guardedStep`".
- `Repetition.lean:229` joins the two with `rfl`, unfolding the other file's definition.
- **Fix:** prove the bridge through `IterateFind.step_eq` (Minor 3). Keep both definitions, since `guardedStep` is in 03a's audited surface. Optionally, record the restatement in the ledger as disclosed.

### 6.5 The lint attestation

Attestation 4 used the presence-only lint, so its "0 findings" missed check 8/8b (§3). Re-run it with `campaign_style_lint.py --check8b`, before and after the fix.

### 6.6 Two `@[simp]` attributes outside G3-6's list

- `StateLoop.lean:186` `@[simp] theorem orbit_zero` and `:190` `@[simp] theorem orbit_succ` are the only `@[simp]` attributes in the six files.
- Policy §1 says: "None carries `@[simp]` unless a gate approves it". G3-6 (A) approved "all the listed ones" in packs 03a, 03b, 03c and 03e. 03l was not among them, and its pack lists no attributes.
- Proofs rely on them:
  - explicitly, on 14 lines in 6 files (`StringLoops`, `HardCoreGL`, `HardCoreLoops`, `GGMReductionEval`, `GraphIsomorphism/EfficiencyRep`, `EncodingMachines`);
  - implicitly, in every non-`only` `simp` on an orbit goal, for example the zero cases of the four `orbit_eq` (`simp [start]`).
- **R-03l-2, options (recommended first):**
  - **(A)** Approve both under G3-6's terms (each is the defining equation of a structural recursion, oriented to unfold one round). **Cost:** none.
  - **(B)** Drop them. **Cost:** a replay of `StateLoop`, `StringLoops`, `Repetition` and the roughly ten consumer modules, adding `orbit_zero`/`orbit_succ` explicitly wherever `simp` relied on them.

---

## 7. Effect on other packs and on ch. 5–8

**Users of the 35 public definitions** (`users.py`, code lines outside the defining file):

| Users | Definitions read | Kind | Pack |
|---|---|---|---|
| `Build/IterateFind.lean` | `hostEntry`, `hostRet`, `hostTM`, `copyTM`, `HostState` | 7–9 unfolding sites | 03l |
| `Build/StringLoops.lean` | `orbit` | through `orbit_zero`/`orbit_succ` | 03l |
| `Randomized/Repetition.lean` | `IterateFind.step`, `orbit`, `gstep`, `gstepBound`, the `IterLoop`/`EmitLoop` data, `XorLoop.rounds`, `BlockLoop.rounds` | 9 unfolding sites | 03a |
| `Asymptotic/HardCoreGL.lean`, `HardCoreLoops.lean` | `orbit`, `gstep`, `gstepBound` | lemmas only | 03i |
| `Asymptotic/GGMReduction.lean`, `GGMReductionEval.lean` | `orbit`, `gstep`, `gstepBound` | lemmas only (the `show` at `GGMReduction.lean:312` restates its own `stateLoopFun`) | 03j |
| `ZeroKnowledge/EncodingMachines.lean`, `GraphIsomorphism/Efficiency.lean`, `EfficiencyRep.lean` | `orbit`, `gstep`, `gstepBound` | lemmas only | 03k |
| `ThreeColoring/Machines.lean` | `orbit` | lemmas only | 03g |

There are no users of `Clean` or of the `MajLoop`, `EqLoop` and most `XorLoop`/`BlockLoop` data outside their files.

**By fix:**
- **Major 1:** evidence only.
- **Minor 2:** `DESIGN.md` (not a pack file) and `Repetition.lean`'s prose (03a: an erratum to its pack, no statement change).
- **Minor 3:**
  - additive lemmas in 03l's four files;
  - proof edits in `IterateFind.lean` (03l) and `Repetition.lean` (03a: proofs, out of audit scope, no statement text changes);
  - 03g, 03i, 03j and 03k are untouched; they only gain lemmas they may use later. The G3-5 clean-up removes their `stateFind` copies anyway, and with them most of their `gstep`/`gstepBound` uses.
- **Minor 4:** docstrings only.
- **R-03l-1:** under (A), ledger entries and a registry row only. Under (B), the files listed in §6.1.

**Ch. 5–8: unaffected.**
- In `wt-s2b-fix`, `wt-prong-a`, `-b`, `-c` and `-d`, the set of (file, kind, line text) users of the 35 definitions is identical to `wt-g03r`'s. So no ch. 5–8 file reads any of them.
- The ch. 2–4 files that those worktrees changed (`PRFLemmas`, `MultiMessageLemmas`, `GGMReduction*`, `GraphIsomorphism/Efficiency*`, `ThreeColoring/Machines`) use only `StateLoop` theorems (`headBit_poly`, `tail_poly`, `isNil_poly`, `lenLe_comp`, `gstep_poly`, …). These matter only under R-03l-1 (B).
- No file in any worktree declares into `Complexity.StateLoop` or `Complexity.IterateFind` besides these four files. So the new `_eq` names cannot collide. The exception is main's separate `Complexity.BlockLoop` (§6.3).

**Ordering with G3-5.** The queued G3-5 clean-up changes `StringLoops.lean:36–38` ("the private state-loop form `polyTimeComputable_stateFind`") and `Repetition.lean:40–46`. Minor 3 and Minor 2 touch the same two files, so land all of them in the one gate 03 repair PR.

---

## 8. Rulings requested

**R-03l-1: duplication found in 03l (§6.1).**
- **(A)** Ledger now (four DL entries and a §14 registry row); pay back at the `main` landing. Recommended.
- **(B)** Clean up in the gate 03 repair PR.
- **(C)** Accept permanently.

The costs of each option are in §6.1.

**R-03l-2: the `@[simp]` attributes on `StateLoop.orbit_zero` and `orbit_succ` (§6.6).**
- **(A)** Approve them under G3-6's terms. Recommended; no cost.
- **(B)** Drop them, which needs a replay of about 13 modules.

No other item needs a ruling.

## 9. Proposed closing condition

1. Major 1: the full print is in `evidence/l/axioms.log`, with the attestation reworded.
2. Minor 2: the DESIGN erratum and the `Repetition.lean` prose sync.
3. Minor 3: the 39 lemmas, the 16 re-pointed sites, the seal log, and the lint re-run with check 8/8b.
4. Minor 4: the 13 docstrings plus `Clean`'s.
5. R-03l-1 and R-03l-2 ruled; under R-03l-1 (A), the ledger rows written.
6. Then a delta re-audit of the new lemma statements and docstrings only: about 45 short declarations.
