# Gate 48 · landing edit LE-g48 (finding G48-01): Mathlib's `abs_sub_le_of_nonneg_of_le` in `bb1_sim_real`

**Verdict: PASS, pushed.** `land/pairings-bb1-sim` (PR #357) is now
**`dfdc56f21898abe2d9d6cef83b0cfe57da87d28d`** (parent `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`), a fast-forward.
- The edit is proof-only: 1 file, +1/−3, exactly the brief's change. The statement, the docstring and every other line are
  byte-identical.
- The replay rebuilt **4/4 modules with rc 0**, 0 `error:`/`error(` and 0 `sorry`. The state check gives **1432/1432 OK**.
  The 4 rebuilt oleans have link count 1. Snapshot #5 and `olean-replay-bb1sim` rehash **0/0/0**, before and after.
- Admissions stay at **192**, with every per-module count unchanged.
- **Axioms:** `bb1_sim_real` and `bb1_sidSecure` use the standard three axioms, and both `#sorry_trace`s are empty. The
  probe log equals phase 2's except for two closure sizes.
- **Rule 10, coe-A on `BonehBoyenSecurity`:** **0 errors** and **2319 requests**. The request rows are **equal** to
  phase 2's, and the Lean log is byte-identical.
- Lint is unchanged.
- **New snapshot-#6 candidate:** `$SP/olean-replay-bb1sim-g48`, output map (Mathlib excluded) SHA-256
  **`0858dccbee016da1da450f2b2ca0d1f5094ee42646b9496d5278f2b45cb07caf`** (1463 entries).

Run on 2026-11-17, 10:15–10:30 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
The job's directory is `$SP/le-g48-work`.
- **Evidence:** `le-g48-evidence.zip`, beside this file, with `SHA256SUMS` and `omitted-SHA256SUMS`. Its own SHA-256
  is not recorded here, because the zip contains this file.
- **Diff:** `le-g48.diff.txt`, SHA-256 `759d4160c486d36c9453900cc0ae8f2d1b04c3ba17cd7f080acf122a412e950e`.
- **Builds:** no `lake build`, no cache get. One Lean process ran at a time. Before every module and probe, the job
  checked the host's slot count (fewer than 3 `lean` processes), polling every 30 s. It never had to wait: the counts
  seen were 1–2.

## The edit
`git diff 7a98ba01 dfdc56f2`, the whole diff (`--numstat`: `1 3 TCSlib/…/IdentityBased/BonehBoyenSecurity.lean`):
```diff
@@ -125,12 +125,10 @@ theorem bb1_sim_real (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
         ProbComp.abs_expect_sub_le_expect _ fun r => ?_
     _ = uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
         rw [← ProbComp.prob_eq_expect, Bridge.prob_sample_eq_uprob]
-  have h01 : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → |x - y| ≤ 1 := fun x y _ _ _ _ =>
-    abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
   by_cases hr : (G.inst κ r).order < 2 ^ ℓ.eval κ
   -- bad coins: two probabilities differ by at most `1`
   · rw [if_pos hr]
-    exact h01 _ _ (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
+    exact abs_sub_le_of_nonneg_of_le (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
       (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
   -- good coins: the chain of `BB1Sim.prob_sidGame_coins`
   · rw [if_neg hr]
```
- Lines 128–129 were deleted, and line 133 was replaced; line 134 stays. Before the edit, the job asserted all four
  original lines byte for byte.
- The one-liner worked as written, so no `(n := 1)` was needed.
- **Mentions of `h01`:** only lines 128 and 133, both removed. Neither the docstring nor the proof sketch mentions it. The
  comment `-- bad coins: two probabilities differ by at most 1` is still true and is unchanged.
- The new line is 90 characters, within the 100-character limit. The file has 223 lines (was 225).

## Commit and push
- **Worktree:** a sparse worktree (`git worktree add --no-checkout`, then `git sparse-checkout set --no-cone
  /TCSlib/Cryptography/AdvancedEncryption/IdentityBased/`) at `$SP/le-g48-work/wt`.
  - **Deviation:** the worktree was **detached at `7a98ba01`**, not on the branch. `land/pairings-bb1-sim` is already
    checked out in phase 2's landing worktree `$SP/bsp2/landwt`, and git does not check a branch out twice.
  - The push went `HEAD:land/pairings-bb1-sim`, as the brief says.
- **Before the commit**, after a fetch: `git ls-remote origin land/pairings-bb1-sim` = `7a98ba01…` (unchanged).
- **Commit:** `git commit -S -F <msg> -- <file>`, giving
  **`dfdc56f21898abe2d9d6cef83b0cfe57da87d28d`**, with tree `32a108b0c8bfbe7bda7e56aa370e6f64a942232a`.
  - Subject: `LE-g48: use Mathlib's abs_sub_le_of_nonneg_of_le in bb1_sim_real (Gate 48 G48-01)`.
  - The body is one paragraph, and the message ends with the two required trailers.
  - Author and committer are `Claude <noreply@anthropic.com>`.
  - The signature is an ed25519 SSH signature by **`SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`**, the key of
    `7a98ba01` and the records commits. The job read it with phase 2's `sigfp.py`.
- **Push** (after every check below): `git push origin HEAD:land/pairings-bb1-sim` →
  `7a98ba014..dfdc56f21 HEAD -> land/pairings-bb1-sim`, a fast-forward with no force. After the push, `ls-remote` gives
  `dfdc56f2…`.
- **Local refs:** the job did not move the local branch `land/pairings-bb1-sim`. It still points at `7a98ba01`,
  checked out in `$SP/bsp2/landwt`. Update it with `git -C $SP/bsp2/landwt pull --ff-only` (or fetch) when convenient.

## Replay (snapshots.md job recipe, on #357's replay tree)
- **Copy:** `cp -al $SP/olean-replay-bb1sim $SP/olean-replay-bb1sim-g48`. The copy has 1464 files, all hard links, and
  3346 Mathlib symlinks (copied as symlinks). The tree already had its overlay and the NthRootLemmas olean
  (`c0a9cff0…`), so no overlay step was rerun. The job never wrote into `olean-replay-bb1sim`.
- **Export:** a `git archive` of `dfdc56f2` (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, lake files,
  `lean-toolchain`; 1584 files), with `.lake/packages` symlinked. The edited file equals the commit's.
- **Plan:**
  - State: phase 2's `state.json` after its update at `7a98ba01` (`f62821f0…`), copied.
  - A pre-check of that state at `7a98ba01` against the copy gives `RESULT OK`.
  - `downorder.py dfdc56f2 7a98ba01`: changed 1, **down 4**.
  - `fullorder.py`: 1432 modules, byte-identical to phase 2's order.
  - `stateplan plan`: **4 to build, 1428 reused**: `BonehBoyenSecurity`, `IdentityBased`, `AdvancedEncryption` and
    `TCSlib`.
- **Build** (`tools/run-build-g48.sh`, 10:19:25–10:19:38): phase 2's `run-build-bsf.sh` with this job's paths and a 30 s
  poll, calling the recipe's `runner.py` unmodified, one module per call.
  - **4/4 rc 0**. `permod.py`: `error:` 0, `error(` 0, substring 0, `sorry` 0, warnings 0, no log/record mismatch.
  - Sources are bound to `dfdc56f2`, 4/4.
- **Accept:**
  - `stateplan update`: 4 modules, none left out. `check` over the full order gives **1432/1432, RESULT OK**, again at
    the end.
  - **Link count 1** holds for exactly the 4 rebuilt oleans. Every other file is a hard link.
- **Rehash** (`snapmap.py verify` for snapshot #5 against `map-3f540c22` `fca1b6a3…`; `tools/replayverify.py` for
  `olean-replay-bb1sim` against phase 2's map `b43812d0…`, plus 3346 Mathlib symlinks and the one NthRootLemmas olean):
  **0/0/0, RESULT OK for both**, before the copy, after the build and after all checks.
- **Output map** (`mapnoml.py`, Mathlib excluded): **1463 entries, SHA-256
  `0858dccbee016da1da450f2b2ca0d1f5094ee42646b9496d5278f2b45cb07caf`**. It was recomputed after all probes and is
  unchanged.
  - Against `olean-replay-bb1sim` (`b43812d0…`): 1462 equal, **1 changed** (`BonehBoyenSecurity`, `fa1c3a37…` →
    `bbcea599…`), 0 added, 0 removed. The other 3 rebuilt oleans are byte-identical to before.
  - Against snapshot #5: the same 4 changed and 5 added as phase 2.
- **Admissions** (`tipcensus.py`, phase 2's record sets plus this build): **192**. The per-module table equals phase 2's
  head census line for line, with `BonehBoyenSecurity` at 0. The 34 no-record modules are the same.

## Axioms and Rule 10
- **Axioms:** phase 2's probe `AxiomsBsf.lean`, the same source (`9c53df3b…`), through `rule10_g48.sh` (phase 2's
  `runner_full_gated.py`).
  - rc 0, 0 errors. The one `sorry` warning is the control's.
  - `AXIOMS-LIST 76 constants, 0 non-standard`.
  - `bb1_sim_real` and `bb1_sidSecure`: `[propext, Classical.choice, Quot.sound]`.
  - `#sorry_trace`: no direct `sorryAx` user for either.
  - The control is still reported as `NONSTANDARD [sorryAx]`.
  - **The log differs from phase 2's in two lines only**, the closure sizes: `bb1_sim_real` 15,352 → **15,349** and
    `bb1_sidSecure` 20,373 → **20,374**. The `have` with its `linarith` terms went away, and
    `abs_sub_le_of_nonneg_of_le` came in. `bb1_sim_random` (13,412) and the census are unchanged.
- **Collector** (9 owners, phase 2's template): rc 0. Its log is **byte-identical** to phase 2's.
- **Seal, canonical coe-A on `BonehBoyenSecurity`:** `rule10_b_gated.sh`'s `mkseals_coe.py` line, restricted to this
  owner, then `runner_full_gated.py` and `sealsum.py` as there. Strict seals, B seals and paired controls were not
  rerun, as the brief asked.
  - rc 0, **0 errors**, install and end records present. `requests 2319 terms 49 excluded-terms 25 stored 3`, the same
    as phase 2's `mkseals-coe-A.log`. The sealsum row is equal (`2319 0 0 1 1`).
  - **Request set:** the 2319 `rows` are **equal** to phase 2's, and so are `requested`, `term_names`,
    `term_in_closure`, `term_excluded`, `term_readers`, `stored_constants` and `closure_modules`.
  - The seal JSON differs only in `rev`, `source_sha256`, `probe_sha256` and the insertion offsets and line maps (−145
    bytes, −2 lines). The insertions are equal once offsets and lines are set aside.
  - The probe source differs from phase 2's by exactly the 3-line edit.
  - The seal Lean log is **byte-identical** to phase 2's (`f0f42dff…`). The removed local `have` was not a constant, so
    no request changed.

## Lint
- **`style_lint`** on `BonehBoyenSecurity.lean`: 0 findings.
- **`campaign_style_lint --check8b TCSlib/Cryptography`:** **92 FAIL / 104 WARN over 529 files**. The non-INFO lines
  are byte-identical to phase 2's head run (empty diff).
- The only INFO change is `BonehBoyenSecurity.lean` 225 → 223 lines.

## Deviations and notes
- **Detached worktree:** the worktree was detached instead of on the branch (see above). The local branch ref was not
  moved.
- **Reduced seal set:** only the coe-A seal on `BonehBoyenSecurity` was run, as briefed. The other 35 seals and the
  controls were not rerun. The collector log is byte-identical, and only this owner's source changed.
- **Probe prefix:** `BSF2` was kept, so the generated probe sources compare with phase 2's byte for byte.
- **Slot polling:** the slot poll inside phase 2's `runner_full_gated.py` stays at 20 s. This job's drivers gate every
  runner call first, with a 30 s poll.
- **Cleanup:** the worktree and the export were removed. `$SP/olean-replay-bb1sim-g48` and `$SP/le-g48-work/run`
  (12 MB) are kept, and nothing else was deleted.
- **Not touched:** `$SP/olean-replay-bb1sim` and `$SP/olean-snapshot` (read and hard-linked only), other agents'
  directories, and every other records file.
