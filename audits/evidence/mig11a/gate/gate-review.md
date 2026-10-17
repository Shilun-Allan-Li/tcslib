# Review of the statement-gate audit of PR #117 (MIG-11a, the row contracts)

**Verdict: the gate can close.** The audit is PASS, 0 blockers, 0 majors, 2 minors, 0 notes,
and I confirm it. Both minors are true and correctly graded.

| # | Auditor | Verdict | Fix |
|---|---|---|---|
| 1 | minor | **ACCEPT (minor)** | Docstring-only (`repair-docstring.patch`, tested). No width hypothesis is needed. The two instance contracts need no change. |
| 2 | minor | **ACCEPT (minor)** | Record correction. Re-run at `1358ff73`: **0 FAIL, 69 WARN over 79 files**, the same WARN set as the tip. `Contract/Counter` (131 lines, 3 public) has no WARN, and check 8 names none of the six new definitions. |

## Inputs checked

- **PR head:** `origin/lean/mig11a-row-contracts` = `1358ff736bf93d40d3f12ed5c8b61268afd9e1e1`, with parents `b131d239` (MIG-11a `08bcc57d` stacked on #116's `93c4c630`) and `455cb240`.
  - Against the tip `f139d21a`, which contains #116, the head changes four Lean files: `Build/Catalog`, `Build/Contract`, `Build/Contract/Catalog`, and the new `Build/Contract/Counter`.
  - The lint script is unchanged between the tip and the head.
- **Bundle:** `infra_local/gate-dispatches/33-mig11a-statements-gate/mig11a-bundle.md`, SHA-256 `84d0442f…b99b`, as commissioned. It has 39 sections with no duplicates; `BUNDLE-FILES.txt` has 39 entries. The README says its Lean files come from `1358ff73` and everything else from `455cb240`.
- **Replay:** `replay-lm11a.log` (equal to the evidence copy).
  - The header reads `replay-lm11a at b131d239 … (86 modules)` and the last line `# modules=86 failed=0`.
  - All 86 rows show `exit=0 errors=0`, with a sorry sum of 57, in the order of `replay-order.txt`.
  - It was run at `b131d239`, not `1358ff73`, but **no `.lean` file differs** between the two. The merge `455cb240` brought only records, so the replay covers the head's Lean exactly.
- **Screens:** `logs/screen-{base,head}.txt` read 549 → 559 declarations, 320 → 321 pairs, and 105,754 → 105,830 characters, as the auditor says.
- **CfgRecord call sites:** I counted them myself. `copyTM_run_ofCfg` appears at 1779 and 3474, `compareTM_run_ofCfg` at 4804 (plus a prose mention at 4551), `decrementTM_run_succ_ofCfg` at 2923 and `incrementTM_run_succ_ofCfg` at 2924. This matches the auditor's count.
- **Worktrees:** `review/mig11a-gate/wt-pr` (`1358ff73`) and `wt-tip` (`f139d21a`), both detached and clean after testing.

## Minor 1: `counterRowContract`'s docstring (ACCEPT, minor)

**True.** At `Build/Contract/Counter.lean:43–49` the docstring calls `fix` "the width-preserving
word map" and says the endpoint is "the word's interval holding `v`". The formal statement says
something narrower:
- neither the parameters nor `hrun` require `v.length = w.length`;
- the endpoint (`post`, lines 79–84) writes `FinTM.bufferTape v (q - pos)` on the
  `|w|`-cell interval `[pos, pos + |w|)` and leaves every other cell unchanged.

The auditor's counterexample checks out clause by clause: `fix [] = some [true]`,
`fix (_ :: _) = none`, and a two-step stationary machine satisfy `hrun` with `|v| = 1 ≠ 0 = |w|`.
If `|v| > |w|`, the interval holds a prefix of `v`. If `|v| < |w|`, the excess cells become blank.

**Severity: minor is right.** The formal endpoint is exact and both instances are correct, so only
the prose overstates. That is a documentation defect, not a misleading statement.

**Fix: docstring only. Do not add a width hypothesis.** Adding one would:
- change the definition's signature;
- restrict a generic constructor whose contract is already exact without it;
- buy nothing for the instances.

Replacement text, the whole docstring paragraph at lines 43–49:

```lean
/-- **The contract of a successful counter row** (MIG-11a, user 2026-10-16): one constructor for
the increment and the decrement. Given a machine `M` over `FlagPhase`, its tape `i`, the word map
`fix` it computes and the bit `lead`-cells it carries through, and the row's framed theorem
`hrun`, this is the contract indexed by pairs `(w, v)` with `fix w = some v` and `w` delimited at
the head `pos` of tape `i`: time `2 · |takeWhile lead w| + 2`; endpoint at `done true`, with each
cell `q` of the word's interval `[pos, pos + |w|)` holding `bufferTape v (q - pos)` and every
other cell unchanged; exits both verdicts; the head of tape `i` within
`[pos - 1, pos + |takeWhile lead w|]` and every other head fixed. No width condition on `fix` is
assumed: the interval holds exactly `v` when `|v| = |w|`, as for both instances (`incFixed` and
`decFixed` keep the width).
```

The proof-sketch paragraph that follows is unchanged.

**The instances need no change.** `incrementTM_contract` and `decrementTM_contract` say the
interval holds `v`. That is true, because `incFixed` and `decFixed` keep the width.

**Are the width facts published?**
- **`decFixed`: yes, in effect.** The public `counter_dec_spec` (`Build/CounterLoop.lean:443`)
  says, in its `some v` branch, `v.length = w.length`. It is usable after rewriting with
  `decFixed w = some v`, a `match` on a constructor, exactly as StepClock's private
  `sc_dec_success_width` (StepClock.lean:293) does.
  - It is not named after the definition, so check 8 still lists `decFixed` as uncovered in
    `CounterLoop` (pre-existing).
- **`incFixed`: no.** The only width lemma is the private `rt_incFixed_length`
  (`Build/RecordTable.lean:2265`).
  - The public `incFixed_replicate_true_append` and `incFixed_eq_none_iff_replicate`
    (`Build/Convention.lean`) give width only after a list decomposition.
- **Neither gap affects this gate.** The contracts are exact without width, and MIG-12's
  arithmetic transport already takes `hlen : v.length = w.length` as its own hypothesis
  (CfgRecord.lean:2877), from `binDigits`' width.
- **Follow-up, not required here:** publish `incFixed_length : incFixed w = some v → v.length = w.length`
  beside `incFixed` (Convention) and `decFixed_length` beside `decFixed` (CounterLoop, from
  `counter_dec_spec`).
  - Doing so clears check 8's `decFixed` entry.
  - The two privates `rt_incFixed_length` and `sc_dec_success_width` would then become copies
    of public lemmas, so they should cite the new ones. That is a natural MIG-12 cleanup.
  - I have not patched this, because it lies outside #117's files.

**Tested** (`repair-docstring.patch`, SHA-256 `c6f1c51eaa298759b19a7ba474a825a9544cf3fe332eb782cd538828ed447842`, against `1358ff73`):

| Check | Result |
|---|---|
| `git apply` | clean |
| Elaboration of `Contract/Counter` against `oleans-lm11a` | repaired: exit 0, 0 errors, 0 warnings; original: the same (`out/Counter-{repaired,orig}.out`) |
| Freeze (`privstmt`) | `STATEMENT CHANGED: []`; the only change is `counterRowContract`'s docstring |
| Lint | 0 FAIL, 69 WARN over 79 files, unchanged; `Contract/Counter` is now 134 lines (3 public), with no WARN |
| Added lines | at most 100 characters |

No copy-text screen is needed, since the change is comments only and the screen strips them.
The worktree is reset.

## Minor 2: the lint attestation (ACCEPT, minor)

**True.** `logs/lint-head.txt` reports `Contract/Counter.lean 122 lines; 2 public`, which is
before `counterRowContract` was factored out. The final file has 131 lines and 3 public. The log
also predates #116's merge: it shows `Finite.lean`'s `Computes`, `ComputesFunInTime`,
`ComputesFunInTimeVia`, the Zone/ZoneTape check-8 lists, and `wordPatch` and `serializeK` as
uncovered. All of these are covered at the head. Its total, 72 WARN, is therefore a pre-#116
count.

**Severity: minor is right.** This is a records defect.

**The corrected attestation**, re-run with the head's `scripts/campaign_style_lint.py` over
`TCSlib/Complexity/TuringMachine` (`review/mig11a-gate/lint-head-1358ff73.txt`):
- At `1358ff73`: **0 FAIL, 69 WARN over 79 files.**
- Against the tip `f139d21a` (0 FAIL, 69 WARN over 78 files) the WARN set is identical. Only
  Catalog's line count in its existing size WARN changes (13117 → 13224), plus the INFO lines of
  the four touched files.
- `Contract/Counter.lean`: 131 lines, 3 public / 0 private, no WARN.
- **Check 8 lists none of the new definitions** (`compareStop`, `copyTM_contract`,
  `compareTM_contract`, `counterRowContract`, `incrementTM_contract`, `decrementTM_contract`).

To record it, add `lint-head-1358ff73.txt` as a new log and keep the stale `lint-head.txt` as is.
In the resolutions, note that the original was run before the factoring and before #116 merged,
and quote the corrected line. With the docstring patch applied, the result is the same:
0 FAIL, 69 WARN over 79 files.

## Can the gate close?

**Yes.** There are 0 blockers and 0 majors. The two minors are a docstring correction (patch
ready) and a record correction (log ready); neither changes a statement. The four row contracts
and their field equations stand as audited, and the replay covers the head's Lean.
