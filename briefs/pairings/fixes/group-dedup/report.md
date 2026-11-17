# DW-11 follow-up · `Pairing/Group.lean`: one generic prime-order bijectivity lemma; reuse Mathlib

Filed by the maintainer from the job's returned report (the harness refuses report-file writes by sub-jobs). The full
logs, tools and diffs are in `group-dedup-evidence.zip` (`48d787d4dd9943be620620f1924c755e31162dcc05c5684a579a479502b88f9c`,
308 files with inner SHA256SUMS; `README.txt` maps the folders).

**Verdict: PASS, pushed, draft PR #365** (`fix/pairing-group-dedup` → `cryptography/pass-shelat-ch2-4`), two signed
commits on records tip `5aed99076d2bd4e5d6f831aed88739fc3ce475b6` (Lean = TS2 `13fc8060`).

| Commit | Hash | Tree | Diff | Content |
|---|---|---|---|---|
| 1 | `6fc5f49456507dab5901045356ea40acf42bdd67` | `ba10f0a2…` | +25/−17 | new generic lemma; the two bijections re-proved from it; `pow_mod_card` in `pow_val_add`, `pow_val_mul` |
| 2 (head) | `5eaddd171bceccee917929e7f319ff9202994c59` | `9710ac7d…` | +3/−2 | `pow_mod_card … B.card_GT` in `pow_val_mul_GT`; one `## Main results` line |

**Lemma** (public, `TCSlib.Cryptography.Pairing`, before `namespace BilinearGroup`; Mathlib has no exact statement —
nearest `IsCyclic.unique_zpow_zmod`, `zmodCyclicMulEquiv`, `finEquivPowers`/`finEquivZPowers`, different shapes):

```lean
theorem pow_val_bijective_of_prime_card {M : Type*} [Group M] [Fintype M] {p : ℕ}
    [Fact p.Prime] (hM : Fintype.card M = p) {g : M} (hg : g ≠ 1) :
    Function.Bijective fun a : ZMod p => g ^ a.val
```
proved from `orderOf_eq_prime`, `pow_card_eq_one`, `pow_injOn_Iio_orderOf` and `Fintype.bijective_iff_injective_and_card`.

**Checks at the head:** decls2 1 ADDED / 0 / 0 (against `5aed9907` and `bfa1f5a4`); `touched.py` 1 ADDED + 5 CHANGED
(proof bodies only; all headers, statements and docstrings byte-identical apart from the new lemma and the one added
module-docstring line); no `Nat.mod_add_div` left. Replay on `$SP/olean-replay-grpfix` (`cp -al` of `olean-replay-cs1-s6`):
22/22 rc 0, 0 errors/sorry/warnings, state 1434/1434 OK, link count 1, parent and snapshot #6 rehash 0/0/0, output map
`286777672d4e61f1be0ba98fca72b01d8cd9aa281eb811d100d7fe499679c49c` (only `Pairing/Group.olean` differs from the parent).
Admissions 192 = 192 per module (census derived with `censusderive.py`; older record sets had been removed in a disk
clean-up). Axioms: 8 constants standard (new lemma, the 5 touched, `bb1_sidSecure`, `jouxKeyIndist_of_dbdhAssumption`);
no `sorryAx` user in any trace; Joux's closure shrinks 10,316 → 8,589. coe-A on `Group.lean`: 567 requests at base and
head, 0 errors, identical rows, byte-identical seal logs. Lint 92 FAIL / 103 WARN, nothing new; `style_lint` 0.

**Deviations:** one trial compile and one standalone probe before commit 1 (single processes, slot-gated); a failed base
axioms attempt with no toolchain file (no Lean ran; rerun passed); commit 2 at the maintainer's request.

**Adoption:** if #365 merges onto a tip whose Lean is still TS2's, `olean-replay-grpfix` is the replay at the merge tree
(step-3 diff against `5eaddd17` must be empty); otherwise re-replay (22 modules, ~100 s).
