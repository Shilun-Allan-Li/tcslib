# External audit pack, round 2 — `NP` is closed under polynomial-time preimages (PR #177, an API gate)

**Round 1** (`pack.md`, at `ce00b6d3`; findings `findings.md`): **PASS, 0 blockers, 0 majors,
2 minors, 10 notes**, on the theorem `mem_NP_of_polyTimeReducible` in `ClassNP/Reductions`. The
resolutions are `resolutions.md`.

**Why a round 2.** The merge condition then failed. #175 merged first, so #177 took a merged-tree
replay (`replay-lnpc2`, `Reductions`' downstream, 127 modules). `ClassNP/TMSAT` failed at line 1089
(unsolved goals) and 32 modules behind it could not load its olean
(`evidence/round1-fix/merged-tree/replay-lnpc2-failed.log`; `TMSAT` is the only module that failed
on its own). The cause: `Reductions`' new import of `PClosure` brought `Mathlib.Tactic.Linarith`
(through `TuringMachine/CounterProgRun`) into every module downstream of `Reductions`. Linarith's
closure activates Mathlib's `@[simp] Nat.cast_min`, which rewrote the goal's `↑(min a b)` in
`tmsat_take_computes` while the hypothesis `hw` passed to the same unrestricted `simp` kept it
(`merged-tree/TMSAT-under-lnpc2.out`). This is the trap gate 82 recorded for #171.

**The user's rulings (2026-11-04):** the theorem moves to `ClassNP/PClosure`, beside
`preimage_mem_P`, so that no other module's environment changes; and `TMSAT`'s step is made robust
in this PR. `PClosure` does not import `Reductions` (where `≤ₚ` is defined), so the theorem is
stated in `PClosure`'s own form, for preimages: `preimage_mem_NP`.

**The PR now:** #177 on `lean/np-closure`, head `a0d511ec61b2e40b2216e44c07278531fc33a2e6`: the fix
commit `02aedc76` (`evidence/round1-fix/round1-fix.patch`) and the campaign merged in (#175 among
it; no other Lean change). Against the campaign, #177 changes `ClassNP/PClosure` (blob `7acc5fab`)
and `ClassNP/TMSAT` (blob `d5f4e37f`); **`ClassNP/Reductions` is the campaign's** (round 1's
theorem, import and `prefixTM_copy` sketch are gone from it).

## What changed since round 1 (verify)

| Class | Change |
|---|---|
| **New public** (`PClosure`) | `Complexity.preimage_mem_NP {L' : Language Bool} {f : List Bool → List Bool} (hf : PolyTimeComputable f) (h' : L' ∈ NP) : f ⁻¹' L' ∈ NP` (16 → 17 public; `evidence/round1-fix/freeze-PClosure.txt`) |
| **Removed** (from round 1) | `Complexity.mem_NP_of_polyTimeReducible` and `Reductions`' import of `PClosure` |
| **`TMSAT`** | `tmsat_take_computes`' last step: in each case of `a.length ≤ b.length`, `simp only [hm]` first replaces `min a.length b.length` by its value, then the step's `simp` runs (case 1 unfolding the file's own `polyTape`; case 2 with `List.take_of_length_le`); the intermediate disjunction `hend` is gone. Its docstring gains a `**Proof sketch.**`. No statement changes (`freeze-TMSAT.txt`: one private body) |

## Brief for the auditor

1. **The statement and the proof.** `preimage_mem_NP` is round 1's theorem for the preimage form:
   with `L ≤ₚ L'` by `f`, `L = f ⁻¹' L'`. Is the form right for `PClosure` (it mirrors
   `preimage_mem_P`), and is the proof (round 1's, its last step now `Set.mem_preimage`) correct?
   Does a consumer holding `L ≤ₚ L'` get `L ∈ NP` from it with no missing step?
2. **The home.** `PClosure` gains no import; nothing else's environment changes. Is that right?
3. **`TMSAT`'s hardened step.** Is the new step correct, and does it no longer depend on the simp
   set? The module elaborates with 0 diagnostics as it is (`TMSAT.out`) and with
   `import Mathlib.Tactic.Linarith` added (`TMSATLinarith.*`); the old step with that import fails at
   its `simp` (`TMSATOldLinarith.*`, line 1090 after the added line), which shows the test
   discriminates. Is the step's remaining reliance on unfolding `Cfg.workTapeSymbols` and
   `Action.apply` (other files' definitions, unchanged from the base; the file predates rule 10)
   acceptably disclosed as inherited?
4. **Rule 10** for the new theorem: sealed over the same six definitions as round 1 with the three
   `@[simp]` TCSlib definitions of `PClosure`'s closure erased, 0 diagnostics
   (`PClosureSealed.*`; `scripts-note.txt`); the six controls close unsealed and fail sealed
   (`PClosureSealControl.*`).
5. **Duplication.** The screen (10 files: round 1's nine and `TMSAT`): ⟨summary⟩. Round 1's
   idiom pair with `polyTimeComputable_pairSwap` moves with the proof.
6. **Lint.** `TMSAT` keeps 9 policy-linter findings, all present at the base (10 there; the
   touched lemma's sketch is added): is leaving them for the deferred cleanup acceptable in a PR
   that touches the file?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lscp3` (the snapshot of the campaign after #175): `PClosure` with
  an axiom print, 0 diagnostics, `preimage_mem_NP` on `[propext, Classical.choice, Quot.sound]`
  (`PClosureAx.*`); `TMSAT`, 0 diagnostics.
- **API copies** (`api-copy-search.txt`, with each ref's name and object id, per round 1's note 11):
  of 117 origin refs, only `lean/np-closure` declares `preimage_mem_NP`,
  `mem_NP_of_polyTimeReducible`, `mem_NP_of_reduc*` or `NP_closed_under*`.
- **Lint** (`lint-head-ClassNP.txt`, `style-lint-*.txt`): `ClassNP` 0 FAIL, 17 WARN over 21 files
  (the campaign's after `main`'s merge-in); the policy linter 0 findings on `PClosure`, 9 inherited
  on `TMSAT`. `TMSAT`'s one line over 100 characters (1044) is the base's.
- **Replay:** `replay-lnpc3.sh` (`merged-tree/`), the two files' downstream closure, 66 modules,
  from `oleans-lscp3`, pinning both blobs; precheck passed. **Pending.**

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/88-np-closure-api/findings-r2.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `np-closure-api-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
