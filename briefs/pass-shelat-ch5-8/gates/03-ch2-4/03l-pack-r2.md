# Gate 03l ([PS10] ch. 2–4, the `Randomized/Build/` machine layer, and the clean-module host), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e28773ef3bda6f7b4b112ec1657427bfef01e374` (the branch after #201 and #203 merged; its Lean files are #203's head `f29be161`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 1 major (#1, the empty axiom attestation), 3 minors and 210 notes**; the review kept the severities and added six missed items (M1, unledgered duplication, would have been a major) (`gate03l-findings.md`, in the bundle,
  verbatim).
- **The repair:** major 1 by evidence (`evidence-repairs/03l/axioms.log`); everything else in gate 03 clean-up part 1, #203 (DL-16: the clean-module host harvested from `ClassNP/SAT.lean`'s private layer into public `Turing.ModuleHost`, registry row H14, consumed by `SAT.lean` and `IterateFindHost.lean`; DL-18: `UnaryMul` uses `PairSplit`'s parser; DL-19: `BlockLoop` renamed `BlockMapLoop`; minors 2–4), per ruling R-03l-1 (B). The full delta is `evidence-r2/03l/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03l-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03l-review.md` (in the bundle).
- **The deliverable:** **`gate03l-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03l-r1.md` (the
   findings, grouped as the review grouped them, and the review's missed items `M1`, …) say
   whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR (clean-up part 2,
     after #195), and the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03l/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement, rename and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.
3. **It gates the host's contract** (registry row H14, `machine-library-design.md` §14: "contract
   gated at gate 03l's delta round"). Restate `Clean`, `host_call` and `host_clean` in your own
   words; say whether the contract is generic in what its two consumers vary (the modules, the
   control states and their table, the return map, the start state), whether its time and
   no-anchor-visit clauses are what a third consumer would need, and whether `SAT.lean`'s
   instantiation (section B of the diff) preserves SAT's public statements.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** The host declarations moved to `Turing.ModuleHost` and were generalized (`Clean`, `clean_install`, `clean_emit`, `HostState` → `State`, `hostEntry` → `entry`, `host_call`, `guard_add`, `host_clean`; `host_call` and `host_clean` now exclude every control state, not only the anchor); `IterateFind.hostRet`'s type and `IterateFind.hostTM` (now an abbreviation) follow; `StateLoop.BlockLoop` → `StateLoop.BlockMapLoop` (17 declarations, statements kept); `BlockMapLoop.blk` is private. The old → new list is `evidence-repairs/03l-cleanup1/statements.md` (in the bundle). No statement of `exists_pairSplitTM`, `exists_unaryMulTM`, `IterateFind.polyTimeComputable_find` or `SAT.lean`'s public theorems changes.
- **New public declarations:**
- **the host** `Turing.ModuleHost` (new file): `Clean`, `clean_iff`, `State`, `state_eq`, `entry`,
  `entry_eq`, `hostTM` (with `simps k tm_q₀`), `hostTM_step_inl`, `clean_install`, `clean_emit`,
  `host_call`, `host_clean`, `guard_add`, `first_halt`, `live_prefix`, `request_budget`;
- `IterateFindHost.lean`: `hostCtrl`, `hostCtrl_eq`, `hostRet_zero` … `hostRet_four`, `hostTM_eq`,
  `copyTM_k`;
- the parser `Turing.PairParse` (`PairSplit.lean`): `cfg` (with `simps`), `cfg_inputSymbol`,
  `cfg_workTapeSymbols`, `cfg_congr`, `apply_cfg_stay`, `apply_cfg_advance`, `parse_first`,
  `parse_block`, `rewind_run`;
- the reading lemmas: `IterateFind.step_eq`; `StateLoop.gstep_eq`, `gstepBound_eval`,
  `IterLoop.{start,step,acc,out}_eq`, `EmitLoop.{start,step,out}_eq`;
  `MajLoop.{start,step,acc,out}_eq`, `XorLoop.{start,step,acc,out,rounds}_eq`,
  `EqLoop.{step,out,flag}_eq`, `BlockMapLoop.{start,step,acc,out,rounds}_eq`.

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03l-findings.md`, `review/gate03l-review.md`, `resolutions-03l-r1.md`, `evidence-r2/03l/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Complexity/Randomized/Build/{IterateFind, IterateFindHost, PairSplit, StateLoop, StringLoops, UnaryMul}.lean`, `TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean` (new) |
| Context | `03l-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows), `machine-library-design.md` §14 (row H14), `evidence-repairs/03l-cleanup1/statements.md` and `seal.log` |
| Out of scope | tactic proofs; clean-up part 2 (after #195) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/l2/` in the bundle)

### Attestation results at `e28773ef3bda6f7b4b112ec1657427bfef01e374` (evidence under `evidence/l2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 27 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   17 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 139 prints of every public theorem and lemma in this pack's files:
   139 use only the standard axioms, and 0 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 7 files.

The replay is the 416-module replay at `af91d53a`, overlaid by the re-check at #201's head
(`evidence-repairs/03ac/replay.log`) and by #203's builds and re-check
(`evidence-repairs/03l-cleanup1/`); each line of `replay.log` is the newest check of its module,
and the Lean files at the pin equal #203's head. The rule-10 seal of #203 (8 consumer files, with controls) and lint with check 8/8b are in `evidence-repairs/03l-cleanup1/` (in the bundle).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row (or row group): `<row>: fixed / recorded / scheduled / not resolved —
<reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.
