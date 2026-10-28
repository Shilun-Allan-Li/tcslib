# External audit pack — the polynomial bounds' constructibility moves to `Constructible` (PR #175, an API gate)

**Why this PR.** The space hierarchy's fill (B6's H, `SpaceComplexity/Hierarchy.lean`) proves the
corollary `SPACE_linear_ne_NP`, which needs `Complexity.spaceConstructible_poly` at degree two. The
lemma was in `SpaceComplexity/Savitch.lean`, outside `Hierarchy`'s import closure. **The user ruled
(2026-10-27): move it to `Constructible.lean`, beside the logarithmic and linear rows, with its
statement unchanged, by an API PR with its gate and a replay of the downstream closure.**

**The PR:** #175 on `lean/scp-constructible`, head `6ae641a27333a177203b0b276afe392366dbf967`: the
move commit `550024b4` (`evidence/patches/`) on the campaign tip after #172, and the campaign merged
in by `6ae641a2` (its one Lean change is #174's `NDHost`, outside both files' closures). The two
files' blobs: `Constructible` `791f3a48`, `Savitch` `6ea81136`.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Moved** (`Savitch` → `Constructible`, statements unchanged) | the public `Complexity.spaceConstructible_poly`; the eight privates `scp_tailδ`, `scp_tailO`, `scp_transduce_copy`, `scp_transduce_tail`, `scp_tail_pow_le`, `scp_value`, `scp_time_arith`, `scp_space_arith` |
| **Changed text in the moved block** (`evidence/moved-block.diff`, three hunks) | the theorem's docstring gains the tag `[AB09, p. 79]`; the dominance step `logSpace n ≤ n + 1` is proved through `logSpace_eq` and `Nat.log_le_self` instead of citing `Machines/ARMWidth`'s `logSpace_le_succ`, which is outside `Constructible`'s closure; the proof sketch cites the new step |
| **Imports** | `Constructible` imports `ClassNP/Transducer` (its closure gains `ClassNP/Transducer`, `ClassNP/PolyTimePairing`, `ClassNP/PolyTime`, `TuringMachine/Build/Primitives`; no cycle). `Savitch` drops that import, which only the block used; it imports `Constructible`, so its closure is unchanged |
| **Docstrings** | `Savitch`'s module docstring (status, main results) says where the lemma is; `Constructible`'s lists it among its main results |
| **Unchanged** | every other declaration of both files |

## Brief for the auditor

1. **The move.** Is the statement of `spaceConstructible_poly` unchanged, and is the block's text
   unchanged except for the three hunks of `evidence/moved-block.diff`? Is the freeze a pure move
   (`evidence/freeze-Savitch.txt`, `freeze-Constructible.txt`: one public and eight privates leave
   `Savitch` and arrive in `Constructible`; nothing else added, removed or changed)?
2. **The home.** Is `Constructible` the right home (beside `spaceConstructible_logSpace` and
   `_linear`, in a file `Hierarchy` already imports)? The cost is four
   modules added to `Constructible`'s closure and a replay of its downstream closure, 53 modules
   (`evidence/merged-tree/down-lscp.txt`).
3. **The one proof change.** The dominance step `logSpace n ≤ n + 1` was
   `logSpace_le_succ n` (`Machines/ARMWidth`, public). It is now
   `by rw [logSpace_eq]; have := Nat.log_le_self 2 n; omega`, through `Basic`'s published equation
   of `logSpace`. Is that sound and within rule 10? The restatement of a one-line fact is disclosed
   as a dedup-window item (moving `logSpace_le_succ` into `Basic`, where `logSpace` is defined;
   `ARMWidth` is a colleague's file).
4. **Rule 10** (with the scope of 2026-10-23). The block landed sealed (PR #166, gate 77, PASS,
   `campaign/gates/77-scp-landing/`); the seal is re-taken here at its new home, over the new
   step.
   - It is sealed over the 12 other-file definitions it reaches (`transduce`, `transducerTM`,
     `FinTM.polyUnaryTM`, `FinTM.prependTM`, `FinTM.bufferedCompTM`, `FinTM.ComputesFunInTime`,
     `FinTM.ComputesInTime`, `FinTM.ComputesInSpace`, `MultiTapeTM.spaceUsed`,
     `MultiTapeTM.initCfg`, `Cfg.init`, `logSpace`), with the three `@[simp]` TCSlib definitions of
     the environment erased (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`); the sealed copy
     elaborates with 0 diagnostics (`evidence/ConstructibleSealed.*`, generator
     `evidence/scripts/mkseal_scp.py`).
   - Its 15 controls (12 `rfl`, two of them usage forms; 3 `simp` controls of the erasure) close
     unsealed and fail sealed, each at its own goal (`evidence/ConstructibleSealControl.*`).
   - Every `rw`/`simp` argument is classified in `evidence/inspection.txt`: own-file names, two
     other-file theorems (`transduce_cons`, `logSpace_eq`), Core and Mathlib theorems, locals. Is any
     other-file definition passed to `simp` or `rw`, or closed by reduction?
5. **Duplication.** The screen (`evidence/screen/`, 12 files: the two changed files and every file
   whose rows the block cites) at the move commit `550024b4` against the same population at the
   base: 844 declarations and 1,146 pairs at both, none new and none gone (`pairdiff.txt`); no pair
   involves the moved block. Two known items stay for the dedup window: the inline `hD'` (the conversion
   `computesFunInTime_ifEq [] [true] [false]` → `[decide (x = [])]`, which is #171's
   `Turing.FinTM.computesFunInTime_decideEq []`; already in the duplication ledger,
   `evidence/ledger-excerpt.txt`), and the
   restatement of item 3. Is that adequate? Does anything else in the block re-derive a published
   lemma?
6. **Records.** Are both module docstrings accurate and public-facing?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lhh` (the snapshot of the tree after #172; both files' closures
  are the same at the tip, whose only further Lean change is `NDHost`):
  - `Constructible` with four axiom prints (`evidence/ConstructibleAx.*`): 0 diagnostics;
    `spaceConstructible_poly`, `spaceConstructible_iff`, `_logSpace` and `_linear` on
    `[propext, Classical.choice, Quot.sound]`;
  - `Savitch` (`evidence/Savitch.out`): the one expected sorry warning (`savitch`), nothing else.
- **API copies:** every origin branch (111 refs) has `spaceConstructible_poly` in exactly one file:
  `Savitch` on 107, `Constructible` on this PR's branch (`evidence/api-copy-search.txt`).
- **Lint:** `SpaceComplexity` 0 FAIL, 82 WARN over 107 files at both base and head; the only
  differing lines are the two files' size and count INFO lines (`evidence/lint-*.txt`). The policy
  linter: `Savitch`'s one finding (no `## Main definitions` heading) is the base's
  (`evidence/style-lint-*.txt`). No line over 100 characters.
- **Replay:** `replay-lscp.sh` (`evidence/merged-tree/`), the downstream closure of both files, 53
  modules (`down-lscp.txt`; `Savitch`'s is inside `Constructible`'s), chained from `oleans-lnfapi4`
  (#174's snapshot, the tip's Lean), pinning both blobs. Its precheck passed. **Pending** (a merge
  condition of its own).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/86-scp-constructible-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `scp-constructible-api-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
