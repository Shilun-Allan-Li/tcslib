# Gate 135 · owner readers for the Ladner fills (PR #302)

**Not yet clear to merge** · PR #302 is a draft. Seyoon dispatches and merges.
The Lean commit is `50bb801a28ffd86ce7b47c91d47c257ab024fade`, against campaign Lean
`b313afe522991f2114390952f26ffe7de825bace` (the campaign after #301). This is the first audit.

## Scope and ruling

The Codex Ladner route draft (`campaign/items/ladner/fill-routes-request/delivery/`) needs owner
readers R1–R6 before any fill. Seyoon approved them on 2026-11-14 (`campaign/backlog.md`, P3.4),
to be landed by the maintainer as one gated PR:

| Reader | Home | Statement |
| --- | --- | --- |
| R1 `Complexity.polyTimeComputable_iff` | ClassNP/PolyTime | `PolyTimeComputable f ↔ ∃ M C c, M.ComputesFunInTime f (fun n => C * (n + 1) ^ c)` |
| R2 `Complexity.polyTimeReducible_iff` | ClassNP/Reductions | `PolyTimeReducible L L' ↔ ∃ f, PolyTimeComputable f ∧ ∀ x, x ∈ L ↔ f x ∈ L'` |
| R3 `Complexity.NPHard_iff` | ClassNP/Reductions | `NPHard L ↔ ∀ L', L' ∈ NP → PolyTimeReducible L' L` |
| R4 `Complexity.NPComplete_iff` | ClassNP/Reductions | `NPComplete L ↔ L ∈ NP ∧ NPHard L` |
| R5 `Turing.FinTM.decidesInTime_iff` | ClassP/DTIME | `M.DecidesInTime L T ↔ M.ComputesFunInTime (fun x => [indicator L x]) T` |
| R6 `Turing.MultiTapeTM.indicator_of_mem`, `indicator_of_not_mem` | TuringMachine/Deterministic | `x ∈ L → indicator L x = true`; `x ∉ L → indicator L x = false` |

`patch/campaign-to-head.patch` in the carrier is the whole change (4 files, 39 added lines),
including a bullet in Deterministic's list of local modifications for R6.

## Brief for the auditor

1. Check each reader states its definition (or the branch of it) exactly, sits beside it, is not
   `@[simp]`, and is proved from its own file: R1–R4 by `Iff.rfl`, R5 by the published
   `Turing.FinTM.computesFunInTime_iff`, R6 by the `if` of `indicator`.
2. Check the whole-proof seals (`seals/` in the carrier): all 7 bodies pass with every other-file
   definition they reach irreducible, and the 34 paired controls each close natively and fail
   sealed.
3. `SOURCE.json` lists `PolyTimeReducible` among the changed declarations: the inventory splits
   the file at declarations, and R2 sits between the definition and its `≤ₚ` notation line, which
   the splitter then attributes to R2. Check that the definition and the notation line are
   byte-identical.
4. Check the copy screen on the four files: BASE and HEAD both `declarations screened: 47; copy
   pairs: 5; reproduced text: 342 chars`, no changed pair.
5. Check the replay and the absence of name clashes: `Turing.FinNDTM.decidesInTime_iff`
   (ClassNP/NTIME) is a different declaration in another namespace.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the 403-module downstream closure on the
  campaign snapshot after #301 (876 objects; prospective tree
  `f386bf8042badf2199606e47db1b859d0a9485ad`). 403 passed, 0 failed; the 65 admissions are
  inherited from the campaign.
- Metadata: all 7 readers use standard axioms only. Lint: no new style finding; the campaign
  check-8 rows only shrink.
- `evidence/DATA-CARRIER.json` and its recovery map hold 1,304 logical files: replay receipts and
  logs, seal and control sources and logs, metadata, QA, both screens with the population and
  scorer, the campaign versions of the owners, the patch, and the drivers.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate135-ladner-readers-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
