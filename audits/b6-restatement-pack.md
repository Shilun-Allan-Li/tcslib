# External audit pack — RD-3: `space_universal` restated forward-only; `space_hierarchy` re-routed (statement gate)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e, cluster B6). On
2026-10-12 the user decided (design `machine-library-design.md` §16b item 3, backlog RD-3) that
B6 takes the **window route** and that `space_universal` keeps only its **forward clause**, as
[AB09, Exercise 4.1] states it. `SpaceComplexity/Hierarchy.lean` was gated at **P4.3** (closed
at round 3: `audits/ch4-p43-findings.md`, `-r2-`, `-r3-`; resolutions `audits/ch4-p43-resolutions.md`).
P4.3's findings 4 and 5 shaped the two-clause statement and its sketch that this change replaces.
All four theorems of the file stay sorried. **This gate audits one statement change and two
rewritten sketches.**

| Declaration | Change |
|---|---|
| `Complexity.space_universal` | **statement restated**: the forward clause only; the simulated output untagged |
| `Complexity.space_hierarchy` | docstring only: the proof sketch moves to the window route; the statement is byte-identical |
| `Complexity.LOGSPACE_ssubset_PSPACE`, `Complexity.SPACE_linear_ne_NP` | unchanged, docstrings included |
| module header | updated to describe the new route |

**Bundle:** `audits/b6-restatement-bundle.md`. It holds this pack, the standards, the P4.3 records,
the file before and after with the patch, the logs, the design document, the backlog, and
every library file the new sketches cite, so that each citation can be checked.

## The change (verify)

**Before** (P4.3): for every code `α` there is `C > 0` such that, for every `s` and `x`, (i) if the
coded machine computes some output within `s` visited work cells, then `SU` on
`⟨bits s, ⟨α, x⟩⟩` outputs `true :: output` within `C·(s + logSpace |x| + 1)` cells; and (ii)
otherwise `SU` outputs `[false]` within the same space.

**After:** for every code `α` there is `C > 0` such that, for every `s`, `x`, `output` and `t`, if
the coded machine computes `output` on `x` in time `t` having visited at most `s` cells, then
`SU` on `⟨bits s, ⟨α, x⟩⟩` computes the same `output`, untagged, having visited at most
`C·(s + logSpace |x| + 1)` cells. Nothing is claimed when the coded machine overruns `s` or does
not halt.

[AB09, Exercise 4.1, p. 93] asks for a TM `SU` such that if `M_α` halts on `x` before using `t`
work cells, then `SU(α, t, x) = M_α(x)` and `SU` uses at most `C·t` cells, with `C` depending
only on `M_α`. The docstring lists the deviations:
- `C` depends on the code `α`, as for `Turing.universal`;
- the `+ logSpace |x| + 1` addend pays for reading the simulated input, which is a suffix of
  `SU`'s input, through a binary position;
- "before using `t` cells" is read as "at most `s` visited cells".

**Why the route changed** (Finding B, design §16b item 3). The chapter-1 interpreter tracks the
input head in unary on its fourth tape. `Turing.universalInterpreter` writes a `true` marker on
tape 3 at `.start`, and `applyRecord` moves that head with the input head, so its space is
`Θ(input travel)`. The present sketch's premise, constant-factor space, therefore fails for
`S = o(n)`.

**The window route.** The diagonalizer runs one fixed self-application universal machine `U₀`
inside a window of radius `a·g(n)` on the configuration-record rows (`Build/CfgRecord.lean`,
`Build/RecordTable.lean`), stopped by a configuration-count clock, and flips its verdict. It
needs only `U₀`'s forward direction with a space ledger. The old budget loop, head caps,
interval counters, core clock and probe/replay go.

## Brief for the auditor

1. **Fidelity.** Is the restated `space_universal` a faithful formalization of [AB09, Exercise
   4.1], with every deviation necessary and declared? Rule on the `+ logSpace` addend: the
   drafting review thought an addend-free statement might be reachable with an `O(1)`-cell
   boundary test that re-scans the header. Should the statement be stronger?
2. **Strength.** The new statement is weaker than the old: the failure clause is dropped.
   Confirm that nothing needs that clause: no Lean declaration consumes `space_universal` (the
   attached greps), and the re-routed hierarchy uses its sibling `U₀` instead. Is the untagged
   output right?
3. **The window-route sketch of `space_hierarchy`.** Check it as a proof plan:
   - the inclusion step;
   - `U₀`'s forward ledger `C_α·(s + 1)`, with the native input device;
   - the diagonalizer: input validation, the radius `r = a·g(n)`, the initial record, and the
     windowed runner's exits (halt, window exit, clock);
   - the clock width `|Q₀| + posWidth n + 3·k₀·(2r + 1) + 1` against
     `Turing.FinTM.configBound U₀ n r`;
   - the output-summary tag, and the space count `O(g n)` uniform in the code part of the input;
   - the contradiction: padding the payload after a fixed code, `hfg` used once at the fixed `A`,
     window containment from `abs_pos_lt_card_visited` and `mem_visited_of_ne_none`, halting
     within `configBound`, and the flip;
   - the alphabet reduction.

   Report any step that does not hold as written.
4. **Finding B.** Verify it from `UniversalInterpreter.lean`.
5. **Fill obligations.** Are they complete and correctly named in the host vocabulary of design
   §14? The maintainer records three open points:
   - `U₀` has no public statement yet; it is to be a public row built from H2 and H5;
   - the windowed runner needs three exits, while `counterLoopTMVia` has one;
   - the space-preserving normal form (`one_work_tape_binary_spaceUsed`) is proved, but two small
     steps around it are not: the space clause of `exists_codeTM`, which is time-only, and a
     decider's space bound at every time, since `DecidesInSpace` bounds it at the halt.

   Is anything else missing?
6. **Freeze.** Only `space_universal`'s statement changed (`audits/logs/b6-restatement-freeze.log`;
   patch `audits/evidence/b6-restatement/hierarchy.patch`).
7. **Documentation and policy** (`policy.md`): the status labels, attribution, the literal
   proof sketches, and the 100-column limit.
8. **Records.** Check design §16b item 3, the three superseded design rows, and backlog RD-3
   against the file.
9. Report anything else the change or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Elaboration** (`audits/logs/b6-restatement-elaboration.log`): read-only against the
  fills-6/CH34-D4 snapshot, 0 errors and exactly the four sorry warnings.
* **Names.** Every library name the new docstrings cite exists as a public declaration; the
  maintainer checked each one by grep. The file is in the bundle.
* **No consumer.** `space_universal` is not used by any Lean declaration. It is named in
  planning documents, briefs' sorry inventories and audit probes; the probes' `#print axioms`
  lines stay valid because the name is unchanged.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/b6-restatement-findings.md`. The gate closes when it has zero blockers and zero majors.
