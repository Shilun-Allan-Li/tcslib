# Chapter-6 circuit surface — audit loop resolutions (OPEN, round 2 pending)

Protocol: `workflow.md` §3. Round 1: pack `audits/ch6-circuits-pack.md`
(commit `05971a42`, auditing `28690c01`), findings
`audits/ch6-circuits-findings.md` — **0 blockers, 4 majors, 7 minors,
4 notes**; gate open. The findings file is preserved verbatim; the sent
pack is immutable, and its errata are acknowledged below. All fifteen
findings were **accepted in full** after source verification; no finding
was contested. Repairs are prose/ledger/docstring only — **zero Lean
statements changed** — as §5 of the findings expressly permits for
deliberately deferred bridges.

## Round-1 repairs (findings 1–11)

| # | Sev. | Repair |
|---|---|---|
| 1 | major | `FeedForward.lean`: `Circuit.toFeedForward` re-described as a **semantic wrapper** (single unrestricted `⟨Fin n, C.eval⟩` gate + identity wires; `size = depth = C.depth + 1`; never discharges `OnlyUsesGates`; only evaluation preserved) in the declaration docstring, the module docstring, and the section header; the false `C.size * C.depth` prose bound removed. Catalog entry rewritten to match. `Hierarchy.lean`'s already-accurate disclosure untouched. |
| 2 | major | `Basic.lean`: divergence ledger rewritten — the normal forms are *alternating trees over base clauses*, not [OD14, Def 4.26]'s layered circuits (no common input layer, unequal literal paths); the three size/depth measures declared non-interchangeable with the clause-of-two-literals example (normal-form size 1 / depth 0 vs `toCircuit` size 3 / depth 1), the root-counting convention, and the `.node []`/`.clause []` depth asymmetry; the mutual-block header de-attributed from Def 4.26. |
| 3 | major | `PPoly.lean`: "All are class-preserving" restricted to the polynomial union, with the auditor's own counterexample (`allOnes ∈ InSIZE (fun _ => 1)` vs no size-1 circuit in AB's input-counting model for n ≥ 2) recorded in the ledger; `InSIZE` labeled as this model's size class with transfer requiring an explicit simulation. `Hierarchy.lean`: "Def 6.2's `SIZE(T)` **is** `InSIZE`" weakened to "is rendered, with declared divergences — not the same fixed class". Facade `SizeClasses` bullet likewise. |
| 4 | major | `HardFunctions.lean`: the "strictly the stronger" comparison replaced by the precise statement — neither quantified bound implies the other on the strength of the `S + 2n` conversion, with the auditor's n = 20 instance (5242 → 5202 ≪ 41943) in the ledger; "no bound runs the other way" corrected to "no polynomial bound" (depth-exponential unrolling exists). Facade bullet now reads "the tree-circuit analogue of [AB09, Thm 6.21] … no **tree** circuit". |
| 5 | minor | `PPoly.lean` ledger: graph conventions collected (unused nodes/inputs permitted; `Gate.inputs` not injective; `andGateOp 0` is a constant-**one** operation; no primitive constant-false). `Basic.lean` ledger: empty AND/OR value/size/depth conventions. `UnaryLanguages.lean`: "no constant gate" corrected to "no primitive constant-false". Catalog: `FeedForward` entry says the raw model enforces no basis; classes impose `stdGateOps` via `OnlyUsesGates`. |
| 6 | minor | `CircuitSat.lean`: "the tree is forced" → "the chosen carrier"; the FeedForward Tseitin map described as **unimplemented, not impossible** (binary clauses for `id`/`NOT`; the layer/node dependent sum as a variable index). `Encoding.lean`: the adjacency-matrix representation described as not implemented (preorder numbering possible), not unavailable. |
| 7 | minor | Stale "TCSlib has no machine model / no `P`" corrected at the three sites round 1 found (`CircuitSat.lean`, `Encoding.lean`, facade `UHalt` bullet), aligned with the earlier N5 wording: the machine model and `P` live on this branch; the missing items are the simulations/reductions, tracked in `backlog.md` §3. |
| 8 | minor | `UnaryLanguages.lean`: "size 2 at every length" → "at most 2 (1 on the all-ones branch)". `Parity.lean`: the `2⌈log₂ n⌉ + 2` depth narrated as an upper bound (with the n = 1 depth-0 literal noted), in the ledger and the `xorFuel_depth` docstring. |
| 9 | minor | `NCAC.lean`: `NC_eq_AC` docstring now says the **unions** coincide, no levelwise equality asserted. |
| 10 | minor | `Hierarchy.lean`: the length-3 remark re-attributed to the local tree counting bound, not [AB09, Thm 6.21]. `Universal.lean`: "Ex 6.1" → "Exercise 6.1". Pack-side errors acknowledged as pack errata below. |
| 11 | minor | Attestation discrepancy acknowledged as pack erratum below; the sweep list and its counts reconciled there. |

## Round-1 recordings (notes 12–15)

All four advisory notes are recorded as inherited interface guidance in
`backlog.md` §3 (gate-by-gate family construction against
`OnlyUsesGates stdGateOps`; the CKT-SAT reduction route from the audited
`Std.Sat.CNF ℕ` carrier with a total string map and fixed rejecting word;
dense variable renumbering before unary indices; the
campaign-decidability → `ComputablePred` bridge for `P ⊊ P/poly`). No
implementation obligation attaches to this round.

## Pack errata (round-1 pack, immutable as sent)

1. **Finding 10 (sources).** The pack placed Theorem 6.22 in "§6.5"; it is
   in **§6.6** of the published 2009 edition. The ranges "Defs 6.1–6.5"
   and "Defs 6.9–6.14" mix definitions with examples, a lemma, and a
   theorem; read them as section ranges, not definition lists.
2. **Finding 11 (sweep-list count).** The pack attested "the 23-module
   circuit list"; the attached `scripts/circuit_module_order.txt` has
   **22** entries. The count was stale: the list had 23 entries until
   `DecisionTree` was relocated out of the tree (commit `193470a3`,
   which removed its line) shortly before the pack was written. The
   verification of record for the audited commit is the 39-module batch
   sweep over the current 22-entry list plus the Switching/LMN reverse
   dependencies and the catalog (zero errors), re-run after this round's
   repairs.

## Round 2

Round-2 pack: `audits/ch6-circuits-reaudit-pack.md`. Scope: verify that
each repair discharges its finding; re-issue the task-1 verdicts for
[AB09] Defs 6.1 and 6.2 (the two *divergent-undeclared* rows) and the
Thm 6.21 row; sweep the minor repairs; confirm the notes' recording.
Gate closes on zero blockers/majors.
