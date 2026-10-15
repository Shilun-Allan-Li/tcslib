# External audit pack — zone/virtual-input layer (§13), statement gate, tranche A-S2

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4b,
track A; design `machine-library-design.md` §13/§13a/§13b). Tranche A-S1
(the virtual-input half) closed in one round
(`audits/vhost-infra-resolutions.md`); this round audits **A-S2, the zone
half**: Z2 (`Build/Zone.lean`, new — the Hennie-Stearns carrier), Z3
(`Codes2Tape.lean`, new — deterministic two-work-tape codes), and Z4
(three space-annotation statements appended to
`Robustness/{AlphabetReduction,SingleTape}.lean` via the shared-file
mechanism). The gate closes on zero blockers and zero majors
(`workflow.md` §3), failure-mode-5 rule in force.

Audited at commit `c43f3a53` (branch `complexity/arora-barak-ch3-4`; the
A-S2 spec commit is `ca2bb11b`). **The audit object is the statement
surface**: 25 new definitions/structures, **18 `sorry`d declarations
(21 sorry warnings — three `Zone.lean` definitions carry sorried capacity
proof fields)**, and 3 skeleton-time proofs (`zoneCellOf_bits`,
`zoneBase_succ`, `MachineCode2.decode_encode`). Z2 is the campaign's
single highest-risk spec (§13a): assume it is wrong until your own
arithmetic says otherwise.

## Brief for the auditor

1. **Blind-restate every definition** from its body before its docstring,
   and **re-derive the layout arithmetic yourself**: `zoneCapacity i =
   2·2^i`, `zoneBase i = 2·(2^i − 1)` (verify the telescope), `zoneIndex`
   via `Nat.log2 (s / 2 + 1)` (verify the floor-division sandwich claimed
   by `zoneIndex_eq_iff` at even and odd `s`, at `s = 0`, and at zone
   boundaries), the home/slot-to-cell maps including the **documented
   left/right presence-data asymmetry**, and the physical extent bound of
   `zoneTape_blank_outside` (`|c| > 2·zoneBase ℓ + 1` — check both signs
   and `ℓ = 0`). Then `ZoneContents` (note what it does **not** carry),
   `zoneTape`, `zoneSlot`, `zoneSide`, the shift ops, the head-step ops
   (including the `headI`-on-empty convention: popping an empty `R_0`
   yields the blank virtual cell), `Code2TM`/`serialize` (compare
   record-for-record against the attached `CodeNDTM.serialize`: 27 vs
   2·27 records per state, same `actionBits₂`), the three scheme
   structures (compare against the attached `Encoding.lean` and
   `EXPCOM.lean` mirrors), and the three Z4 statements.
2. **Assess the spec-time design refinements** (recorded in §13a and the
   module docstring; each is a deviation from the textbook's surface
   presentation and needs a verdict):
   (a) **pairwise shifts** — level `i` moves `2^(i−1)` cells between
   zones `i − 1` and `i` only, with the classical multi-level rebalance
   as a cascade of these ops; verify the honesty lemmas
   (`zoneSide_shiftInW/OutW`) are true *structurally* (adjacent zones in
   the inner-first concatenation) and that a cascade of pairwise ops can
   reproduce the [AB09] §1.7 discipline with the same geometric amortized
   cost — if the pairwise decomposition loses the amortization, that is a
   **blocker**;
   (b) **fullness excluded from the carrier** — the `{empty, half, full}`
   invariant is the consumer's; check no sorried contract silently needs
   it (the shift rows' guards and `hroom` hypotheses are the suspect
   spots);
   (c) **one shift machine per direction and side, level in unary on the
   scratch tape** — verify the row statements quantify correctly over
   `ℓ`, `i`, and contents, that the budget `c·(2^i + i + 1)` is the right
   shape for the amortization, and that the visited-interval clause
   (`±(2·zoneBase (i+1) + 2)`) actually contains every cell a level-`i`
   shift must touch, scratch staging included;
   (d) the `zoneShift` wrapper's **dependent `hroom` hypothesis** and its
   guard semantics ("realizes the pure op exactly where the guard fires")
   — is the contract honest, or can a row be instantiated outside its
   guard to claim a false transformation?
3. **Argue each of the 18 sorried statements true as literally stated**,
   or exhibit the problem (boundary cases: `ℓ = 0`, `i = 1`, empty zone
   words, exactly-full zones, `s` at `zoneBase` boundaries, even/odd
   cells, blank home, `numStates = 0`, `t = 0`). The three `Zone.lean`
   defs with sorried capacity fields (`zoneShift`, `zoneMoveRight`,
   `zoneMoveLeft`) need their field obligations checked for provability
   under their hypotheses — a false capacity field is a **blocker** (the
   def is then uninhabitable as specified).
4. **Z3 fidelity**: the serialization's fixed enumeration order against
   `CodeNDTM.serialize` with the choice bit removed; the
   `UniformMachineCode2` clauses against `UniformMachineCode` (the
   deterministic `decode`'s `toFinTM`, the joint polynomial, both
   branches); the sketches' claimed constants (27 records per state, the
   halved minimum-length guard) — the round-1 miscount lesson of the ND
   gate (finding 3 there) applies squarely here.
5. **Z4 shapes**: all three statements carry `space ≤ c·(S + 1)` at
   **every** horizon with coefficient-constant form; verify the sweep
   argument (union of origin-containing intervals bounded by the sum of
   cardinalities), the block-coding argument, and that the composed
   `one_work_tape_binary_spaceUsed` is literally the plan §2.7 fallback
   deliverable. Flag any missing hypothesis (monotonicity of `S`? the
   statements avoid it deliberately — check they can).
6. **The Ex 4.1 design-time obligation** (§13 Z4; recorded to be
   discharged in this pack): the maintainer's assessment is below —
   sanity-check its reasoning and flag disagreements as notes.
7. **Debt screen (failure mode 5)**: the tranche must add no copies; the
   ledger line is below. `Zone.lean` deliberately does **not** copy the
   `SweepCell` machinery it cites as precedent — verify.
8. Report in the standard table and severity scale; propose missing
   machine-checkable sanity statements (candidates to weigh: a
   `zoneTape`-injectivity-from-contents lemma; `zoneSide` length
   arithmetic; a named `zoneIndex` computation table for small `s`; a
   `Code2TM.serialize`-length lemma mirroring the received grammar
   bounds).

## The Ex 4.1 design-time assessment (maintainer; the §13 Z4 obligation)

Plan §2.7 flags Thm 4.8's space-efficient universal (Ex 4.1) as chapter
4's largest single risk, with two candidate routes. Assessment at A-S2
spec time: **the two-tape universal route is plausible and preferred; Z4
is retained as the audited fallback.** Reasoning: the stage-1 universal
over `Code2TM` codes hosts the coded machine's two work tapes on two
physical tapes (no tape reduction inside the universal — the Z1
virtual-input layer carries the input discipline), so its work space is
the hosted space plus the table/clock administration,
`O(S + |α| + log t)` — Ex 4.1 grade — *provided* the stage-1 design
carries the Z1/Z2 space rows through its interpreter loop, which is
exactly what the §12/§13 space mandate makes routine. The fallback
(`one_work_tape_binary_spaceUsed` + the received conversions) is
independent of the universal and additionally serves the chapter-1
retrofit surface, so its three statements are kept and audited now; the
stage-1 design review selects the primary route, and this obligation is
thereby **discharged** (the risk register no longer waits on an unmade
assessment).

## Known deviations and declared anomalies (verify they are benign)

* The three skeleton-time proofs (flagged, rfl/arith-grade).
* The Z4 statements re-sorry two closed audited files (the shared-file
  mechanism, flagged); their existing audited surfaces are untouched —
  verify additivity from the attached sources.
* `SingleTape.lean` crosses the size line (1,029); justification recorded
  in the plan's decision log (48 additive Z4 lines; splits belong to D7).
* `Codes2Tape.lean` imports `NDCodes.lean` (a chapter-3 statement surface)
  solely for `actionBits₂`/`workPair` — the recorded
  "never a second serialization" decision; flag if anything else leaks
  through that import.

## Repository-side attestations (verify or challenge)

* Elaboration: `Build/Zone`, `Codes2Tape`,
  `Robustness/{AlphabetReduction,SingleTape}`, and the `TuringMachine`
  facade all check at exit 0, zero `error:` lines, fresh `.olean`s; the
  tranche adds exactly 21 sorry warnings over 18 sorried declarations
  (13 + 2 + 3).
* Style lint: 0 FAIL over both directories; every sorry carries a literal
  **Proof sketch**; the one new size WARN is justified as above.
* **Duplication ledger (failure mode 5): new copies — none.**
* The A-S1 fill (11 targets) is concurrently dispatched and owns
  `Build/VirtualInput.lean` + `Simulation.lean`; this tranche touches
  neither.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (including failure mode 5);
findings verbatim into `audits/zone-infra-findings.md`; the gate closes on
zero blockers and majors, after which the A-S2 fill epoch dispatches and
the stage-1 builds (Hennie-Stearns + the two-tape universal) have their
complete statement substrate.
