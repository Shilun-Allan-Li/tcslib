# External audit pack — Chapter 7, Phase 1 (randomized computation, full statement surface)

Audited Lean surface: commit `76fe2f46` on `complexity/arora-barak-ch7` (green,
repaired). This pack/bundle were regenerated on top of it. This is the
**statement-audit gate of the Chapter 7 campaign** (`AroraBarakChapter7Plan.md`),
covering the full statement surface in one phase: Tier A probability/spectral facts,
Tier B randomized classes over an abstract verifier model, the polynomial-time machine
instantiation, **and the three new support modules that the recent fill added**
(counter-program input-shift, a poly-time prefix calculus, and the `pairEncode`
fixed-randomness circuit builder). Record findings in `audits/ch7-phase1-findings.md`.

> **Provenance — read first.** This gate runs **retroactively**, and the surface has
> two layers:
> 1. The original 10-module surface (Tier A + Tier B + `PolyTimeModel` skeleton),
>    maintainer-reviewed over three fidelity rounds, approved at `4a683979`.
> 2. Three **new** support modules and three filled `PolyTimeModel` targets delivered
>    by a *different-vendor model* (commit `722738a1`). That commit **did not compile**
>    as delivered (its author could not run Lean); it was repaired to green at
>    `76fe2f46` with **no statement or signature changed** (see attestation 1). The
>    repairs were pure proof-engineering.
>
> The product under audit is the **statements, their definitions, and (for the
> remaining `sorry`s) their proof sketches** — not tactic scripts, which Lean checks.
> Treat every statement, proved or sorried, with equal suspicion: a *wrong-but-proved*
> statement is the worst outcome, and the new modules are externally-drafted, so
> blind-restate them like any other surface.

Source text: [AB09] ch. 7 (2007 web draft; reference pair under
`blueprint/src/references/`): Lemma 7.5; Definition 7.4 (`BPP`/`RP`/`coRP`/`ZPP`);
Theorem 7.8; Theorem 7.10 + Corollary 7.11; Lemma 7.9; Theorem 7.17; Theorem 7.18; and
§7.B Lemma 7.37, Theorem 7.38, Lemma 7.40, Theorem 7.41. The auditor must have the
chapter at hand.

## Repository-side attestations (maintainer, remote machine — verify or challenge)

1. **Statement freeze.** The fill modified one previously-audited file,
   `Randomized/PolyTimeModel.lean`, by replacing three `sorry` bodies only: a
   comment-stripped comparison of `243b106b` (pre-fill) vs `76fe2f46` (post-repair)
   shows the **same 20 declarations with zero signatures changed, added, or removed**.
   The three new modules and the three one-line facade imports are **pure additions**.
   No other audited `.lean` file is touched.
2. **Elaboration.** Full **13-module** fresh-olean sweep via `scripts/lean_check_tree.sh`
   in `scripts/ab_ch7_module_order.txt` order (Lean 4.25.0, Mathlib at the branch pin;
   **`lake build` not used** — banned on the campaign branch): every module exits 0,
   emits a fresh `.olean`, **zero `error:` lines**.
3. **Admissions inventory.** Exactly **4** `declaration uses 'sorry'` warnings
   tree-wide:
   * `Expanders/Chernoff.lean:66` — `walk_visits_concentration` (Theorem 7.41),
     **intentional and permanent** (book omits the proof).
   * `Randomized/PolyTimeModel.lean:248,255,273` — `polyTimeModel_closedUnderMajority`,
     `…_closedUnderAny`, `…_closedUnderShiftOr`: the three open fill targets (a
     polynomial loop of `P`-decider queries with vote/OR aggregation). Each carries a
     proof sketch.
4. **Axiom hygiene (anti-tamper).** `#print axioms` on the fresh olean tree: the fill's
   closed leaves — `CounterProg.run_shiftInput`, `CounterProg.Goes.prepend_input`,
   `polyTimeComputable_takePrefixByLength`/`…dropPrefixByLength`,
   `DAGCircuit.pairEncode_eval`/`…_size`, `DAGCircuitFamily.pairEncode_eval_eq_true_iff`,
   `Randomized.polyTimeComputable_takePrefixByLen`/`…dropPrefixByLen`,
   `polyTimeModel_verifierHasCircuits`, `polyTimeModel_closedUnderRace` — all print
   exactly `[propext, Classical.choice, Quot.sound]` (a subset for two of them); **no
   `sorryAx`**. `adleman_polyTime` prints `sorryAx` as expected, via the still-open
   `closedUnderMajority`.
5. **Policy conformance.** `scripts/style_lint.py` reports fill-style findings (missing
   `**Proof sketch.**` markers on some landed proofs, `Classes.lean` > 1000 lines, a
   few undocstringed helpers, Lean "unused simp arg" / "unnecessary simpa" linter
   warnings in the repaired modules). These are scoped to fill closure and alter no
   statement; flag any you believe bear on fidelity.

## What is under audit

The original surface, unchanged (see the prior pack revision for its full table): Tier A
(`Expanders/{Basic,Mixing,Walks,Chernoff}`, `Randomized/{SchwartzZippel,ErrorReduction}`)
and Tier B (`Randomized/{Classes,Adleman,SipserGacs}`), headline results Lemma 7.5,
Theorems 7.8/7.10/7.17/7.18, Lemma 7.9, §7.B Lemmas 7.37/7.40 + Theorems 7.38/7.41.
`Randomized/PolyTimeModel.lean` instantiates the abstract model; `closedUnderRace`,
`closedUnderAnswerIs`, `closedUnderNot`, `verifierHasCircuits`, and
`inSigma2_polyTimeModel_iff` are proved, the three closures above remain `sorry`.

**New support surface (this revision):**

| Module | Key definitions | Key statements |
|---|---|---|
| `TuringMachine/CounterProgInput.lean` | `CounterProg.shiftInput` (shift an abstract state's input position) | `run_shiftInput`, `Goes.prepend_input` — a bounded suffix run stays valid after prepending already-consumed input, with positions shifted |
| `ClassNP/PolyTimePrefix.lean` | `PrefixByLength.take`/`drop` (on `pairEncode u s`, return `s.take \|u\|` / `s.drop \|u\|`; malformed pairs → `[]`), via a counter program | `polyTimeComputable_takePrefixByLength`, `…_dropPrefixByLength` |
| `CircuitComplexity/PairEncode.lean` | `DAGCircuit.bufferInputs` (route a circuit's inputs through buffered copies/constants), `DAGCircuit.pairEncode` (compute `C` on `pairEncode x r` with `r` fixed), `pairWiring`/`pairEncodeInput` | `pairEncode_eval`, `pairEncode_isFaninTwo`/`isWellFormed`, `pairEncode_size` (`= n + C.size`), `DAGCircuitFamily.pairEncode_eval_eq_true_iff` |

These discharge, respectively, `takePrefixByLen`/`dropPrefixByLen` (hence
`closedUnderRace`) and `verifierHasCircuits` (hence Adleman's circuit hypothesis).

## Known deviations (verify benign; flag others)

All deviations from the prior pack revision still apply (ℚ-counting Chernoff — **CH7-Q1,
highest priority**; Las Vegas `ZPP` — CH7-Q2; statement-only sign-corrected Thm 7.41 —
CH7-Q3; explicit `polyLen a k n = a·(n+1)^k`; certificate `VerifierModel` with named
closures — CH7-Q4; Cor 7.11 erratum; fixed-randomness circuit route). New with this
revision:

* **The circuit buffer adds `n` vertices** (`pairEncode_size = n + C.size`), because the
  library's `pairEncode` *doubles* the first component, so each free input feeds two
  encoded coordinates via two buffered copies, with the separator and the fixed word `r`
  as constants. The overhead is polynomial and independent of `r`'s contents.
* **`PrefixByLength.take`/`drop` are total**: on a malformed pair (`pairDecode = none`,
  e.g. the forbidden aligned `10`) they return `[]`, matching `pairFstD`/`pairSndD = []`.

## Specific questions for this phase

Carry over CH7-Q1..Q4 from the prior revision (CH7-Q1 — ℚ-Chernoff fidelity — remains
priority one). New, on the added surface:

5. **Circuit fidelity.** Does `pairWiring`/`pairEncodeInput` realize the library's
   `Turing.pairEncode (List.ofFn v) r` *exactly* as circuit input wires (doubled first
   component as two copies per bit, constant separator `[false,true]`, constant `r`)?
   Does `DAGCircuitFamily.pairEncode_eval_eq_true_iff` state the intended acceptance
   correspondence that `polyTimeModel_verifierHasCircuits` consumes — neither off by a
   coordinate nor collapsing when `n = 0` or `r = []`?
6. **Prefix fidelity + the bridge.** Do `PrefixByLength.take`/`drop` agree with
   `Randomized.takePrefixByLen`/`dropPrefixByLen` as used in `closedUnderRace` (the fill
   bridges them by `simp` unfolding — confirm the two definitions are the same
   function, so the poly-time proof is about the function `closedUnderRace` actually
   uses)? Is the malformed-input convention (`→ []`) faithful to `pairFstD`/`pairSndD`?
7. **Input-shift semantics.** Do `CounterProg.run_shiftInput` / `Goes.prepend_input`
   state the "execute on the suffix = execute on the whole with position shifted"
   property correctly, with no sign/▸off-by-one in the position arithmetic?

## Brief for the auditor

As before: audit the trusted surface (definitions, statements, sketches); do not review
tactic scripts. Hunt infidelity, trivialization, unprovability, missing hypotheses.
Blind-restate every definition (old and new) before reading its docstring; argue each
sorried statement (Thm 7.41 and the three closures) true-as-stated or exhibit the
problem; attempt ≥3 adversarial instantiations (`n = 0`, `r = []`, a constant verifier,
a degenerate graph). No blanket approval; justify an empty table with the restatements.
The gate closes only on a round reporting **zero blockers and zero majors**.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = downstream work would build on a wrong statement;
**major** = statement fixable but materially misleading; **minor** = edge case or
naming/attribution; **note** = observation.
