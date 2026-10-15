# External audit pack — Chapter 7, fill gate (the block-query loop and the closed machine surface)

Audited Lean surface: the **merged tree** on `complexity/arora-barak-ch3-4` at
`49658bb6`, where PR #11 and a follow-up merge brought the Chapter-7 campaign. The
summit landed at `d450376` on `complexity/arora-barak-ch7`; the closure sweep and this
pack's first draft sit on top of it at `0c22ae33`. Every ch7 module is byte-identical
on the merged tree to `0c22ae33`, except `ClassNP/PClosure.lean`, which also carries a
comment-only correction from the ch3-4 branch (attestation 1). This revision of the
pack (maintainer, 2026-10-10) re-runs attestations 1, 2, 4 and 5 on the merged tree
and adds question 7 (duplication). This is the **fill-audit gate of the Chapter 7
campaign**: the statement surface was audited and CLOSED at ch7-phase1
(`audits/ch7-phase1-{pack,findings,resolutions}.md`, zero blockers / zero majors at
`76fe2f46`); this gate covers everything the fill campaign **added** to the trusted
surface while discharging the last three machine closures. Record findings in
`audits/ch7-fill-findings.md`.

> **Provenance — read first.** After the phase-1 gate closed, the three remaining
> `PolyTimeModel` closures (`closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr`)
> were reduced to one chapter-neutral primitive — *`P` is closed under running a
> `P`-decider on polynomially many fixed-size blocks with OR / strict-majority /
> XOR-then-OR aggregation* (`briefs/ch7-pclosure-blocks.md`) — and that primitive was
> built and proved in this repository by the maintainer's agent. **No statement of the
> phase-1 audited surface changed** (attestation 1). What is new, and what you are
> auditing, is the surface the primitive added: two machine-infrastructure modules,
> three `P`-closure modules, and three additive headline lemmas in the frozen
> Chapter-1/2 file `ClassNP/PClosure.lean`.
>
> The product under audit is **definitions and theorem statements** — not tactic
> scripts, which Lean checks. Everything in scope is *proved*; remember that a
> wrong-but-proved statement is the worst outcome, so blind-restate each definition
> and statement before reading its docstring.

Source text: [AB09] ch. 7 (2007 web draft; reference pair under
`blueprint/src/references/`): the implicit machine-closure steps of Theorem 7.8
(`ZPP = RP ∩ coRP`: the OR amplifier), Theorem 7.10/Corollary 7.11 and Theorem 7.17
(majority repetition), and Theorem 7.18 (the XOR-shift OR of the Sipser–Gács proof).
The loop host itself is §1.2-folklore machine engineering ("simulate the machine on
each block"), audited for model fidelity rather than against a numbered theorem.

## Repository-side attestations (maintainer, remote machine — verify or challenge)

1. **Statement freeze / drift.** `audits/evidence/ch7/ch7-fill-drift-attestation.md`:
   of the 13 phase-1 modules, 12 are comment-stripped **identical** to the audited
   baseline `76fe2f46`; `Randomized/PolyTimeModel.lean` has the **same 20
   declarations, same order, zero signatures changed, import block byte-identical** —
   only the three `sorry` bodies became proofs. The frozen `ClassNP/PClosure.lean`
   gained exactly the three headline lemmas (additive; baseline sequence is an
   ordered prefix; one import added). No other pre-existing `.lean` file differs.
   **On the merged tree**, `PClosure.lean` additionally carries the ch3-4 branch's
   P0-gate correction (finding 5) to the docstrings of `lenEq_mem_P` and
   `lenLe_mem_P`. It is comment-stripped identical to `0c22ae33`. "No other file
   differs" holds relative to the ch7 branch. On the merged tree, the rest of
   `TCSlib/` is the ch3-4 campaign's own audited material and lies outside this gate.
2. **Elaboration.** Full **19-module** fresh-olean sweep (the 13 phase-1 modules plus
   the six fill modules, `scripts/ab_ch7_module_order.txt` order) via
   `scripts/lean_check_tree.sh` (Lean 4.25.0, Mathlib at the branch pin; **`lake
   build` not used** — banned on the campaign branch): every module exits 0, emits a
   fresh `.olean`, **zero `error:` lines** (`audits/logs/ch7-fill-sweep.log`).
   **Re-run on the merged tree** with the four touched facades (`Expanders`,
   `Randomized`, `ClassNP`, `TuringMachine`) appended: 23/23 modules exit 0, zero
   `error:` lines (`audits/logs/ch7-fill-merged-sweep.log`).
3. **Admissions inventory.** Exactly **1** `declaration uses 'sorry'` warning
   tree-wide: `Expanders/Chernoff.lean` — `walk_visits_concentration` (Theorem 7.41),
   **intentional and permanent** (book omits the proof; CH7-Q3, confirmed at
   phase-1). The fill campaign closed every other admission.
4. **Axiom hygiene (anti-tamper).** `audits/logs/ch7-fill-axioms.log`: 36 headline
   prints on the fresh olean tree — the Tier A/B results, all eight `polyTimeModel`
   closure/instantiation theorems, `adleman_polyTime`, `sipser_gacs_polyTime`,
   `zpp_eq_rp_inter_corp_polyTime`, the three `mem_P_of_block*` lemmas, the three
   block tests, `polyTimeComputable_emitIter`/`_xorD`, the slice lemmas, and
   `FinTM.exists_emitIterTM` — 35 print exactly
   `[propext, Classical.choice, Quot.sound]`; the single exception is the
   intentional Theorem 7.41 stub, which prints `sorryAx` as expected. **Re-run on
   the merged tree**: the 36 print lines are byte-identical
   (`audits/logs/ch7-fill-merged-axioms.log`).
5. **Policy conformance.** `audits/logs/ch7-fill-lint.log` over the 19-module
   surface: the fill modules and the closure's documentation sweep leave **one**
   standing finding — `Randomized/Classes.lean` is 1,328 lines (the documentation
   sweep grew it from the 1,266 lines first stated here; > 1,000, policy
   "must split"). Splitting a frozen, audited module is deliberately **not** done
   unilaterally at closure; the proposed disposition (split the counting layer out
   of `Classes.lean` post-gate, statements unchanged) is submitted to this round for
   approval. Flag if you believe the size bears on fidelity. **Re-run on the merged
   tree** (`audits/logs/ch7-fill-merged-lint.log`, five directories): 0 FAIL. This is
   the only WARN on the ch7 surface.

## What is under audit (the new trusted surface)

| Module | Key definitions | Key statements (all proved) |
|---|---|---|
| `TuringMachine/Build/EmitIterEmbed.lean` (18 public) | `SafeRun` (run avoiding a state strictly inside), `padAction`/`embedCfg` (tape-padding, state-injecting embedding of an `m`-tape module into a `k`-tape host) | `runFrom_output_prefix` (output-prefix commutation), `runFrom_output_extends` (append-only output), `embed_step`/`embed_run` (module runs embed step-for-step on live, off-exit states). *(Erratum, ch7 fill gate round 2, R2-4: `control_step`/`control_step'` were listed here, but they are private helpers of `EmitIterBody`, not exports of this module.)* |
| `TuringMachine/Build/EmitIterBody.lean` (1 public) | the body machine, copier and round lemmas are private | `FinTM.exists_emitIterTM`: machines for a step `g` and a chunk `e` within `C·(n+1)^c` budgets, plus an orbit length envelope `∀ w i, |g^[i] w| ≤ b·(|w|+1)^l`, yield one machine computing `w ↦ (range (a'·(|w|+1)^k' + 1)).flatMap (fun i => e (g^[i] w))` in `C·(n+1)^c` normal form |
| `ClassNP/PolyTimeBlockLoop.lean` (22 public) | `sliceTakeAt`/`sliceDropAt` (keep the first pair component, take/drop `a·(n+1)^k` of the second), `xorD` (truncating bitwise XOR of a pair's components), `blockDone`/`isNilB` (loop-state conventions) | `polyTimeComputable_emitIter` (the `FP`-level loop, consuming `exists_emitIterTM`), `polyTimeComputable_xorD`, the slice/`take1`/`headD`/`tail`/`isNil`/`or`/`not` `FP` helpers, `flatMap_range_eq_single`, `length_pair_components_le` |
| `ClassNP/PolyTimeBlockTests.lean` (3 public) | `blockAt a k z i` — the `i`-th length-`a·(n+1)^k` block of `pairSndD z`, `n = ‖pairFstD z‖` | `polyTimeComputable_blockAnyTest`, `polyTimeComputable_blockXorAnyTest` — the one-bit OR / XOR-then-OR aggregated block tests of a `P` indicator are poly-time |
| `ClassNP/PolyTimeBlockMajority.lean` (1 public) | private vote-counter loop | `polyTimeComputable_blockMajorityTest` — the strict-majority aggregated test is poly-time |
| `ClassNP/PClosure.lean` (**+3**, frozen file) | — | `mem_P_of_blockAny` (`{z \| ∃ i < a'·(n+1)^k', pairEncode (pairFstD z) (blockAt a k z i) ∈ V} ∈ P`), `mem_P_of_blockMajority` (strict majority of block indicators, `a'·(n+1)^k' < 2·countP`), `mem_P_of_blockXorAny` (nested pair `⟨⟨x,u⟩,v⟩`; blocks of `u` XORed with `v`, truncating) |

Consumption (already audited statements, proofs now closed): the three
`PolyTimeModel` closures reduce to the three headliners exactly as
`closedUnderRace` reduced to the slice primitives at phase-1.

## Known deviations and design choices (verify benign; flag others)

* **Truncating XOR.** `xorD` and the `mem_P_of_blockXorAny` statement use
  `List.zipWith xor` semantics (truncate to the shorter word) — the convention the
  phase-1 audit already confirmed for `shiftOrVerifier` (phase-1 finding 1 sweep).
* **The brief's sketch was wrong and is superseded.** `briefs/ch7-pclosure-blocks.md`
  sketched `xorD` as a one-register counter program; a one-pass register machine
  cannot pair bits across the separator. The landed `xorD` is instead a customer of
  the emit-iteration loop (one XOR bit per round). The *statement* is as the brief
  proposed; only the construction route changed.
* **Orbit-only envelope.** `polyTimeComputable_emitIter` demands
  `∀ w i, (g^[i] w).length ≤ b·(w.length+1)^l` — over **all** inputs and iteration
  counts, not only scheduled rounds. Customers discharge it with absorbing done
  states. (An earlier draft hypothesis quantifying over all state words was
  undischargeable and was replaced before any consumer landed; the statement was
  never part of an audited surface.)
* **Unary aggregation state.** Vote counts and countdowns are unary words inside the
  `pairEncode`d loop state; polynomial budgets enter only through
  `polyTimeComputable_polyUnary`-style unary schedules (the Argument-A discipline).
* **`blockAt`'s length source.** The block length and count schedules are evaluated
  at `(pairFstD z).length` — for the nested `blockXorAny` surface, at
  `(pairFstD (pairFstD w)).length`, i.e. the *inner* first component `x`, matching
  `shiftOrVerifier`'s `p x.length`.

## Specific questions for this gate

1. **Block fidelity.** Does `blockAt a k z i = ((pairSndD z).drop (i·q)).take q`,
   `q = a·(n+1)^k` at `n = ‖pairFstD z‖`, match the block conventions of
   `anyVerifier`/`majorityVerifier` (blocks of the random string at `p = polyLen a k`)
   and — through `blockAt a k (pairFstD w) i` with the *nested* length source — of
   `shiftOrVerifier`? Check off-by-one in `i·q`, the `+1` in the round count
   `a'·(n+1)^k' + 1`, and the degenerate schedules `a' = 0`, `a = 0`, `k = k' = 0`.
2. **Headline-statement fidelity.** Are the three `mem_P_of_block*` sets precisely
   the `some true`-sets of the three verifier constructions on `pairEncode`d inputs
   (given the efficiency witness's iff), so that complementation gives the
   `some false`-sets? Pay attention to the strict majority (`K < 2·count`, no
   off-by-one at even/odd `K`) and to malformed pairs (`pairFstD z = []` conventions).
3. **The loop statement.** Is `exists_emitIterTM`'s computed function — concatenation
   of `e (g^[i] w)` over `i ∈ range (a'·(|w|+1)^k' + 1)` — the right general form,
   and is its budget genuinely `C·(n+1)^c` (no hidden dependence on the orbit beyond
   the envelope)? Is the envelope hypothesis non-vacuous and dischargeable (the three
   customers and `xorD` discharge it; try to construct a natural customer that
   cannot)?
4. **Embedding soundness as stated.** Do `padAction`/`embedCfg` state the intended
   "module untouched on the padding tapes" semantics (no tape aliasing, inputs read
   through `Fin.castLE`, output preserved), and do `embed_step`/`embed_run`'s
   hypotheses (live states, off-exit, host transition equals padded module
   transition) match how a dispatch-style host actually behaves at its exit state?
5. **Output-prefix commutation.** Is `runFrom_output_prefix` the correct statement
   (the table never reads the output; output is append-only, per
   `runFrom_output_extends`), and is it strong enough for the round assembly's
   claim that the install call's own output stays empty?
6. **`PClosure` extension safety.** Do the three additions interact with the
   existing closure calculus only additively (no instance/namespace capture, no
   changed behavior of the pre-existing 13 declarations)?
7. **Duplication (this repository's `audits/TEMPLATE.md` failure mode 5, attached).**
   Screen the surface for duplicated proved material and verify the maintainer
   pre-screen (`audits/evidence/ch7/ch7-fill-duplication-screen.md`, attached). It
   reports no copies of pre-existing repository material. It does report one family of
   renamed re-proofs inside the stack: the OR, XOR and majority loops each carry their
   own copy of the same orbit, length and init lemmas, which puts
   `PolyTimeBlockMajority` at 4 of 14 declarations (28.6%), over this repository's
   one-fifth threshold. Report each confirmed copy family at **major** with the
   proposed fix "human acknowledgment required"; the gate may not close over them
   until the human maintainer accepts the debt and names its resolution. The family
   above is **already acknowledged** (the human maintainer, 2026-10-10: it is resolved
   in this repository's 12.2c refactor, as one generic lemma set with statements
   unchanged). Confirm its extent; it then does not hold the gate, though any further
   family you find does. Say whether
   the screen missed any copy, including re-derivations it cannot detect. Separately,
   compare the public `EmitIterEmbed` embedding layer (`padAction`/`embedCfg`/
   `embed_step`/`embed_run`) with the §12 `Build/Embed.lean` layer (attached). Report
   the overlap as facts, meaning what one layer states that the other does not, and do
   not propose a merge of the two; that merge is already scheduled in this
   repository's per-theme refactor (12.2c).

## Brief for the auditor

As at phase-1: audit the trusted surface (definitions and statements); do not review
tactic scripts. Hunt infidelity, trivialization, and missing hypotheses.
Blind-restate every definition before reading its docstring; attempt ≥3 adversarial
instantiations (suggested: `a' = 0`; `z` a malformed pair; `V = ∅` and `V = univ`;
`cE = cG = 0` budgets; an `e` emitting multiple bits per round). No blanket
approval; justify an empty table with the restatements. The gate closes only on a
round reporting **zero blockers and zero majors**.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = downstream work would build on a wrong statement;
**major** = statement fixable but materially misleading; **minor** = edge case or
naming/attribution; **note** = observation.
