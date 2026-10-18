# Ch3–4 fill campaign — B4 membership: `TQBF ∈ PSPACE` (`Complexity.TQBF_mem_PSPACE`, `ClassPSPACE/TQBF.lean`, one target)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 13957bf73eb37763259be1fd01a5cca9bd03c21f HEAD`
  succeeds. That commit contains:
  - the P4.3 statement layer and its closed gate (`audits/ch4-p43-*`, three rounds);
  - B4a's proved codec `exists_adjacency_codec_cnf` and its 119 privates
    (`audits/fills-4-integration.md`);
  - the §12.8 rows, all proved: Catalog Part 3, `Build/Scan`, `Build/InputCall`, `Build/Seam`,
    `Build/CfgRecord`; R8.0b and the §12.7 counter loop (`Build/CounterLoop`);
  - this brief's order list `briefs/orders/ch34-b4-mem.txt`, base sorry set, screen base, and the
    pre-ship log `audits/logs/ch34-b4-mem-preship.log`;
  - the B4 pre-issue promotion (user, "Promote first"): the CNF grammar facts made public in
    `Formulas/CNFEncoding.lean`, and `MultiTapeTM.spaceUsedByTape_le_card_Icc` moved to
    `Build/Catalog.lean` (both listed in "Cited infrastructure").

  If the check fails, **stop**.
- Create your working branch off the campaign branch: **`fill/ch34-b4-mem`**. Record the base hash
  in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ch34-b4-mem.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, the sanity-case evidence (ground rule 11), and
  `SHA256SUMS`.

## Parallel batches this round (disjoint files or declarations; never edit another batch's file or declaration)

| Batch | Brief | Owns |
|---|---|---|
| **B4, TQBF membership** | `briefs/ch34-b4-mem.md` | `ClassPSPACE/TQBF.lean`: **`TQBF_mem_PSPACE` only** (ground rule 1) |
| §12.10 W2-S, continuation 2 | `briefs/w2-fill-oraclesim-cont2.md` | `TuringMachine/Build/OracleSim.lean` |
| §12.8b record tables, continuation 2 | `briefs/w1-fill-recordtable-cont2.md` | `TuringMachine/Build/RecordTable.lean` |
| B5a, the canonizer | `briefs/b5a-fill-canon.md` | `TuringMachine/CodeSimulator.lean`, by declaration |
| B5a, the uniform simulator H1 | `briefs/b5a-fill-h1.md` | `TuringMachine/CodeSimulator.lean`, by declaration |

Also in flight (wave 5): S1b (`briefs/ch34-s1b.md`, `SpaceComplexity/ConfigGraph.lean`), B3a
(`briefs/ch34-b3a.md`, `SpaceComplexity/Constructible.lean`) and B5b (`briefs/ch34-b5b.md`,
`Diagonalization/EXPCOM.lean`, by declaration). **Not yours** (cite, never edit): the §12.8 A–C
files (`Build/Catalog`, `Build/Seam`, `Build/Scan`, `Build/CfgRecord`, `Build/InputCall`; their gate
has closed), and the promoted rows' files (`Formulas/CNFEncoding.lean`, `ClassNP/SAT.lean`,
`ClassNP/Tautology.lean`). A parallel batch's work is invisible to your base and your screen.

## What this is

Fill **[AB09, Theorem 4.13, membership half]**: `theorem TQBF_mem_PSPACE : TQBF ∈ PSPACE`
(`ClassPSPACE/TQBF.lean:1839`; sketch `:1820–1838`, binding). This is the only `TQBF` target in this
batch. The hardness half and the completeness corollary stay sorried; they belong to a later B4
batch.

**The space obligation, exactly.** `Complexity.PSPACE` is `⋃ c, SPACE (fun n => n ^ c + 1)`
(`SpaceComplexity/SpaceClasses.lean:47`). `Complexity.SPACE s` is
`{L | ∃ c M, M.DecidesInSpace L (fun n => c * s n)}` (`SpaceComplexity/Basic.lean:138`). So you
must exhibit `M : FinTM Bool` and a constant `c'` such that, for **every** `x : List Bool`
(invalid encodings and `x = []` included):

```
∃ t, M.ComputesInTime x [MultiTapeTM.indicator (TQBF : Set (List Bool)) x] t ∧
     M.tm.spaceUsed (M.tm.initCfg x) t ≤ c' * (x.length ^ c + 1)
```

The sketch's own target is `c = 1`, that is `SPACE (n + 1)`: "`O(n)` cells, inside
`SPACE (n + 1) ⊆ PSPACE`". Deliver `TQBF ∈ SPACE (fun n => n + 1)` and close with
`Complexity.space_poly_subset_PSPACE 1` (`SpaceClasses.lean:69`), with `SPACE.mono` bridging
`n + 1 = n ^ 1 + 1`. There is no time bound: `t` is existential, so the `2^m`-round walk is fine.
`spaceUsed` sums the visited cells of **every** work tape, origins included (`Turing.MultiTapeTM.spaceUsed`,
`TuringMachine/Deterministic.lean:263`), so every tape costs at least one cell, even at `x = []`.

**The recursion is a depth-first walk with linear state.** The sketch realizes [AB09]'s recursive
evaluator iteratively: "a partial-assignment word of one trit per prefix variable (the book's
footnote: the linear-space global-array variant) walked depth-first by the loop combinator, with
no per-level formula copies" (`TQBF.lean:1828–1830`). The "stack" is therefore one constant-size
record per prefix variable. That is at most `|x|` records, since the prefix length is bounded by the
input length (P4.3 round 1, §5). It is not a stack of frames: round 1 found that "no stack of copied
formulas or logarithmic-size return addresses per variable is needed"
(`audits/ch4-p43-findings.md:154`). The total is `O(|x| + 1)` cells.

**The route is the §12.8 machine route, not an ARM.** Two earlier records place `TQBF ∈ PSPACE` on a
"wide ARM": the plan's decision row (`AroraBarakChapters3-4Plan.md:1017`) and `backlog.md:911`. §12.8
superseded that route; neither record binds you. §12.8 lists `TQBF ∈ PSPACE` among its walkers
(`machine-library-design.md:1134–1140`), with its row map in the §12.8a consumer table:
"R8.2 (validation folds, clause evaluation, the trit odometer), R8.5b (input re-reads), R8.3"
(`:1928`; also `:1418`). Design R8.2 says the same: "Validators elsewhere (TQBF's well-formedness
pass …) are folds too" (`:1215–1217`). The sketch's own words, "a §12 loop/catalog consumer", agree.

**Proved modulo: none.** Every row the route cites is proved at the tip. Their modules carry no
`sorry`: Catalog, Scan, CounterLoop, InputCall, Seam, Embed, Simulation, Encoding, CNF, CNFEncoding,
QBF, QBFEncoding, SpaceClasses, Basic, Convention and MeyerTableau. A complete delivery's axiom print is therefore within
`[propext, Classical.choice, Quot.sound]` with no `sorryAx`.

**B4a is frozen, and it is not your problem.** The codec's CNFs are indexed non-explicitly:
`Fintype.equivFin` numbering, gate CNFs chosen by `.choose`, and `Finset.univ.toList` order
(`TQBF.lean:302–307, 1515–1518, 1532–1535`). That matters to the hardness emitter, not to you.
Membership neither emits nor evaluates any B4a formula. **Do not cite, call or change any B4a
declaration** (`TQBF.lean:114–1811`).

**Read first:** `TQBF.lean`'s module docstring and the target's sketch; `Formulas/QBF.lean`
(`truthAux`, `truth`, the free-variables-read-`false` convention); `Formulas/QBFEncoding.lean`;
`Formulas/CNFEncoding.lean`'s grammar (`:85–166`); the P4.3 records listed under "Gate guidance";
design §12.8 R8.2, R8.5 and §12.8a §6; `Build/Scan.lean`'s input fold; `Build/CounterLoop.lean`'s
two contracts; the **proof** of `Turing.exists_inputSeekTM` (`Build/InputCall.lean:270–533`) as
the model idiom; `policy.md`; `workflow.md` §4.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/fills-5/B4MemPreShip.lean.txt`, re-run at the issue tree (`audits/logs/ch34-b4-mem-preship.log`): 0 errors.
It is check-only. It imports only `TCSlib.Complexity.ClassPSPACE.TQBF` and `#check`s the target
and every row named below, so the route needs no import.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `ClassPSPACE/TQBF.lean:1839` | `Complexity.TQBF_mem_PSPACE` | validate-first input fold; depth-first odometer under `counterLoopTM`; one pass over the matrix per leaf, using the index-lookup idiom; `DecidesInSpace` packaging at `SPACE (n + 1)` | — |

- **Owned:** `ClassPSPACE/TQBF.lean`, for this target's **body**, a flagged Fill appendix in its
  docstring, the status text of ground rule 3, and new `private` declarations. Put every new
  private in **one block between `def TQBF` (`:1813–1818`) and the target's docstring (`:1820`)**,
  so that no hunk touches B4a's block, the hardness docstring or the corollary.
- **Not yours:** `TQBF_PSPACEHard`, `TQBF_PSPACEComplete` (sorried; leave them so),
  `PSPACE_eq_P_of_pspaceComplete_mem_P`, `exists_adjacency_codec_cnf` and all 119 B4a privates
  (frozen), every other file, and the facade `ClassPSPACE.lean`.

### Proof route (binding; the docstring's sketch, its named obligations, and three sanctioned refinements)

The sketch names four obligations: "the depth-first assignment walker (a §12 loop/catalog
consumer), the CNF evaluator machine (one-pass per clause over the decoded matrix), the parser reuse
(`Complexity.QBF.decode` realized by the chapter-2 parser machinery), and the `DecidesInSpace`
packaging". Fill them as follows.

1. **Validate the entire input first, by one input fold** (R8.5d, `Turing.inputFoldTM` /
   `inputFoldTM_run_ofCfg`, `Build/Scan.lean:535/645`). Fold the native input with a finite
   automaton `δ : A → Bool → A` (`[Fintype A]`). It accepts exactly the strings
   `x = pairEncode q m` (`Turing.pairEncode`, `TuringMachine/Encoding.lean:118`) with
   `(Std.Sat.CNF.parse m).isSome`. The language is regular: aligned doubled bits up to the `[false,
   true]` separator (`Turing.pairDecode`, `:122`), then the LL(1) CNF grammar
   (`CNFEncoding.lean:88–151`). Construct `δ` as a product of the pair stage with the grammar
   automaton.
   - **On rejection, output `[true]`.** Both failure modes decode to a true formula. A pair-decoding
     failure gives `⟨[], CNF.fallback⟩`, and a parse failure gives the matrix `CNF.fallback = []`
     under any prefix. Prove this semantic fact as a private lemma.
   - **No matrix verdict before validation completes** (gate guidance, A13).
   - **Sanctioned refinement (i), replacing "the parser reuse".** The chapter-2 parser machinery is
     private (`ClassNP/SAT.lean`: `sat_pipeline_poly` `:1094`, the syntax automaton
     `satSyntaxStep` `:332`, `satSyntax_spec` `:445`, `sat_parse_repr` `:321`). It cannot be cited.
     Realize the decoding by this fold plus grammar facts. Take those facts **from the promoted public
     rows** in `Formulas/CNFEncoding.lean` ("Cited infrastructure").
2. **The depth-first walker** is an iterative odometer over a work-tape word with one constant-size
   record per prefix variable. Rounds run under **`Turing.counterLoopTM`**, the loop combinator
   (`counterLoopTM_run_escape`/`_run_done`, `Build/CounterLoop.lean:1445/1383`). Its fuel word must
   have value at least the number of rounds; an all-`true` word of length `|x|` suffices on valid
   inputs. The walk exits by the escape anchor once the root verdict is known.
   - Each round: (a) evaluate the matrix at the current complete assignment (obligation 3), giving
     the leaf verdict `v`; (b) one **`Turing.scanTM`** odometer pass over the record word
     (`scanTM_run_ofCfg`, `Catalog.lean:12372`; the carry family of R8.2), propagating `v` and
     advancing the assignment; (c) leave by the escape anchor on overflow, else return to the round
     anchor.
   - The record and the transducer are yours (non-binding plan below). The invariants are binding:
     - each record holds the variable's quantifier and its current branch/value bit, plus anything
       else of constant size you need;
     - no per-level formula copies (sketch; gate guidance);
     - the walk computes `QBF.truthAux m qs (fun _ => false) 0` (`Formulas/QBF.lean:94–104`).
   - The sketch's "one trit per prefix variable" may become any constant-size record. State the
     record you use in the Fill appendix.
3. **The CNF evaluator re-reads the matrix from the input**, one scan per clause. It never stores a
   copy of the matrix and never restricts the formula. The sketch says "re-reading prefix bits and
   matrix bytes from the input". Reach the matrix start by rewinding (`Turing.FinTM.timed_rewind`)
   and skipping the doubled prefix. That skip may be a counter-loop over pairs, or
   `Turing.exists_inputSeekTM` (R8.5b) on a binary position you compute once.
   - The clause semantics are `Std.Sat.CNF.eval`: a literal `(v, p)` holds iff the value of `v`
     is `p`.
   - **Free variables read `false`**: every index `v` at or beyond the prefix length (QBF.lean's
     divergence list; gate guidance).
   - **Sanctioned refinement (ii), the index-lookup idiom.** No row reads "the work cell at the unary
     index on the input". Assemble the lookup **from public rows, in the style of
     `exists_inputSeekTM`'s proof** (`InputCall.lean:282–292`). Cite that proof as an idiom only;
     its private helpers stay private. The steps:
     - count the literal's unary run (`v + 1` `true`s) into a fixed-width binary index word, one
       `Turing.incrementTM` per `true`, the input head advancing. This is a `counterLoopTM` whose
       round escapes on the terminator `false`. Use width at least `|x| + 1`, so the `incFixed`
       overflow branch is unreachable;
     - `copyTM` the index word to scratch;
     - run `counterLoopTM` over the scratch copy with a fixed-length round "assignment head right by
       one record", built from Catalog's hand-table lemmas. The copy's value is the run length
       `v + 1`, so start the head one record before record `0`;
     - read the value cell;
     - return the head the same way, or by any rewind whose contract you prove;
     - `clearTM` the scratch and the index.

     Fixed banks are reused for every literal. A direct lockstep (one `counterLoopTM` whose round
     moves the input head and the assignment head together) is an acceptable alternative, **if it is
     composed from `counterLoopTM` rounds and Catalog rows**. Do **not** hand-write a monolithic
     evaluator table: that would mirror `SAT.lean`'s private `satEvalTM` (`:557`). See the hazards.
4. **`DecidesInSpace` packaging.** Assemble the phases with `Turing.phaseHostTM`/`phaseHostTM_run`
   (`Seam.lean:813/830`) or R2 seams (`seamCompTM_run_ofCfg`, `seamCompTM₂_run_ofCfg`). The phases
   are: validate → (reject: answer `true`) → initialize the record word and fuel → walk → answer.
   - Embed sub-machines on dedicated tapes by R1 (`Turing.embedEmitTM`, `embedEmitTM_runFrom`).
   - The answer phase emits exactly one bit and halts (`Turing.FinTM.emitAction`, `emit_halts`,
     `Simulation.lean:88/126`). No earlier phase writes output.
   - The space ledger is head intervals per tape, taken from the trajectory clauses of every
     contract, turned into a cardinality bound per tape (`Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`, now in
     `Build/Catalog.lean`), summed and absorbed into `c' * (|x| + 1)`.
5. **Sanctioned refinement (iii).** The route is the §12.8 machine route above; the "wide ARM"
   mentions are stale. Say so in one sentence of the Fill appendix.

### Reference plan (non-binding; any plan meeting the binding route and ground rules is acceptable)

This plan is a maintainer paper check only. The pre-ship probe checks names, not this plan.

- **Record word.** Two cells per prefix variable `i`, laid out `(bᵢ, qᵢ)`: the current branch/value
  bit, then `quantBit qᵢ` (`true` = `∃`). Build it by an initialization `counterLoopTM` over the input
  pairs. The round reads one aligned pair and writes `[false, q]` with `Turing.writeAdvTM`
  (`Scan.lean:266/323`, whose contract has exactly the round shape), dispatching on `q`; it escapes
  at the separator. Use the input copied and mapped to all-`true` (`inputCopyTM`, then `scanTM` with
  `scanMap`, `scanResult_map`) as fuel.
- **Short-circuit odometer.** The backward pass of `scanTM` with `δf := scanKeep` starts from the
  state "carrying `v`". The layout `(b, q)` means the backward pass reads `qᵢ` before `bᵢ`. At record
  `i`, carrying `v`:
  - if `bᵢ = false` and `v ≠ quantBit qᵢ`: write `bᵢ := true` and stop. The first branch returned
    the neutral value, so try the second;
  - otherwise: write `bᵢ := false` and keep carrying `v`. Either `v` decides the quantifier, or this
    was the second branch, whose value is the node's.

  An overflow past record `0` carrying `v'` means the root's value is `v'`. Invariant: whenever
  `bᵢ = true`, the first branch's subtree had the neutral value of `qᵢ`, so no accumulator is needed.
  `m = 0` is uniform: the empty word overflows at once with the leaf verdict.
- **Cross-round data lives on tape.** Every `counterLoopTM` round starts at the anchor state, so the
  leaf verdict, the clause flag, the formula flag and the final verdict sit in constant-size flag
  cells.
- **Space.** The record word takes `2m + O(1)` cells, the fuel `|x|`, the index and scratch `|x| + 1`
  each, plus constant flags. Every head stays in `[-2, |x| + 2]` of its origin.

## Gate guidance (binding)

The P4.3 resolutions carry exactly one membership item into the fill briefs: "the membership
evaluator's validate-first discipline" (`audits/ch4-p43-resolutions.md:53–58`). It binds together
with the audit text it summarizes:

- **Round 1, S5** (`audits/ch4-p43-findings.md:102`): "Validate the entire encoding, then traverse
  assignments depth first with constant-size information per quantified variable and evaluate the
  serialized CNF by scans. Invalid syntax returns true through the specified fallback; free
  variables read false."
- **Round 1, §5** (`:154`):
  - "trailing garbage makes the total decoder select the true fallback, even if a scanned prefix
    looked unsatisfiable";
  - the prefix length and every decoded index are at most the input length;
  - "matrix evaluation rereads the input and assignment bank";
  - the `O(n+1)` bound includes "initialization and parser failure paths".
- **Round 2, Membership** (`audits/ch4-p43-r2-findings.md:214`): "Reusing fixed banks gives
  `O(n+1)` visited cells."
- **Round 2, adversarial case A13** (`:272`): "A syntactically complete false empty-clause matrix,
  then one trailing bit: the latter must take the true fallback. Validation precedes any verdict."
  This is a permanent sanity case (ground rule 11).
- The module docstring's deviations (i)–(iii) concern the codec and hardness only. "The package is
  existence, not an algorithm" is not your concern.

## Cited infrastructure (public and proved at the issue commit)

- **Classes and measures:** `Complexity.PSPACE`, `Complexity.SPACE`, `SPACE.mono`, `SPACE.mono_const`,
  `space_poly_subset_PSPACE`; `Turing.FinTM.DecidesInSpace`, `ComputesInSpace`,
  `ComputesInSpace.mono` (`SpaceComplexity/Basic.lean`); `Turing.FinTM.ComputesInTime`;
  `Turing.MultiTapeTM.indicator`, `spaceUsed`, `spaceUsedByTape`, `visitedByTapeHead`.
- **Formulas:**
  - `Complexity.TQBF`, `Complexity.QBF`, `QBF.Quant`, `QBF.truthAux`, `QBF.truth`, `QBF.quantBit`,
    `QBF.quantOfBit`, `QBF.encode`, `QBF.decode`, `QBF.decode_encode`;
  - `Std.Sat.CNF.eval` (Std), `Std.Sat.CNF.numVars`, `Complexity.eval_congr_of_lt_numVars`;
  - from `CNFEncoding`: `serializeLit`, `serializeClause`, `serialize`, `takeTrues`, `parseLit`,
    `parseClause`, `parseClauses`, `parse`, `fallback`, `decode`, `parse_serialize`,
    `decode_serialize`, `numVars_decode_le`.
- **Pairs:** `Turing.pairEncode`, `pairDecode`, `pairDecode_pairEncode`, `eq_pairEncode_of_pairDecode`,
  `pairDecode_eq_none`, `length_pairEncode`, `dbl`, `pairEncode_eq_dbl` (`TuringMachine/Encoding.lean`).
- **Scan (R8.4/R8.5d):** `inputFoldTM`, `inputFoldTM_run_ofCfg`, `inputCopyTM_run_ofCfg`,
  `writeConstTM_run_ofCfg`, `writeAdvTM`, `writeAdvTM_run_ofCfg`.
- **Catalog:**
  - Part 3: `ScanPhase`, `mealyRun`, `scanResult`, `scanTM`, `scanTM_run_ofCfg`, `scanKeep`,
    `scanFold`, `scanMap`, `scanCarry`, `scanResult_fold`, `scanResult_map`, `scanResult_carry`,
    `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `seekStartTM_run_ofCfg`, `seekEndTM_run_ofCfg`,
    `compareTM_run_ofCfg`;
  - the hand-table lemmas: `tapeAction`, `inputMoveAction`, `step_of_tapeAction_move`,
    `step_of_tapeAction_write`, `step_of_inputMoveAction`;
  - R3: `copyTM_run_ofCfg`, `clearTM_run_ofCfg`, `incrementTM`, `incrementTM_run_succ_ofCfg`,
    `incrementTM_run_overflow_ofCfg`;
  - `Turing.incFixed` (`Build/Convention.lean`) and `Complexity.Meyer.incFixed_eq_none_iff`
    (`CircuitComplexity/MeyerTableau.lean:416`, in `TQBF`'s closure through `Inclusions`).
- **CounterLoop:** `counterLoopTM`, `counterLoopCfg`, `counterLoopOrbit`, `counterLoopTM_run_done`,
  `counterLoopTM_run_escape` (both carry the counter-head interval and the body-heads trajectory
  clause), `counterLoop_time_le`, `counterWord`, `counterWord_value`, `counterOverhead`,
  `counterOverhead_le`, `decrementTM_run_succ_ofCfg`, `expandTM_run_ofCfg`.
- **InputCall (R8.5b):** `Turing.exists_inputSeekTM`.
- **Seam (R2):** `seamCompTM`, `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`,
  `seamCompTM_visitedByTapeHead_ofCfg`, `seamCompTM₂`, `seamCompTM₂_run_ofCfg`, `seamReleaseTM`,
  `seamReleaseTM_firstReturn`, `phaseHostTM`, `phaseHostTM_run`.
- **R1/Simulation:** `embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitTM_visitedByTapeHead`,
  `MultiTapeTM.runFrom_mapState_of_agreeOn`; `Turing.FinTM.bufferTape`, `FinTM.timed_rewind`,
  `FinTM.emitAction`, `FinTM.emit_run`, `FinTM.emit_halts`.
- **The pre-issue promotion** (landed at the ancestor, public and proved):
  - in `Formulas/CNFEncoding.lean`, namespace `Std.Sat.CNF`, promoted from `ClassNP/SAT.lean`'s
    privates (`SAT.lean` and `ClassNP/Tautology.lean` now cite them):
    - `parse_repr : parse x = some φ → x = serialize φ`, with `takeTrues_repr`, `parseLit_repr`,
      `parseClause_repr` and `parseClauses_repr`;
    - the six-state grammar automaton `syntaxStep`, its residual predicate `SyntaxSuffix` with
      `syntaxSuffix_cons`/`_nil`/`_run` (`SyntaxSuffix q x ↔ x.foldl syntaxStep q = 4`), and
      `syntaxOK` with `syntaxOK_spec : syntaxOK x = (parse x).isSome`;
  - `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` (a head confined to an integer interval visits
    at most its cardinality), moved from `Build/Zone.lean` to `Build/Catalog.lean`, which is in
    `TQBF`'s closure. Do not import `Build/Zone`.
- **Do not cite** any B4a declaration, anything sorried (`TQBF_PSPACEHard`, `TQBF_PSPACEComplete`,
  `ConfigGraph`'s three summits, `Constructible`'s two), or `Build/Zone`.

## Ground rules (binding)

1. **File ownership.** Only `ClassPSPACE/TQBF.lean`, and in it only: this target's body; a flagged
   Fill appendix in its docstring; the status text of rule 3; and new `private` declarations, all
   in the one block between `def TQBF` and the target's docstring. List every new declaration with
   its role. A lemma that genuinely belongs in a shared file is written privately, flagged in
   `REPORT.md` as a promotion candidate, and promoted by the maintainer at integration
   (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration, **B4a's 119 privates and
   `exists_adjacency_codec_cnf` included**: no renames, re-signatures, restatements, body changes or
   attribution edits. Docstrings stay. A flagged **"Fill appendix"** on the target records the three
   sanctioned refinements and your record layout.
3. **Status text.** Only these two changes, each flagged:
   - the module docstring's "Main results (three phase-P4.3 statements remain sorried)" becomes
     "two";
   - the target's "spec, fill pending" tag becomes "proved".

   Leave the hardness and corollary tags alone. No new public declaration.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. The route is in `TQBF`'s closure, checked by reading the import lines:
   - `TQBF` → `Build/CfgRecord` → `Catalog`, `SymbolLift`, `InputCall`;
   - `InputCall` → `CounterLoop`, `Seam`; `CounterLoop` → `Scan`; `Seam` → `Embed` → `Simulation`;
   - `TQBF` → `Inclusions` → `SpaceClasses`, `ClassNP/SAT`, `MeyerTableau`;
   - `TQBF` → `QBFEncoding` → `QBF`, `CNFEncoding`, `Encoding`.

   No TCSlib import may be added. A Mathlib import is allowed only if a needed lemma requires it;
   flag it.
7. **One proof per shared argument.** Cite the landed rows; never re-walk a landed contract inside the
   target. Never write a second loop host, scan trace, input fold, rewind, seam, emission chain,
   field-layout or `mealyRun` lemma for something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report `TQBF.lean`'s final
   line count and its public and private declaration counts, and your block's own counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md` states
   which `private` helpers remain `sorry` (each with a literal "Proof sketch"), and whether the
   target is proved modulo them. A partial is expected and fine; an unreported gap is not.
10. **Binary decider.** `M : FinTM Bool` with `Bool` work tapes. A rich alphabet would bring in
    R8.0, the mandatory R8.5d foreign-input validation and `alphabet_reduction_spaceUsed`
    (design §12.8a §0). None of these is needed here, so do not use one.
11. **Sanity cases, executed** (`decide`, `rfl` or `simp`, in an evidence file `B4MemSanity.lean.txt`
    that `import`s `TQBF`). Since your automaton is private, state each case through your target's
    semantics or through a public restatement in the evidence file.
    - A13: `pairEncode [] [true, false, false, true] ∈ TQBF` (the trailing bit takes the fallback),
      and `pairEncode [] [true, false, false] ∉ TQBF` (one empty clause, complete and false).
    - Free variables: `QBF.encode ⟨[], [[(0, true)]]⟩ ∉ TQBF` and
      `QBF.encode ⟨[], [[(0, false)]]⟩ ∈ TQBF`.
    - `[] ∈ TQBF` (pair-decoding failure).
    - One true and one false two-quantifier formula, for example
      `∀x₀ ∃x₁ (x₀ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁)` true and `∃x₀ ∀x₁ (x₀ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁)` false.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/ch34-b4-mem-screen-base.txt`: **1,472 declarations, 871 pairs, 297,548 characters**.

```sh
# population: audits/evidence/fills-5/ch34-b4-mem-screen-population.txt (the owned file, every file the route reuses, and every hazard below)
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/ClassPSPACE/TQBF.lean \
  TCSlib/Complexity/ClassPSPACE/Games.lean \
  TCSlib/Complexity/Formulas/QBF.lean \
  TCSlib/Complexity/Formulas/QBFEncoding.lean \
  TCSlib/Complexity/Formulas/CNF.lean \
  TCSlib/Complexity/Formulas/CNFEncoding.lean \
  TCSlib/Complexity/ClassNP/SAT.lean \
  TCSlib/Complexity/ClassNP/Tautology.lean \
  TCSlib/Complexity/SpaceComplexity/Inclusions.lean \
  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean \
  TCSlib/Complexity/SpaceComplexity/Basic.lean \
  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean \
  TCSlib/Complexity/TuringMachine/Encoding.lean \
  TCSlib/Complexity/TuringMachine/Simulation.lean \
  TCSlib/Complexity/TuringMachine/Build/Convention.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/Scan.lean \
  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean \
  TCSlib/Complexity/TuringMachine/Build/InputCall.lean \
  TCSlib/Complexity/TuringMachine/Build/InputLength.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Build/Embed.lean \
  TCSlib/Complexity/TuringMachine/Build/Loop.lean \
  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean \
  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean \
  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean \
  TCSlib/Complexity/TuringMachine/Build/Zone.lean \
  TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean
```

- **No new cross-file pair** with an owned-block declaration on one side, except a pair this brief
  pre-discloses (measure it and report it).
- **Known hazards:**
  - **`ClassNP/SAT.lean`'s private CNF machinery.** Never copy:
    - the syntax automaton and its proofs (`satSyntaxStep`, `satSyntaxSuffix*`, `satSyntax_spec`,
      `:332–457`);
    - the one-way scanner (`satScanTM`, `satScan_*`, `:459–537`; use R8.5d's `inputFoldTM`
      instead);
    - the streaming evaluator (`SatEvalControl`, `satEvalQ`, `satEvalAction`, `satEvalTM`,
      `satEvalCfg` and the `satEval_*` lemmas through `satEval_computes`, `:541–1000`). Your
      evaluator is composed from §12 rows (route 3), never a transcribed table;
    - `sat_parse_repr*` (`:239–329`), which duplicates `Tautology.lean`'s `taut_parse*_shape`
      (`:247–332`): one mirror pair already exists.
  - **B2b's certificate cycler** (`SpaceComplexity/Inclusions.lean`). Never copy its host, answer,
    anchor and rewind tables (`b2b_answerTM`/`_run`, `b2b_anchorTM`, `b2b_rewindTM`/`_run`), its
    ledger (`b2b_ledger_bound`, the head-interval cardinality step inside `b2b_host_contract`), or
    its packaging (`b2b_mem_PSPACE_of_ledger`, `:457`). Use `FinTM.emit_halts`, `FinTM.timed_rewind`
    and `space_poly_subset_PSPACE`; a one-line packaging of your own is fine. Measure it.
  - **Catalog's private scan trace.** `mealyRun_append` and `mealyRun_length` (`Catalog.lean:12262/12282`)
    are private. Prove your odometer's `scanResult` lemma by your own induction on the record word.
    If you find yourself restating either, stop and flag it as a promotion request instead.
  - **The input-seek idiom.** `InputCall`'s private seek machine (`inputSeekMachine`,
    `inputSeekStep`, `inputSeekRewind` and their lemmas, `:140–260`) and `InputLength`'s counting
    helpers are models, not sources. Your round machines are your own hand tables over the Catalog
    step lemmas.
  - **Game recursion.** `Games.lean`'s `positionValue`/`winner_of_value` has the `truthAux` shape;
    write your walker's correctness induction against `truthAux` directly.
  - **The record odometer.** `RecordTable.lean`'s carry odometer for `recordNextTM` is in flight and
    invisible to your base. If a pair appears at integration, the maintainer factors it.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair, measured).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-b4-mem.txt`. It has **73 modules**: the upstream closure
  of `ClassPSPACE/TQBF.lean`, plus every module downstream of it (`ClassPSPACE`, the facade), at the
  issue tree.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-b4-mem.txt )
  ```

  **Base sorry-warning set, 8** (`audits/logs/ch34-b4-mem-base-sorries.txt`, one entry per declaration). Yours:
  `ClassPSPACE/TQBF` 1 of its 3 (`TQBF_mem_PSPACE`). Record the base list by name first. S1b and B3a
  own two modules of your closure, so report any difference from what has landed by your base.
- **Final checks:**
  1. Your owned module: zero errors, and exactly two sorry warnings (`TQBF_PSPACEHard`,
     `TQBF_PSPACEComplete`). For a partial, add your rule-9 helpers.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**8 − 1** for a complete delivery).
  3. Re-run the pre-ship probe `audits/evidence/fills-5/B4MemPreShip.lean.txt`: 0 errors.
  4. Run your sanity evidence (ground rule 11): 0 errors.
- **Axiom prints** for the target: exactly within `[propext, Classical.choice, Quot.sound]`, with no
  `sorryAx` (proved modulo: none).
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/ClassPSPACE`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `SpaceComplexity/Constructible`: spaceConstructible_logSpace, spaceConstructible_linear
- `SpaceComplexity/ConfigGraph`: NSPACE_subset_exp_dtime, NL_subset_P, polyTimeReducible_of_mem_NL

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 1/1, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; the Fill appendix (refinements (i)–(iii), your record
      layout and transducer); both status updates.
- [ ] The space ledger: each tape's head interval and the final constant `c'`.
- [ ] Requested shared lemmas and escalations, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none" (or the
      pre-disclosed pairs, measured).
- [ ] File sizes; the final sweep tail; the re-run probe; the sanity evidence; the target's axiom
      print; the lint line. The diff touches only your block, the target, and the two status lines.

## Known pitfalls at this pin (hard-won)

- `TQBF` is a `Set`-valued `Language Bool` over `QBF.decode`, and `QBF.truth` is a `Prop`; the
  indicator is classical (`MultiTapeTM.indicator`, `open Classical`). Prove
  `indicator TQBF x = verdict` by `if_pos`/`if_neg` from your semantic lemma; never `decide` it.
- The fallbacks are `true`: `decode x = ⟨[], CNF.fallback⟩` when `pairDecode x = none`, and the
  matrix is `CNF.fallback = []` when `CNF.parse` fails. `truthAux [] qs σ i` is true for every
  prefix (by induction on `qs`).
- **Index conventions.** `serializeLit (v, p)` is `true^(v + 1) ++ [false, p]`: the run has `v + 1`
  cells, and the literal holds iff the variable's value equals `p` (`Clause.eval`: `a i == n`). Every
  literal begins with `true`, and so does every clause announcer: on the backward direction a run's
  left end is not delimited.
- **Free variables.** `truthAux` binds variable `i` by `Function.update` from the all-`false` base.
  A lookup at `v ≥ m` must read `false`. If your head walks off the record word into blanks, the
  return trip cannot rely on a delimiter scan started from the blank region.
- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; `0` and `|input| + 1` are the clamped blanks.
  `inputFoldTM_run_ofCfg` needs `inputPos = 1` at entry and restores it; `FinTM.timed_rewind` returns
  the input head to `1`.
- `pairEncode q m` doubles `q`: the quantifier bit `i` sits at input positions `2i + 1` and `2i + 2`,
  and the matrix starts at `2|q| + 3`.
- `counterLoopTM`: every round starts at the body anchor `a`, so data crossing rounds lives on tape.
  The final round's exit anchor is a single state, so the root verdict goes to a tape cell first. The
  fuel's value must exceed the rounds used, so that the escape fires below the value
  (`counterLoopTM_run_escape` needs `r₀ < value`). `counterLoopCfg` ignores the body configuration's
  state field. `counterWord` freezes at zero while the machine wraps.
- `simp` unfolds a machine's definition inside `counterLoopOrbit M …` arguments too, so terms stop
  matching. `generalize counterLoopOrbit M τ c r = o at …` first.
- `∑ r ∈ Finset.range d, τ (orbit r) + counterOverhead w (d + 1)` parses as
  `(∑ …) + counterOverhead …`.
- `scanTM` transduces a **delimited** word: blank cells cannot be data, and its `δb` sees the cells
  right to left. Its accumulator is `A : Type`, and `ScanPhase A` needs `[Fintype A]`.
  `phaseHostTM`'s states `Σ i, Ph i` need `[Fintype I]` and `[∀ i, Fintype (Ph i)]`, and
  `DecidableEq` likewise. `FinTM` wants `State : Type`.
- `incrementTM` is fixed-width: `incFixed` returns `none` on the all-`true` word (the overflow
  contract; `Complexity.Meyer.incFixed_eq_none_iff`). Size the index word so that the overflow
  branch is unreachable.
- A structure update inside `runFrom` needs an ascription:
  `({c with state := some s, inputPos := 1} : Cfg k Bool S x)`.
- `omega` treats products and powers as atoms; use `ring` first to expose them. `decide` cannot
  evaluate `Nat.bits`. The linter needs a literal "Proof sketch" before every `sorry` (partials only).
- `CNF` here is `Std.Sat.CNF` (`TQBF` opens `Std.Sat (CNF)`).
