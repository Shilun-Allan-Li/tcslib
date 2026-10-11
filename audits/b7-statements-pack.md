# External audit pack — B7 statement mini-phase (P4.4b): input access, the oracle-input simulator, query reshapings

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). B7 is
the deterministic-logspace cluster. Its targets were stated and audited at
phase P4.4: `audits/ch4-p44-findings.md` and `audits/ch4-p44-resolutions.md`,
attached. The targets are:

- `ImplicitlyLogspaceComputable.comp` (composition, [AB09] Lemma 4.17(1));
- `LogspaceReducible.trans`;
- `mem_LOGSPACE_of_logspaceReducible` (Lemma 4.17(2));
- `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE`;
- `multLang_mem_LOGSPACE`.

**Why a statement mini-phase.** Fill research found that the received
logspace program layer (`SpaceComplexity/Machines/*`, a colleague's audited
compiler, `LogProg.compile_space`) cannot host the audited routes. Two
capabilities are missing:

- **G1, oracle-served input.** A call presents its callee with a
  *physically* laid-out virtual input (the whole host input, or its leading
  `1`-run, plus register words). Nothing serves a callee's input symbols
  through further calls.
- **G2, random access to a non-unary input.** The ARM input instructions
  presuppose unary-first inputs.

This PR (#24, `integrate/b7-statements`, commit `db99af44`) lands the
missing contracts as **statements with sketches**, plus proved helpers. It
records two **route changes** to audited statements in
`audits/ch4-p44-resolutions-addendum.md`:

- T3 goes direct, via the new N2;
- `comp` is derived from N2 and N4.

**No proof is under audit except the small proved helpers. What you audit is
the statements:** are they true, adequately strong for their consumers, free
of vacuity, and well placed? The gate closes on zero blockers and zero majors.

## What is proposed (verify)

| File (new unless noted) | Declarations | Status |
|---|---|---|
| `Logspace/InputAccess.lean` | the input-read fragment `LogProg.readIn_run` (exits in state `ex x[i]?` with everything else restored; head range `[-1, \|bits(\|x\|+1)\|]`, independent of `i`); **N1** `implicitlyLogspaceComputable_id`; `inputBitLang`/`inputLenLang` and their membership corollaries; `LogProg.vword_whole₁`; `indicator_indexLang_pairEncode` | 2 sorried (`readIn_run`, N1); the rest proved |
| `Logspace/PreimageHost.lean` | the oracle-input simulator: the program `LogProg.OIS.prog M` (**defined**), with run contract `OIS.run` and space contract `OIS.compile_decides`; the clamping table `OIS.nextPh`; **N2** `mem_LOGSPACE_preimage (hf : ImplicitlyLogspaceComputable f) (hC : C ∈ LOGSPACE) : {x \| f x ∈ C} ∈ LOGSPACE` | 3 sorried (`OIS.run`, `OIS.compile_decides`, N2); the program and table are definitions |
| `Logspace/QueryReshape.lean` | **N3** `implicitlyLogspaceComputable_dropIdx`; **N4** `ImplicitlyLogspaceComputable.compQ`; proved helpers: `dropIdx`, `dropIdx_pairEncode`, `compQ`, `compQ_pairEncode`, `pairEncode_ne_nil`, `mem_indexLang_compQ_iff`, `compQ_length_le` | 2 sorried (N3, N4) |
| `Logspace/Reductions.lean` (changed) | import `QueryReshape`; `comp`'s docstring corrected (its sketch claimed a received capability that does not exist) | statements unchanged; 4 targets still sorried |
| `Logspace/Mult.lean` (changed) | import `InputAccess`; docstring corrected (the cited parse toolkit reads only `⟨1ⁿ, ⟨u, w⟩⟩`; the acceptance condition is Q8's) | statement unchanged; 1 target sorried |
| `SpaceComplexity.lean` (facade) | the three new modules | — |

The derivations of the frozen targets from the new contracts elaborate in the
attached pre-ship probe:

- T3 is N2 at `C`;
- `comp` combines N2 with N4: the query languages of `g ∘ f` are preimages of
  `g`'s along `compQ f`;
- T2 and T5 are logic.

## Brief for the auditor

1. **Truth.** Blind-restate every sorried statement from its signature, then
   decide whether it is true as stated. The statements are N1–N4,
   `readIn_run`, `OIS.run` and `OIS.compile_decides`. Give the argument, or a
   counterexample. N2 is [AB09] Lemma 4.17(2) in preimage form; N1 is
   logspace random access.
2. **The fragment and the engine as reusable contracts.** These two are
   meant for later logspace programs: the PATH reduction's transducer, matrix
   indexing, and the NL side.
   - **`readIn_run`.** Is the frame clause ("everything else restored")
     exactly right? Is the head range right, including at `i ≥ |x|` and
     `x = []`?
   - **`OIS.run`.** It requires the oracle laws only on *genuine* queries:
     length at `i ≤ |v|`, bit at `i < |v|`. Is that both sufficient and
     necessary? Is the work-register range `±S` right, with `S` the space up
     to time `t` rather than up to the first halt?
   - **`OIS.nextPh`.** Does the clamping table match `moveInputPos` at both
     boundaries, including `v = []`?
   - **`OIS.compile_decides`.** Should its radius parameter `B` be a
     monotone space function instead?
3. **Adequacy.** Do N1–N4 suffice for all five frozen targets, by the
   routes in the addendum? Do they leave nothing implicit that the fill
   would have to invent, such as a missing length bound, an unstated
   canonicality, or the behaviour on malformed queries?
4. **The route changes.** Are the addendum's two route changes sound
   replacements for the audited P4.4 routes, and is the original statement
   gate's reasoning preserved where it still applies?
5. **Vacuity and degenerate cases.** Check, in particular:
   - each oracle and engine contract for vacuous satisfaction (for example,
     an empty language, or an engine whose run contract holds because
     nothing ever halts);
   - `f` constant, and `C` empty or everything;
   - `x = []`;
   - malformed `⟨x, bits i⟩` queries.
6. **Placement and naming.** The files are campaign-owned under `Logspace/`
   and add declarations to the colleague's `Complexity.LogProg` namespace.
   Is that acceptable, or should they take their own namespace? Is N1
   better stated as `ImplicitlyLogspaceComputable id` or as the two
   memberships?
7. **Docstrings.** Check the two corrected sketches, and every new docstring
   for accuracy. T3's docstring still describes the superseded `χ_C` route;
   say whether to correct it now or by a flagged appendix at fill.
8. **Duplication.** No new copy-text pair appeared (53 before and after).
   Is any proved helper a re-proof of a received lemma?
9. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Elaboration** (`audits/logs/b7-statements-sweep-{before,after}.log`): the
  8 new, changed and downstream modules exit 0 with 0 errors. The sorry
  warnings are exactly the 7 new statements plus the 5 existing B7 targets
  (and `Path`'s 2 and Immerman–Szelepcsényi's 3, unchanged).
* **Probe** (`audits/evidence/b7/B7StatementsProbe.lean.txt`): 0 errors, and
  no sorry of its own. It runs `readIn_run` on a concrete program and `OIS`
  on a concrete decider, and derives T2, T3, T5 and `comp`. Its axiom prints
  (`audits/logs/b7-statements-axioms.log`) show `sorryAx` only through the
  12 sorried declarations; the proved helpers lie within the standard triple.
* **Freeze** (`…-declfreeze.log`): no existing statement changed.
* **Lint** (`…-stylelint.log`): 0 FAIL, 0 WARN.
* **Screen** (`…-screen-{before,after}.txt`): 53 pairs before and after. The
  screen script is attached.
* **Inputs.** All new and changed sources, the received `Machines/` layer the
  contracts cite, `ImplicitPoly.lean` (the engine's template), and
  `SpaceComplexity/Basic.lean` are attached.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/b7-statements-findings.md`.
