# External audit pack: 12.2c T2a, the record-table find universe fix and the B4 pre-issue promotion (five maintainer Lean changes)

Campaign: Arora-Barak chapters 3–4 (`AroraBarakChapters3-4Plan.md` §4e, "12.2c placement").
12.2c is the campaign's parallel cleanup track. It keeps every public name and statement unless
an item says otherwise, and each item gets a PR and an audit gate. This gate covers five small
maintainer changes, landed by PR on `integrate/fills-5`:

| # | Item | Change | Statement change? |
|---|---|---|---|
| 1 | **FAC-1** (`backlog.md`) | `TCSlib/Complexity/TuringMachine.lean` imports seven campaign files it was missing, each with a Contents entry: `Build/VirtualInput`, `Build/Zone`, `Codes2Tape`, `NondeterministicSpace`, `OracleAgreement`, `OracleFinite`, `OracleNondeterministic`. `Codes2Tape` and `Build/Zone` were not reachable from `TCSlib.lean`, so CI never built them (`policy.md`, "Exports"). Five stale "Statement phase" labels are refreshed. The colleague-owned `Build/EmitIter*` files stay out; they are reachable otherwise | no (imports and docs only) |
| 2 | **H-1** | The chapter-1 audit program `audits/programs/ch1-infra-BridgeExportAxioms.lean`, which had failed at every commit since `TMSAT_mem_NP` was proved, now expects all 12 of its targets to be admission-free, and passes | no (audit program) |
| 3 | **Item 6's prerequisite export** (plan §4d, item 6; user, 2026-10-10, from the RB5 review) | **New public** `Turing.embedEmitTM_tr` in `Build/Embed.lean`: the forwarding transformer's transition at the action level (below) | **yes: one new public theorem** |
| 4 | **Universe fix, user option (b)** | `Turing.exists_tableFindTM` (`Build/RecordTable.lean`) restated from `{Γ : Type*}` to `{Γ : Type}` | **yes: one universe restriction** |
| 5 | **B4's pre-issue promotion** (user: "Promote first") | `ClassNP/SAT.lean`'s private CNF parse-inverse lemmas and six-state grammar automaton become **12 publics** in `Formulas/CNFEncoding.lean` (namespace `Std.Sat.CNF`: `parse_repr`, `takeTrues_repr`, `parseLit_repr`, `parseClause_repr`, `parseClauses_repr`, `syntaxStep`, `SyntaxSuffix`, `syntaxSuffix_cons`/`_nil`/`_run`, `syntaxOK`, `syntaxOK_spec`). `SAT.lean` and `ClassNP/Tautology.lean` (whose five private `taut_*_shape` duplicates are deleted) now cite them. `MultiTapeTM.spaceUsedByTape_le_card_Icc` moves from `Build/Zone.lean` to `Build/Catalog.lean` with the same name and statement | **yes: 12 new publics; one public relocated** |

**Item 3's statement:**

```lean
theorem embedEmitTM_tr (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) (q : S)
    (inp : Option Symbol) (w : Fin k → Option Symbol) :
    ((embedEmitTM ι M).tr q inp w).inputTape = (M.tr q inp fun i => w (ι i)).inputTape ∧
      (∀ i, ((embedEmitTM ι M).tr q inp w).workTapes (ι i) =
        (M.tr q inp fun i => w (ι i)).workTapes i) ∧
      (∀ j, j ∉ Set.range ι → ((embedEmitTM ι M).tr q inp w).workTapes j = (none, 0)) ∧
      ((embedEmitTM ι M).tr q inp w).output = (M.tr q inp fun i => w (ι i)).output ∧
      ((embedEmitTM ι M).tr q inp w).state = (M.tr q inp fun i => w (ι i)).state
```

It is proved from Embed's private slot-inverse lemmas, so the slot search stays private.
`CookLevin/Hardness.lean`'s `clPlacedAction_eq` currently obtains this fact by unfolding R1's
private `embedSlot` with `change`. Item 13 will replace that by a citation.

**Item 4's reason.** The record-table continuation escalated (rule 4) that `exists_tableFindTM`'s
mandated route, a loop under `counterLoopTMVia`, cannot be instantiated at `Γ : Type*`:
`counterLoopTMVia` (`Build/CounterLoop.lean`) and `phaseHostTM` (`Build/Seam.lean`) take their
alphabet in `Type`. The agent reproduced this with a minimal probe (`Application type mismatch …
Type u … expected Type`). The user chose to restate the row rather than generalize the two hosts.
The generalization is recorded as the optional backlog item UNIV-1.

## Brief for the auditor

1. **Item 3, correctness and fitness.** Check that the statement says exactly what item 6
   requires: the source action on each selected tape, `(none, 0)` on every other tape, and input
   move, output and successor state unchanged. Check that it is true of `embedEmitTM` and sound
   for every `ι` and source. Check that it suffices for item 13. The attached probe
   `audits/evidence/12.2c-t2a/EmbedExportProbe.lean.txt`, appended to `Embed.lean`, derives the
   selector form that `clPlacedAction_eq` needs from the export alone. Say whether a single
   conjunction is the right public shape, or whether separate lemmas would serve consumers
   better.
2. **Item 4, consumers.** Confirm that restricting `exists_tableFindTM` to `Γ : Type` loses no
   intended consumer: S1b and Savitch instantiate it at `RecSym Q T : Type`, and no declaration
   cites it yet. Confirm that the rest of the row's statement is byte-identical, and that rows 14
   and 16 (still `Type*`) do not need the universe-zero hosts on their routes.
3. **Item 1, the facade.** Check that each new import is a campaign file, that the Contents
   entries describe their modules correctly, and that the refreshed status labels are accurate.
   The maintainer checks:
   - the extended facade elaborates;
   - all 15 `Complexity` root imports elaborate together with it;
   - no public name of `Codes2Tape` or `Build/Zone` collides with any other public name in
     `TCSlib` (49 names against 8,365).

   Challenge the coverage if you think it insufficient.
4. **Item 2.** Check the refreshed expectations against the current admission state, and that
   the program still tests what its header says.
5. **Freeze.** Apart from items 3 and 4, no public statement changes. Re-establish this from the
   bases and the patch (`audits/evidence/12.2c-t2a/`).
6. **Documentation.** Item 3's docstring sketch, item 4's flagged "Universe" paragraph, and the
   facade Contents.
7. **Item 5, the promotion.** Check that each promoted declaration states exactly what its private
   original stated, that SAT's and Tautology's other declarations changed only in the names they
   cite (`audits/logs/b4-promotion-freeze.log`), and that the relocated lemma's statement is
   byte-identical. Rule on the public names, and on whether Catalog's private `catalog_space_bound`,
   a special case of the relocated lemma, should be retired now or later.
8. Report anything else the records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

- **Elaboration.** These were checked read-only against a tip-consistent olean tree
  (`audits/logs/12.2c-t2a-checks.log`, `audits/logs/rt-find-universe-fix.log`):
  - `Embed`, with the export and with the appended probe: 0 errors (the two unused-variable
    warnings predate the change);
  - the facade, and the root's `Complexity` imports together: 0 errors;
  - `RecordTable`, with the fix: 0 errors, and its six open rows warn;
  - the H-1 program: PASS.
- **Replays** (user-run, fresh `.oleans`):
  - `audits/logs/12.2c-t2a-replay.log`: the downstream closure of `Embed` and the facade, 92
    modules, **0 errors**, with sorry warnings exactly the expected base;
  - `audits/logs/fills-5-replay.log`: the closure of `OracleSim`, `RecordTable`, `CodeSimulator`,
    `SAT`, `Tautology`, `CNFEncoding`, `Catalog` and `Zone`, including items 4–5. That is 54
    modules, **0 errors**. One out-of-campaign facade first failed to load a non-campaign
    `.olean` missing from the snapshot; a gap-closure run compiled that module and then the facade
    with 0 errors (see `audits/fills-5-integration.md`).
- **Axioms:** `embedEmitTM_tr` depends on `[propext, Quot.sound]`.
- **Lint:** 0 FAIL over `TuringMachine` (`audits/logs/12.2c-t2a-stylelint.log`,
  `audits/logs/fills-5-stylelint.log`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into `audits/12.2c-t2a-findings.md`.
The gate closes when it has zero blockers and zero majors.
