# 12.2c T2a gate (five maintainer Lean changes): resolutions (CLOSED, round 1)

## Round 1 (2026-10-12): 0 blockers, 0 majors, 5 minors, 13 notes

The findings are verbatim in `audits/12.2c-t2a-findings.md`. The pack is
`audits/12.2c-t2a-pack.md`, with its 42-section bundle `audits/12.2c-t2a-bundle.md`. The five
changes under audit were:
1. FAC-1's facade wiring;
2. H-1's audit-program refresh;
3. item 6's export `Turing.embedEmitTM_tr`;
4. the `exists_tableFindTM` universe restriction;
5. the B4 pre-issue promotion: twelve CNF-grammar publics and one relocated lemma.

The auditor confirmed the following:
- **Integrity.** Patch reconstruction is byte-identical for all nine affected files (note 6).
- **The export.** It is correct, documented, and fit for item 13 as a single conjunction
  (notes 7–8).
- **The universe restriction.** It is authorized, byte-identical apart from the binder, and
  loses no intended consumer. Rows 14 and 16 need no analogous restriction (notes 9–10).
- **The facade's import delta and the H-1 program** (notes 11–12).
- **The freeze.** The only authorized changes are present: 13 new public names and one binder
  (note 13).
- **The promotion.** Each of the twelve promoted declarations matches its SAT original after
  normalization, and SAT's and Tautology's remaining code is identical (notes 14–15).
- **The relocation.** The relocated lemma is byte-identical (note 16).

The auditor also checked the parse-inverse and automaton facts exhaustively on all 131,071 bit
strings up to length 16.

| Finding | Disposition |
|---|---|
| 1 (minor): the facade/root coverage is overstated. `TCSlib.lean` has 16 `Complexity` imports, the check covered 15 (excluding `NPReductions`), and neither replay includes `TCSlib.lean` | **Accepted; the pack's wording is corrected here.** The checks covered the fifteen `Complexity` facades that have build products in the campaign snapshot, together with the extended facade and `ComputationalModels`. `NPReductions` (received, untouched by T2a) and the non-`Complexity` areas were not elaborated together with it. A whole-root elaboration needs every module's build product, so it is recorded for the next whole-tree replay, at the latest the campaign closure gate. |
| 2 (minor): Zone's public-declaration counts are inflated by two docstring lines matched as declarations. The comment-stripped count is 38 → 37, not 40 → 39, and the pre-promotion explicit population is 47, not 49 | **Accepted; the corrected counts are recorded here.** No statement or name is affected. Since the fidelity gate (finding 5 there), the name screens use a comment-aware, namespace-qualified enumerator (`scripts/vendor_afm26/namescreen.py`). Future freeze logs use comment-stripped enumeration. |
| 3 (minor): the fills-5 lint evidence predates the promotion commit and excludes `Formulas` and `ClassNP` | **Resolved by evidence.** Lint was re-run at the gate-close head over `TuringMachine`, `Formulas`, `ClassNP` and `Programs` (`audits/logs/gate-close-t2a-vendor-stylelint.log`): **0 FAIL** in all four. The warnings are file-size only. |
| 4 (minor): stale status texts. The facade replaced four, not five, "Statement phase" labels. It keeps "Spec phase: contracts stated, fills pending" for the construction library. Zone's header says every contract is sorried. "Are retired through the G3/G4 gate" should be future tense | **Resolved (comment-only).** The count is corrected here (four). The construction-library entry now says "Proved, and audited at the shared-infrastructure gates": `Build/Convention`, `Wrappers`, `Loop` and `Primitives` have no admissions. Zone's status section now states that everything except the two shift rows is proved, and that those rows are scheduled for retirement through G3/G4. The facade's Zone entry reads "are scheduled for retirement through the G3/G4 gate". |
| 5 (minor): "Zone, its only user" misidentifies the defining module as a consumer | **Accepted; corrected here.** The lemma was formerly *defined* in Zone. After the relocation, Zone has no code occurrence of it and keeps access through its `Catalog` import. At this commit its only code caller is Catalog's `catalog_space_bound`, derived from it under note 16. The fills-6 B4-membership delivery adds a second, in `TQBF.lean`. Zone's docstring still mentions the move. |
| 6–15, 17 (notes) | Confirmed. Note 17's wording is adopted: the fills-5 replay was successful **after gap closure**. |
| 16 (note): retire `catalog_space_bound`'s duplicated proof now | **Done.** The private lemma is now proved from `MultiTapeTM.spaceUsedByTape_le_card_Icc`, keeping its wrapper so that no caller changes. Catalog elaborates with 0 errors (read-only, at the gate-close head); the replay of this round covers its dependents. |
| 18 (note): regenerate the blueprint references | **Recorded** in `backlog.md` §5 (this commit): the SAT/Tautology blueprint pages still name the promoted declarations' old private names. They are regenerated at the next blueprint increment. |

**Gate CLOSED.** All five T2a changes are accepted. Item 13 (MIG-21) may now proceed.
