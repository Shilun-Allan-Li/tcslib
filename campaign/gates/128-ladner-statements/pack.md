# Gate128 — Ladner statement and reading phase

**Prepared for Codex audit. Not yet clear to merge: #249 — external audit pending.**
Seyoon alone dispatches, rules on design/debt and merges; no audit is dispatched here.
PR https://github.com/Shilun-Allan-Li/tcslib/pull/249; branch `codex/ab34-ladner-statements`.
BASE `9b5dcf46408db681bcbc721930ef2203fa6bc47d` / whole MAC8; audited HEAD `1096e50b4e105392737ec52939b1db0cdbd9316d`.
Final records/exchange pins and bundle SHA/section count are supplied by the published
exchange README and complete issued prompt. Frozen private preparation wording is
historical data; this pack and STATUS.md give the current remit.

## Surface and authorization

The user selected Codex for this round, overriding the template’s generic different-vendor sentence. This is the approved statement/reading phase, with six direct mathematical admissions intentionally retained. The separately pending SAT reader and quantified preparation/numeric/memo premises block the identified fill route, not statement preparation. No new host/API/import/home/route/debt decision is inferred.

PLAN Track3(c),(f), the recorded LD1–7 decisions, and `LADNER-design.md` supply the approved definitions/statements and planned `Diagonalization/Ladner.lean` home, `Complexity` namespace, necessary readings and facade wiring. The design note was recorded before source. No separate new LD10 ruling is invented for that planned layout. An optional seventh bounded-padding theorem was not added. No proposed SAT verifier reader or extra iterator import was applied.

Only two Lean paths change:

- NEW `TCSlib/Complexity/Diagonalization/Ladner.lean`, 17 authored public declarations;
- `TCSlib/Complexity/Diagonalization.lean`, the authorized Ladner import and module documentation/Contents wiring.

The new file is genuinely absent at BASE. There is no invented empty source or BASE blob. Tracked `.lean` paths are 1,003→1,004; the full map preserves unchanged nested/non-build paths too, so this is not a count of replay modules. After removing only the authorized import from the facade's comment-stripped code, its old code/import order is exact BASE; it had no authored declaration surface. The umbrella `TCSlib.lean` is byte-exact and its existing Diagonalization import exposes the new module. No unrelated old Lean blob changes.

Actual owner SHA256 is `166c77cc4d86b0ae1a4e2d32967628cc5f3f4710c7ec5fc0cedbde5c75333311`. Its entire comment-stripped formal code string is exact to the string extracted from the frozen v2 prototype (`Ladner-v2.lean.txt`, file SHA256 `56c999de7f9a86a9d67cf4de3e567381fc448d2f798435602a99d79783bb3a6a`); this is a file hash, not a Git revision. The substantive difference is module/declaration prose stating the approved conventions. All six mathematical holes remain.

## Complete authored inventory

All names below are in namespace `Complexity`. Source and full compiled types, universes, owner/kernel names, privacy/kind, simp/unfold flags and complete AX sets are supplied for all 17; this is not a generated-constant/global census.

| Role | Names | Status |
|---|---|---|
| Four new definitions | `padSAT`, `ladnerMachine`, `ladnerH`, `SAT_H` | Standard axioms only |
| Six interface readings | `mem_padSAT_iff`, `padSAT_congr`, `ladnerMachine_eq`, `ladnerH_eq`, `ladnerH_le`, `SAT_H_eq` | Proved, standard axioms only |
| Six mathematical targets | `ladnerH_polyTime`, `SAT_H_mem_NP`, `ladnerH_bounded_of_mem_P`, `ladnerH_unbounded_of_not_mem_P`, `SAT_mem_P_of_padSAT_NPHard`, `SAT_H_intermediate` | Six direct intentional `sorry` bodies |
| Existential packaging | `ladner` | Uses the admitted `SAT_H_intermediate`; also has sorryAx transitively |

Thus ten authored definitions/readings are standard-only, while exactly the six targets and dependent packaging have sorryAx. The packaging theorem is not an independently proved Ladner theorem. No omitted private/generated type is promoted to exact equality. There is no compiled BASE ABI comparison for an absent owner.

`padSAT h` comprises a SAT word ψ, followed by a false separator and `|ψ|^(h |ψ|)` true bits. `ladnerMachine i` uses the existing uniform code scheme on `Nat.bits i`. Strong recursion defines `ladnerH n` as the least index strictly below `log₂(log₂ n)` passing every bounded acceptance test on words of length at most `log₂ n`, otherwise the cap. The membership test uses only earlier padding values; proved readings identify it with the global padded language and bound H by the cap. `SAT_H` is exactly `padSAT ladnerH`.

## Source fidelity and conventions

Use the full recorded design/source check and linked primary sources. The author-linked available book is a January 2007 draft, with a different theorem number; the older Duke chapter also has different numbering. The 2009 contents/assignment support the campaign's Theorem 3.3 location. Exact2009 Exercise 3.6 part(a)/(b) wording remains unverified. Public docstrings use the approved [AB09, Theorem 3.3 and its proof] fallback, not a claim that those exercise parts were checked. No private book PDF/page images are bundled.

Review these declared choices rather than silently replacing them:

1. The short-input test is acceptance equivalence `M_i.ComputesInTime x [true] (i*|x|^i) ↔ x∈SAT_H`, not a total Boolean output within that deadline. At empty input the indexed deadline is zero; zero-time acceptance and padded-language membership are both false. A total-output test at the same clock would be wrong.
2. The enumeration uses the existing uniformly timed `expCode`, avoiding unbounded per-code simulator constants. Its infinite padded-index/normal-form facts remain fill obligations.
3. Padding is the literal final-false separator with a true unary suffix, and logs are floor `Nat.log 2`.
4. SAT retains its total CNF-decoder convention: malformed words decode to a satisfiable fallback and are in SAT. A later verifier must preserve that convention.
5. LD6 uses NPHard, a weaker premise than NPComplete, yielding the approved stronger theorem. The general h premise includes polynomial-time bits of h and eventual divergence, not monotonicity or mere ordinary unboundedness.

## Actual replay and precise metadata lineage

Root's actual Nlad2 replay at audited 1096 passes **2/2**, 0 failures, static 0 mismatches / **6 direct admissions**, whole MAC8 **895→896** without splicing. Static admission counts are scoped to the two replayed modules; no whole-snapshot admission census is claimed. The output adds only the Ladner object, rewrites the facade object and preserves all other 894 old object hashes. The new owner has six warning rows; the facade has none. The standard replay deliberately excludes the umbrella root per maintainer workflow; root source/export is captured but no umbrella elaboration is claimed.

The complete Nlad2 request/RESULT, module logs, source/object maps and helper inputs are retained in `review/evidence/actual-validation162/inputs/passed-Nlad2/`. The independent MAC8 receipt, all 895 object hashes and1,003-source map are also present. Every replay input hash equals the adopted MAC8 anchor.

Fresh imported metadata for all 17 selected constants and the proof checks actually ran at 63eb/whole Nlad1. Their original pins are preserved. Current 1096 changed only one facade documentation word to remove scanner false positives. The owner bytes and object are exact: Nlad1/Nlad2 owner olean SHA256 `6b7b2adeb3182d7c610c75d166eebb66a3cad3ae5752e8cf4a6a44a88ae2fc96`. All 115 existing internal TCSlib project owner-import source blobs and objects are present and exact across BASE/63eb/1096 and MAC8/Nlad1/Nlad2; the facade is outside that closure. This supplies an explicit transport argument, not a relabelled fresh 1096 execution. Whole MAC8 and Nlad1 object maps are exact before and after the five plain checks. The later complete Nlad2 output map matches its passed replay. No plain metadata/control execution is relabelled as importing Nlad2.

Metadata uses full raw Expr representations, not pretty-printer width or fingerprints. Every selected raw type, universe, name/owner/privacy/kind and default-simp/unfold flag is supplied. AX names are complete for the 17 selected constants. No theorem proof value is rendered, and no full generated/global type, AX or simp equality is inferred.

## Full owner TCSlib boundary and effective controls

The collector independently seeds all 17 selected authored roots with their full type and value. Within its TCSlib/own-owner scope it follows constant types and same-owner definition values; foreign TCSlib definition RHS stays opaque. Every encountered theorem is type-only: its proof value is not recursively followed, including same-owner generated theorems. Core/Mathlib heads are outside this guard collector. WORKFLOW §2 lines 71–80 permits Core/Mathlib reduction by `rfl`/`decide`/`show` while forbidding explicit definition arguments to `simp`/`rw`/`unfold`; the separate full argument review covers those sites too. See `review/bindings/RULE10-SCOPE-CLARIFICATION.json`. Within the standing WORKFLOW §2 rule-10 scope it reaches exactly nine other-file TCSlib ordinary heads:

`Complexity.NP`, `Complexity.NPComplete`, `Complexity.NPHard`, `Complexity.P`, `Complexity.PolyTimeComputable`, `Complexity.SAT`, `Complexity.expCode`, `Turing.CodeTM.toFinTM`, `Turing.FinTM.ComputesInTime`.

The six recorded theorem boundaries comprise four authored theorems that are also independently seeded roots, plus two generated local theorems: `padSAT_congr._proof_1_1` (the separator-length `omega` subproof) and `ladnerH.eq_1` (the own strong-recursion equation). Their types are traversed. The raw 146 definition rows, literal source origins and explicit arguments disclose no additional ordinary other-file TCSlib head. The nine-head guard is installed at line50 before the first owner header; both auxiliaries are generated later inside that actual section. `review/bindings/THEOREM-BOUNDARY-REVIEW.json` preserves every boundary row and exact source origin. No recursive theorem-proof closure or full generated-proof-value census is claimed.

All eight source homes are fully captured. Projection/abbreviation exclusions are explicit; no projection seal is claimed. There are no default-simp definition rows among these heads. The existing public `CodeTM.toFinTM_k` field-simp is additionally disabled in both variants.

Native and sealed inputs contain all 17 literal owner declarations and the six private evidence checks, with the guard before every header/definition/body. They differ only by the nine-head local irreducibility line. Both actual runs pass with 0 errors and exactly 6 intended sorry warnings. All six edge proofs have standard-only AX sets. The six distinct checks execute in both variants; they were not merely left as unexecuted candidates.

For every head, the same direct point/delta and abstract equation goals give **18 effective pairs**: 18 distinct kernel-checked positives and precisely the same 18 intended sealed refl failures (actual Lean exit 1/errors 18). All sources, raw logs, command/exit/count/hash receipts and uncapped definition/control rows are supplied. The argument review covers every actual definition/reading/packaging proof and explicit simp/rw/unfold/change argument. Own ladnerH unfolding is allowed; other-file/Core/Mathlib definitions are not passed as rewrite/simp/unfold arguments.

The six checks cover empty-word exclusion, padded membership and SAT_H nonemptiness conditional on an explicit SAT witness, H(0)=H(1)=0, and the published zero-time obstruction. Conditional witnesses are not an unconditional SAT_H≠∅ proof. Preserve exponent 0/0^0, caps near 4/16, malformed inputs and last-false parsing as semantic audit cases.

Attempts 01/02 were interrupted shared-lock-access queues, not source failures or PASS. The superseded overbroad foreign-RHS collector is excluded. Actual jobs 03–07 used the authorized shared lock sequentially, one own job under local3/machine5/j4/nice10, no olean output. The complete prior prototype132 and readiness149 packets retain their failed/debug and narrower four-head/unexecuted-probe history; only actual validation162 supports current proof-boundary/edge claims.

## Quantitative host route remains open

The statement phase does not complete or approve a fill route. The pending `SAT_exists_linear_verifier` proposal is not used by the source; it blocks the identified sharp-SAT route, not these approved headers. Other explicit numerical/preparation/memo premises also remain unresolved.

Existing successful conditional probes have these limits:

| Existing route transfer | Actual prior check | Still required |
|---|---|---|
| Uniform bounded acceptance plus composition | exit0/error0/sorry0 | Query-preparation machine, its clock, polynomial bound on the **numeric** deadline cost and final envelope |
| Sharp SAT search via `mem_P_iff`/`exists_proj_decider 1 1` | exit0/error0/sorry0 | A P verifier V with exact certificate length `|x|+1` and the full SAT equivalence |
| Generic FP iterator/readout composition | exit0/error0/same six main holes | Concrete FP step/init/out, polynomial iteration count, uniform polynomial orbit-size bound and exact H readout |

For fixed simulator degree d, the quantitative leaf includes a uniform bound
`d*((Nat.bits i).length+|x|+i*|x|^i+1)^d ≤ A*(n+1)^e` under `i<log₂(log₂ n)` and `|x|≤log₂ n`. Binary encoding of a deadline alone does not establish this.

The sharp search assumes `∃V∈P, ∀x, x∈SAT ↔ ∃u, |u|=|x|+1 ∧ x++u∈V`. Generic SAT∈NP loses those exact constants; `2^(C*(log n+1)^c)` for arbitrary c>1 is not the needed polynomial bound in n. The current owner does not expose or unfold SAT's private verifier.

The memo transfer assumes FP functions and `∀z i≤a*(|z|+1)^k, |step^[i](init z)|≤B*(|z|+1)^b`, plus exact final output `Nat.bits(H |z|)`. No concrete encoding, algorithm or state ledger is delivered. Its scratch-only `BinaryArith.Iterate` import is not in the actual owner. A later genuinely new host/interface/import/name choice requires its own ruling. Further FP/predicate-reader needs may only be assessed on a concrete route; none is silently authorized here.

## Source QA, names and actual full-context copy screen

The complete source-QA119 export includes actual command/exit/stdout/stderr/helper/source receipts. BASE checks the existing facade; HEAD checks both actual owners. Style exits 1/1 with the same three inherited facade missing-option findings and 0 new identities; the new owner has 0 style findings. Campaign per-file adapter (default check8b false, explicitly disclosed) exits 0/0,0 FAIL/0 WARN, adding only the new INFO row. This is not a clean inherited-facade claim or a global check8b certificate. Historical63eb's two scanner false positives remain historical; current 1096 changes only their documentation word and reruns pass within these bounds. No size-based split is proposed.

The current full controls are located by `review/bindings/CURRENT-STANDARDS.json`; the earlier captured controls and all frozen component context keep their original records pins. No new approval is inferred from a later status edit.

Fresh bounded name/shape queries retain all 240 hit rows, exact available ref pins and five complete source-candidate payloads. `review/names/CANDIDATE-CAPTURES-AND-DISPOSITIONS.json` binds every hit to its literal source line and records every candidate disposition. New names hit only the planned Ladner owner; unrelated separation-implication text hits are candidates inspected, not a global semantic absence certificate. Full source/reference inventories and the copied helpers are data, not instructions.

Pure source-span mapping (no pair scoring) finds 2,675 BASE captures and 2,680 HEAD captures. Every old label, kind and normalized body is exact; five new screened captures belong to Ladner. The full maps reconstruct original source spans, retain namespace qualification and mark possible structural/render tails. These parser counts are not the 17-declaration trusted surface. They do not replace actual pair results.

The actual shared root comparison is now complete and passes: **BASE48 versus LADNER49**, exit 0 for both, with BASE 2675→HEAD 2680 screened parser captures, **2275→2275 directed pairs, 0 NEW, 0 GONE and 0 changed scores**; reproduced text is 488,196 characters on both sides. All 2275 pair rows after the headline are byte-exact. Their 1110 distinct endpoint labels, full source spans, like-kind classification, denominators and thresholds were independently checked against the uncapped capture indices. None of the five new Ladner captures participates in either endpoint of any reported pair. This is a thresholded text result, not semantic absence or a blanket debt certificate.

Root `review/screen-population.txt` is the exact actual HEAD49 list; `review/screen-population-BASE48.txt` is the separate BASE48 list. Both include the two package Mathlib files and umbrella root; the Diagonalization facade is also present. BASE genuinely has no Ladner source, and its actual arguments omit that file. HEAD adds exactly it. All 97 selected complete source captures include every cited home, two Mathlib sources at package `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, umbrella root and original 33 context. No empty BASE file or old 33 comparison is substituted.

The actual LADNER raw output is 220,748 bytes, SHA256 `0b56da2474b29ff6e8835908c0235c480500a109994724477a0bd4be8643a6fe`, actual elapsed 1351.124790625181 seconds, exit 0, with source hashes unchanged. `review/screen/actual-root-run/` retains complete REQUEST/driver/RESULTS/COMPLETE/progress, all three raw outputs and both actual pairdiff outputs. `review/screen/ACTUAL-RUN-BINDING.json` verifies all 151 actual shared-driver source/tool inputs through full captures or exact aliases. The unrelated NAT phase is preserved only for runner-input completeness, not promoted into Ladner source/replay/AX evidence.

`review/screen/PAIR-COMPARISON.json` retains every actual directed pair and exact score; `review/screen/DISPOSITIONS.json` records complete empty NEW/GONE/changed-score inventories and their limits. No existing debt family is discharged, old proof exempted, new debt exception granted or global absence asserted. Keep the current duplication ledger’s family scopes, owners and resolution windows. The earlier 47/48 idle waiter was terminated before any screen and remains explicit historical preparation, not a result; its exact inputs/disposition are under `review/screen/historical-waitonly47-48/`. This preparer started no Lean or screen job. All conclusions above derive from actual root output and linear source/pair validation.

## Auditor remit

Restate all four definitions independently, compare the accepted conventions to the source check, and argue why each of the six admitted statements is literally true or report a concrete counterexample/missing premise. Check recursion well-definedness and the three routine reading proofs as interface work, not six-hole fills. Check at least three degenerate instances logically against the equations, including n=0/1, i=0/zero deadline, empty prefix/0^0, malformed SAT words and nonmonotone but eventually diverging h. Preserve the distinction between eventual divergence and ordinary unboundedness.

Verify actual source/facade freeze and absence-at-BASE, full 17 compiled metadata/AX bounds, exact nine-head TCSlib complete-owner guard placement and all 18 paired control identities, explicit definition arguments and the final exact-population screen. Do not turn the conditional host probes into completed premises or infer a new API/import decision. Report unapproved copies/debt at TEMPLATE severity; no blanket approval, fill readiness, global absence, gate closure or merge clearance follows.

Use `# | Severity | File · declaration | Claim | Evidence/counterexample | Proposed fix`, then a verdict with counts. Put the required four definition restatements, six literal-statement assessments and adversarial checks in table evidence rows even if no defect is found; factual assessments may be marked note and counted. A bare PASS does not supply the required reasoning. Identify unresolved evidence/source gaps explicitly.

**Deliver your findings as a downloadable file named `gate128-ladner-statements-findings.md`** (the findings table and the verdict line, no other wrapping), and also paste its content in your reply. Do not push, edit source/records, merge, dispatch another auditor or fill mathematics.

## Independent provenance and current context

The exact-head two-module replay passes static0 mismatches/6 deliberately admitted
mathematical obligations from the ENTIRE MAC8 snapshot. All895 input hashes equal the
independent adoption anchors and remain unchanged; output896 adds the new Ladner
module, rewrites the facade and preserves the other894 old object hashes. The six direct holes and the theorem packaging their final conclusion retain
their disclosed sorryAx dependency. The ten definitions/readings and six private edge
probes use only standard axioms. There is no claim of mathematical completion or a
new root-facade elaboration. Necessary quantitative simulator and memo/state bounds
remain external fill obligations, not approved new public host interfaces.

The three independent public anchors live under
`campaign/status/2026-11-08-mig1-merge/`: receipt.json, object-hashes.json and Lean-tree.json.
Exact checking helpers, toolchain/package lock, sanitized environment example and local
slot context are included in reproduction-tools/. Recorded executions retain their
original source/snapshot pins; no frozen historical receipt is relabeled a new run.

Campaign changes after MAC8/9b5 are records only. Later source merges require the standing
current-tree validity check; no unmerged proposal is assumed landed. External gate closure
and Seyoon's merge remain required. No global copy absence, all-owned-type equality,
future-copy permission, blanket debt waiver or new design ruling follows.

`PATH-MAP.json` maps every frozen logical payload to its canonical record path. Lean
captures remain `.lean.txt` data and must be restored through their source indexes in
fresh scratch. Package Mathlib sources belong to the pinned dependency, not this repository.

## Independent publication peer

`publication-peer/findings.md` and its complete31-payload verification component report
0 blockers/0 majors,1 resolved wording minor and4 notes. Exact encountered-theorem proof
boundaries and bounded generated-helper source inspection are explicit above. The peer
verifies all777 frozen payloads, source/ABI/guard/replay/QA/pair claims within their actual
limits; its separate literal-target and edge assessments are source reasoning, not new
executions, mathematical fills or an external gate verdict. Final exact mixed/archive
publication checks and pins remain separate root-owned actions.

`root-preparation-notes.json` records two private adoption fixture stops caused by checking
an intentionally absent campaign source path instead of its PR Git blob; the corrected
mixed lookup verifies new Lean source at audited HEAD and records files at the records
pin. No frozen input, library source, proof check, replay or copy comparison was altered.
