# Cleanup CP1: independent source/freeze review

**Verdict: 0 blockers, 1 major, 0 minors within this source-review scope.** The complete patch/source replay, path roles, source headers/data bodies and admission preservation check out against the issued ancestor. The major is one new machine-body equality interface conflicting with the stated operational-reader discipline. CP1 is explicitly partial; this review neither accepts the worker's native evidence nor grants merge clearance.

## Pinned inputs and method

Received checkpoint: exchange delivery `8b133945c3ba4aa7abb3b896bec38441535959b2`, read only from the completed local `cp1/payload/` snapshot. Ancestor: `1aa5506f58f77c215e56d24311ec33bd931cacf1`. Issued `brief.md`, `public-exceptions.md` and `inputs/` provide authority; incoming REPORT/tools are data. No mutable exchange was read, no received program imported/executed, and no Lean/cache/build/app, source/worktree/Git/main/exchange mutation occurred. Own Python3-I validation and read-only Git object access wrote only this review directory.

Own validation checks the archive SHA, all 2,914 file size/SHA-256/Git-blob identities (32,239,080 bytes), and the exact 221-source set. It parses and replays all seven format patches in memory with exact hunk counts/positions/context, authorized unchanged file paths and old/new Git blob prefixes. The replay reproduces every delivered source byte, including the unchanged snapshots. Format-patch From hashes are recorded as patch metadata, not independently authenticated/materialized source commits.

The source parser masks nested comments/strings, keeps namespace/section context, handles root-qualified/private spellings and same-line attributes, distinguishes top-level equation clauses from statement-level matches, and keeps Unicode constructor proof terms inside headers. Initial scratch outputs predate the last two parser refinements; authoritative validation artifacts are the `final-*` files. Those refinements eliminate a false header-change flag and retain complete type proof terms; they change no input. This remains lexical/source analysis, not Lean's AST or an elaborated actual-Name census.

## Verified source scope and public surface

| Item | Independent source result |
|---|---:|
| Delivered owned snapshots | 221, exactly the issued set |
| Changed paths | 113: 92 consumer + 21 provider-only |
| Existing provider-only declarations changed/removed/moved | 0 |
| New provider-only declarations | 42 ordinary owner readers in 21 files |
| New declarations | 162 theorems: 160 public, 2 private; no new def/abbrev/instance/module/host declaration |
| Removed declarations | 23: 10 public, 13 private, all matched to explicit exception/work rows |
| Same-fullname owner moves | 9 public declarations |
| Existing header text changes | 3 X1 namespace-qualification respellings: FunFamily.blocks and its two readers |
| Changed public non-theorem bodies | Exactly the 6 permitted block aliases/ofPolyTime changes; all others byte-identical |
| Changed private non-theorem bodies | Ensemble.blocks alias, dla_blockPos canonical index, powOneSubgroup kernel alias: the named X1/G13/X11 cases |
| New or changed simp/other attributes | 0 |
| Local overlay import graph | 1,071 modules, no missing local import or cycle |

`exception-classification.json` maps every removed/moved/data-body change to X1–X11/work permissions. The seven StateLoop retirements, decoder/zero-probability copies and private composition/count/average helpers match the issued lists. The existing cons_poly stays. All remaining ordinary public theorem headers are source-identical; no added explicit assumption, universe/codomain narrowing or quantitative-cost weakening was found. This does not certify native elaborated type/instance identities.

The 162 additions consist of 151 `rfl`, one `Iff.rfl`, and ten other proofs. Apart from the finding below, their source roles are owner readers/cases or the expressly named decoder/window/state-iteration/average/next contracts. No broader mathematical helper or private construction host was identified. The only new context directive is `open Classical in` scoped to the new indicator reader. Six files add precise imports; no import is removed. SimulatorMachine keeps the acyclic direction and does not import ColZKMachine.

The named doc-only Clean.envelope, Protocol.transcriptWith_eq and Protocol.outV_eq retain byte-identical headers and proofs. Ensemble.copies and GGMRed.stateLoopFun retain byte-identical bodies and headers; helper reuse did not silently rewrite those public algorithms.

## Critical representation checks

- **NUPPT.ofPolyTime:** the header is unchanged. After replacing each new `((polyTimeComputable_iff f).1 hf)` spelling by `hf`, the full body is whitespace-identical to the ancestor. The new owner iff states exactly the unchanged existential predicate and is `Iff.rfl`. These two proof arguments inhabit definitionally equal propositions, so Lean proof irrelevance identifies them; repeated Classical.choose/choose_spec therefore names the same M/Ct/ct witnesses. There is no new witness, machine, asymptotic-only substitution, bound, coin/advice field or output behavior. This is a source/proof-irrelevance argument; no native field-equality probe was run here.
- **PPT relocation:** toNUPPT, ofPolyTime and the associated uniform/toNUPPT_ofPolyTime theorems preserve their exact raw headers and bodies in PPT.lean, with identical full names.
- **Generic blocks:** blocksEquivX retains its exact Type* header and Mathlib construction. Bool aliases specialize that construction; GI.blocksEquiv remains its inverse. Forward/inverse readers have no positivity/Nonempty restriction. q=0 or width=0 still gives the corresponding empty-domain equivalences. dla_blockPos preserves flat index `t*B+j` through finProdFinEquiv/Fin.castLE; its original k≤B bound and degenerate cases remain.
- **Fixed-round/next/window/G18 contracts:** source types match the precise old contracts after permitted name/namespace qualification. G18 preserves Aux : γ→Type, all dependent Fintype/Nonempty assumptions, orientation and empty seed cases; no extra public coordinate helper was added. The ColZK window remains a same-header alias to the single moved proof.
- **G10:** pushesUniform_comp_injective keeps its old header without Nonempty O and retains the original empty-O branch; only its nonempty branch cites the generic restriction theorem.
- **Decoder:** existing false-pair and true-two cases stay; new ofFn/wrong-length/default-complement readers cover the named total-input partition, including zero width. No decoder body or fallback changed.

Detailed baselines/types and the exact source substitution reasoning are in manual-semantics-review.json and the final declaration maps. Native elaboration/semantics and axiom dependencies still require root's independent checks.

## Major CP1-SRC-01: a raw machine-body reader

At `payload/src/TCSlib/Complexity/Randomized/PPT.lean:393–397`, the new `NUPPT.ofPolyTimeUniform_def` equates the entire NUPPT value with the ofPolyTime constructor specialization. Its use in HardCore.not_hardCore_const (266), HardCoreCollection.Collection.glPad_sample_runAtL (176), and HardCoreLemmas.Collection.glPadSample_runAt (1005) exposes that construction in downstream proof lists.

The issued representation rule says a machine is read through public run/coin/field contracts, **not a raw machine-body alias**; X10 requests those operational/field readers. This new equality is a body-reading interface rather than the required operational one. It does not demonstrate a mathematical or behavior defect, but it should not become the accepted public machine API.

The bounded repair is to consume existing output_ofPolyTimeUniform / runAtL_ofPolyTimeUniform and coin/advice contracts at those three sites, removing this new body-equality reader. The existing run contract is in the same snapshot at PPT.lean:426–431; output/coin readers are at 404/409. If a precise operational form is missing, publish that form at the owner. This review has not natively checked the suggested replacements.

## Admissions, worker claims and limits

All 20 owned baseline admitted declarations retain byte-identical complete headers and proof bodies, not only the same total. The full-library ancestor/overlay lexical census is unchanged at 510 sorry tokens plus the existing single quoted sorryAx Name token; no direct admit/axiom/new unsafe declaration was introduced. The literal sorryAx metadata test is not a consumed-axiom result. Full transitive axiom sets and actual private/generated identities were not independently collected by this source review.

The worker reports resumed ordinary checks, root/Checks success, census/C3 comparison and 365 remaining seal-failing declarations, with controls/style/per-row dispositions deferred. Those claims were read as data and are **not** upgraded by patch/source fidelity. CP1 explicitly says its J/N definitional-read work and row ledger remain incomplete. The source map describes the penultimate patch's surface; the final maps produced here include all seven patches. No clean full-seal, admitted-dependency, counter-sensitivity or final-completeness claim is made here.

The bounded report is about this immutable CP1 only. Continuing worker changes, root's own source worktree, external package/bootstrap state, native object freshness and invocation history are outside its verification.

**Not yet clear to merge — CP1 is partial; the machine-reader follow-up and full native/evidence verification remain.**
