# Final explicit tactic-list review

**Static delta verdict: 0 new/touched foreign ordinary-definition or abbreviation body reads; 0 unresolved new/touched items.** This does not assert that the complete inherited source is rule10-clean or that any native seal failure is cleared.

Scope is independently derived from base `eee107e92a7db11f1f8c98a5c2867304f57ddc54` to final head `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`: **61 changed Lean files = 54 mathematical files + 7 import/option-only facades**. All 54 mathematical files are included, without a touched-declaration filter in the complete inventory. The full 1,108-file source SHA list remains the reconciled final review snapshot.

## Coverage and classification

The complete textual inventory contains **4,119 explicit items**. Of these, **1,555 items across 613 distinct heads** occur in new/changed formal declaration bodies; 1,413 occur on changed code lines. Declaration comparison excludes comments/docstrings and normalizes whitespace. Every inherited definition candidate below also has an exact byte-identical raw source-line match at base, with the old line recorded.

| New/touched item kind | Count |
|---|---:|
| Published TCSlib theorem, including typed receiver/proof-field equations |720|
| Published Core/Mathlib theorem, including generated equations and theorem aliases |492|
| Owner-local definition body |114|
| Local proof/let fact |209|
| Inline `show … from/by …` proof term |20|
| Unresolved or foreign definition body |0|

Classification uses actual declaration keywords and homes from current local primary sources, not `_eq`/name-prefix assumptions. The 37 manual head mappings in `final-explicit-primary-supplement.json` cover generated or receiver-qualified cases that the legacy textual resolver cannot identify directly. Examples include `H.gen_uniform.runAtL_eq` = `NUPPT.Uniform.runAtL_eq` (NonUniform.lean:95), `henc.runAt_eq` = `NUPPT.Computes.runAt_eq` (PPT.lean:313), and the exact BitPublicKeyScheme `S.correct` field (PublicKey.lean:234), rather than an unrelated theorem sharing a suffix.

Core/Mathlib checks include `Function.comp_apply/comp_def`, List/Fin/Nat/Bool equation lemmas, Fintype cardinal equations and BigOperators theorems. `Finset.sum_*`, `Fintype.sum_*`, `List.sum_replicate`, `abs_of_nonneg` and `zero_add` are theorem/lemma outputs of the adjacent `to_additive` attributes, not ordinary definitions. `mul_add/mul_sub` alias actual theorems; Batteries' alias elaborator preserves theorem kind. `List.cons.injEq` is emitted by Lean's constructor-injectivity generator as a `thmDecl`. `finProdFinEquiv_apply_val` and the four `yaoMain_*` field equations are published `simps` theorem outputs.

Proof projections were checked as propositions: `D.sum_prob`, `p.sum_prob`, `T.f_perm`, `S.correct`, `zero_mul`, and `mul_zero` consume published proof laws. Pinned Lean `Meta/Structure.lean:92–111` generates safe proposition-valued projections as **theorems**, while data projections become definitions. They are not silently treated as reducible data definitions. Source/factory lines and SHA256 values are recorded in the supplement.

The owner-body items remain in the definition's own file, including local construction equations and machine run-contract proofs. No compiler `.eq_N`/`.eq_def`/`.eq_unfold` item head occurs anywhere in the 4,119-item inventory. Every nested `rw`/`simp` inside an inline proof is also inventoried. The final sources contain no unsupported `simp +…` flag prefixes, parenthesized rewrite configuration, or bare multiline `unfold`/`delta` form in this scope. This is source inspection, not Lean syntax elaboration or an implicit-read certificate.

## Abbreviations

**Zero explicit items name a TCSlib source `abbrev`**, across both changed and unchanged declarations. Implicit abbreviation notation was not used to excuse an explicit list entry. The 15 new public abbreviations have their published owner interfaces:

| Abbreviations | Owner reading interfaces |
|---|---|
| MAC/SignatureScheme `oracleSpec` | Authentication.Defs `oracleSpec_eq`132/267 |
| `hsGen`, `hsSign` | HashAndSign `runAt_hsGen`256, `runAt_hsSign`277 |
| FixedLengthScheme `indSpec` | Composability.Defs `indSpec_eq`129 |
| `padEnc`, FixedLengthPKScheme `indSpec` | PublicKey `runAt_padEnc`194, `indSpec_eq`505 and dom/rng fields |
| MsgSampler `simSpec`, `snmSpec`, `SnmState` | SimNonMalleable `simSpec_eq`132, `snmSpec_eq`176, `SnmState_eq`186 |
| `ccaGen`, `ccaEnc`, `ccaDec` | CCA2Scheme `runAt_ccaGen`252, `runAt_ccaEnc`259, `runAt_ccaDec`270 |
| `GarbleSeed` | Garbling `GarbleSeed_eq`222 |
| HybridProtocol `Coins` | Hybrid `coins_eq`149 |

Machine interfaces retain their stated domain/premises; this audit does not replace them with machine-body aliases. The older Encoding `Graph` abbreviation predates this delta. The exact recorded `PolyExpr.eval`/`glNeed` notation policy remains unchanged; it is not generalized to other names.

## Inherited explicit-read record

The source resolver retains **134 inherited TCSlib definition candidates in 13 files**, representing 51 distinct definitions. All 134 are ordinary source `def`s; none is an abbreviation. Exactly 3 are the recorded `PolyExpr.eval` notation exception; the other **131 remain explicit-read debt**. No `glNeed` explicit item occurs. The GI family contributes 42 candidates, or 39 after recording its 3 exact `PolyExpr.eval` exceptions.

| File | Inherited candidates |
|---|---:|
| `TCSlib/Complexity/ClassP/BinaryArith/Loops.lean` | 34 |
| `TCSlib/Complexity/Randomized/PolyTimeModel.lean` | 29 |
| `TCSlib/Cryptography/Asymptotic/Adversary.lean` | 1 |
| `TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean` | 18 |
| `TCSlib/Cryptography/ZeroKnowledge/Defs.lean` | 5 |
| `TCSlib/Cryptography/ZeroKnowledge/Encoding.lean` | 5 |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean` | 7 |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean` | 1 |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean` | 11 |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean` | 2 |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean` | 4 |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean` | 8 |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean` | 9 |

`final-explicit-inherited-debt.tsv` retains every head, owner, current/base line, definition home/line and exception tag; `source_failure_exclusion` is explicitly false on every row. GI examples remain visible: Efficiency's `GI.ilayout`323/328/333/338/343; Proofs' `Protocol.outV/transcriptWith/exec/moverIsV`487/496; Closeness' `samplePerm`154 and `permFailBound`574; Simulator's `NUPPT.inArg/inCoins/advInput`482. Namespace homes matter: `GI.instanceVertexCount` is the separate Proofs definition, so the global GraphIsomorphism reader is not asserted to repair it.

These annotations preserve inherited debt. They do not suppress a source failure, confer a waiver, or replace root's final full-closure seal/failure reconciliation. Core/Mathlib entries in unchanged declarations remain in the complete inventory; no whole-file absence claim is made without the optional fresh kind catalog/scan.

## Existing mechanism and optional fresh run

The selected scanner is **Gate04 evidence-r5/tools/scan.py**, SHA256 `5a8f30fe15d70e976e6a59e2aab42ae1bb6bec1b6d2f14587bb86f800d2a1ac6`, with `declx.py` `ffa3743f32fe22b19b4d18b5c233b916c23c7288ffe74e8aa8afb69f220af2c2`. It is the 255-line hardened version that handles numeric `nth_rw` prefixes and indented `unfold/delta` continuations across blank/comment lines. The older Gate07 copy lacks that hardening. Both were read as source data; neither was imported or executed here.

The scanner's historical table is TCSlib-only, its receiver/local name resolution is textual, and it does not supply Core/Mathlib kinds without a complete table. Its original C1 classification also omits def-proj/def-aux/def-private and misses irreducible-definition parents in its equation-lemma branch. The extractor preserves the exact native table and broadens those definition subclasses plus def-irreducible to def in a second scanner table; no name/home row is dropped. Reducible/instance definitions remain separately flagged. Proposition-valued projection theorems remain thm rows. Optional unrun `final-explicit-catalog.source.txt` preserves the original kind classifier as inert source data, imports all 54 final modules and logs actual imported `Lean.Name`/kind/home rows for all namespaces. It installs no seal/attribute and reconstructs no actual Name from a string. Its metadata-only heartbeat setting cannot change already imported library proofs. The 113-line extractor validates the pinned manifest, full library SHA snapshot, native source/footer/object/row completeness and writes a fresh TSV under ignored scratch; it never starts Lean or the scanner.

`final-explicit-scan-invocation.md` gives the separate reviewed root-only steps. All source/helper proposals are **unrun**. Raw scanner C2/C3 sections must not be interpreted as passed unless their fresh seal/proof-term inputs exist; this task's static explicit-list result is C1 only. No source failures are excluded from the proposed scan.

## Review artifacts and limits

The authoritative head-corrected inventory is `final-explicit-static-inventory-v2.json`; the earlier diagnostic inventory used an identifier regex that split internal question marks and is superseded. The final inventory follows Lean identifiers such as `List.getElem?_map` intact. `final-explicit-tcslib-resolution.json`, `final-explicit-primary-source-catalog.json`, the manual supplement and `final-explicit-classification.json` retain the source-kind provenance and all classifications. Preparation/line-map/name resolution is textual; optional native metadata validation and root's fresh seals remain independent.

Only independently authored static inspection code, Git read operations and Python AST parsing were executed. No received scanner/helper was imported or executed, no Lean/cache command ran, and no library, Git or campaign evidence was changed. Files written are ignored audit data/proposals only.
