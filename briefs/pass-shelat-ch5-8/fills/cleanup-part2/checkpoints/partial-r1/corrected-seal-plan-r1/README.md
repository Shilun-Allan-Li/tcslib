# Corrected received-partial seal request plan

**DATA ONLY — no new native attempt, result, acceptance or policy ruling.** This plan targets immutable delivery `0c4d4f60203021f3a3b93f88eaf7c9085c6ab885`, reported source `03ead73ab38e74621800367c072f6fd3f0f70991`, ancestor `1aa5506f58f77c215e56d24311ec33bd931cacf1`. The maintainer's later local repairs, including API-01, are excluded. No frozen source report, payload, library, Git or exchange was modified.

## Scope and request arithmetic

The required owner set is the exact union of all 97 issued consumers and all 26 changed providers, totaling **123**. The existing 98 plans cover the 97 consumers and ClassNP/PolyTime; 25 changed providers were missing. All remain in owners.json and per-owner files, including four owners with empty request lists. Empty lists are not native passes.

| Request set | Owner/name pairs |
| --- | ---: |
| Received standard plans, 98 owners | 95,177 |
| Received strict plans, same 98 | 95,408 |
| Corrected existing 98: omit only eval itself | 95,331 |
| Restored eval.match_1 / eval._sunfold in those 98 | 154 |
| Added 25 provider plans | 7,544 |
| Corrected 123-owner plan | **102,875** |

There are 77 exact eval omissions among the existing 98 and 79 among all 123. Both eval.match_1 and eval._sunfold remain requested wherever foreign in the closure. No eval-prefix wildcard or source-failure exclusion is used. The catalog predicts 102,148 semireducible and 727 already-irreducible requests; those are metadata counts, not new runtime installation observations.

## Verified data derivation

Own build_plan.py runs only Python3-I standard-library parsing and writes this new ignored directory. It invokes no Git, Lean, cache/build/app process or incoming program. It verifies the frozen independent source-review manifest, raw input hashes, compressed/uncompressed final census hashes and source snapshots.

The final received catalog has 374,594 unique actual-name metadata rows, including 20,018 TCS-home rows. Every one of the 221 native closure blocks is checked against that catalog and the complete transitive **TCSlib import closure** from the independently replayed source graph. Exact dependency and eligible-name sets agree for all 221, not only the selected 123. This is conservative import-closure coverage, not a term-only name selection. Core/Mathlib/non-TCS constants are outside this inherited seal domain and still require the separate explicit-list review; no complete transitive non-TCS package-graph claim is made here.

The two received 98-owner probe archives are parsed as text, never executed or imported. The parser accepts only explicit Lean.Name.anonymous/str/num constructor tuples and JSON string literals, with full grammar/end checks; it does not eval code or construct Names from printed spellings. Their exact request sets match the catalog closure sets minus the three previously omitted eval-related names for standard, and all catalog closure rows for strict. Removing precisely the inserted seal block, its one join-separator newline and the EOF instrumentation recovers every received source byte in both archives. The old probe bodies therefore match this incoming partial snapshot; their claimed runtime outcomes are not adopted.

## Exact method and its coverage limits

The corrected existing-method set retains the received collector's explicitly documented selection:

1. Every foreign constant homed in a TCSlib module of the complete native import closure, without a namespace/private/generated/source-failure filter.
2. Definition means ConstantInfo.isDefinition, which the pinned Declaration.lean:507–509 implements as defnInfo only. Theorems, constructors, recursors and inductives are not ordinary definition requests. The full metadata catalog is retained; the one opaque repr constant is separately listed (40 owner/name pairs). ReducibilityAttrs.lean rejects non-defnInfo declarations for this attribute.
3. The received collector excludes instances. **This is an inherited method coverage limit, not a Lean inability to seal instances and not a notation ruling.** All omitted semireducible def-instance identities are separately retained: 5,129 owner/name pairs, 118 unique names. The full catalog also retains theorem-instance metadata, which lies outside the inherited defnInfo selection.
4. Reducible non-matchers are omitted by that inherited method/validation boundary. The 955 unique identities (40,262 pairs) are listed without turning them into newly approved notation. Policy treats reducible abbreviations as notation, but explicit tactic-list use still requires published readers where available. Other generated reducible declarations remain an explicitly recorded method limit. No unsafe reducibility override is proposed.
5. The sole additional exact ordinary-definition notation omission is Complexity.PolyExpr.eval itself. Its matcher and _sunfold auxiliary are not omitted.

The incoming REPORT at 357–360/689–691 conflates instance omission with inability/notation. The pinned ReducibilityAttrs.lean:101–135 has no instance guard: semireducible defnInfo declarations may receive local irreducibility regardless of the instance flag. This is a source reading, not a new runtime experiment. Neither the incoming report nor this plan supplies a new user ruling for the instance filter.

## Optional instance-inclusive supplement

optional-instance-inclusive-supplement-DATA.json proposes only an optional **data union**: add the 5,129 currently omitted semireducible definition-instance pairs, yielding 108,004 pairs. It is not the approved method, a native request source or a runtime result.

The raw names/home/kind/status/flags exist in the native catalog, but the received closure emitter deliberately skipped their actual Name components. Those fields are explicitly null/unavailable in the supplement. No Name is reverse-engineered from a display string. Any future instance-inclusive native harness must obtain/select the actual environment Names with exact metadata checks before installing attributes. The current 102,875 requests already have actual native components.

## Files and future consumption

- owners.json: complete required scope, source hashes, closures, row counts, omission identities and unrun status.
- per-owner/*.requests.jsonl: every request with native actual-name metadata and exact str/num component arrays; four zero-byte files are intentional.
- per-owner/*.plan.json: the corresponding complete closure/count/coverage record.
- request-name-component-catalog.json: all 3,162 distinct native component rows available from the received closure data.
- metadata-catalog-TCS.json: all TCS-home metadata, retaining every kind.
- existing-98-reconciliation.json and missing-25-provider-plans.json: exact old/new set reconciliation and added scope.
- excluded-semireducible-instances.json and other-inherited-method-omissions.json: identities and per-owner membership for every listed method limit.
- input-bindings.json, summary.json, metadata-manifest.json: raw provenance and all output hashes.

The JSONL is data suitable for one String payload parsed at runtime, so a future installer need not generate a Name-expression AST per literal. Fold the supplied str/num components to actual Names; verify existence, home, kind/matcher and expected reducibility for every request, and check installation/end coverage. Do not use Name.fromString, rebuild components from printed names, enable unsafe reducibility, or reuse these source pins for a later repaired overlay. No installer, native run or result is produced by this task.

**Not yet clear to merge — this is an unrun request plan with explicit inherited coverage limits.**
