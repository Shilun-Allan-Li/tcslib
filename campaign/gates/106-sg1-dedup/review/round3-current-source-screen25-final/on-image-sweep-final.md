# Bounded five-file raw on-image contract sweep

Public canonical: `Turing.FinTM.exists_comp_on_image` in the already included Composition home.
The raw contract fixes arbitrary M,U,f,g,T1,T2; image-only hU uses T2(|x|); result is
an existential N computing g with the exact budget2*T1+T2+2.

| Member | Complete raw contract? | Disposition |
|---|---|---|
| `Complexity.sat_comp_on_image` | yes | Same raw contract, ALREADY a direct citation of FinTM.exists_comp_on_image. Retain compatibility name/header; no repair needed for this member. |
| `Complexity.satSafeValue_poly` | no | Inline call ALREADY uses the public raw on-image existential theorem; surrounding client arithmetic/computation is not another implementation of that raw theorem. |
| `Complexity.sat_pt_numVars` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |
| `Complexity.sat_pt_drop` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |
| `Complexity.taut_comp_on_image` | yes | SOLE raw-contract rederivation found: identical public statement, but reconstructs buffered composition. Parent accepted mechanical same-PR repair; agent A owns actual fix. This task edits no source and executes no consumer proof. |
| `Complexity.taut_verifier_mem_P` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |
| `Complexity.clQueryCode_machine` | no | Already applies published operational buffered-composition computation result in a client machine/class proof. No second matching raw existential reconstruction found in this source block. |
| `Complexity.clNative_image` | no | Different CLASS-level polynomial packaging: second machine correct only on f image with budget measured at |f x|. Already uses published bufferedCompTM computation fact; remaining witness/majorant packaging is not the same raw existential contract, not covered automatically by seven retention kinds, and not proved an unavoidable new API. |
| `Complexity.clRecords_native` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |
| `Complexity.clTrajectory_native` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |
| `Complexity.clFinalCount_native` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |
| `Complexity.clSearch_native` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |
| `Complexity.clVisitRows_native` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |
| `Complexity.clA5Iter_native` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |
| `Complexity.clA5EqNum_native` | no | Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection. |

Two exact raw-contract members were found: SAT already cites the public theorem;
Tautology rebuilds the same theorem and is eligible for the standing mechanical same-PR
re-point. Root assigned A to repair it; this source-only sweep made no actual edits.
CounterLoop and SingleTape contain no candidate raw on-image closing under these hooks
or complete signature shapes. All five files and all candidate bodies are retained.

Hardness.clNative_image is a different class-level image premise/majorant wrapper.
Its direct clients are not counted as new raw composition implementations. The seven
accepted debt kinds do not grant a new image-closure acknowledgment or API decision.
This is bounded candidate enumeration plus source inspection. No compiled consumer,
rule-10 seal, axiom check, replay, global semantic absence claim or gate clearance is made.
