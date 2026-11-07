# Internal Gate 06B route review

Read-only internal reviewer, source merge `0a549ec16dd44b8d3694c3a23a04f943b63fcf2d`.
No edits, Lean/cache runs or Git mutations. Proposed terms are untested.

The minimal authorized repair retains the explicit evaluator cost and weakens its
specification to canonical inputs. The G3-1 review (`gates/03-ch2-4/review/gate03b-review.md`,
lines 190 and 253) states that correctness on canonical encodings implies correctness on all
decodable strings; it permits SamplerCanonical as a proved lemma and hspec as a consequence
of the canonical specification. PLAN's shorthand does not justify removing the relationship
between the arbitrary supplied evaluator H and predicate h.

1. Replace `def SamplerCanonical` by a theorem whose conclusion is its present body, directly
   from `T.toCollection.sample_eq_encD`. No `deriveSamplerCanonical` identifier exists.
2. Keep `hH : PolyTimeComputable H`; replace the public decodable-input specification by
   `henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]`.
   Derive the old local specification with
   `T.toCollection.apply_of_decD (v := fun i x => [h i x]) henc hw`.
3. Apply this consistently to `otProtocol_outV`, `otProtocol_simulators`,
   `otProtocol_hbcSecure`, and `yaoProtocol_hbcSecure`; remove their `hcanon` assumptions.
   Keep `otProtocol_polyTime`'s existing cost interface and refresh the 06B prose.

EnhancedHardCore remains necessary under G3-8. It contains unpredictability only, not an
evaluator or correctness for fixed H. Collection.HardCore.evaluator produces some evaluator
and cannot justify this arbitrary supplied H. A bare hEHC route cannot replace henc and hH.

**Not yet clear to merge — interface repairs and verification remain.**
