# a9 generic actual receiver endpoint

BobStageZero.acceptProb_eq_stage0 identifies the acceptance probability of the actual
bit-OT hybrid receiver view, paired with any prescribed Alice output word, with stage zero
of GateHybridMessage.sample over the original addressed seed tape. It takes the protocol's
round/order/Bob-zero/sender readers; the first-tape length and call count; C/S/n/v and the
four seed readers; Bob's wire-input agreement and actual answer-bit reader; and the first
message's explicit payload equation. No Functionality, Yao name, semantic definition,
probability identity or machine is introduced. The helper is135 lines, one public theorem.

The theorem consumes BobViewShape, OTAnswerWords, SimulationBound and SamplerEndpoints
unchanged. Reuse search and exact nearest relatives are recorded in SEARCH.md. This is a
consumer composition; no existing proved probability material is re-derived or copied.

ConcreteBobStageZero is evidence only. It specializes every premise to Y.circ, yaoSeed,
actual yaoHybrid/privA/privB/Coins, the actual circuit values of Fin.append x y, and the
published Yao payload/readers. The full concrete proof is33 lines with every reader and
both input facts explicit; reusing facts already needed for the other security steps makes
the final frozen-body application shorter. It pairs an arbitrary Alice output α.

## Verification

Generic and concrete normal01 checks PASS, zero errors/warnings/admissions. Both files
pass all4 complete-file A/B strict/coe seals:8/8 total, no exceptions. Full imported TCSlib
definitions are sealed, notation/abbrevs excluded as prescribed, and -DmaxErrors=0 is used.
Both error: and error(...) forms are counted. Stored trace covers305 constants over the18
historical helper snapshot modules and concrete probe: every sorry closure empty, axioms
only propext/Classical.choice/Quot.sound. Style lint0; max width below100; no new simp attr.
The historical CoordinateSwap is included only in the trace snapshot; root now owns it,
and neither its source nor any other old helper source is part of this source handoff.

The earlier a7 factory and a8 original concrete endpoint handoffs remain immutable; their
exact manifest digests were verified again, recorded in prior-handoff-hashes.json. This
handoff contains only the new helper source and matching normal completed olean, the actual
consumer's completed olean, and the full a9 evidence. No frozen/root-owned edits, commits,
pushes or final delivery actions were made. The final audit batch completed normally and
no own job remains live.
