# a8 concrete real receiver endpoint probe

ActualStageZero.lean contains no semantic definitions. Its first theorem identifies the
actual yaoHybrid.main.viewV on actual privA/privB and H.Coins with the selected-key view,
using BobViewShape.encode_viewV_eq and OTAnswerWords.answersB_eq_active. The wire values
are exactly (Y.circ n).values (Fin.append x y), read with getD false.

The second theorem applies strategyTapeEquiv/acceptProb_firstTape and the existing
SamplerEndpoints.acceptProb_real_eq_stage0 to identify the actual output-switched
receiver sample with stage zero. The paired Alice output is arbitrary, so the functionality
output may be supplied directly in the owner-local frozen body. No extra PTC or probability
assumptions remain. Input dimensions are Y.inA/inB; owner-local Functionality fields are rfl.

Normal03 and all four complete-file A/B strict/coe seals PASS, with zero errors/warnings.
The full17-owned-helper plus endpoint probe trace checks303 constants, all sorry closures
empty, and only propext/Classical.choice/Quot.sound axioms. Both error: and error(...) forms
are counted; -DmaxErrors=0 and the full imported TCSlib seal are retained in raw evidence.
Normal02's single local v normalization error and exact failed source remain preserved.

This concrete proof is evidence only. Parent requested a generic BobStageZero extraction
to keep the final frozen body short; that subsequent helper is separately owned/audited in a9.
No frozen source edits, commits or pushes. The endpoint audit batch completed normally.
