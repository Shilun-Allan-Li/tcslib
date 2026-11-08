# Maintainer proposal 03: PolyTimeComputable.comp

**Unapplied, uncompiled proposal data only.** One existing composition proof block uses `FinTM.computesFunInTime_iff.mpr` to construct its computation contract and `.mp` to read `hM` input by input. The complete header, original machine witnesses, coefficient `a * (C + C' * (C + 1)^c' + 1)`, degree `max c (c*c')`, arithmetic bound proof, imports, data, direct admissions and every other source/proof byte are unchanged.

The issued worker role for `ClassNP/PolyTime.lean` remains **PROVIDER_ONLY**. X12 allows only new ordinary owner readers there and freezes existing proofs; none of the enumerated exceptions covers this theorem proof. This separate maintainer proposal grants no worker permission expansion or scope ruling and is not applied to any source or delivery.

This patch independently targets the immutable partial source, without incorporating proposals 01/02. Exact source/result/patch/header/block/reader/role hashes are in `03-comp.json`. Prior proposals, frozen reviews and local consumer/API fixes remain untouched. Elaboration and required native/sealed checks remain for root.
