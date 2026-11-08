# Maintainer proposal 02: output_length_le

**Unapplied, uncompiled proposal data only.** The patch changes one computation-hypothesis access in `Complexity.PolyTimeComputable.output_length_le` to the existing `FinTM.computesFunInTime_iff.mp` reader. The complete header, C/c witnesses and polynomial bound, machine output-length step, imports, direct admissions and all other source/proof bytes are unchanged.

The issued worker role for `ClassNP/PolyTime.lean` remains **PROVIDER_ONLY**, permitting new ordinary owner readers and explicitly forbidding changes to existing proofs. X12 and the three J/N definition exceptions supply no exception for this proof. This separate maintainer proposal grants no worker permission expansion or scope ruling and has not been applied anywhere.

The patch is independently based on the immutable partial source; its proposed full-file result does not include proposal 01. Exact source/result/context/reader/permission hashes are in `02-output-length.json`. Previous proposals, frozen reviews and the current local consumer/API repairs remain untouched. Native and sealed verification are deferred to root.
