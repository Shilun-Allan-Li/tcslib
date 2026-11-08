# Three concrete provider-proof proposals

These standalone patches change only the proofs of Complexity.polyTimeComputable_id,
Complexity.PolyTimeComputable.output_length_le and Complexity.PolyTimeComputable.comp
in ClassNP/PolyTime. They use the existing FinTM.computesFunInTime_iff contract.
Every public header, witness, coefficient/degree, data definition, algorithm,
import and admission remains unchanged. The individual source/result hashes and
boundary notes accompany each patch.

They are **unapplied and uncompiled proposals**, not part of the worker's payload
or the eight current local consumer/API edits. The existing worker PROVIDER_ONLY
restriction remains: issued-r1/public-exceptions.md X12 freezes original provider
proofs. A continuation scope ruling is needed before giving a worker permission
to make these edits; no such ruling is inferred from the patches.

The three examples make the scope choice concrete. Any broader permission for
witnessed provider Rule10 proof repairs must still preserve all public statements,
costs, algorithms and admissions, forbid unrelated refactors, and require exact
fresh failure/repair evidence for each changed declaration. No such broader
permission is granted by this record.

**Not yet clear to merge — these provider proof proposals remain unapplied and uncompiled.**
