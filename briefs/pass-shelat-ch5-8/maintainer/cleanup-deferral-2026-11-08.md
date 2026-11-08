# Cleanup deferral and independent fronts

On2026-11-08 PST, Seyoon preferred postponing the cleanup continuation for about
a week to reserve tokens for other work, and asked whether other campaign prongs
could proceed. Park the continuation until the user resumes it; this is a priority
deferral, not a scheduled restart or an exception to any acceptance requirement.
Keep partial PR #248 draft and its checked source/evidence intact. The unanswered
worker-choice and original-provider-proof-scope questions can wait until resumption.
No provider proposal is applied and no new job is prepared or dispatched here.

## Independent work available

The Gate06 PLAN requires each prong's own statement gate before its fills; it
does not impose an A-to-B-to-C-to-D order or make cleanup a universal prerequisite.
06A authentication,06B secure computation and06D randomness are closed.06C remains
pending; its findings are absent from the local campaign inbox at this check.
PR #232 remains open/draft at its frozen audited head. New proof work would use
a separate branch; final landing still needs the applicable comments, current-source
reconciliation/checks, PR review and user merge. Do not advance the audited head.

Two contained candidate units, rather than a new broad fill, are:

| Candidate | Why separable | Limit |
| --- | --- | --- |
| Randomness.not_isExtractor_effSources, Extraction.lean:122 | Gate06D is closed; its30-module static local import closure includes neither Games/Efficiency nor Composability. The proof concerns rejection sampling, entropy and an efficient sampler. | Still substantive proof work; no native attempt, completion estimate or promised cheap fill. |
| SecureComputation.uprob_not_good_le, Garbling.lean:415 | Gate06B is closed; its3-module static local import closure includes neither unfinished reduction-efficiency nor Composability. It is a finite-probability correctness bound. | A component of garbling, not completed Yao security; no proof or cost estimate is claimed. |

The precise target positions above refer to frozen Gate06 source
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b`, not the current campaign source where
the prong modules have not landed. Import-closure independence is a static source
observation, not a proof that every future implementation choice avoids all shared
interfaces. The choices do not adopt new primitive endpoints or commission a worker.
Ask Codex or Claude before preparing any new external audit/fill.

Low-cost maintainer work can also process the already-dispatched06C audit when
it arrives and refine the Implications assumption/dependency index. Concrete RSA/
Rabin-to-PKE wrappers still need their normalization bridge; precise PKE CPA work
waits for its06C statements/proofs, and no public-key CCA2 construction is claimed.
Full authentication/learning reductions often use the unfinished T1/T2 framework;
filling them would remain conditional on that infrastructure, so they are not the
first recommendation for a small, independently completed result.

Efficiency and the remaining Gate03 restaging retain their explicit cleanup
prerequisites. Do not treat a token-saving pause as permission to bypass them or
to merge the partial cleanup. The partial PR remains a durable restart point.

## Follow-up: overlap with deferred cleanup

The user asked whether proof progress could conflict with seal cleanup. The earlier
static independence check concerned Games/Efficiency and Composability, not every
cleanup dependency. Direct comparison of Gate06 source
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b` with the delivered cleanup candidate
`32b827c017bc321ea40577bc8f27131df2c35e1a` (diff from issued source
`1aa5506f58f77c215e56d24311ec33bd931cacf1`) finds:

- Neither proposed target file exists at the cleanup issue ancestor or is edited
  by its current122-path source delta. Both are Gate06 additions.
- Garbling.lean and its full3-module local import closure have zero paths changed
  by that cleanup delta. This is the lower-overlap candidate.
- Extraction.lean has14 changed dependencies in its30-module closure: ClassNP
  PolyTime/PolyTimePairing; Randomized PPT/PolyExpr; TM Convention/Wrappers/
  Deterministic/Encoding/Simulation; Asymptotic Adversary; InformationTheory
  Extractors/FinDist/LeftoverHash/StatisticalDistance. Its independence from T1/T2
  does not imply independence from cleanup integration.

These are pinned current-payload observations, not a promise about every future
cleanup change or a proof of complete Rule10 cleanliness. Keep further proof edits
on a separate branch and within the selected theorem's scope, consume published
owner lemmas, and verify new/touched proofs under the required seals/explicit-read
checks. Retain all inherited failures. Do not silently change shared providers or
add new foreign-body reads to the deferred debt. If the chosen proof needs a shared
interface repair, stop that dependent step and record the prerequisite. Repeat the
source-matched affected/seal checks when the lines of work are combined.

Garbling's finite failure bound is the preferred contained proof candidate if the
user elects further fills. Extraction remains possible with more integration risk.
No fill is prepared or commissioned by this comparison.

**Not yet clear to merge — independent narrow work is available; cleanup acceptance and Gate06 landing remain open.**
