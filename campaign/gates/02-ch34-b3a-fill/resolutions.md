# B3a fill gate: resolutions (round 1, CLOSED)

**Gate:** the B3a fill gate (`audits/ch34-b3a-fill-pack.md`, bundle SHA-256
`7770623f02b3312899f936634f0164e8ab355b0e7a32d51f5aec7122e55170e2`, 49 sections).
**Findings:** `audits/ch34-b3a-fill-findings.md`, preserved verbatim.
**Verdict: PASS, 0 blockers, 0 majors, 3 minors, 8 notes. The gate closes at round 1.**

The auditor confirmed:
- the freeze, by applying the cumulative patch to the base, which reproduces the 538-line head
  byte for byte;
- both realizations against P4.1's minors 1–2 and the brief's routes, including the empty input,
  length 1, the width changes at powers of two, a halt during emission, and an empty source bank;
- both space ledgers, recomputed in full;
- the duplication ruling: no failure-mode-5 major for `b3a_seam_space` or `b3a_cfg`;
- the replay, axiom and walk evidence, as log and probe correspondences.

## Minors

1. **The bundle lacked most of the union screen's population** (42 of 66 files, among them
   `Build/Convention.lean`), so the historical screens could not be reproduced from the packet,
   and the `b3a_cfg`/`Cfg.ofWords` comparison could not be certified. **Resolved by erratum:** the
   pack now says which screen results the packet reproduces (the delivery's 24-file population)
   and which rest on the historical logs (the 66-file union screen). The lesson is recorded for
   future packs: a bundle carries every file of every screen population its pack cites.
2. **The evidence-completeness claim exceeded the packet.** The delivery manifest lists 27 files,
   and only five payloads were attached. **Resolved:** the delivery's sanity and pre-ship sources,
   their logs, the bootstrap and final sweep logs, the bundle check and the axiom log are added to
   `audits/evidence/ch34-b3a-fill-gate/delivery/`. Each file's SHA-256 matches its entry in the
   delivery manifest. The pack's erratum restricts the integrity attestation to what is attached.
   The shim note stands as the auditor reads it: the delivery's agent used its shim; the
   maintainer never compiled or ran it.
3. **F6-1(b)'s proposed retirement was invalid as written.** The public additive Seam lemmas
   (`seamCompTM_spaceUsedByTape_le_add` and `seamCompTM_spaceUsed_le_add`) need a live
   `Cfg.ofWords` endpoint for the second phase, and `b3a_seam_space` is used at a genuine halt.
   **Resolved:** backlog F6-1(b) now prescribes promoting a general-configuration additive
   corollary of the public trajectory theorem (`seamCompTM_visitedByTapeHead_ofCfg`), deriving the
   canonical corollaries from it, and then replacing the private helper, in the shared-file
   window.

## Notes

Notes 4–11 record no findings. Note 8's suggestion, to define `b3a_cfg` through `Cfg.ofWords`
once the comparison is supplied, is added to F6-1(b).
