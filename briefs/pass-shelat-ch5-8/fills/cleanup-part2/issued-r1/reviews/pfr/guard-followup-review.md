# PFR manifest guard — companion static follow-up

**0 blockers, 0 majors, 0 minors in the added guard.** This supplements the original review without changing it. The latest prepare_pfr.py is 6172 bytes, SHA-256 `650edf1d270d5e130a926a5840fead75ba9888e12684f2f38451af91ad769b8f`; the originally reviewed version was `52b83d8e2dd73ab7a70cf7d66e5d4da439fb77e1417e3ba2fd09b9618b48110e`.

The initial review did not flag that coordinated changes to the static import/order metadata could satisfy the internal consistency checks without matching the externally frozen inventory. The new guard at prepare_pfr.py:28–33 closes that gap: it first requires the exact frozen DELIVERY-MANIFEST SHA-256 `70dd1a408a2c0c46af7ab2da50ff50520b26b2983e298492935008debb1a2cbd`, then checks every recorded leaf's canonical containment, byte count and SHA-256 before parsing PFR module/order/configuration metadata. Because the manifest bytes are fixed, its exact 15-file list is fixed as well. A missing leaf, escaping link, changed size/hash, or coordinated metadata-and-manifest change fails before object/runtime directory creation or package/native execution.

An independently authored read-only text check removed precisely the six added lines (28–33) and recovered the original prepare source SHA-256 `52b83d8e2dd73ab7a70cf7d66e5d4da439fb77e1417e3ba2fd09b9618b48110e`. Thus no other prepare code changed. The wrapper, native runner, probe and runbook hashes remain exactly those in the original final review.

Independently rechecked the frozen manifest and all 15 contained leaves against live bytes; all match. This was our own data/hash calculation, not execution or import of prepare_pfr.py. No supplied tool, native command, Lean/Lake/cache/build/app, negative-control harness or Git mutation was executed in this follow-up. The API agent's separate guard tests are not claimed as this review's execution evidence.

The overall conclusion remains static-only. Root's chosen maintainer native status is explicitly NOT_RUN/host-deferred; worker checkpoint-0 serial PFR bootstrap and the ordinary-PATH identity probe remain mandatory before dependent checks. No native owner, object ABI, overall baseline or cleanup acceptance result follows from this guard review.

**Not yet clear to merge — the guarded route is statically reviewed; final issue bindings and worker verification remain.**
