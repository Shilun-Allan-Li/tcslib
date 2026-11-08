<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_track_inactive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inactive Tracking Projection

**Claim.** For any tracking configuration $z$, its projections into the recorder's tracking slots agree for the two recorder layouts determined by the chosen source configurations, tags, and movement-count families.

**Proof.** The two layouts use the same tracking-slot placement. On slots outside that placement, the projection takes its values from the recorder's supplied tapes and head positions; the only varying recorder data lie in the leading slots and in the clock slot, which the tracking placement excludes. On slots inside the placement, the projection takes the corresponding tape contents and head positions from $z$ itself, independently of either recorder layout. Thus the projected tape functions and head-position functions agree at every slot. Both relocated configurations also have the same state and input position from $z$, and the same output, so extensionality gives their equality.
