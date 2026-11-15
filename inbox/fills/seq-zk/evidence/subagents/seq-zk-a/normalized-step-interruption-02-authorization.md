# Additional lead-authorized proof debugging

Request:

NormalizedStep check02 still has active elaboration (Lean13864 under wrapper13848), not a wait. Sparse sample02 now shows evalExact + deep Meta.isDefEq/unfoldBothDefEq, so broad simpa was removed but one exact transport still triggers expansion; I cannot assign a precise source line from that sample alone. Proposed safer rewrite: prove target directly with fully typed statClose_iff; apply hclose.abs_uprob_sub_le to the composed test, prove the REAL test-probability equality pointwise at concrete r using hfixed r and OneWay.uprob_congr, then public uprob_fst; no whole-StatClose map/rewriting/exact transport remains. Also make the real-history argument to the fixed-point theorem explicit. Request authorization for one further targeted own SIGINT13864 after preserving attempt02 source/sample. This is continued diagnosed unification debugging, not timeout/E-RES; prior headroom6.011GiB. I will add diagnostic source checkpoints if this narrower proof still stalls.

Lead response (verbatim):

Authorized targeted SIGINT13864 after exact-child verification/source+sample preservation. Apply the direct typed statClose_iff/test-probability proof you described. Add lightweight tactic trace markers before each major have/transport so any remaining stall can be assigned to an exact source stage from your own checker temp stdout, rather than another blind attempt. Use concrete sampler/test function equalities and OneWay.uprob_congr; avoid whole-StatClose transport/unification. Record this additional diagnosed attempt/interruption fully. c is free and I will ask for read-only review if needed; you retain sole edit ownership.

This is the lead’s additional authorization under Seyoon’s best-judgment exception, not a separate direct user reply. It is another diagnosed unification-debugging interruption, not a timeout or E-RES.
