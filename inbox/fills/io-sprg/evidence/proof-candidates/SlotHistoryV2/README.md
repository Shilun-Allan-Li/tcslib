# Slot history V2 — staged, not executed

slot_history_v2.py is an adapted checker for root to archive and run. Python syntax
was parsed with ast.parse only; no candidate module/function, Lean, Git, cache or
process inspection command was executed. Old tool and host/M0 files are unchanged.

The only accepted overlap is the exact active wrapper pair:

| Event | PID | UTC |
| --- | --- | --- |
| Prior search ACQUIRE |93883|2026-11-18T15:07:27Z|
| Owner ACQUIRE / overlap start |93983|2026-11-18T15:07:45Z|
| Owner RELEASE / overlap end |93983|2026-11-18T15:07:48Z|
| Prior wrapper RELEASE / correction cutoff |93883|2026-11-18T15:08:34Z|

All4 events must occur exactly once, match the correction JSON's4 full slot lines,
and have the exact expected active pair/starts/slot counts. The JSON's observed
child93887 and confirmed overlap endpoints are also checked. No PID-only, command
substring, time-range or generic overlap-waiver flag is offered. Every other overlap
fails, including an extra wrapper, reused PID at a different timestamp, different
release time, or a second occurrence. Duplicate/missing events, backwards tagged
timestamps, unexpected slot counts and unmatched releases also fail. k3 remains
restricted to the old cache-get command guard; this is not a child-process audit.

Successful output derives max_concurrent_job_wrappers=2 and historical serial=false.
Both old-compatible all_logged_acquisitions_serial_after_recorded_reaps and the clear
all_tagged_wrapper_acquisitions_serial fields are false. The known3second violation
is explicitly retained. No assertion can represent whole history as serial.

A separate post_correction block starts after the exact15:08:34 prior release.
It counts later acquisitions/max wrappers and reports serial=true only if that
observed suffix is valid and has at least one acquisition. With no later acquisition,
serial is null. --require-closed additionally fails on any active tagged wrapper.
These are intended outputs conditional on root's successful run, not validation
results from this drafting agent.

Every tag=io-sprg record is extracted byte-for-byte in source order. The selector
checks the actual fourth event field, so another job's command merely mentioning the
tag is not copied. Every tagged REAP is retained in the log AND reap_records, with
reaper PID/dead PID/payload/line and whether it matched an active acquisition. Matched
acquisitions retain the prior unreleased_reaped provenance and do not invent an end
time, child death time or cause. Correction JSON contents/hash, complete source hash,
extracted hash and checker hash bind the new result. The JSON's recorded SIGTERM
action is preserved as provenance; wrapper timestamps do not independently prove a
child's lifetime or successful termination details.

No global host cap, other-job seriality, actual simultaneous Lean-process count,
or complete child-process history is claimed. The max2 figure concerns tagged
wrapper reservations after recorded reaps only. The known one-at-a-time violation
is never excused by the host's broader slot policy.

Root invocation after archiving the candidate under a new tool filename:

    python3 -I evidence/tools/slot_history_v2.py \
      --out evidence/host/final-slot-audit --require-closed

--out is mandatory. The old evidence/host directory itself is refused, output files
are exclusively created, and any existing output/source alias fails. Choose a fresh
directory for each run; failed runs retain their full tagged log and failure summary.
The source/correction flags permit root's isolated fixtures; defaults read the live
host log and existing correction record without changing either. Input/open failures
still return nonzero; audit failures write statusFAIL and return1.

Root-only suggested checks, all UNRUN here: current complete history; missing/doubled
known record; changed known timestamp/PID; any second overlap before/after correction;
extra active wrapper; REAP of an active stale wrapper; unmatched release; active suffix
with --require-closed; no postcutoff acquisition (serial=null); reused output refusal.
