# Actual final8 BASE/HEAD lint and size completion

Both exact canonical helpers executed against the preserved43-file BASE/HEAD exports, selecting only the eight changed owners. The style helper uses its unchanged main with an observational finding collector and ROOT set to the actual side export. Campaign helper has no explicit-list CLI: the adapter calls its unchanged check_file for all eight, defaults check8b to false, preserves all findings, and prints main-equivalent severity/exit results. This is an eight-file check, not a whole-TCSlib campaign lint.

Actual style exits are1/1, with68 BASE and68 HEAD findings. All68 identity occurrences remain inherited; no new or removed identity.40 identities have raw source positions or dynamic line counts changed. Actual campaign exits0/0, zero FAIL and9 WARN/9 INFO each; all18 findings inherited, no new or removed identity,14 raw changes. Only source positions and dynamic source/proof line counts are normalized for identity comparison. Full raw messages, counts, every identity disposition and exact stdout/stderr are retained; inherited findings are not called clean.

Size checks exit0/0 (context counts only):1,345,452→1,344,346 bytes;25,434→25,416 splitlines. Five owners exceed1000 lines on both sides, no600/1000 threshold crossing. Each per-file full before/after size/hash and all deltas are retained.

REQUEST binds exact source files, source hashes and canonical helper Git blobs/hashes. RUNS preserves actual argv/exit/timing/output and helper/adapter hashes. All16 source hashes remain exact after execution. This supplement executes no Lean jobs or copy-text screens and leaves frozen403 QA unchanged.
