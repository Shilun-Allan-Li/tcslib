# Public-key encryption facade review

[PR #256](https://github.com/Shilun-Allan-Li/tcslib/pull/256) opens the first slice of the
[approved pilot](../cleanup-incremental-2026-11-09/final-r1/PKE-PILOT.md).
Seyoon merged #248 at `e398d5cb7ead61a6946497af6bca6f26630b5f7b`. Its Lean and checker inputs match the
verified cleanup head `7750947a65d262b8a4e4e557b6dae2a48865807a`.

The pilot head is `968f0640b91a5739c63aa71c8ce505e8b25666c4`. It adds the facade and its root import.
The five facade imports are already in the previous root closure.
The source comparison covers 1,074 unchanged inputs from the verified
cleanup replay and the exact single-import root change. The facade
adds no declarations, so there are no new proof bodies or definition
owners to seal in this slice.

The facade, standalone route probe, library root and campaign Checks
all pass `scripts/lean_check_tree.sh` on one isolated object tree.
The probe resolves all 22 fully qualified declaration names in the
facade docstring. The facade passes both style checks. The root's
six pre-existing plain-style findings reproduce byte-for-byte.

`VERIFICATION.json` binds the checked source, object and log hashes.
`pilot-checks.zip` contains the probe, source snapshots, checker output
and verification driver. Its SHA-256 is `d52a22b4c17d91feb42bf48d91d71b554c9933b741fb882239e5d01a1de61d1f`.

The next slice moves the scheme interfaces after this PR lands.

**Clear to merge — the facade and its root export pass the pinned checks.**
