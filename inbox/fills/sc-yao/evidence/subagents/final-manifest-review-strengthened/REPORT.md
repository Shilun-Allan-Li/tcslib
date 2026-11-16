# Strengthened helper-seal runner review

The two concrete prelaunch gaps from the earlier final-manifest review are closed in the
reviewed source. Parent run_final_helper_seals.py now holds LOCK_SH, and every spawned
runner receives --read-only-import-lock. Each runner opens the same root driver lock and
holds its own shared lock reference for the entire process lifetime, with no early close
or unlock. The ordinary check_modules writer retains LOCK_EX on that same file. Thus the
identified case of a controller exiting while a runner survives no longer releases the
surviving runner's protection against a cooperating normal writer. Multiple shared readers
can coexist, so the former parent-exclusive/child-shared deadlock is avoided.

Before spawning, the controller hashes all272 probe sources and writes the expected map.
After all workers complete, it asserts exact result count, exact probe set and uniqueness,
then compares every row's source_sha256 with that initial map. Both the preexisting
before/after imported-artifact equality assertion and all diagnostic/fresh-output checks
remain present. The shared wrapper invocation, separate output-only trees, single own
bootstrap import path and host cap are unchanged.

All272 prepared probe hashes and all68 source hashes were re-compared with the earlier
independent inventory and remain identical. This supplement preserves the exact reviewed
strengthened tool versions and hashes. It is a static source/metadata review, not a Lean
run or a runtime locking experiment, and it does not claim the pending seals passed.
Runtime results and complete final evidence packaging remain the lead's responsibility.
