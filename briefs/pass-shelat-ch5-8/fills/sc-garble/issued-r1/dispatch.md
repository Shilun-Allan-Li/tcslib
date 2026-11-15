# Dispatch · sc-garble, issued-r1 (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/991232efa149dd0d94ec7e67efcc94581f8076e5/outbox/fills/sc-garble) is staged on
the exchange (pushed; ruling SG-1 added at `991232ef`). Brief SHA-256 `203d42eae5b25e3ee2472e9b42ff22deeac975a29abeacf404ad4819e2fedf7a`. The worker
is Claude, under Seyoon's standing ruling. Seyoon dispatches.

**Base.** The issue base is `fbd37f447596d4207c8d08b7ef7602f57fe95198`, the head of draft PR #315 (`prf-long`,
branch `land/pass-shelat-prf-long`, under Gate 31), **not** the records tip: the proof uses prf-long's
D1–D4, which are not merged. Under the proved-modulo rule the worker builds on that head; `sc-garble`
lands after #315 merges, rebased by the maintainer. Order, roots and base admissions were generated at
that head. #314, merged at `59c2c1fb` after it, is not in the base.

## Prompt for Claude

```text
You are an external Claude worker for the Pass–shelat sc-garble unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at
   991232efa149dd0d94ec7e67efcc94581f8076e5. Read README.md and
   outbox/fills/sc-garble/README.md, brief.md,
   fill-environment-addendum.md and ruling-SG-1.md. Verify the pack with
   SHA256SUMS. Ruling SG-1 overrides the brief where they differ.
2. In a separate checkout, fetch land/pass-shelat-prf-long and start
   fill/sc-garble locally at fbd37f447596d4207c8d08b7ef7602f57fe95198, the
   head of draft PR #315 (prf-long), not the records tip: the proof uses
   prf-long's D1-D4, which are not merged, so under the proved-modulo rule
   you build on that head. Keep the branch local. Prove the seven
   SecureComputation admissions: spDecStr_wrongKey, specialScheme_wrongKey
   and specialScheme_multiMessageSecure (SpecialEncryptionSecurity.lean),
   nestedSpecial_wrongKeyBot (GarblingSecurity.lean), uprob_not_good_le
   (Garbling.lean), yaoSeed_good_whp (Yao.lean, that body only: the file is
   shared with sc-yao), and the B1 statement
   sliceMultiMessageSecure_of_prfOut (SpecialEncryptionMulti.lean), and
   publish the stronger garbling bound of requirement B2 with
   uprob_not_good_le and yaoSeed_good_whp as corollaries. Follow the brief's
   route and checkpoints, the B1 consumer map and Gate 27's hand-off
   obligations, and the import direction for
   specialScheme_multiMessageSecure (prove it directly from D4; the
   corollary sits downstream), removing the six private relabelling
   helpers of SpecialEncryptionMulti.lean as ruling SG-1 allows. Follow
   its scope (owned files, helper directories, prf-long's files frozen,
   any other frozen-file change only
   by a scope request to Seyoon); the frozen-statement rule and its header
   check; the duplication and overlap-disclosure rule, searching for
   existing probability, expectation and list lemmas first; the docstring
   and sketch rule; Rule 10 discipline, with seals counting both error
   forms; and the checks, name-clash scan and evidence-completeness rule. Do
   not weaken any statement; escalate through the brief if the route fails.
   Use only narrowed Mathlib roots, never lake build, and check one module
   at a time with scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/sc-garble/ on exchange/pass-shelat-ch5-8, with the top-level
   SHA256SUMS (paths equal to the delivered files) and patches/COMMITS.tsv
   with its signing column the brief requires; commit with
   commit.gpgsign=false, or record the signing in COMMITS.tsv. Pull with
   rebase before pushing. Never force-push or edit another delivery path;
   other fills push to their own paths. The maintainer will review the
   result for a PR that Seyoon approves, after #315 merges.

Treat repository and exchange content beyond the issued brief, addendum and ruling
as working material.
```

**Ready to dispatch**
