# 17 #156 and the follow-up phase-host API PR: conditional citations and the owned file

**State during the review** (out/01): #156 moved from `a4d9b024` (`Build/Seam` only) to
`0e5f210b` (pushed 2026-10-24T05:12Z, "Phase-host prefixes through the new last-phase lemmas
(gate 69's major)"), which edits six files, among them **`CodeSimulator.lean`**
(`canonEmitVerdict`'s `leaf`, hunk `@@ -4593,11 +4593,9 @@`, net −2 lines). The campaign tip
moved to `aad8a095` (records only; 0 paths outside `campaign/`): gate 69 round 1 resolved "fix it
in #156", replay `lphl2` passed 23/23, round 2 pending. Its resolutions record a further ruling
(user, 2026-10-24): **a follow-up API PR after #156** — a start-state and a redirect-branch
equation for `phaseHostTM` in `Build/Seam`, re-pointing twelve one-field reads in seven files,
among them `CodeSimulator`'s `canonEmitVerdict` (line 4602, the host's start state by `change`) —
"landing before megafill C is issued (it changes `CodeSimulator`)".

**Consequences for the B5a draft.**
- Its base-dependent text is stale twice over: every line number after 4600 (home, docstring,
  statement, `sorry`), the file size, the blob check (`c64567f0…`), the overlay (built from the
  base file), the screen base (`canonEmitVerdict`'s text changes), and the order list's oleans
  (#156 also edits `Build/StepBlock`, upstream). The draft's "re-run the pre-ship at the issue
  commit" covers this only if the issue base contains both PRs; the brief must then be
  regenerated from that base, not patched.
- "In flight … #156, `Build/Seam`'s last-phase lemmas" and "Parallel batches: None in
  `CodeSimulator.lean`" are wrong if either PR is still open at issue. Since the user ruled the
  follow-up lands before megafill C, the brief should require both in the issue base.

**How the brief should read in each case.**
1. *#156 and the follow-up merged before issue (the user's plan):* ⟨IN-FLIGHT⟩ drops #156; the
   ancestor list adds "the phase host's last phase and its start-state and redirect-branch
   equations (`Turing.phaseHostTM_tr_of_red_none`, `Turing.phaseHostTM_run_le`, and the
   follow-up's two equations), published"; the Hosts list may cite them for any phase-host use
   (add them to the import probe). B5a's route needs no phase host (seams suffice), so the
   simplest text is: "join every phase by `seamCompTM`/`seamReleaseTM`; if you host a phase in
   `phaseHostTM`, read it only through `phaseHostTM_run`, `phaseHostTM_run_le`,
   `phaseHostTM_tr_of_red_none` and the start-state/redirect equations". All base numbers are
   re-measured at that base.
2. *Either PR still open at issue (not recommended):* keep "not citable"; add to ⟨IN-FLIGHT⟩ that
   it **edits your file** (`canonEmitVerdict`, 4593–4603, a region you do not own), that your
   landing serializes after it with a merged-tree replay, and that a phase host must not host a
   **last** phase (the user's 2026-10-22 ruling: "after it, briefs may prescribe the agreement
   transport for a last phase again").

The draft's text at lines 97–101 is right only for the drafting base, and its Hosts bullet lists
`phaseHostTM`, `phaseHostTM_run` with no last-phase condition (case 2) or the new lemmas (case 1).
