# Dispatch · bb1-sim fill, issued-fill-r1 (Claude, lead plus up to 2 sub-agents)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/c797f6f2c4c69e261277cd033bf2441fe4811df8/outbox/fills/bb1-sim)
is staged on the exchange at `c797f6f2c4c69e261277cd033bf2441fe4811df8`.
- It is on local branch `stage/bb1-sim-fill-exchange`: an SSH-signed commit on the exchange tip
  `860b45dcaf477cb70d5bcbc62c254b31f5e2ecf7` that adds only `outbox/fills/bb1-sim/` (34 files).
- It is pushed 2026-11-17.
- Brief SHA-256: `d4d029a4083d1c6b31f0c5183927334f391434ce22165928a25dd135f8342c9a`.

The worker is Claude (standing ruling: Claude for fills), a lead with up to 2 sub-agents. Seyoon dispatches.

**Bases.**
- **Issue base** `89a18a8225be1b76166af12a15179da291747783`, #346's head (Q9: stacked on T4's PR).
- **Patch base** `72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c`: the records tip `ca129d64cd54a92aabe517e5262058664b49f651`
  merged into the issue base (tree `b5a5842dd0a5af86975864b29065bec44758f561`).
- **Check base** `7cfe2b1b9a7e001d9ae972811cf85a332518111d`: #340's head `916afc25c21f5e52b4b01958186ad55d2f615fd1`
  merged in (tree `02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d`).

Both base commits are deterministic and unsigned; the pack's `tools/mkbase.sh` reproduces them.

**Records pin.** `fc0aa4e12977d7b79fb59f4d88a94412bdb90d3b`: the records commit that carries `briefs/pairings/fills/bb1-sim/issued-fill-r1/`. The
maintainer writes its full hash here, and in the prompt below, after committing.

**Before dispatch** (maintainer):
1. Commit `briefs/pairings/fills/bb1-sim/issued-fill-r1/` to the records branch. Put that commit's full hash for
   `fc0aa4e12977d7b79fb59f4d88a94412bdb90d3b` in the **Records pin** line and in the prompt.
2. Push the exchange commit. If it is replayed onto a newer exchange tip, put the pushed hash in the pack link, the
   staging line and the prompt.
3. Seyoon answers the open point in the README (patch base form; the pack implements (A)). If he chooses (B) or (C),
   re-pin the bases before dispatch.

## Prompt for Claude (lead, up to 2 sub-agents)

```text
You are the lead Claude worker for the pairing fill bb1-sim (Boneh-Boyen
T2 bb1_sim_real, T3 bb1_sim_random, and the Games/Relational targets
expect_simulate_rel and expect_sample_rel) in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned
Mathlib). You may use up to 2 sub-agents on disjoint files.

1. Read exchange/pass-shelat-ch5-8 at
   c797f6f2c4c69e261277cd033bf2441fe4811df8. Read README.md and
   outbox/fills/bb1-sim/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS
   (shasum -a 256 -c, from its directory). You are the lead the brief
   describes. The records of this issue are at commit fc0aa4e12977d7b79fb59f4d88a94412bdb90d3b of
   cryptography/pass-shelat-ch2-4
   (briefs/pairings/fills/bb1-sim/issued-fill-r1/, equal to the pack).
2. In a separate clone, fetch by name cryptography/pass-shelat-ch2-4,
   land/pairings-bb1-machine (#346, head
   89a18a8225be1b76166af12a15179da291747783) and fill/pairings-pair-bdh
   (#340, head 916afc25c21f5e52b4b01958186ad55d2f615fd1). Run the pack's
   tools/mkbase.sh: it must print the patch base
   72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c and the check base
   7cfe2b1b9a7e001d9ae972811cf85a332518111d. Start fill/bb1-sim at the
   patch base; run every build and check at the check base with your
   commits on top. Keep every branch local and commit with
   commit.gpgsign=false (also on the exchange).
   - Insert the ten approved readers verbatim from the pack's readers/
     (after Defs.lean:430 and BonehBoyen.lean:412); the results must
     have SHA-256 97ecb6e0... and 88454d6f... as the brief pins.
   - Prove expect_simulate_rel and expect_sample_rel (bodies only) and
     T2 and T3 (bodies and refreshed proof sketches) along design r1 §3
     (briefs/pairings/fills/bb1-sim/design-r1.md), with helper modules
     under IdentityBased/BonehBoyenSecurity/, using the probe's
     RealReads/setup_out interface and its proved step-M lemmas
     (inbox/fills/bb1-sim-statements/probe/ at a3cb45f6) as the ruling
     requires. Headers and statement prose stay frozen; bb1_sidSecure
     and prob_simulate_rel stay byte-identical.
   - If #346 merges during the job, rebase onto the records tip before
     you deliver, exactly as the brief's Rebase section says.
   Follow the binding rulings the brief lists (Q1-Q11, the Q7 follow-up,
   BS-F01: use CharP.natCast_injOn_Iio; DW-10 Q3: the FinDist coercion is
   notation), policy.md and the standing rules: frozen files change only
   by a scope request to Seyoon; readers only (Rule 10); no edit to
   Games/Probability.lean, Pairing/*, T4's files, cleanup Stage 1's homes,
   the GSW files or other campaigns' files; line width at most 100;
   files at most 1000 lines; no @[simp]; [BB04] tags only from the DW-7
   transcription; never fabricate an excerpt or location. Use only the
   pack's Mathlib roots, never lake build and never an unfiltered lake
   exe cache get, and check one module at a time with
   scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Run the brief's checks: the bootstrap (193 modules) and the sweep at
   the check head (13 modules plus your helpers, root excluded);
   admissions (base 22 in 10 modules, exactly the four targets removed:
   18 in 8); decls2 against the patch base (ADDED exactly the ten
   readers plus your declared helpers, 0 CHANGED, 0 REMOVED); the
   StmtDump and the frozen-header check with controls; the reader
   insertion check with controls; axioms (standard everywhere, and
   bb1_sidSecure standard with T4 in) with a sorry dependency trace;
   Rule 10 canonical seals A and B, strict and coe (coe-A canonical), on
   every changed owner (Relational, Defs, BonehBoyen,
   BonehBoyenSecurity, each helper) with base seals of the four existing
   owners, paired controls (a pair per reader and per helper
   definition) and the explicit-unfold scan; lint against the baseline
   92 FAIL / 104 WARN over 524 files; sizes; the name-clash and shadow
   scans; and the reuse and overlap disclosures. If a target looks false
   or a header does not elaborate, do not weaken it: report it as a
   question for Seyoon.
4. Sub-agents (at most 2): each owns files disjoint from the others',
   with its own git worktree and its own TCSlib olean tree, and
   .lake/packages linked to yours; only you run lake and fetch the
   cache. One Lean process at a time on the host, for all agents,
   through one lock. Only you commit on fill/bb1-sim, run the final
   checks and deliver. Sub-agent logs go under
   evidence/subagents/<name>/; REPORT.md records who did what.
5. Deliver checkpoint 1 (the readers inserted and every helper
   statement elaborating, with decls2, the StmtDump, the clash scan and
   an outline mapping T2's and T3's chain to the helper lemmas) as soon
   as it is ready, and the final, only under inbox/fills/bb1-sim/ on
   exchange/pass-shelat-ch5-8: REPORT.md; patches/ (git format-patch
   <patch base>..fill/bb1-sim, with COMMITS.tsv and its signing column);
   src/; evidence/ with its manifest; and the top-level SHA256SUMS
   (paths equal to the delivered files). Pull with rebase before
   pushing. Never force-push, never edit another path and never push a
   campaign branch. The maintainer reviews the result for the bb1-sim
   PR that Seyoon approves, and the bb1-sim gate audits it.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

After the three steps above:

**Ready to dispatch**
