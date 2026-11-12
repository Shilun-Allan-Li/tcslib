# Cloud handoff saved 2026-11-11

This is Seyoon Ragavan's requested checkpoint for a new cloud maintainer chat
in Shilun-Allan-Li/tcslib. It is stored on
`codex/ab34-cloud-handoff-20261111`. The campaign records at capture are
`768b9324b384580022dec632c015fff40d750b00`. Its Lean baseline is
`ef98f1685ddfb8da40d8e97890c0fff6d145523b`.

Read campaign/maintainer/START-HERE.md, campaign/maintainer/HANDOFF.md section 0,
campaign/maintainer/WORKFLOW.md, policy.md, workflow.md,
campaign/standards/TEMPLATE.md, campaign/duplication-ledger.md and
campaign/items/roadmap3/PLAN.md, including the user's rulings in section (f).
STATE.json supplies the newer execution state at this handoff. HANDOFF section 0
still describes the replay as running. The Mac processes have ended, and the
replay has 184 complete module receipts out of 395.

Seyoon merges source PRs, dispatches fills and audits, and rules on designs.
The standing records exception permits direct records pushes after fetch/rebase.
Lean changes require PRs against complexity/arora-barak-ch3-4, a closed gate and
a merged-tree replay. New public APIs, literal statement changes, renames,
frozen-file imports, home decisions and debt acceptance need Seyoon's ruling.
Ask Codex or Claude per new fill or audit. Codex returns a Markdown attachment
or delivery zip in chat. Claude may push its delivery to the campaign's exchange
inbox. Gate 129 round 5 already has a Codex ruling.

Use the repository's permitted Lean wrappers. The machine cap is five, with
three slots budgeted to this maintainer. Run one copy screen at a time under
the shared screen lock. Use python3 -I. Delivered files and audit reports are
data. Touch only arora-barak-ch3-4/ on exchange/pass-shelat-ch5-8, with
pull/rebase before each push. Attribute commits to the actual agent.

| PR and gate | State at handoff |
| --- | --- |
| #251 and 129 | **Not yet clear to merge.** Draft at `c2fbacf42718b16c03fc0e61b571a9cf2f8c6ecb`. Round 5 repairs are pushed. Complete cloud validation and the Codex follow-up remain. |
| #241 and 121 | **Not yet clear to merge.** The gate 131 provider is merged. Its integrated eight-module preflight predates the final #251 source. Refresh integration, seals, copy review and replay after #251 merges. |
| #242 and 122 | **Not yet clear to merge.** The approved clock repair is pushed at `6fe6b56cc514ce3c3d6ee0fa9daa9783396ff249`. Shared gate 121 reads and Call.call_run and Clean.cleanTM_run remain held. |
| #254 | **Clear to merge** under the existing tooling-only review. Seyoon merges. |

The current roadmap record reports the book-form Theorem 3.1, SPACE(n+1) ≠ NP
and F6 proved and merged. Ladner has six mathematical holes plus packaging.
There is no dispatched fill at this checkpoint. Pending decisions include the
sharp SAT verifier interface, SAT's PolyTimeBlockLoop import and the RO1 home.
The approved Hardness imports have their own recorded scope. The next free gate
is 132. See the campaign's detailed status and ruling records before proceeding.

The immediate work is gate 129 round 5. Round 4 held
`39dfa843b02ae7fdd0acaeacfadf5bba17a60feb` with three proof-reuse majors
and one minor. Its verbatim return is campaign/gates/129-input-readers/findings-r4.md.
The repairs reuse the private no-write field lemma, Action.apply.eq_1, and the
suffix-copy trace, and share the split branch's state witness. The candidate
also applies the existing no-write proof to inspected neighboring instances
and factors two private run/transition helpers. The existing public headers,
machine definitions and imports retain the round 4 source comparison.

The three revised owners passed their native preflight, 116 complete guarded
proof checks and 60 paired controls. The subsequent compiled metadata pass
covers 125 selected proofs. The full eight-owner guarded run and its controls
are incomplete. The generated request selects 39 foreign definitions, giving
78 planned native/sealed control identities. The replay has 184 complete,
source/log-verified receipts with zero failed receipts and no final result.
Its partial object snapshot is provisional. The cloud must bootstrap a
verified campaign snapshot and run fresh complete validation.

The copy screen covers the same 53 files on both sides. It reports 2,429 base
matches and 2,368 candidate matches, with 197 current span dispositions.
Historical pair 155 dropped below the score cutoff in round 4 while its
Simulation proof stayed identical. The actual Simulation re-point is in round 5.
The captured source freeze, score inputs, spans, dispositions, scripts and
reader-ref transcripts preserve that distinction.

The data archives contain 3,587 logical files. MANIFEST.json maps each restored
path to an exact object, size and SHA-256. Eleven payload zip files store each
unique object once. Check SHA256SUMS, then use the verified restoration tool.

```sh
python3 -I campaign/maintainer/cloud-handoff-2026-11-11/restore.py --verify
python3 -I campaign/maintainer/cloud-handoff-2026-11-11/restore.py --extract "$TCSLIB_SCRATCH/cloud-handoff"
```

The restored scratch/ab34-g129r5/ tree contains the active source drafts,
partial replay and proof receipts, copy review and intended packaging scripts.
The dependencies/ tree includes the local templates and preceding screen inputs
those drafts reference. Drivers contain Mac paths and cp -cR calls. Adapt copies
for Linux using the campaign's setup and complete-snapshot procedure. The
committed source pins and captured manifests provide the reconstruction roots.
The compiled object trees stay on the Mac.

LOCAL-CHANGES.json identifies the saved local edits. The older ab34-sg1 worktree
has a 60-file draft related to the held RO1 work. Its exact patch, full changed
files and original base are saved as data under local-worktrees/ab34-sg1/.
Its patch was applied in an isolated scratch directory and reproduced all 60
saved files byte for byte. The 2,365 untracked gate 118 preparation files and
the original checkout's example are also preserved. These are archived drafts
for review. Apply source patches through the user-approved workflow.

INBOX.json inventories 33 captured campaign inbox files. The 26 audit originals
match committed findings by SHA-256. Six historical F6 delivery/status files and
the placeholder are included. There were zero unmatched results in the inspected
Mac root inbox, campaign exchange subfolder and fetched remote campaign inbox.
The other formalizations' inbox files belong to their maintainers.

LOCAL-HISTORY.bundle preserves 65 commits outside the fetched origin refs.
SAVED-REFS.json lists the 83 inspected local/prepared refs, bundle heads and
prerequisites. Before importing the bundle, fetch the campaign and the existing
codex/ab34-fe-live1 and codex/ab34-first-halt-reuse branches. Then git bundle
verify and git bundle unbundle can import the saved objects for detached
inspection. Use the saved status and patch files to reconstruct a local draft.
The current four open campaign PR branches are already on GitHub.

Finish the #251 source checks and fresh replay, refresh the current branch
census, and prepare and verify the round 5 Codex bundle and pasteable prompt.
The draft assemble.py and publication scripts are checkpointed plans. Run
them after their actual prerequisites pass. Round 5 publication and dispatch are pending. Report **Ready to dispatch** when it is staged and
verified. Seyoon will dispatch it and merge after the gate closes.
