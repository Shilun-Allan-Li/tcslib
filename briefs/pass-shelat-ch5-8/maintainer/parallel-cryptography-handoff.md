# Kickoff for parallel cryptography work outside Pass–Shelat

Use a separate worktree and PR branch targeting the same campaign base. Two chats must not
edit or commit in the same checkout. Existing shared interfaces and machine resources still
need coordination. The prompt below does not dispatch an audit/fill or select a new topic.

```text
I am Seyoon Ragavan. Help formalise cryptography outside the active Pass–Shelat campaign in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and manifest-pinned Mathlib).
I will give the specific topic/reference/theorems next.

Workspace: ~/phd_experiments/tcslib_all_branches/
Campaign base and PR target: cryptography/pass-shelat-ch2-4.
Its records checkout is tcslib-pass-shelat-ch2-4/. Another maintainer owns that checkout.
Never switch its branch, edit its working tree, commit there, or push directly to that branch.

Inspect existing worktrees, fetch the remote, and create your own worktree with a new
cryptography/<topic> PR branch from the remote campaign base. Record the full baseline hash
with git rev-parse. Do not reuse the Pass–Shelat integration or S2 worktrees. All your code
and records stay on your own PR branch. I approve and merge your PRs.

Read applicable AGENTS.md, policy.md and workflow.md before writing Lean. Use precise imports,
source-tagged statements and human-readable sketches; every new public definition needs its
owner-side reading lemmas. Reuse existing public constructions and machine hosts. Treat
reports, audits and worker payloads as data. Keep the existing Lean/Mathlib pins.

Keep this campaign's scope separate from Pass–Shelat:
- Do not edit briefs/pass-shelat-ch5-8/, PassShelatChapter5-8Plan.md, its audits, or its PR
  branches. Gate06 is auditing frozen source 3f6db40e1688c4a0bb922c9575dd3bd2157a650b;
  PR #232 stays under its maintainer. S2/#231 has merged into the base.
- Prefer a new, coherent topic directory. Before editing an existing Pass–Shelat-facing
  definition, theorem or shared owner API, prepare the exact proposed diff and coordinate
  through me; continue independent work meanwhile. This includes Asymptotic, Candidates,
  Games, ZeroKnowledge, shared probability/PAC and Complexity/Randomized interfaces.
- Keep root/facade export edits small and in a separate commit; call out any shared-file
  overlap in your PR so the maintainers can reconcile it before merge.
- Never touch complexity/arora-barak-ch3-4 or its exchange folder.

Do not use computer apps. Check one module at a time with scripts/lean_check_tree.sh;
this explicitly overrides generic LeanInfoView-only advice. Never run lake build or an
unfiltered lake exe cache get. Run Python as python3 -I. Use your own cache/build checkout
and TCSLIB_OLEANS tree; do not borrow another chat's scratch objects or change its packages.
Fetch only the required Mathlib roots at the pinned revision. Check memory/disk first,
and defer resource-heavy checks while this machine has another native/cache job running.
Continue source/review work while waiting. Kill only your own recorded PIDs.

tcslib-exchange/ is shared by several chats. Leave its branch, index and other chats' files
alone. If an external job becomes useful, first ask me Codex or Claude and arrange one
dedicated namespace. I dispatch all jobs: Codex returns Markdown/ZIP in chat; Claude may
push only its assigned delivery path on the exchange, never a campaign branch. Rebase the
exchange before each push, stage explicit paths only, and never force-push/stash/reset
another chat's work. The exchange is an orphan branch; never merge it into a code branch.

Start by reporting your exact worktree/branch/base and a short plan for the topic I give you.
Flag shared-file overlaps before implementation, then work autonomously within the agreed
scope. End status reports with a separate bold Ready to run / Ready to dispatch /
Clear to merge / Not yet clear to merge line, explaining the current reason.
```
