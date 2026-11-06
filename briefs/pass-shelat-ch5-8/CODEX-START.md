# Starting a new maintainer chat (Codex or any agent)

Paste this as the first message of a new chat whose workspace is a clone of
`https://github.com/Shilun-Allan-Li/tcslib`:

```
You are taking over as maintainer of the Pass–shelat formalization campaign in this repository.
Check out branch cryptography/pass-shelat-ch2-4 (git fetch first), then read, in order:
briefs/pass-shelat-ch5-8/AGENTS.md, briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md (all of it), the
last 30 rows of PassShelatChapter5-8Plan.md, and policy.md. Those files are your binding instructions.
Then check the live state (open PRs, the exchange branch exchange/pass-shelat-ch5-8 and its inbox/),
tell me in a few lines where things stand and what you will do next, and continue from the
hand-off's §6 "Next" items. Ask me rulings as multiple-choice questions, recommended option first.
```

Notes:
- **Codex and nested instructions.** Codex reads `AGENTS.md` files from the repository root down to
  its working directory. The root `AGENTS.md` is the repository's generic Lean workflow; the
  campaign's instructions are in this folder's `AGENTS.md`, which the prompt makes it read.
- **Fresh environments.** The maintainer's scratch (olean trees, worktrees) does not carry over. A new
  environment sets up Lean per `fills/fill-environment-addendum.md`: a narrowed cache fetch for the
  needed roots, then a bootstrap.
- **No exchange access.** If the new agent cannot push to the exchange branch, it can still prepare
  everything in the records and ask the user to relay.
