# Dispatch · dw10-seal-inventory, issued-r1 (Claude, lead plus up to 2 sub-agents)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/aae6bc0654354e4e75e22b3ab6cbf7198921d89c/outbox/audits/dw10-seal-inventory)
is staged on the exchange at `aae6bc0654354e4e75e22b3ab6cbf7198921d89c` (local branch `stage/dw10-exchange`, an
SSH-signed commit on the exchange tip `d929cc21ec817b2518d57a7262e42744728f029a` that adds only
`outbox/audits/dw10-seal-inventory/`; **not yet pushed**, so the link resolves only after the push). Brief SHA-256
`24efc89b969d1427660839ef9e1fad26dd64fd7c12986dcc506ff9f9bb0ea6fb`; pack `SHA256SUMS` SHA-256
`c59293d9baecb4513fafcc3fa6abb20de7fc03269e1d28efd02191697f93ce13`. The worker is Claude (standing ruling: Claude for
fills and all other external jobs), a lead with up to 2 sub-agents on disjoint owner sets. Seyoon dispatches.

**Base.** Issue base `f472accd5e000a53d0fbe02b5414435429ce4a70`, the records tip at staging; its Lean equals
`a6d01b1bd1a92e2ac0be9999689467fea7e4e77b` (the merge of #341; `TCSlib` tree
`06b51ea90a9a0ef49e1dc3e7034ba32ec9b75fe6`). Checks only: no Lean branch, no PR.

**Ruling.** DW-10 (Seyoon, 2026-11-17): "inventory now, fix in Stage 2"; seal-B-only items and files outside the
campaign are listed and handled by separate ruling (`cleanup-stages.md` § *Historical seal debt*).

**Records pin.** `<RECORDS-PIN>`: the records commit that carries this folder. The maintainer writes its full hash
here, and in the prompt below, after committing.

**Before dispatch** (maintainer):
1. Commit `briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/` to the records branch; put that commit's full hash for
   `<RECORDS-PIN>` in the **Records pin** line and in the prompt.
2. Push the exchange commit. If it is replayed onto a newer exchange tip, put the pushed hash in the pack link, the
   staging line and the prompt.

## Prompt for Claude (lead, up to 2 sub-agents)

```text
You are the lead Claude worker for the Pass-shelat DW-10 job
dw10-seal-inventory (the historical seal-debt inventory, checks only) in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned
Mathlib). You may use up to 2 sub-agents, on disjoint owner sets.

1. Read exchange/pass-shelat-ch5-8 at
   aae6bc0654354e4e75e22b3ab6cbf7198921d89c. Read README.md and
   outbox/audits/dw10-seal-inventory/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS
   (shasum -a 256 -c, from its directory). You are the lead the brief
   describes. The records of this issue are at commit <RECORDS-PIN> of
   cryptography/pass-shelat-ch2-4
   (briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/, equal to the
   pack); the #248 seal ledger, the 2026-11-10 provider rulings, the
   SG-F07/SY-F07/C-F02 records, DW-5's README and tools and the
   deferred-work register are there too.
2. In your own clone, fetch cryptography/pass-shelat-ch2-4, main and
   exchange/pass-shelat-ch5-8 by name. Work at the issue base
   f472accd5e000a53d0fbe02b5414435429ce4a70 (its Lean equals
   a6d01b1bd1a92e2ac0be9999689467fea7e4e77b; check it). This job is
   checks only: change no .lean file, commit to no Lean branch, open no
   PR. Keep every branch local and commit with commit.gpgsign=false.
   Bootstrap order.txt (613 modules) into one olean tree with
   scripts/lean_check_tree.sh, one module at a time; record its object
   map, make it read-only, and rehash it at the end. Use only narrowed
   Mathlib roots, never lake build and never an unfiltered lake exe
   cache get. Run Python as python3 -I.
3. Run the brief's Rule 10 canonical suite on the 434 owners of
   owners.txt: collectors; seals A and B, strict and coe (coe-A
   canonical), whole-file over the full TCSlib import closure, with
   -DmaxErrors=0 and the install and EOF records, reporting requests
   and errors per declaration; paired controls; the explicit-unfold
   scan; the generated-equation reads. On the 21 files of
   list-only.txt run the seals and the scan only. Then reconcile every
   row of ledger-historical.tsv, ledger-current.tsv, provider-pairs.tsv
   and named-findings.tsv (FIXED_SINCE, STILL_OPEN or CHANGED), list
   every failure they do not have as NEW, and classify each open item
   (STAGE2, SEAL-B-ONLY, STRICT-ONLY, STATEMENT or OUTSIDE) with its
   likely fix. Do not change the owner set or decide an open question
   yourself: report it as DW10-W1, ... with the recommended option
   first. Follow policy.md and the standing rules.
4. Sub-agents (at most 2): each owns an owner set disjoint from yours
   and from the other's (owners.txt, column agent, suggests the
   split), with its own git worktree and probe directory, reading your
   olean tree read-only, and .lake/packages linked to yours; only you
   run lake and fetch the cache. One Lean process at a time on the
   host, for all agents, through one lock. Only you commit, merge the
   tables, reconcile and deliver. Sub-agent logs go under
   evidence/subagents/<name>/; REPORT.md records who did what.
5. Deliver checkpoint 1 (bootstrap, collectors, and the seals and scan
   of every file that holds an input item, with a status for every
   input item in inventory.tsv) as soon as it is ready, and the final,
   only under inbox/audits/dw10-seal-inventory/ on
   exchange/pass-shelat-ch5-8: REPORT.md with the totals, the Stage 2
   fix list grouped by file and the lists for separate ruling;
   inventory.tsv; evidence/ with its manifest; and the top-level
   SHA256SUMS (paths equal to the delivered files). Commit as
   "audit dw10-seal-inventory: checkpoint N" and "... final". Pull
   with rebase before pushing. Never force-push, never edit another
   path and never push a campaign branch. The maintainer will review
   the result and turn it into the cleanup Stage 2 brief and the
   questions for Seyoon.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

After the steps above:

**Ready to dispatch**
