# Independent proof audit: client publication

The combined statement audit passes 0/0/1/4, its comment-only F01 repair is
verified, and 31 independent proofs are now filled and checked. Seventy owned
admissions remain. The shared-reader/loop readiness holds are unchanged.
This is one proof-review packet on existing draft PR #250, with no new PR branch.

| Item | Identity |
|---|---|
| Branch | `cryptography/lwe-sis-construction-statements` |
| PR / target | #250 / `cryptography/lwe-sis-constructions` |
| Statement freeze | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Passed-gate/doc-repair baseline | `13aff4d33d282ccaed2727af3febc0ebddeba0e5` |
| Filled Lean/root | `f293b63200ee3c6de6e709925f67c4d60fdc7b4a` |
| Bundled records | `ebb0422cd08c44494b3b0c76020de18492cb8ff7` |
| Bundle SHA-256 | `c7837eb73e59a5d0ee0cdda33ae275bb096e80715a10f3f6f1b84004d921d675` |
| Sections / bytes | 2,796 / 43,628,531 |
| Source / record attachments | 153 / 2,643 |
| Reviewer | Codex, under the user's morning selection |

Five exchange checksums, both ordered revision-qualified indexes, extraction and
all 2,796 revision/path Git blobs pass. `review-publication.json` records the
private prepared publisher commit; it is not an already published exchange pin
and may change during the required rebase. The actual pushed pin is printed by
the helper. No new external job is dispatched by preparing these inputs.

## Run on the client

GitHub publication is unavailable in this sandbox (native DNS failure and the
connector's earlier HTTP 403). The user offered client publication:

```sh
python3 -I ~/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-construction-statements/briefs/lwe-sis-constructions/fills/04-construction-independent/publish_review.py --worker codex
```

The helper verifies a clean own checkout/private publisher, 153 source and seven
owned payload hashes, and the frozen proof source. It refuses a closed/non-draft
or differently targeted #250, pushes only its own feature branch, and updates
the draft title/body. It rebases the separate private publisher before pushing
only `lwe-sis-constructions/` changes to the orphan exchange. It never switches
or edits another maintainer's checkout, touches the shared exchange index, force-
pushes, stashes, resets, pushes a central ref, merges or dispatches a worker.

If an operation fails or the rebase conflicts, stop and inspect that failure and
any completed feature-PR step; do not bypass the guards. `--check-only` performs
the local checks without any network or mutation. Five simulated scenarios test
updating #250 and rejection of a closed/non-draft PR or foreign exchange path;
they perform no actual remote operation.

## Dispatch after publication

Paste the printed kickoff into a fresh Codex auditor chat. It supplies the actual
immutable exchange commit and the source/records/bundle identities above. The
auditor reads GitHub directly and returns `lwe-sis-independent-proofs-findings.md`
as Markdown in chat. No ZIP is needed; do not dispatch against an unpublished
prepared exchange commit.

The scope is all 31 fills in seven modules, all 220 frozen source declarations,
the complete 589-constant inventory and 48 backing contracts. The final fresh
144-module sweep passes in 303.792 seconds; the final axiom probe takes 53.149
seconds. All 31 targets are standard-axiom only. Two older compiler helpers move
emitting module; separate probes verify all 575 prior level/type representations
exactly, with baseline-object provenance explicitly attested. Seventy other
admissions, all N01–N04 obligations and user-controlled integration remain.

**Ready to run — publish the #250 update and its owned packet, then dispatch the
printed Codex prompt. No merge is ready.**
