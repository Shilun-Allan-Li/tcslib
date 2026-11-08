# Codex construction-core statement review

The user freshly selected **Codex** for this gate. The user dispatches the job;
no review execution, verdict, merge or publication is claimed here.

| Item | Identity |
|---|---|
| Frozen Lean/root | `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf` |
| Bundled records | `4f403f777cda259ced52d74243d7ff7f9d547f99` |
| Audited dependency | `0769cba3e44c56700349f954190fc99d9e622270`, PR #236 |
| Draft branch | `cryptography/lwe-sis-phase1-statements` |
| Central integration / PR target | `cryptography/lwe-sis-constructions` |
| Exchange gate | `lwe-sis-constructions/outbox/gates/02-construction-core-r1/` |
| Bundle SHA-256 | `2e9e72b2211e33afbcbdf727f875d4cf27bcb0efb45b7000883391048dd1f9aa` |
| UTF-8 sections / bytes | 400 / 3,611,753 |
| Prepared local exchange commit | `a3c7e489569707a6a80c76037ae0eb3087b6061b` |

The prepared exchange commit is **not a published pin**. The publication helper
rebases before pushing, so use the successful command's printed exchange commit.
All 400 attachments have been extracted, hashed and compared with their exact
revision-qualified Git objects. Both indexes and the gate/payload checksums agree.

## Client publication

The connector rejected retargeting PR #236 with HTTP 403, and native Git/GitHub
networking remains blocked. Run with the client's ordinary credentials:

```sh
python3 -I /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-phase1/briefs/lwe-sis-constructions/gates/02-construction-core/publish_review.py --worker codex
```

This retargets #236 to the central LWE/SIS branch, pushes the new draft branch,
creates/updates its draft PR against that same central branch, and rebases/pushes
the private exchange publisher within this namespace. It performs no merge or
central/campaign push, force, stash or reset, and leaves the shared exchange
checkout/index alone. An error stops the command. `--check-only` performs only
the local source/payload validation.

After success, paste its printed kickoff into a fresh Codex chat. Codex reads
GitHub directly and returns `lwe-sis-core-statements-findings.md` as Markdown in
chat. No ZIP attachment is needed. Source/records pins and the bundle hash remain
unchanged by exchange rebasing. The vendor-neutral pack stays frozen; this
separate record captures the fresh reviewer choice.

**Ready to run — client publication and the Codex kickoff are prepared. The
statement review is undispatched and no merge clearance is claimed.**
