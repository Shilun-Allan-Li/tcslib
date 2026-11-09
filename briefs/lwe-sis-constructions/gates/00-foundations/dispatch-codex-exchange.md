# Codex audit: GitHub inputs, Markdown output in chat

The user selected Codex and explicitly requested exchange-hosted inputs. The auditor
does not need an attachment. This supersedes the earlier attachment-based kickoff;
it does not change the mathematical source, evidence, audit scope or source-access limits.

| Item | Identity |
|---|---|
| Remote exchange | `exchange/pass-shelat-ch5-8` |
| Dedicated namespace | `lwe-sis-constructions/` |
| Gate | `lwe-sis-constructions/outbox/gates/00-foundations-r1/` |
| Publisher checkout | `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange-lwe-sis-publish` |
| Publisher branch | `publish/lwe-sis-phase0-r1` |
| Initial remote exchange base | `5b1d70d558542bf491680b4b9ee2379038bbfd3f` |
| Frozen Lean/root | `4364d0e0fe9accd649b6acb4751e8684aa93ad1e` |
| Bundled records | `06cdbc030168d9e6662b12960882d8ca6f5b1fa7` |
| Bundle SHA-256 | `9e39453ac97f8fbdc8014a302aa18c40b41f7e4692641ca5b141e0d79f25e68b` |
| Bundle sections | 155 |

The remote exchange root and protocol were inspected at the initial base. The chosen
namespace did not exist. The separate sparse clone checks out only the root protocol
and the new namespace. The shared checkout's branch, index and other files are untouched;
the protected other-campaign namespace is not checked out in the publisher clone.

Seven explicit files are prepared: the namespace README and the gate README, frozen
bundle, two manifests, SHA256SUMS and an extraction verifier. `exchange-publication.json`
records every file's hash. The bundle is unchanged. The verifier successfully recovered
all 155 original attachments and checked each length and SHA-256. No Lean check was rerun
for this transport-only change.

## Publication

Run from any directory:

```sh
python3 -I /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-crypto-parallel-kickoff/briefs/lwe-sis-constructions/gates/00-foundations/publish_exchange.py
```

The script checks the dedicated clone, branch, remote, clean index and prepared hashes;
runs `git pull --rebase origin exchange/pass-shelat-ch5-8` with automatic stashing disabled;
checks pending changes are only under the dedicated namespace; then makes a normal push
to the exchange ref. No force, reset, stash, campaign destination or code-branch merge
is used. A conflict or rejected push stops; inspect it rather than forcing anything.

After success, the script prints the exact publication commit, a permalink to the gate
README, and the pasteable Codex audit prompt. Use that verified publication pin, not the
initial exchange base or an unpushed local commit. Remote publication is not claimed
before this succeeds. The user dispatches the fresh Codex chat.

The auditor reads the root exchange README, namespace README and gate README at that
commit, verifies SHA256SUMS and the revision-qualified manifests, then follows the pack
at the start of the bundle. It returns `lwe-sis-phase0-findings.md` in chat, without
pushing, filling proofs, modifying branches or dispatching another job.

**Ready to run — the exchange publication is prepared; the network block must be
resolved before the GitHub audit can be dispatched.**
