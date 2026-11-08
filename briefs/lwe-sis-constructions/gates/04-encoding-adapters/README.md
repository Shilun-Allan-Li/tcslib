# Encoding-adapter statement gate

The next isolated draft is `cryptography/lwe-sis-adapter-statements`, in
`tcslib-lwe-sis-adapters`, targeting `cryptography/lwe-sis-constructions`.
It starts from the remotely verified central base
`2c37f3f486822a52f4a9e337c6b742e995ebb118` and the audited dependency stack
`ff8345b1d2ac2f605d81cdf6c23216aadb918abb` (#236 and #237). Neither dependency
is merged by this work. Their scoped statement/proof gates pass; their source-policy
and landing obligations remain open.

Frozen Lean/root: `6eec97be8f54d9990340900a5595dab32fb477f5`.
The new mathematical file is `TCSlib/Cryptography/Encoding/BinaryArith.lean`.
It has 20 declarations: 3 definitions, 3 proved complete defining equations and
14 admitted semantic/length/round-trip/efficiency statements with sketches.
No nontrivial fill starts before the external statement gate.

[REPORT.md](REPORT.md) records the full scope and evidence. A fresh serial
93-module sweep passes with 14 new and 17 inherited admission warnings.
All 263 earlier owned constants retain their recorded kinds, visibility and
axiom sets. The 20 new constants are precisely the 20 source declarations;
exactly 14 use sorryAx. Nine consumed public machine contracts have only standard
axioms. Scoped style is 0 FAIL / 2 unchanged WARN over 19 files.

The only existing-file Lean overlap is the Encoding facade's import/contents
entry, in its own commit. Shared owner definitions, probability readers, source
registry, root exports and pins are unchanged. The separate probability-reader
proposal is still unapplied; these adapters do not require it.

## Publication and review

The pack is `audits/lwe-sis-adapter-statements-pack.md`. The prepared input belongs
under `lwe-sis-constructions/outbox/gates/04-encoding-adapters-r1/` on the orphan
exchange. `build_review.py` assembles source/records-pinned inputs; it neither
publishes nor dispatches. The publication receipt distinguishes a prepared local
commit from a remotely retrievable revision. No new draft PR is claimed until
client publication succeeds.

The user selected **Codex** for this new statement audit and dispatches it.
Run the prepared client command:

```sh
python3 -I /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-adapters/briefs/lwe-sis-constructions/gates/04-encoding-adapters/publish_review.py --worker codex
```

`--check-only` performs local verification
without network access or mutations. The command publishes the records-only
proof-audit intake to #237's draft branch if it is still open, then pushes only
the new adapter draft branch and creates/updates its draft PR against the central
branch. It rebases the private sparse publisher before pushing only our exchange
namespace, then prints the exact kickoff. It never merges or pushes a central/
campaign ref, and never operates on the shared exchange checkout/index.

The auditor reads GitHub directly and returns
`lwe-sis-adapter-statements-findings.md` as Markdown in chat. No ZIP is required.
Codex is selected; no dispatch or remote publication is claimed yet.

**Not yet clear to merge — the adapter statement gate and proof fill remain,
alongside retained source-policy/landing obligations and user PR approval.**
