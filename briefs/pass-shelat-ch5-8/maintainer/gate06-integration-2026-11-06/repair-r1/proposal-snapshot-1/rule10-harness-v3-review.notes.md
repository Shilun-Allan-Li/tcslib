# Rule-10 harness V3: serialized requests, no budget change

**Stable preparation tool; native V3 outcome pending.** Frozen library:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. No library edit, Lean/cache command, Git command,
app, or existing-evidence mutation was performed in this invocation. Only ignored repair
artifacts were written. Root retains publication and all native checking.

## V2 disposition

The bounded-depth V2 BPPBridge retry failed at generated INSTALL **14:0** and EOF **2684:0**,
again with `maximum recursion depth reached in the code generator`. No install/EOF seal markers
appeared. This attempt remains **invalid harness evidence**. Increasing `maxRecDepth` to 8192
was insufficient; do not try larger budgets. The concrete compiler failure is known, while
its precise relation to literal lowering/inlining is still an inference, not an isolated native
control result.

V3 replaces the growing generated expressions, rather than changing options. The original
V1 and V2 probes, manifests and logs remain intact. This note supersedes the V2 retry method
for future Gate06 attempts; historical evidence is not rewritten.

## Stable tool and fresh destinations

Tool: `prepare_rule10_harness_retry_v3.py`.
SHA-256: `ae79f1ec66e93c8bc7749a53e12e3d383feda020ad2978520a0cfa24b12eb5de`.

It reads the **original** completed `seal-manifest.json` and original collector/catalog evidence,
not the V2 manifest. It regenerates ordinals **19–51** only, preserving every original record's
ordinal/module/source identity, raw source SHA, closure, complete ordered request rows, counts,
actual-Name policy, installed-status checks and EOF checks.

- New labels: original label plus `_HarnessV3`.
- Scratch: `.lake/ps-maintainer/gate06/rule10/seals-retry-v3/`.
- Saved sources/records: `seals-retry-v3/*.source.txt` / `.json`.
- Manifest: `seal-retry-v3-manifest.json`, with the original `library_verification`, original
  probe-record format, new source maps/fingerprints, and `original_manifest_sha256`.
- Sensitivity sources: fresh `controls-retry-v3/` scratch/saved directories and
  `controls-retry-v3-manifest.json`.
- Builder snapshot: `harness-retry-v3-builder.source.txt`.

Every destination must be absent; existing attempts are never overwritten. All outputs remain
`PREPARED_NOT_RUN`, with sensitivity flags false, until root runs and reviews them.

## Request representation and unchanged validation

For each INSTALL and EOF command, V3 emits **one escaped Lean String data literal** containing
newline-separated rows with tab-separated `(spelling, home)` fields. A fixed-size runtime loop
splits rows and fields and pushes pairs into the same `requests` array. It rejects malformed
rows, empty fields and a request count different from the exact original count. Empty request
sets have an empty string and zero parsed rows, handled explicitly.

The control catalog also had a growing four-tuple literal. V3 serializes all four fields
(spelling, home, matcher, reducibility) into one data string; its runtime parser validates the
Boolean matcher field and retains the original metadata checks. The fixed three-reader array
is preserved verbatim and does not grow with the seal set.

Preparation rejects empty/control-containing fields and duplicate spellings, and checks an
exact Python round trip of **all ordered fields**, including the control metadata. JSON escaping
preserves quotes, backslashes and Unicode. The generated payload is fingerprinted as part of
the probe. There is no silent filtering or parsed-row omission.

Only the request-construction region changes. The existing code before it and from the
actual-Name catalog onward is byte-identical for a given label. In particular, requests are
resolved against uniquely matching **actual imported Lean.Name values**; `mkIdent n` still uses
those values. No Name is reconstructed from a string. Home/definition checks, irreducibility
installation, active/already counts, per-name logs, verified counts and EOF installed-status
checks are unchanged. Full seal coverage is retained.

V3 adds **no `maxRecDepth` option** and no scoped `set_option ... in` command. Original source
options and proof budgets are preserved (the pinned default is 512). The earlier harness's
`maxHeartbeats 0` behavior is unchanged. No unsafe option or reducibility override is introduced.
The large literal no longer creates one constructor/instance expression per request row in the
command; the parser's code shape is independent of the number of rows.

## Controls and native acceptance order

The three fresh controls use BPPBridge's **full 2,482-name closure**:

1. Anonymous-only `inArg` body equality unsealed: pass with zero errors.
2. Identical anonymous equality sealed: exactly one error at its recorded `rfl` proof line.
3. Sealed positive file: all three exact `inArg_eq`, `advInput_eq` and `uexp_def` readers pass.

Catalog checks, complete installation counts and EOF installed-status checks must succeed;
harness failures never count as sensitivity. These controls do not assert matcher sensitivity
for the new attempt. Root should first obtain a valid BPPBridge harness, then check these three
controls before interpreting the remaining retry survey. Source failures with valid markers
remain failures for review, not exclusions or automatic passes.

## Static validation and limits

The complete preparation was executed with every write/mkdir intercepted in memory: **33 seal
probes + 3 controls, 108 prospective outputs**, zero actual evidence/scratch-probe writes.
Checks covered original source-byte recovery, exact name/home ordering and counts, complete
control matcher/status round trips, fresh-path rejection, no remaining request-array literal
builds, no recursion option changes, and equal request-parser line counts for zero versus
thousands of rows. Invalid delimiter, duplicate and empty-field fixtures were rejected.

Python syntax and serialization checks passed. Lean syntax/elaboration, compiler behavior,
native installed-name counts and sensitivity have **not** been verified by this agent. Root
will run the serial native queue. The previous notes' coded-diagnostic parser finding remains
applicable; root owns the v3 runner/parser and preserves old logs.

| Reference | SHA-256 |
|---|---|
| Original seal manifest | `75b11d1cf5324eea8066b898e5c37a677de266513cdde4be697ef8bf8149ba73` |
| Original seal builder | `fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a` |
| Invalid V2 BPPBridge log | `6aa2c948e88d67bbd4d6222608beab29ac8ad9aefc4fb9e55b8dca6f1bce3a6f` |
| Frozen V3 preparation tool | `ae79f1ec66e93c8bc7749a53e12e3d383feda020ad2978520a0cfa24b12eb5de` |
