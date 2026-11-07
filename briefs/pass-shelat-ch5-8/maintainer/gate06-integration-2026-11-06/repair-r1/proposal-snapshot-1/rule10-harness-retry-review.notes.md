# Rule-10 generated-command recursion and coded diagnostic review

**Preparation only; native retry and sensitivity checks are pending.** Library head remains
coordinator-pinned `e9d64158461bfe24ddc88ab885bc4017899b4c16`. This invocation edits only ignored
repair artifacts, and runs no Lean/cache/Git or app. Existing evidence, original probes,
original builders/runners, manifests and library source are untouched.

## Failure classification and root-cause evidence

`G06Seal_019_TCSlib_Cryptography_Randomness_BPPBridge.log` contains two diagnostics:
probe **13:0** and **2680:0**, both `maximum recursion depth reached in the code generator`,
with an inline stack headed by `inferInstance`. These are the generated INSTALL and EOF
`run_cmd` commands. Neither line belongs to `source_to_probe_lines`. There are zero
`G06-NAME`, `G06-SEAL` or `G06-SEAL-END` markers. This is **invalid harness evidence**; it says
nothing about whether BPPBridge's original proofs survive sealing.

The probe contains **2,482** request pairs. Splitting the literals into 128-entry chunks still
places every chunk inside one generated command. Ordinal 18 completed both seal markers with
1,922 requests; the largest remaining request set is ordinal 20 with 2,647. The size-dependent
compiled command, including its literal/instance code, is the likely source of excess compiler
recursion. The log identifies the compiler phase and command boundary, but does not isolate a
particular array-lowering operation; that narrower mechanism remains an inference.

Pinned Lean 4.25 source evidence:

- `Lean/Compiler/LCNF/Simp/SimpM.lean:145–170`: compiler `withIncRecDepth` compares
  `MonadRecDepth.getRecDepth` with `getMaxRecDepth` and emits exactly this code-generator error,
  including the inline stack. It is not a heartbeat exhaustion diagnostic.
- `Init/Prelude.lean:4690`: **`defaultMaxRecDepth := 512`**.
- `Lean/Util/RecDepth.lean:15–16`: the `maxRecDepth` option uses that default.
- `Lean/Elab/BuiltinCommand.lean:501–510`: flat `set_option` updates command/scope options;
  the command `in` macro creates a section and closes its local scope. Do not wrap INSTALL in
  `set_option ... in run_cmd`: that could discard the local irreducibility attributes.

The earlier 1024 default assumption is explicitly superseded by the pinned value **512**.

## Frozen preparation tool

`prepare_rule10_harness_retry.py`, SHA-256
`8d91291640dbac9bc142db2c72b8ef17c17036f5637b349071c964f76cb57595`, is stable for root review/invocation.
It regenerates only ordinals **19–51**, preserving all 33 original probe-record schemas,
raw source bytes, closures, ordered request rows, counts, and original ordinal/module mappings.
It uses the reviewed actual-Name catalog and both `seal_command` phases unchanged internally.

The only command-option change is flat, bounded `set_option maxRecDepth 8192` immediately
before each generated command, followed by flat `set_option maxRecDepth 512` after it.
INSTALL is restored before any original source command. EOF is raised only after the original
source bytes. No source proof gets an increased budget; none of these 33 original source files
sets `maxRecDepth`. The previous `maxHeartbeats 0` harness behavior is preserved. There is no
reducibility override beyond the existing local irreducibility installation.

Fresh destinations, without overwriting prior attempts:

- Scratch: `.lake/ps-maintainer/gate06/rule10/seals-retry/*_HarnessV2.lean`.
- Saved sources/records: `seals-retry/*_HarnessV2.source.txt` and `.json`.
- Main `seal-retry-manifest.json`: original `library_verification`, original-format `probes`,
  plus `original_manifest_sha256`, retry provenance/options and refreshed byte/line maps.
- `controls-retry-manifest.json` and `controls-retry/`: three controls under the **same BPPBridge
  2,482-name closure**, with the same bounded harness method. These are the anonymous-only
  `inArg` unsealed/sealed pair and the sealed three-published-reader positive control.

After the first future probe has a valid harness, root should run these controls: unsealed
passes; sealed anonymous `rfl` fails exactly once at its recorded proof line; sealed public
readers pass; every catalog, installation count and EOF installed-status check succeeds.
The control proof bodies also run at **512**. Flags remain `PREPARED_NOT_RUN`/unverified.

Static validation executed the whole preparation with every output operation intercepted in
memory: 33 seal probes + 3 controls, 108 prospective outputs, no actual record or scratch-probe
writes. It checked exact request-set equality, recovery of all original source bytes, duplicate
output rejection, source fingerprints, and restoration to 512 before every control proof.
This is not native elaboration or sensitivity evidence. Root owns the v2 runners.

## Is a depth increase sufficient?

**8192 is an appropriate bounded first retry**, because the diagnosed compiler guard reads
this budget. It is not a structural guarantee for arbitrarily large generated literals.
Do not jump to 32768 or an unlimited budget without evidence: a larger recursive command can
still consume substantial stack/resources. Keep the original failed attempt and require the
new native installation/EOF markers and exact counts before interpreting source diagnostics.

If this retry still fails, prefer a constant-size-code data route: emit one escaped string
containing the validated `(spelling, home)` rows, parse it at runtime, require the exact original
row count, exactly two nonempty fields per row, and unique spellings, then retain the existing
actual-Name catalog/home/definition/installed-status checks. Forbid delimiter/control characters
in each original field and fail on every parse anomaly; do not use `filterMap` to drop malformed
rows. Resolve actual imported `Lean.Name` values from the catalog, never reconstruct names from
strings. This avoids a large constructor/let expression in the compiled command. It is a
fallback design, **not implemented or verified** in the minimal depth-only preparation.

## Coded diagnostic parsing bug

The current generic regex requires literal `error:` and misses
`error(lean.unknownIdentifier):`. The completed HashAndSign log has **7** located errors;
old parsing counts **6**. The missed diagnostic is probe **1719:8**,
frozen source **286**, unknown identifier `runAt_hsGen`.

A compatible location pattern is:

```python
r'(?m)^(?P<path>.+?\.lean):(?P<line>\d+):(?P<column>\d+):\s+error(?:\((?P<code>[^)\r\n]+)\))?:'
```

Preserve line/column and optional error code, and use the same parser for numeric counts and
source/harness classification. Validate source identity, native return code, fresh object and
all seal markers independently; a parser miss must never become a passing result. Unlocated
or unrecognized diagnostics plus a failing return code remain setup/harness failures to review.
Synthetic plain/coded/warning/FAIL-summary parsing checks and the real 6→7 HashAndSign count
passed in Python. No v2 runner or old evidence was edited here.

The old pattern occurs in `check_probe.py`, `run_seals.py`, `run_controls.py`, and the
`build_seals.py` completed-collector error-text guard. Root's separate v2 work should reconcile
those consumers without rewriting historic result JSON/logs.

## Evidence fingerprints

| Input | SHA-256 |
|---|---|
| Original seal manifest | `75b11d1cf5324eea8066b898e5c37a677de266513cdde4be697ef8bf8149ba73` |
| Original BPPBridge probe | `9eda4d5bb25915bf3a74b21b6fd409707535d2f2919e13282ded2c17e1a12d97` |
| Original BPPBridge failure log | `d047365c188d84afc3d13075589ca81c9003f748fa5a96edb9fce8262cb6a443` |
| Original seal builder | `fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a` |

The preparation tool itself was not invoked to publish files during this review.
