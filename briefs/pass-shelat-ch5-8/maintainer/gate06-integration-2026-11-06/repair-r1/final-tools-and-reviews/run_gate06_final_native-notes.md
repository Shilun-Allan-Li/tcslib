# Fresh Gate06 final native runner proposal

**Proposed and not executed.** The companion `run_gate06_final_native.py` is a native-runner adapter only. It neither collects nor prepares probes, edits library source, replays base source, resumes an earlier attempt, nor selects a historical ordinal range. Root must review it and finish the source freeze/replay/collector/preparation steps before running it.

Runner SHA-256: `ea720bbe6fef9467efef1f8dbeb8c01ca3bb3b66e597a3ed2b3ce512f774f509` (476 lines).

## Fresh inputs and configuration

The fixed integration root is `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.

- Scratch: `.lake/ps-maintainer/gate06/rule10-final-r1` in that root.
- Evidence: main records `briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1`.
- Native tree: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/oleans-gate06-r1`.

Base/head and N are deliberately **not** copied from the initial survey or the currently mutable source. They come from the fresh final `pins.json`/`modules.json` and are independently verified against the complete committed library snapshot, actual base/head diff, changed-source fingerprints, mathematical-file set and import closures using the existing builder validators. Exact import/option-only complements are checked; no new waiver is added. Any further source change requires fresh final inputs, not a retry overlay.

The CLI requires `--adapter-sha256 REVIEWED_SHA256`, the independently reviewed hash of the newly prepared `final-adapter.json`. That sidecar must bind the exact fresh `final-preparation.json`, seal/control manifests and collector result. Both preparation sources are captured and pinned independently:

| Tool/configuration | SHA-256 |
| --- | --- |
| `prepare_gate06_final_collector.py` | `a402e458b32f65edb272276dfb8b6dd9ed59b992024b586b42ccfebe737470f4` |
| `prepare_gate06_final.py` | `130f92d412ed7d60f3496c3928b06621f1ebde81363ecb5fbb7ff0fc91ccdb54` |
| `build_seals.py` | `fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a` |
| `build_controls.py` | `484009543d095685b50fea244427adf4907de11bd5ef6a9e17e76fe08c60cf89` |
| constant-AST request adapter | `ae79f1ec66e93c8bc7749a53e12e3d383feda020ad2978520a0cfa24b12eb5de` |
| `prepare_audit.py` (archived data, not called) | `055e652d9769044d757960586a94f4feffe78a942ca2d9555f02db9dccfa258f` |
| `touched.py` (archived data, not called) | `95d47b5541adcf4670120ab761890a2be899c3f1e77e367a459cac7ad96ffe97` |
| `collect_body.lean` (archived data, not executed) | `751aa8f8385a05690a0a0097acaff6d93e7349067b5e16a5a59662db0cafb57b` |
| `check_probe_v2.py` | `5048912fda9ecd1eb6dd9a238d94bfd73d55a70e9e7d2c4a2df75bfda7e9d146` |
| G06 `evidence-run/setup-summary.json` | `4618c1f0290464d44477bf6b493663af3e0a572917fc7088af47db5a18be6de2` |
| `scripts/lean_check_tree.sh` | `366dab40e8e8f0f13e14118e14c3d6be1bc1b36604e6c9ccdebb03bc96cdf335` |
| `lean-toolchain` | `dbbf063fc415c8e718172605f23a8f86679a3c320eff6d3890cc009534452925` |
| `lake-manifest.json` | `cad7de215c4cc216d03acb77cb1abfbe9f3b4062a8988b29459504f932015100` |
| generic S2 validator source | `0c58a5d287dd1487dc5bbda47283ad4ab9e3c5fe0ba50e9c902c369df55fa7e8` |

All seven archived preparation tool aliases are verified using `tool_saved_names`; the Lean body is an inert `.source.txt` copy. Root's actual G06 checker remains unmodified. The hash-pinned setup JSON must name the intended G06 tree exactly. The S2 native tree is never a runner target. Changing one of these reviewed tools/configuration bytes fails preflight and requires review, rather than silently refreshing a hash.

## Reuse and validation boundaries

The stable original `run_seals_v3.py` and `run_controls.py` were read, including the former's reuse path and the latter's all-eleven acceptance conditions. The newer S2 driver was read functionally. The proposed adapter loads its hash-pinned source for **generic** path, instrumented-source, source-location, diagnostics, actual-name-row and marker validators. Its generic path globals are explicitly configured to the fresh G06 root/scratch/evidence. The new adapter supplies its own dynamic context, G06 invocation and no-base/no-retry run loops.

It never calls S2 `load_context`, `verify_axiom_rows`, `assert_frozen`, `invoke`, `prepare_base`, `load_base`, `run_seals` or `run_controls`. Therefore S2's fixed HEAD, five-module `OWNED`, 1292 axiom-row census and all-standard-only axiom rule are unused. The old V3 payload tool is imported only for `configure_builders`; its historical retry `main`, range and frozen head are not called. Its constant-AST transformation applies to every one of the fresh N seals and all eleven controls.

Preflight reproduces every prepared whole-file probe and every control byte for byte using the pinned builders and the constant-AST adapter. It verifies all original-source hashes, insertion maps, one-to-one line maps, saved copies, full collected request rows, collected status counts and canonical fresh paths/labels. The complete library snapshot includes every library source; each source, consumed input, own runner, helper and tool is rechecked around native invocations. Source coverage includes anonymous commands through whole-file instrumentation and complete closure requests, with the separate anonymous control.

The native checks retain and validate:

- one matching START/source-hash/END footer, parsed coded and ordinary diagnostic counts, return code, captured probe bytes and source stability;
- a fresh nonempty correctly hashed object with modification time at/after start for rc0, including a check of the collector's object;
- exact unique `G06-NAME` rows with spelling=actual printed identity, expected home and previous status, installed irreducible status, exact full-name-set equality, install counts and EOF counts/order;
- source-mapped errors between installation and EOF; inserted-harness, import/dependency, missing-marker and setup failures are distinct from valid sealed source failures;
- all five unsealed/sealed negative pairs plus one sealed three-reader positive control; exact body regeneration/region hashes, exactly one rfl site per negative, before/after catalogs, body markers, installation/EOF order, and the sole expected negative diagnostic at that proof site.

The effective original TCSlib objects in the module/closure set are fingerprinted using the shell script's ordered search paths, and the resolved paths/hashes must remain stable around probes. This records native dependencies; it does not prove their source provenance or replace root's completed source-matched native replay. Probe objects occupy the fresh scratch module paths, so previous ordinals' objects are not reused.

Axiom displays/inventory remain the fresh collector's data, with all-stored counts validated by its existing parser. This runner adds no all-standard-only test, no expected axiom total and no clearance of existing statement admissions or `sorryAx` dependencies. Final axiom comparison, explicit-unfold scan and failure reconciliation remain separate root review requirements.

## Outputs, failure handling and eventual commands

Each selected command requires an absent fixed output directory, `native-seal-runs` or `native-control-runs`, inside the fresh final evidence directory. There is no run-ID, attempt-selection or resume option. Each probe gets a fresh subdirectory, original checker source/log/JSON/PID files, launcher log and separate immutable classification JSON. The run saves runner/validator/checker/shell/configuration sources, all consumed input hashes, dynamic base/head/scope/library fingerprints and effective native-object fingerprints. No previous evidence is imported as coverage.

Every ordinary source failure is retained and the seal survey continues across all N. Controls still run under `run-all` after ordinary seal failures. Harness failures are retained as invalid harnesses; freeze/input changes abort further work with an incomplete summary and remaining labels. All failures return a failing overall status and require review. Inherited identity is never inferred automatically, and there is no base-source replay or exemption path.

After root reviews the script, freezes/commits the final source, completes the affected native replay, prepares and natively checks the fresh collector, prepares all probes/controls and reviews the resulting final-adapter hash, the eventual entry point is:

```text
python3 -I /absolute/path/run_gate06_final_native.py run-all --adapter-sha256 REVIEWED_FINAL_ADAPTER_SHA256
```

`run-seals` and `run-controls` can be used separately; neither can reuse an existing output directory. Root must keep the source/input/object tree frozen and run the sole Lean process for that tree. A failed/incomplete final epoch is preserved; choosing a later epoch requires new reviewed configuration, not editing this runner's results.

Only Python AST parsing and read-only source/hash inspection were performed on this proposal. The runner, preparation adapters, builders, validator imports, native tools, Lean/cache commands and apps were **not executed**. No library, Git, final scratch or evidence directory was changed by this task; only separate ignored runner/notes artifacts were saved.

**Not yet clear to merge — final source pins and preparation do not yet exist, and the proposed native runner still requires root review and execution.**
