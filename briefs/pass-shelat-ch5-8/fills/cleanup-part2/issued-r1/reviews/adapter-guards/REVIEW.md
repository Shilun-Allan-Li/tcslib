# PFR adapter guards: non-native simulation

**Result: 25/25 expected outcomes; no native claim.** The sources were read fully before execution and bound to prepare_pfr.py `650edf1d270d5e130a926a5840fead75ba9888e12684f2f38451af91ad769b8f` and pfr_lean.py `41fda9565be3f77462fe6f2f7b55b798c5bf34fbbc400a648f77e000eb36636d`. No old-version simulation was run. The earlier source-only observation about coordinated inventory tampering is addressed in the tested prepare version by its exact frozen manifest and leaf-content guards.

The own executable capture_only only writes an argv/cwd JSON under this guard scratch and prints an explicit capture-only marker. It never invokes Lean and never writes an object. The adapter was configured against the pinned main source clone read-only, using private fake object/runtime directories. All portable tools, original static supplement files and inspected source/package/config bytes remain unchanged. Only this ignored guard directory was mutated.

| Group | Expected and observed |
|---|---|
| Prepare valid control | 1 accepted; config/object namespace/runtime metadata created only in own fake tree; target not executed |
| Prepare rejection controls | 9 rejected: existing runtime; conflicting logical directory; conflicting logical symlink; physical prefix escaping tree; duplicate metadata; module-path metadata; dependency-order data; order text; coordinated order/import/manifest rewrite |
| Driver valid control | 1 accepted; exactly --root, four pinned flags, source, -o and correct physical output captured |
| Driver rejection controls | 13 rejected: nonlisted existing PFR source, extra argument, wrong cwd, outside-tree output, incorrect in-tree output, expected source-hash drift, lakefile-hash drift, adapter-hash drift, expected binary-hash drift, actual own fake-binary byte drift, actual own scratch-copy adapter byte drift, namespace alias conflict, noncanonical equivalent source path |
| Informational config boundary | 1 accepted after changing only unused pfr_package_pin provenance metadata; argv remained identical |

There are 22 expected nonzero returns and three expected zero returns. The harmless target ran twice: the allowed driver control and the informational metadata-boundary control. There are **zero .olean products**. Every case retains its command/cwd, return code, full stdout/stderr and SHA-256 fingerprints, config hashes and capture status. Results are in results.json and each cases/<name>/result.json, stdout.txt and stderr.txt.

The physical escape case proves the prepare tool rejects before creating the escaping physical prefix: the outside sentinel directory is unchanged and runtime is absent. Rejected logical-alias cases can leave harmless directories inside the owned fake tree because preparation is not transactional; they created no object or outside-tree output.

Inventory mutation cases hit the new outer manifest/leaf integrity guard before package processing. They demonstrate input rejection, not independent execution of every inner duplicate/order assertion. Source-hash/lakefile-hash drift tests alter only own expected-config hashes; real package sources/configs were never edited. Actual-byte hash tests use own harmless fake-binary or scratch driver copies; original portable tools are unmodified.

Runtime config is trusted root-generated input. Its unused pin provenance field is not itself a signed or independently revalidated live package pin. This control neither changed the selected source/argv nor demonstrated a proof/native defect; it limits any claim that every possible JSON mutation is automatically rejected. The runbook's evidence/config integrity obligations remain applicable. No latest-tool defect was identified within the tested invocation guard scope.

This harness was authored here, AST-parsed and run with Python3-I. Portable tools were executed only under the explicit internal guard-test authorization, with real_lean always pinned to the own capture-only executable. No native Lean, cache, build, app, received worker program or identity probe was executed. Successful capture is not compilation, object freshness, ABI, module-header/private-name/constant-owner correctness or a tested final worker environment. Root's native identity/bootstrap checks remain separate.

**Not yet clear to merge — invocation guards were simulated; native bootstrap and cleanup verification remain separate.**
