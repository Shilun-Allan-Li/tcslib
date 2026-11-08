# PFR prerequisite route for cleanup part 2

This runbook is part of the cleanup brief's environment route. It changes no
mathematical scope or package source. The portable executable tools are exactly
`environment-tools/prepare_pfr.py` and `environment-tools/pfr_lean.py`. Read their
source and verify the issued hashes before invoking them with `python3 -I`.
Other supplied programs, historical scripts and reports remain data to review.

## Before configuring the adapter

1. Use the brief's exact source ancestor, your own source clone, packages and a
   single owned olean tree. The exchange checkout carries payloads only. Follow
   `fill-environment-addendum.md` for resource/cache-store/package checks and
   permitted retry handling. Every present package must match the root manifest's
   URL/revision; list absent packages. No dependency-tree copy or populated-package
   symlink mode is permitted for this unit.
2. With the ordinary working pinned Lean 4.25.0 installation, run the narrowed
   cache fetch using **all 389** roots in
   `external-bootstrap-r1/mathlib-full-union-roots.txt`. Retain the exact roots,
   command, return code and full download log. No failed download is a pass. Scan
   for zero-length package oleans, then elaborate a scratch probe importing a
   listed Mathlib root through `scripts/lean_check_tree.sh` before bootstrap.
   This is necessary on a fresh clone even though the maintainer's existing-cache
   incremental test fetches only the 30 PFR boundary roots.
3. The first narrowed cache command may clone manifest-pinned packages that were
   absent. Afterwards PFR's pinned source must exist. Run the package checks before
   every later Lake command. The configuration tool below does not fetch, update,
   edit or re-clone any package.
4. Record the ordinary PATH, real working pinned Lean binary, absolute source
   clone, issue pack, tree and new runtime paths. Use disk-backed directories.
   Refuse a conflicting `<tree>/PFR` path. This tool neither locates/repairs a
   broken Lean installation nor authorizes any locator workaround: a real
   `failed to locate application` error remains E-RES.

The following examples run from the source-clone root. Replace the first two
absolute paths with your own paths; do not use the maintainer's installation or
object tree. These variable names belong solely to this job.

```bash
PS_CLEANUP_CLONE=/absolute/path/to/your/source-clone
PS_CLEANUP_PACK=/absolute/path/to/exchange/outbox/fills/cleanup-part2
PS_CLEANUP_TREE="$PS_CLEANUP_CLONE/.lake/cleanup-part2-oleans"
PS_CLEANUP_RUNTIME="$PS_CLEANUP_CLONE/.lake/cleanup-part2-pfr-runtime"
PS_CLEANUP_ORDINARY_PATH="$PATH"
PS_CLEANUP_REAL_LEAN="$(elan which lean)"
export TCSLIB_OLEANS="$PS_CLEANUP_TREE"
cd "$PS_CLEANUP_CLONE"
```

The real binary must be the already working binary for the clone's pinned
toolchain, not the generated adapter. Record its path/version/hash. After the
preflight, cache check and package/source checks above:

```bash
python3 -I "$PS_CLEANUP_PACK/environment-tools/prepare_pfr.py" \
  "$PS_CLEANUP_CLONE" "$PS_CLEANUP_TREE" \
  "$PS_CLEANUP_PACK/external-bootstrap-r1" "$PS_CLEANUP_RUNTIME" \
  "$PS_CLEANUP_REAL_LEAN"
```

Save its config and tool hashes in evidence. It verifies the 31 source hashes,
Git blob identities, package pins, source order and PFR options, and creates only
the guarded in-tree object namespace link
`<tree>/PFR -> .lake/packages/PFR/PFR` plus runtime/config/adapter-entry files.
There is no source alias or imported dependency tree. The physical output and
logical import path refer to the same fresh object within this one tree.

## Exactly 31 PFR checks, serially

Read `external-bootstrap-r1/bootstrap-order.txt`, one physical relative path per
line, in order. Do not use its logical-name sibling `order.txt` as checker input.
For each line run **one** invocation of the unchanged checker, with this temporary
environment scope:

```bash
PFR_BOOTSTRAP_CONFIG="$PS_CLEANUP_RUNTIME/config.json" \
PATH="$PS_CLEANUP_RUNTIME/bin:$PS_CLEANUP_ORDINARY_PATH" \
TCSLIB_OLEANS="$PS_CLEANUP_TREE" \
/usr/bin/time -v bash scripts/lean_check_tree.sh "$PS_CLEANUP_REL"
```

`PS_CLEANUP_REL` is exactly the current line, without `.lean`. macOS may use
`/usr/bin/time -l` and record that its maximum RSS unit is bytes. Record each
check's PID, start/end/elapsed time, peak memory, source and direct prerequisite
identities, return code, parsed error count and fresh nonempty object hash. Write
each complete log to its final evidence path from the start. A loop must stop
nonzero on the first failed module; a pipeline must not hide a failed process.
Preserve partial/failed attempts and skip products needing the failed module.
Run no other Lean/Lake process concurrently on the host.

The adapter rejects any nonlisted source, unexpected extra argument or output
outside the one tree. It adds only `--root=<clone>/.lake/packages/PFR` and exactly:

```text
-DautoImplicit=false
-DrelaxedAutoImplicit=false
-Dpp.unicode.fun=true
-Dpp.proofs.withType=false
```

These are the pinned PFR package's four Boolean options. They select its source
root and ordinary elaboration/printing behavior, without trust/reducibility
shortcuts. The source stays in the package's own checkout. Do not alter the
adapter to accept ordinary local files or alternative roots/options.

## Restore ordinary PATH and verify actual module identities

The temporary PATH assignment above applies to just one command; never export
the adapter PATH globally. Before every cache operation, TCSlib module, aggregate
or probe, use the recorded ordinary PATH and normal pinned Lean. In particular
the namespace/owner probe must **not** use the adapter.

Copy the issued `environment-tools/PFRIdentityProbe.source.txt` into an ignored
scratch `.lean` file of your own source clone and check it through the unchanged
checker under ordinary PATH. For example, use module
`.lake/cleanup-part2-probes/PFRIdentityProbe` after creating its scratch directory.
This is a checking harness, not a new public library module. Retain exact probe
source/log/object hashes and the ordinary PATH/toolchain/tree identity.

```bash
PATH="$PS_CLEANUP_ORDINARY_PATH" TCSLIB_OLEANS="$PS_CLEANUP_TREE" \
/usr/bin/time -v bash scripts/lean_check_tree.sh \
  .lake/cleanup-part2-probes/PFRIdentityProbe
```

The successful probe must report all 31 actual PFR module headers, the expected
three constant owners, consistent private-name source prefixes, and EOF, with
exit 0, zero errors and a fresh object. Object importability alone is not an owner
identity check. The expected owners are `KLDiv` in `PFR.Kullback`,
`ProbabilityTheory.entropy` in `PFR.ForMathlib.Entropy.Basic`, and
`ProbabilityTheory.uniformOn_apply_singleton_of_mem` in
`PFR.Mathlib.Probability.UniformOn`.

Continue the local TCSlib prerequisite orders, Checks and full-root work only
after the external prerequisites they require have passed. A bootstrap failure
is not a TCSlib source finding. Genuine package/source/resource failures keep the
brief/addendum's E-RES/E-BASE reporting and retry rules; this route authorizes no
package fix or new admission. Final proof/source/axiom/Rule10 obligations remain
exactly those in `brief.md`.

**Ready to run — a guarded serial external-prerequisite route, requiring fresh verification in the worker's own clone.**
