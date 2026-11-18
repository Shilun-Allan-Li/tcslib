# Dormant PHFE audit-tool preparation

Source: exchange commit `bc9d982b83cb35ea351e2fb373752e8688945b1c`,
`inbox/fills/bb1-sim-statements/evidence/tools/`.

The subagent could not write the io-phfe worktree, so this authorized fallback
contains the prepared files. Promote `tools/`, `tool-provenance.tsv`,
`tool-adaptation.log`, `tool-static-inventory.json`, and
`tool-static-syntax.log` beneath the worktree's `evidence/preparation/`.
The fallback `lean-slot.sh` is byte-identical to the pinned copy already there.

## Status

- Thirty text tools were extracted. The committed Python bytecode file was
  excluded; no PDF or bytecode was copied.
- Only `tools/seal/runner_full.py` and `tools/review/runner.py` were adapted.
  Their headers and `tool-adaptation.log` record the exact changes.
- Both use the pinned wrapper at `../../lean-slot.sh` relative to their own
  location, invoked through `bash`; no executable-bit assumption is required.
  They set subprocess `LEAN_SLOT_TAG=io-phfe` and keep `nice -n 10`.
- `tool-provenance.tsv` records the source commit, source path, prepared path,
  original SHA-256, prepared SHA-256, and adaptation flag for all thirty tools
  plus the wrapper. The other twenty-eight tool files retain exact bytes.
- Static `ast.parse` accepted all twenty-six Python files. Parsing did not
  execute any extracted module, subprocess, Lean, lake, or build command.
- The user explicitly overrode the LeanInfoView-only prohibition and selected the
  dispatch slot-wrapped module checks and probes. Serial Lean module checks are active;
  these full audit runners are now authorized for the M0 audit. Tool preparation alone is
not a passing audit.

## Suite read-through and configuration observations

The collector template plus `mkcollect.py` enumerate the selected owners,
their TCSlib import closures, referenced foreign definitions, and the imported
catalog. `mkseals_ab.py` builds strict variants A/B; `mkseals_coe.py` additionally
excludes the FinDist coercion. Variant B seals PolyExpr.eval; coe-A is the
canonical variant required by the PHFE brief. Both instrument source bytes from
a Git revision and preserve original-byte line mappings.

The archived builder and request adapters validate actual Lean Name components,
instance/matcher metadata, installation and EOF counts, and the scoped instance
unfolding mask. `sealsum.py` reports request/error/install/EOF information;
`ctlcheck2.py` checks paired negative/positive controls and prints ALL_OK.
The explicit-reader scan is split between `scan1_g40.py` (lexing and Lean-kind
probe generation) and `scan2.py` (classification); it includes generated
equation-reader targets. `decls2.py` compares public declaration statements;
`touched.py` additionally tracks full declaration bodies and source spans.
The clash tools index both TCSlib and audits. `sk15.py` reports long proofs
without sketches; `widths.py` reports widths over 100 and sizes over 1000.

These inherited files are preserved, not treated as PHFE-ready drivers:

- `drivers/bootstrap.sh`, `drivers/rule10_stmt.sh`, and `clash/probe_clash.py`
  contain BB1-specific absolute Linux paths, revisions, and module lists.
  They must not be invoked for PHFE as extracted.
- `mkctl_bb1s.py` contains BB1/pairing control rows. It does not supply a paired
  control for each new PHFE definition; PHFE coverage still needs preparation.
- The full-file runner retains the original `LAKE_PACKAGES` default under
  `/home/user/fill/tcslib`. Future authorized use would require the job's own
  package directory supplied explicitly; that unrelated default was not edited.
- Both runners retain the historical JSON key `maxrss_kb` for `ru_maxrss`.
  On macOS that system value is in bytes. Preserve that disclosed unit distinction
  in any future evidence interpretation; the narrowly authorized adaptation did
  not rename it.
- `sk15.py` and `widths.py` print findings without setting a failing exit code.
  A future audit must inspect their output, not infer PASS from process status.
- `deliver.py` performs temporary clone/checkout/git-am operations and changes
  delivery directories. `insert_blocks.py` edits its supplied source file.
  Neither was executed in this preparation.

No Git mutation, source edit, Lean process, lake process, or audit-run claim was
made by this subagent.
