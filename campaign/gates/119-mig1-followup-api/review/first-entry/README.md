# Gate 119: approved first-entry theorem

Implemented exactly `Turing.MultiTapeTM.exists_first_entry_of_fixed` immediately after
`exists_first_halt` in the isolated followup worktree's `Finite.lean`. The theorem's complete
header and proof equal the approved proposal byte-for-byte. Its new docstring describes the
fixed-stop hypothesis, least-time argument, strict cut and final-configuration conclusion.

Actual source SHA256:
`e870a56d345d53969a7fa1cd2741476f9f076c517812ce20cea0c0f81b1b59be`.
The theorem begins at line 236; its docstring begins at line 229. `actual-Finite.lean.txt` is
an exact inert copy, and `source.patch` contains the complete insertion.

## Source freeze

Removing only the recorded insertion recovers every byte of the API1160 baseline source
(SHA256 `454e4ab5da22d833873674676293c35154f17f1a371533d53b473b1b912cf9f8`).
The balanced full-header comparison checks all 26 surviving declarations, their complete
bodies, visibility, kinds and order. The sole addition is the approved public theorem
(26 to 27 source declarations, all public). Existing imports, attributes, comments, runtime
and data definitions are unchanged. No public helper or simp attribute was added. The theorem
has no admission, axiom, unsafe declaration or transparency escape.

`source-receipt.json`, `source-freeze.json` and `final-receipt.json` record these checks.
`prepare_source.py` wrote only this owned source file and this evidence folder. Other agents
own the remaining followup source files; this report makes no assertion that their edits are
absent from the shared isolated worktree.

## Actual isolated checks

All native runs used `leanelab.sh` or `leanelab-o.sh`, sequentially, with the environment
sourced and a three-slot local budget under the machine-wide cap of five. The complete mra2
snapshot (895 oleans) was copied to a private whole overlay. Its Finite output link was removed
before compiling there. No shared snapshot was written and no independent snapshots were
spliced. Exact commands, times, source pins and log hashes are in the `*-request.json` and
`*-run.json` receipts; context and dependency pins are in `context.json`.

- Actual full `Finite.lean`: exit 0, zero errors, two warnings.
- Exact new section, with the guard before its docstring and complete header: exit 0,
  zero errors, the same two warning locations. `step` and `runFrom` are irreducible; the
  default simp rules for `Action.apply`, `Cfg.init` and `MultiTapeTM.initCfg` are removed.
- Actual-owner compiled metadata: exit 0, zero errors or warnings. The root belongs to
  Finite, is a public noninternal theorem and has neither simp nor unfold registration.
  The root has no generated descendants; its axiom closure is exactly `propext`,
  `Classical.choice`, `Quot.sound`.
- Fresh controls: all eight pass unsealed; all eight fail with their expected `rfl`
  diagnostic when sealed. Each definition has pointwise and abstracted delta and complete
  equation controls. One diagnostic per own source interval is verified; a same-count
  duplicate-first/drop-last perturbation is rejected.

Both module warnings concern unused simp arguments `hi` and `hw` at untouched old line 178.
No warning points into the inserted theorem. This work did not rerun the baseline module and
therefore does not claim a native baseline warning comparison. The unsealed control input
has one unused lambda-binder `S` warning; the sealed input has no warning. The sealed control
exit 1 is expected evidence of effective opacity, not a failed theorem attempt. No other
native attempt failed; all raw inputs and outputs are retained.

## Boundary and compiled inventory

Explicit rewrite arguments in the approved proof are published theorem equations or local
hypothesis equalities. No foreign definition is passed as a named `simp`, `rw` or `unfold`
argument. `tactic-arguments.json` enumerates every explicit rewrite list.

Compiled type/value citations reach exactly two ordinary foreign TCSlib definitions:
`Turing.MultiTapeTM.step` and `Turing.MultiTapeTM.runFrom`, both covered by the strong seal
and fresh controls. `Turing.Cfg.state` is a structure-projection abbrev; it is disclosed as
an exclusion from ordinary-definition opacity. There is no additional ordinary foreign
definition requiring a guard.

The unfiltered actual Finite owner inventory contains 59 constants, including 56 nonprivate
and 43 nonprivate noninternal constants. This is an after-only inventory, not a baseline
compiled delta. The exact root type, owner rows, direct foreign-definition citations and
root/descendant axioms are in `Metadata.out` and `metadata-verification.json`.

## Limits and handoff

These are isolated actual-module, section, control and metadata passes. Root retains the
integrated five-module chain, complete compiled API delta, merged-tree replay and gate 119.
This report does not close a gate or clear a merge. No Git mutation, commit, push, screen,
cache action, other source edit or target fill was performed by this agent. The owned source
is stable at the hash above and no further edit is planned.

`verify.py` performs the offline reconciliation of the saved source, raw logs, exact control
intervals and metadata. `MANIFEST.json` and `SHA256SUMS` freeze the evidence files; neither
checksums file hashes itself.
