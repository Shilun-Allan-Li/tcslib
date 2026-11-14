# Sampler helper review

This is a static review of `TCSlib/Cryptography/Randomness/Extraction/Sampler.lean`,
prepared without starting Lean. It is not elaboration or seal evidence.

## Implementation and interfaces

`RejectionSampler.chooseWord Ext n t r` tests the first `t` consecutive blocks of
width `n`, returning the first accepted block and otherwise block `t`. Its
`chooseWord_zero` and `chooseWord_succ` readers cover every input. The public
`machine` implements this function with empty advice and constant coin polynomial
`.const ((t + 1) * n)`. Fixing the theorem's parameter before constructing its
witness permits this constant polynomial. It does not weaken uniformity: the
machine has empty advice at every activation parameter.

The `machine_eq`, `machine_uniform`, `machine_coins`, `machine_coinLen`,
`machine_runAtL`, `machine_runAt`, `coinEquiv_eq`, `coinEquiv_ofFn`,
`coinEquiv_symm_ofFn`, and `machine_runAt_coinEquiv` readers expose the complete
machine/coin interface without requiring consumers to unfold it.

`chooseWord_flatten` identifies the string selector with the sibling probability
module's generic selector, through its public `Rejection.select_zero` and
`Rejection.select_succ` readers. `chooseWord_blocks` uses the already-public
`FunFamily.ofFn_blocks_symm` to identify the canonical coin blocks; that list fact
was imported rather than copied. The zero-width case is included.

## Explicit-unfold review

No `unfold`, `delta`, `dsimp`, `simp_all`, `simp [foreignDefinition]`, or
`rw [foreignDefinition]` occurs in this helper draft. The explicitly cited
foreign TCSlib names in rewrites are published theorems:

* `PrefixByLength.take_def`;
* `Turing.pairFstD_pairEncode`, `Turing.pairSndD_pairEncode`;
* `Rejection.select_zero`, `Rejection.select_succ`;
* `NUPPT.runAt_eq`, `NUPPT.runAtL_ofPolyTimeUniform`;
* `NUPPT.coins_ofPolyTimeUniform`, `NUPPT.coinLen_eq`;
* `PolyExpr.eval_const`.

Foreign definitions are consumed by published contracts:
`polyTimeComputable_takePrefixByLength`, `polyTimeComputable_headD`,
`polyTimeComputable_ite`, `BinArith.polyTimeComputable_drop`,
`NUPPT.ofPolyTimeUniform_uniform`, and `FunFamily.ofFn_blocks_symm`.
Mathlib/core list and equivalence equations are cited as theorems, with no
explicit unfolding of their definitions. The `change` in `machine_runAtL` only
beta-reduces the constructed function expression after the published machine run
equation; it does not reduce a foreign TCSlib definition.

The generic map/coin function extensionality proofs and the typed coin equivalence
still need both whole-file seals; static inspection cannot exclude hidden
definitional reduction.

## Searches and promotion requests

Read-only searches used `rg` for these patterns in the existing TCSlib sources:

* `polyTimeComputable_headD|polyTimeComputable_ite|polyTimeComputable_takePrefixByLength|polyTimeComputable_drop`;
* `takePrefixByLength|take_def`;
* `^theorem .*take|^theorem .*drop`, restricted afterward to polynomial-time facts;
* `flatten.*ofFn|ofFn.*flatten`;
* `ofFn.*take|take.*ofFn|ofFn.*drop|drop.*ofFn|take.*drop`.

These found public fixed-drop, single-bit-prefix, arbitrary length-gated prefix,
conditional and head-bit primitives, and public `FunFamily.ofFn_blocks_symm`.
There was no public general fixed-prefix polynomial-time theorem in the searched
source files. `take_poly (n)` should be promoted to
`Complexity/ClassNP/PolyTimePrefix.lean` in the maintainer's shared-file window.
It generalizes the existing public `polyTimeComputable_take1`, whose statement
only covers width one. It is re-derived from the published length-gated prefix
contract, not obtained by copying a private lemma.

The bounded selector and its uniform PPT/coin interface are candidates for
promotion to a shared sampler module if a second consumer needs them. The tuple
and string selection correspondence is generic block/list glue and likewise
belongs on that promotion list.

No private lemma was copied or re-derived in this helper. There are no `overlap:`
items for it. Every new public definition has a complete equation/case reader;
no new abbreviation or global simp attribute was introduced.

## Existing seal-tooling review

The historical meaning of the two seals is recorded in:

* `briefs/pass-shelat-ch5-8/gates/19-nm-sim/worker-report.md`, around line 245;
* `briefs/pass-shelat-ch5-8/gates/18-nm-cca2/worker-report.md`, around line 362.

Seal A exempts `Complexity.PolyExpr.eval` as notation. Seal B includes it.
Both re-elaborate a verbatim whole-file copy with local irreducibility applied
to foreign definitions throughout the full TCSlib import closure. They are not
two different notions of term-reference coverage.

Useful existing components, read as working material rather than instructions:

1. `maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1/Collect.source.txt`
   demonstrates environment-based collection by module ownership, native
   `Name` values, matcher detection, reducibility status and `collectAxioms` for
   every stored constant, including private/generated constants. Its `#axs M
   ["*"]` is the appropriate all-stored approach; enumerating only written
   theorem names would omit generated constants. Its historical seal collector
   skips instances and two notation names, so it should not be copied without
   reviewing and disclosing those filters.
2. The adjacent `build_seals.py` has independently useful `header`,
   `blank_comments_strings`, `instrument`, and `seal_command` implementations.
   `instrument` preserves all original bytes and records exact insertion
   ranges and original-to-probe line maps. `seal_command` validates unique
   actual name resolution and module ownership, installs local irreducibility,
   then checks the installed status again at EOF. Its `main` is hard-coded for
   an old 51-module job and cannot be run unchanged for this fill.
3. The adjacent `tool-inputs/request_payload_adapter.py` replaces huge Lean
   syntax arrays with one escaped tab/newline-delimited data literal. This
   avoids parser recursion/AST size problems without increasing recursion
   options or weakening the request set. It keeps native actual names in the
   resolved environment; a printed private-name string is not directly parsed
   back as an identifier.
4. `maintainer/cleanup-incremental-2026-11-09/final-r1/04-base-whole-file-seals.zip`
   contains `tools/prepare_seals.base-r2.py` and `tools/run_seals.base-r2.py`.
   They illustrate census ownership, request manifests, line-mapped failures,
   no-overwrite result files, exact source hashes, install/EOF marker checks,
   and one-module `scripts/lean_check_tree.sh` calls. They depend on old
   job-specific external paths and pin files and must be adapted rather than
   invoked as-is.

A minimal fill-specific harness can use the first three components' reviewed
ideas while removing the old job's fixed pins/ordinals. It should emit an
environment census separately for base and final (or record the absence of a
new helper at base), obtain the full import closure from the exact sources,
retain generated matcher/projection definitions, exclude reducible
abbreviations only under the stated notation rule, and prepare A/B request sets
differing only by `PolyExpr.eval`. Seal sources must import the original
imports, install the seal before the first original command, append an EOF
verification, and preserve the entire original source, including anonymous
commands. Deliver both request manifests, all collector/probe sources, every
raw log, results, and the tools used.

For paired controls, a small unsealed `rfl` read of a foreign ordinary definition
(for example `padFin`) should pass; the exact same proof with that one ordinary
definition sealed should fail exactly once. A generated matcher/projection
control should similarly validate the collector's coverage if those forms are
used. An explicit `PolyExpr.eval` `rfl` control should pass in A and fail once in
B; a reader-based control using `PolyExpr.eval_const` should pass in both.
Every negative must have precisely one source error, with no harness errors.
The actual elaborated results, rather than this proposal, establish control
validity.

The explicit-unfold scan remains separate: sealing does not prohibit an
explicit `unfold` by itself, and Mathlib/core policy also applies despite those
definitions being outside the TCSlib seal set.
