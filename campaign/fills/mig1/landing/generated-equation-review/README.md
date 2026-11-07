# Convention's lazily generated split-search equations

**Availability finding:** `Turing.solveSplit.eq_def` and
`Turing.solveSplitWith.eq_def` are Lean-reserved equations that can already be
realized from the unchanged Convention import alone, with both definitions
irreducible. They are absent as materialized constants in that imported baseline.
The requesting Primitives proofs cause their compiler realization; there is no
handwritten new theorem or newly designed formula in those proof edits. This
finding does not grant a general exemption from rule 10 or human API review.

The primary probe is `ConventionOnly-v3.lean.txt`, executed with **exit 0,
zero errors** against the complete read-only `oleans-mra2` tree. It imports only
Convention and Lean. Its entire TCSlib closure is Configuration, Deterministic,
Finite, Simulation and Convention; it explicitly rejects a Primitives import.
The full source, raw output and command/hash receipt are retained. No source,
Git state, cache, compiled output or shared snapshot was changed.

## Exact observations

Before any equation-name resolution, both definitions are present, but each
`.eq_def` has `env.contains = false`, `env.contains (skipRealize := false) =
false`, `env.find? = none`, and `isReservedName = true`. The same is initially
true for each `.eq_1` and `.eq_unfold`. The unfiltered Convention-owned census
contains **35** constants, including every private/internal entry; neither
target equation occurs in that census. The two source definitions are at
Convention lines 138 and 227.

After applying the normal `attribute [local irreducible]` to both foreign
definitions, `#check` succeeds, and actual theorem proofs using
`rw [Turing.solveSplit.eq_def]` / `rw [Turing.solveSplitWith.eq_def]` prove their
full equations. Opacity is checked before equation references and after all
consumers. The formulas are precisely:

```lean
solveSplit C e n =
  (List.range (n + 1)).find? (fun i => i + C * (i + 1) ^ e == n)
solveSplitWith f n =
  (List.range (n + 1)).find? (fun i => i + f i == n)
```

Both realized `.eq_def` constants are theorems, nonprivate, **noninternal**,
non-simp, absent from simp's definition-unfolding set, and tagged `defeq` by
Lean. Their stored values are the corresponding lambda-bound `Eq.refl` terms.
The axiom walks of both equations and their consumers are `[propext]` for
`solveSplit` and `[]` for `solveSplitWith`; there is no `sorryAx`.

The environment API distinction matters. `Environment.contains` defaults to
`skipRealize := true`; after the proof consumers it still reports false here,
while `contains (skipRealize := false)` and `find?` see the cross-branch
realizations. `containsOnBranch` is false and `getModuleIdxFor?` returns `none`
in this non-output probe (`mainModule = _stdin`), rather than assigning them
the imported Convention owner. These results explain why a serialized
consumer-module census can gain constants owned by Primitives. This probe
does not serialize an olean; the exact final Primitives owner/delta remains
the root's independent compiled-census evidence. The two `#check` commands
alone do not persist the equations to the following main command in this
run; the after-`#check` absence is recorded separately, not treated as proof
that the names cannot resolve.

Fresh direct-definition controls test each function pointwise and as a whole
function. All **four** unsealed controls close by ordinary refl and are added
as kernel-checked temporary theorems. All four sealed counterparts fail with
the exact corresponding identities and multiplicities (exit 1, four expected
errors). They do not use equation lemmas or simp and contain no admissions.
Thus the equation consumers' success is distinct from silently reducing the
two sealed definitions. `check_evidence.py` validates every raw receipt/hash,
these exact controls and primary-probe invariants.

## Existing alternatives and scope

Convention's complete source declaration list has six public definitions and
twelve public lemmas/theorems. It contains no source-authored reader for either
split-search function; the existing source-authored equations concern seams
and `incFixed`. The compiler's reserved `.eq_1` alternatives are also tested
under the same opacity: they have the same complete formulas, same axiom
sets, no simp membership, and are **internal**. Using them would change the
spelling rather than remove lazy realization. Merely observing the reserved
`.eq_unfold` names is not a proof that those names can be generated; this
investigation does not reference or claim them as alternatives. No consumer
proof or source edit was implemented.

The local Lean 4.25.0 source explains the behavior: `Lean.Meta.Eqns` reserves
the equation names of safe definitions and its reserved-name action requests
`getUnfoldEqnFor? (nonRec := true)`, which calls `mkSimpleEqThm` for these
nonrecursive functions. `Lean.Meta.realizeConst` uses the context just after
import for an imported definition. `Environment.contains` documents its
default realization-skipping behavior. The relevant exact local source
copies/excerpts and full-file hashes are in `compiler-source/` and
`inputs.json`; they are evidence about this toolchain, not a new library API
or policy ruling.

Root's draft disposition is to disclose **two materialized compiler
equations** separately in the unfiltered census and gate, without counting
them among authored exports or saying they were already materialized in the
baseline. The external gate must still assess this published-equation use
under rule 10. No approval to generate arbitrary foreign readers is inferred.

All **five** actual Lean invocations are retained: the first harness attempt
failed with three errors (a list-sorting API mistake and premature metadata
lookup); v2 and the more explicit v3 pass; the positive controls pass and the
negative controls fail as expected. The failed attempt is not primary
evidence. These bounded checks do not certify the full Primitives repair,
the combined landing replay, or gate closure. `SHA256SUMS` covers this folder
except itself.
