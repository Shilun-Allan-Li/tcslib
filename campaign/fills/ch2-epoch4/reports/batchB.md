# Epoch 4, Batch B — TAUTOLOGY coNP-completeness

## Result

`Complexity.TAUTOLOGY_coNPComplete` is filled through the frozen audited
route: inherited membership, SAT hardness for the complement, and the exact
native parse–dual–serialize function. Verification results are recorded below.

## Branch and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib.
- Requested source branch: `complexity/arora-barak-ch1`.
- Source tip observed on clone: `4e6e3e477ca56bf4ee4ffd97d4319ca9c58b793e`.
- Required and object-verified base: `b133a3d42d2de8e2250a74c716e341f33dd3c7a5`.
- Sole working branch: `fill/ch2-e4-B`, created at exactly the required base.
- The committed brief was read from the requested source branch before
  implementation. Its introducing commit follows the required base; as in
  the committed A5 precedent, the brief was retained separately and the work
  was based on the exact pin. Newer unrelated source-branch changes were not
  incorporated.
- Sole modified repository path: `TCSlib/Complexity/ClassNP/Tautology.lean`.
- No push, PR, or changes to any other branch.
- Delivery commit: `39fac01e8b5d7d9d30320df801187efc300863d3`.

Final source: **1749 lines, 84808 bytes**; 28 new private source declarations,
95 total. SHA-256:
`2f2814d285ee2a477ed8e135885ce5f0987612bd861a78b7d1c9e62a685979d9`.

All 67 inherited private declarations are untouched, name by name and byte
by byte. Every original import, declaration, membership proof, and docstring
is retained. The target signature and its entire committed docstring are
unchanged. Removing the new private block and restoring only the original
target proof reconstructs the complete base source byte for byte.
`statement-freeze.log` records the check and the complete name inventories.

## The five hardness links

Let `f` be the witness returned by `SAT_NPHard Lᶜ hL`, and set
`g z = DNF.serialize (CNF.dual (CNF.decode (f z)))`.

| Link | Discharge |
| --- | --- |
| `z ∈ L ↔ f z ∉ SAT` | `not_congr (hred z)`, definitional unfolding of language complement/membership, and classical `not_not` |
| `f z ∉ SAT ↔ ¬(CNF.decode (f z)).Satisfiable` | The unchanged definitions of `SAT` and language membership |
| `¬(CNF.decode (f z)).Satisfiable ↔ (CNF.dual (CNF.decode (f z))).Tautology` | `CNF.tautology_dual_iff`, read in reverse |
| The preceding tautology predicate equals `(DNF.decode (g z)).Tautology` | `DNF.decode_serialize` |
| `(DNF.decode (g z)).Tautology ↔ g z ∈ TAUTOLOGY` | The unchanged definition `TAUTOLOGY` |

These equivalences hold on every string; the language argument has no
well-formedness assumption or branch. `tautDual_poly.comp hf` supplies the
actual polynomial-time composite. The final conjunction cites
`TAUTOLOGY_mem_coNP` directly.

## Transducer and exact output

The inherited six-state `TautSyntax` scanner and its proved
`taut_syntax_parse` equivalence are reused unchanged. No foreign private
lemma is cited.

| Obligation | Discharging private declarations |
| --- | --- |
| Flip only the last bit of a literal record | `tautDualBit`, `tautDualScan`, `tautDual_unary`, `tautDual_literal` |
| Preserve clause/term boundaries, empty clauses, and the unique formula terminator | `tautDual_clause`, `tautDual_serialize` |
| Total parse–dual–serialize identity | `tautDualOutput`, `tautDual_output`, using the inherited `taut_parse_shape` and `taut_syntax_parse` |
| Fixed finite native controller | `TautDualControl`, its two private instances, `tautDualAction`, `tautDualTM` |
| Exact native configurations and transitions | `tautDualCfg`, `tautDual_action`, `tautDual_read` |
| Exact endpoints and no premature anchor visit | `tautDualSegment`, `tautDual_segment_zero`, `tautDual_segment_one`, `tautDual_segment_add` |
| Silent whole-string validation | `tautDual_scan` |
| Chronological bit emission with arbitrary preceding output | `tautDual_copy` |
| Native-head restoration, including empty input | `tautDual_rewind`, `tautDual_copy_end` |
| Successful and malformed complete paths | `tautDual_valid`, `tautDual_invalid` |
| Positive first return and complete clean seam | `tautDual_round` |
| Audited emitting-loop instantiation and polynomial ledger | `tautDual_poly` |

For malformed input the complete scan emits nothing. Only its right-boundary
failure transition emits `[false]`, exactly
`DNF.serialize (CNF.dual (CNF.decode x))` when `CNF.parse x = none`.
It then rewinds and returns. Thus malformed suffixes never leave an emitted
valid-looking prefix. For valid input, the second pass copies every bit
except the polarity bit, with no variable renumbering or length change.
An empty term and an empty formula retain their distinct meanings.

### Assembly choice and normalized return discipline

The emitting library is used explicitly: `FinTM.exists_emitLoopTM` with
`R(n)=0`, hence exactly one positive round. That round contains the complete
finite validation/streaming controller and restores the canonical seam at
its end. This uses the brief's assembly discretion to specialize the general
streaming template to a transformation that needs no persistent cursor or
inter-round data. Its emitted chunk is the complete transformed word;
within the chunk, one native transition copies each bit.

Startup is the genuine initial configuration and takes zero transitions.
The first round transition releases the anchor into syntax control. The
segment proofs exclude the anchor at every intermediate time. Both final
rewind branches restore native head position one, and the exact endpoint is
`Cfg.ofWords` with only the prescribed output changed. Work-tape count is
zero because no work word or scratch storage is needed; the invariant fixes
the logical state to `[]`, and neither clean-call bridge nor a stored-word
result interface is used. The output identity comes from the concrete
native transition table and its complete run proof.

## Runtime calculation

For input length `n`:

- Valid input: one release step, `n` validation steps, one dispatch step,
  `n+1` rewind steps, `n` copying steps, one dispatch step, and `n+1`
  final rewind steps: `1+n+1+(n+1)+n+1+(n+1)=4n+5`.
- Malformed input: one release step, `n` validation steps, one failure
  emission/dispatch step, and `n+1` final rewind steps:
  `1+n+1+(n+1)=2n+3`.

The public constant-machine theorem supplies a fuel machine producing
`Nat.bits 0 = []` within `a(n+1)` steps. Use the common envelope

```
T(n) = a(n+1) + 4n + 5.
```

If `c` is the audited emitting-loop coefficient, its bound becomes

```
c(T(n)+1)(R(n)+2) = 2c(T(n)+1)
                     ≤ 2c(a+6)(n+1).
```

This gives degree one for the standalone transducer. The existing audited
`PolyTimeComputable.comp` accounts for composing it with `f`.

## Verification

| Gate | Result |
| --- | --- |
| Complete owned-module check | Exit 0; zero errors and zero warnings |
| Fresh ordered final sweep | **57/57 passed**, 508.4 seconds; 57 new nonempty oleans; **zero `error:` lines and zero `sorry` warnings** |
| Target and membership | Empty admission roots; axioms exactly `propext`, `Quot.sound`, `Classical.choice` |
| Cook–Levin five and `SAT_reducible_SAT3` | All unchanged-clean, empty admission roots, permitted axioms only |
| Whole owned module | **439 checked kernel declarations**; no direct or transitive `sorryAx`; all axioms permitted |
| Kernel public surface | Original five public declarations and their descendants only; no new public surface |
| Whole campaign kernel inventory | All 57 modules imported; **11040 checked kernel declarations**, zero direct admission roots |
| Source freeze and scope | All 67 inherited privates byte-identical; original target statement/docstring unchanged; only `Tautology.lean` differs |
| Owned-file policy lint | 0 FAIL, 1 WARN: the existing recorded file-size exception |
| Patch replay | Reproduces the exact delivery tree from the required base using an isolated index |
| Incremental bundle | Verified; advertises only `refs/heads/fill/ch2-e4-B`, requires the exact base |
| Working tree / branch isolation | Clean; source branch and remote-tracking ref unchanged |
| Archive | Flat, with `SHA256SUMS` at the root covering every other member |

The bootstrap checked the inherited dependencies in the committed order; an
initial target elaboration exposed a language-membership unfolding mismatch,
which was fixed locally. The owned module and all later facade modules then
passed, followed by the entirely fresh final sweep. The final axiom audit
uses only that final olean tree, traverses checked kernel types and opaque
proof values, and separately verifies that every listed campaign module was
imported. There are no allowlisted admissions. `final-sweep.log`,
`axiom-print.log`, `AxiomAudit.lean`, and `statement-freeze.log` provide the
execution evidence. Existing unrelated linter warnings remain in the sweep;
none is an admission warning.


## Environment and reproduction

- Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Dependency sources were checked out at the committed manifest revisions.
- The first setup invocation could not locate the Lean/Lake executable in
  this container. The included `proc_exe.c` adapter fixes only the current
  process's `/proc/<pid>/exe` lookup by redirecting it to `/proc/self/exe`,
  matching the committed A-cont3/B-cont environment precedent. It changes
  no Lean sources, proof terms, or kernel behavior.
- The setup command then reached `lake exe cache get` and failed while
  extracting the official `leantar` binary because archive ownership could
  not be assigned in this container. The binary itself was extracted;
  its expected versioned filename was restored. The included
  `CacheRequired.lean` resumed the official hash-keyed download/unpack APIs
  for precisely the campaign's Mathlib import closure. An initial all-Mathlib
  download was stopped after narrowing the dependency set. No dependency
  source or repository build configuration was modified. No `lake build`
  command was run.
- Ordered module checks use the committed `scripts/lean_check_tree.sh`.
  Run the committed 57-entry order from the repository root, with a fresh
  `TCSLIB_OLEANS` directory. Run `AxiomAudit.lean` from the repository root
  against those fresh oleans and the pinned dependencies.
- `FreezeAudit.py /path/to/tcslib` reproduces the source/statement check.
- The ZIP is flat. Restore `Tautology.lean` at the sole owned path, or apply
  the included patch from the required base with `git am -3`.

## Shared lemmas, escalations, and continuation frontier

None. All new helpers are private and in the owned file. The target's
statement and audited route are preserved; no continuation is requested.

## Glossary

`L` is an arbitrary coNP language; `f` is its complement's SAT reduction;
`g` is the displayed composite. `n` is native input length; `a` is the fuel
machine's coefficient; `T` is the common body/fuel bound; `R` is the loop's
last round index; `c` is the loop coefficient. Other identifiers name the
unchanged Lean definitions or the private declarations listed above.
