# B7 continuation 3 — targets 9–11

## Result and provenance

**Complete: 3/3 owned targets proved**, with no admitted private helper and no “proved modulo” dependency:

| Target | Result | Construction |
|---|---|---|
| 9. `Complexity.ImplicitlyLogspaceComputable.compQ` | Proved | One finite, mode-parametrized ARM over the received four-oracle bank; bounded all-input halting; `arm_decides_poly`. |
| 10. `Complexity.ImplicitlyLogspaceComputable.comp` | Proved | Pre-ship D2: compose the polynomial bounds and pull both query languages back along `compQ f`. |
| 11. `Complexity.LogspaceReducible.trans` | Proved | Compose the reduction functions and chain their membership equivalences. |

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Initial branch: **`complexity/arora-barak-ch3-4`**.
Base commit: **`0bf08187c1a8c24b3733b4300f3c0d00886dc109`**.
Working branch: **`fill/ch34-b7-cont3`**.
The first repository gate was `git merge-base --is-ancestor aa2373fe57b1b83407bec0ca70d0dbf0d2b9924c HEAD`; it succeeded on the campaign base. See `evidence/ancestry.log`.
No rebase, push, or PR was made.

The binding continuation brief and the previous delivery's `fill-3-REPORT.md` were read before proof work, including the continuation frontier's canonicality caution. The earlier reports, integration record, statement-gate findings/resolutions, P4.4 route findings/resolutions/addendum, policy, workflow §4, and plan §4e were consulted. Targets 1–8 and their helpers were used as proved infrastructure. The new proofs cite no result from `ConfigGraph`, `Path`, or `ImmermanSzelepcsenyi`.

## Completed construction

Let the input host be `h = pairEncode w (Nat.bits p)`, let `n = h.length`, and let `|f x| ≤ C (|x|+1)^e`. The new finite control is `CompState C e`; the one program is `compARM C e mode : ARM 14 4 (CompState C e)`. The mode bit selects bit or length membership. The program itself depends only on the polynomial witness and the mode; `f` is supplied through the already-proved oracle bank `compBank f`.

The common register bound is

```
B(n) = 8 * (2*C+3) * (n+1)^(e+1).
```

The proof checks this bound at every pre-halt configuration, including arithmetic temporaries. `CompReach` and `CompHalt` merely specialize the received `AReach` and `AHalt` with one shared guard `CompGood`; no new reachability semantics or correctness assumption is introduced.

1. **Physical length and shape.** `inputLength_loop` counts the host. `alignedPair_loop` validates the outer pair at stride one and the nested first field at stride two. All pair-layout reasoning uses `pairEncode_getD`; no aligned input scan is reproved. Malformed outer or inner pair shapes return false.
2. **Full output cap before outer decoding.** A shared polynomial subprogram computes `K = (2*C+3)*(n+1)^(e+1)` by bounded repeated multiplication and fixed scaling. `canonicalTail_loop` checks the outer tail's canonicality and width against `Nat.bits K` **before the ARM stores or accumulates `p`**. An over-width canonical query rejects using the frozen `compQ_query_overflow`, which rests on the full `compQ_length_le` bound. A passing width check bounds every reverse-decoder accumulator by `2*K`, within `B(n)`; `boundedDecode_loop` then decodes the bounded outer index. The program never substitutes the smaller `dropIdx` cap.
3. **Independent inner canonicality.** If `w = pairEncode x b`, the program checks whether `b` is empty, or otherwise reads its last physical bit and requires true. The last bit is at physical position `2*w.length-2`. This uses the frozen canonical-tail characterization and the received pair-lookup law. The ARM never decodes the numerical value represented by `b` and imposes no numeric/width cap on that field. Canonical `b` of arbitrarily large represented value is accepted. Empty `b` correctly represents zero.
4. **Exact capped length search.** The saved inner-tail start is `4*x.length+4`, so copying and halving twice gives the base `x.length+1`. The same polynomial routine computes the exact cap `C*(x.length+1)^e`. The length loop checks equality with that cap before issuing a lifted length query. It queries `j` only for `j < cap`, returns the first false `j`, or the cap when every smaller query succeeds. At cap zero it returns zero with no length query. `comp_length_search` proves the exact result `F = (f x).length` using a decreasing remaining-length induction.
5. **Full output layout.** A shared indexed seek covers the virtual prefix at stride one. A hit `p < 2*F` accepts in length mode and queries the lifted `f` bit at `p/2` in bit mode. The next two cells give the separator `[false,true]`. The suffix seek has physical stride two and reads `b[j]` at `4*x.length+4+2*j`. A miss rejects. Thus length mode decides precisely `p < 2*F+2+b.length`; the bit mode also handles separator cells, empty payloads, and out-of-range indices.
6. **Assembly.** `comp_run` joins those fragments into bounded halting on every physical host, including malformed and over-width cases. `comp_mem` applies `arm_decides_poly` with coefficient `8*(2*C+3)`, exponent `e+1`, and the frozen `compBank_mem`. Target 9 uses the already-landed `compQ_length_le` for the function output bound.

The two polynomial evaluations share their multiplication and scaling code. Both query languages share all validation, decoding, length-search, and layout code. All generic copy, transfer, validation, decoding, and indexed-seek obligations are instances of the received public exports.

Target 10 uses the pre-ship D2 bound and proof verbatim, except that the two occurrences of the **function** `compQ f` in set expressions are qualified as `Complexity.compQ f`: inside the theorem namespace, unqualified `compQ` resolves to the newly proved theorem instead. The private `comp_length_le` proof is copied exactly from the explicitly mandated pre-ship probe, with private visibility and a proof-sketch docstring. Target 11 follows the brief's witness exactly.

## Scope, freeze, and flags

- **Only modified source files:** `TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean` (2,621 lines) and `TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean` (184 lines).
- **Imports:** unchanged in both files; no Mathlib or TCSlib import added.
- **Public declarations:** none added. There are 55 new private source declarations in `QueryReshape` and one in `Reductions`, listed individually below. The finite control's generated constructors/instances are private.
- **Frozen material:** the scope audit removes only the added private blocks, replaces only the three owned proof bodies, and reverses only the permitted status substitutions; each resulting file is byte-for-byte equal to the base. Thus all original signatures, other bodies, definitions, attributions, and non-status documentation are preserved. `InputAccess.lean`, `PreimageHost.lean`, `Mult.lean`, and the checker script are also verified byte-identical to the base. See `evidence/freeze-audit.log` and its reproducible script.
- **Status updates (flagged):** the module “sorried” label in `QueryReshape` now says “proved”; target 9's “spec, fill pending” tag says “proved”; the `Reductions` module label now says its phase-P4.4 statements are proved; target 10's tag says “proved”; target 11's tag says “proved”. No other received prose changes.
- **Appendices:** none added to received target docstrings. New private helpers have their own docstrings and the nontrivial proof sketches.
- **Local elaboration option:** `set_option synthInstance.maxSize 2000 in` is scoped only to the new finite control's derived instances. No trust/checking option is disabled.
- **Requested shared lemmas / promotion requests:** none. All reusable input-access fragments were already available; the new helpers are specific to this program and its register layout.
- **New axioms, unsafe declarations, admissions, or private sorries:** none.
- **Mathematical escalations:** none for targets 9–11.
- **Verification scope conflict (flagged):** the brief simultaneously freezes target 12 in the parallel batch and requests that all twelve axiom prints have no `sorryAx`. At this base, target 12 is still its original admission. It is left untouched as required, and its print is reported honestly. Targets 1–11, including all three owned targets, have only the standard axiom triple. Removing target 12's `sorryAx` requires the separate `Mult.lean` delivery; it is not a dependency of this delivery.

## Private declaration inventory

All names below are file-local in `Complexity`; every new source declaration is listed. The role column describes the supporting invariant or machine component.

| File | New private declaration | Line | Role |
|---|---|---:|---|
| `QueryReshape.lean` | `CompState` | 1182 | Finite control for the one composition-query ARM. The two polynomial evaluations share their multiplication and fixed-scaling code; all input access goes through the four proved oracle languages. |
| `QueryReshape.lean` | `compCopy` | 1218 | Saved boundaries and base values use the received bounded copy loop. |
| `QueryReshape.lean` | `compStride` | 1229 | The outer query uses stride one; its first field uses stride two. |
| `QueryReshape.lean` | `compLimit` | 1232 | Each shape validator stops at its previously saved physical boundary. |
| `QueryReshape.lean` | `compAdvance` | 1235 | The finite chains instantiate the public aligned-pair validator. |
| `QueryReshape.lean` | `compFactor` | 1242 | The coefficient is fixed in the control, and can be zero on the inner evaluation. |
| `QueryReshape.lean` | `compFactorAdvance` | 1245 | Fixed scaling uses the public transfer loop, including a zero multiplier. |
| `QueryReshape.lean` | `compDecodeAdvance` | 1251 | The reverse decoder has its standard two increments per transferred unit. |
| `QueryReshape.lean` | `compARM` | 1260 | A single finite ARM supplies both composition-query languages. Registers 0--5 are pointer, host length, outer-tail start, inner end, inner-tail start, and bounded query; 6--8 and 10--11 are arithmetic scratch; 12 is the searched output length and 13 the output-position counter. Register 9 is unused. |
| `QueryReshape.lean` | `compOracle` | 1350 | The actual four-oracle answers, independent of the machine mode and polynomial witness. |
| `QueryReshape.lean` | `compBound` | 1354 | The register bound covers both the full output cap and twice that cap for decoding. |
| `QueryReshape.lean` | `comp_preS` | 1360 | All syntactic side conditions are independent of the input and register values. |
| `QueryReshape.lean` | `comp_bit` | 1394 | A physical input bit uses exactly the already-proved access-bank law. |
| `QueryReshape.lean` | `comp_len` | 1399 | A physical input length call uses the same proved access-bank law. |
| `QueryReshape.lean` | `comp_lifted` | 1404 | A genuine lifted call is answered by the received two-drop identity. |
| `QueryReshape.lean` | `CompGood` | 1413 | One common guard supplies the syntactic and register conditions to both received run relations. |
| `QueryReshape.lean` | `CompReach` | 1417 | Bounded runs use the received reachability relation, with no extra semantic assumption. |
| `QueryReshape.lean` | `CompHalt` | 1421 | The corresponding bounded halting assertion. |
| `QueryReshape.lean` | `comp_product` | 1429 | The multiplication body repeatedly adds the saved multiplicand, preserving the base. |
| `QueryReshape.lean` | `comp_multiply` | 1504 | One power round multiplies the accumulator by its base and restores all scratch. |
| `QueryReshape.lean` | `comp_factor_run` | 1553 | The final constant scaling shares the proved transfer loop, even when the coefficient is zero. Scratch register 11 is restored to zero. |
| `QueryReshape.lean` | `comp_power_run` | 1589 | The power subprogram has a polynomial bound on every intermediate value. |
| `QueryReshape.lean` | `comp_poly_run` | 1633 | Starting from cleared scratch, the shared polynomial routine computes its exact cap. The inner coefficient may be zero; the routine still halts and returns zero. |
| `QueryReshape.lean` | `comp_power_bound` | 1652 | Every required power, at either base and coefficient, fits the full output cap. |
| `QueryReshape.lean` | `comp_bound_room` | 1665 | Twice the full cap and all physical addresses fit the common polynomial bound. |
| `QueryReshape.lean` | `comp_length_search` | 1683 | A capped length search never queries the cap itself. It stops at the first false answer, or returns the cap if every smaller answer is true. |
| `QueryReshape.lean` | `compValues` | 1724 | Boundary vectors keep the physical positions separate from the bounded query and arithmetic scratch. |
| `QueryReshape.lean` | `compValues_apply` | 1728 | Coordinate lookup exposes the vector without unfolding it under an update. |
| `QueryReshape.lean` | `compValues_update` | 1732 | A single update changes just the named coordinate of a boundary vector. |
| `QueryReshape.lean` | `comp_copy_run` | 1743 | The copy stages are all instances of the proved counting copy. |
| `QueryReshape.lean` | `comp_pair_run` | 1759 | Both shape scans cite the same public strided validator; no field canonicality is imposed by this fragment. |
| `QueryReshape.lean` | `comp_ret` | 1784 | Returning at an answer node takes one bounded step. |
| `QueryReshape.lean` | `comp_suffix_address` | 1790 | The suffix of the inner pair is read at doubled physical addresses. |
| `QueryReshape.lean` | `comp_last_address` | 1801 | For a nonempty inner field, its final physical bit is exactly its canonicality flag. The field's represented number is never computed. |
| `QueryReshape.lean` | `comp_canonical_run` | 1817 | The inner canonicality check inspects the empty-field boundary or its last bit. Only the physical pointer changes; no numerical bound is imposed on the inner payload. |
| `QueryReshape.lean` | `comp_outer_prepare` | 1872 | After the outer shape scan, save its boundaries and construct the full output cap. |
| `QueryReshape.lean` | `comp_outer_decode` | 1941 | The bounded outer tail is validated before its numeric value is accumulated. |
| `QueryReshape.lean` | `comp_inner_prepare` | 2053 | The inner cap is computed from the saved first-field separator: dividing its physical position by four gives exactly `\|x\| + 1`. No bit of the inner payload is decoded. |
| `QueryReshape.lean` | `compWalk` | 2085 | The two lookup segments use the received indexing loop at strides one and two. |
| `QueryReshape.lean` | `comp_seek_run` | 2092 | A virtual-prefix or physical-suffix seek is a direct shared-fragment instantiation. |
| `QueryReshape.lean` | `comp_call_return` | 2125 | An oracle-return node returns exactly its answer, preserving every register. |
| `QueryReshape.lean` | `comp_suffix_hit` | 2136 | A matching suffix position accepts in length mode and reads the physical bit in bit mode. |
| `QueryReshape.lean` | `comp_prefix_hit` | 2144 | A matching prefix position reads the lifted `f` bit after halving the virtual address. |
| `QueryReshape.lean` | `comp_suffix_run` | 2166 | A suffix lookup reads exactly the retained payload bit or rejects past its end. |
| `QueryReshape.lean` | `comp_separator_run` | 2215 | Both separator cells and the following suffix have the exact paired-output semantics. |
| `QueryReshape.lean` | `comp_lookup_run` | 2298 | Lookup first seeks within the doubled virtual output of `f`, then delegates the two separator cells and the retained suffix to their common continuation. |
| `QueryReshape.lean` | `compQ_field` | 2339 | The canonicality predicate exactly matches the frozen reshaping definition. |
| `QueryReshape.lean` | `compLang` | 2346 | The two query languages share the program's mode bit. |
| `QueryReshape.lean` | `comp_lang_pair` | 2350 | On a genuine outer query, the indicator is exactly the requested output bit or boundary test. |
| `QueryReshape.lean` | `comp_bad_query` | 2357 | A word with no canonical paired representation is rejected in either mode. |
| `QueryReshape.lean` | `comp_rejected_tail` | 2368 | Both outer-tail failure modes have false answers. Width rejection uses the full composition bound; no unbounded numerical query is stored. |
| `QueryReshape.lean` | `comp_valid_inner` | 2393 | After valid inner syntax, compute the capped length and perform the output lookup. |
| `QueryReshape.lean` | `comp_inner_run` | 2456 | Inner shape and canonicality validation lead either to false or to the proved valid inner computation. Arbitrary first fields and arbitrarily large canonical suffixes are allowed. |
| `QueryReshape.lean` | `comp_run` | 2520 | The composition-query ARM halts correctly on every physical input within one fixed polynomial register bound. |
| `QueryReshape.lean` | `comp_mem` | 2579 | Compile the single mode-parametrized construction against the four proved languages. |
| `Reductions.lean` | `comp_length_le` | 76 | The composite output bound of [AB09, Lemma 4.17] (P4.4 audit, question 2). |

## Verification

All Lean checks used the unchanged `scripts/lean_check_tree.sh`. **No `lake build` was run.** The environment is Lean 4.25.0 (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), with mathlib pinned to `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

The first `lake exe cache get` attempt encountered missing `.ltar` cache files, and an initial bootstrap attempt exposed a stale package-cache link. Those failures are recorded in `evidence/cache-get.log` and `evidence/bootstrap-cache-failure.log`. After selecting the available cache at the verified pinned revision, the **entire 105-module order was bootstrapped fresh from its first entry**, with zero errors and exactly 21 expected base sorry warnings. No project `.olean` from another delivery was used as the final bootstrap result. The base warning list was recorded by declaration name before the fill and is quoted below.

The execution environment needed a `readlink` workaround for Lean's executable discovery (`/proc/<self-pid>/exe` to `/proc/self/exe`). Its source is included as `evidence/lean-self-path.c`. It was loaded using `LD_PRELOAD`; it does not modify Lean, its kernel, the checking script, or dependencies. Reproduction on a normal host requires only the pinned toolchain, cache, and the commands below, without that environment workaround.

Final verification:

| Check | Outcome |
|---|---|
| `QueryReshape` and `Reductions` | Zero errors and zero sorry warnings. |
| Final eight modules, in the brief's order | All exit 0; exactly six remaining sorry warnings: `Path` 2, `ImmermanSzelepcsenyi` 3, `Mult` 1. |
| Whole order's remaining warning set | Eighteen: twelve unchanged upstream admissions from the successful base bootstrap, plus those six. |
| Unchanged pre-ship statement probe | Exit 0, zero errors, no admission of its own; all owned targets print only standard axioms. |
| All twelve target axiom prints | Targets 1–11 are within `[propext, Classical.choice, Quot.sound]`. Target 12 alone retains its original `sorryAx`, as required by its frozen scope. |
| Campaign style lint | `style_lint: 0 FAIL, 3 WARN over 45 files`. |
| Text duplication screen | No new cross-file pair; three new in-file pairs, all below 90%; new copies: none. |
| Statement/body/import freeze audit | Pass; every unowned byte is preserved after reversing the narrowly permitted changes. |
| Patch replay | Applies to the recorded base and reproduces the exact delivery HEAD tree. |
| Git bundle | Verified against its recorded base prerequisite. |
| `git diff --check` | Pass. |

The three lint warnings are file-length notices for `Inclusions`, `InputAccess`, and `QueryReshape`. The first two files are frozen; the enlarged owned file follows this brief’s explicit no-size-cap exception (ground rule 8) and its prohibition on adding source files or changing imports. No lint failure is waived.

A first final sweep caught a tactic-sequencing error in a warning cleanup. It was corrected, checked in an isolated fragment, and the full final eight-module sweep and probes were rerun successfully on the corrected source. The failed cleanup sweep is retained separately from the passing `final-sweep.log` for transparency. It introduced no admission or trust change.

Reproduction commands from the repository root, after applying the patch or importing the bundle:

```sh
lake exe cache get
( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
    < briefs/orders/ch34-b7-cont3.txt )
( tail -n 8 briefs/orders/ch34-b7-cont3.txt | \
    while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done )
cp audits/evidence/b7/B7StatementsProbe.lean.txt .lake/B7StatementsProbe.lean
bash scripts/lean_check_tree.sh .lake/B7StatementsProbe
# Copy evidence/FinalAxioms.lean from this delivery to .lake/FinalAxioms.lean:
bash scripts/lean_check_tree.sh .lake/FinalAxioms
python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity
```

The completed delivery contains the full modified sources, a single-commit format-patch series against the recorded base, a git bundle, logs and supporting evidence, and `SHA256SUMS`. The manifest covers every delivered file except itself. The archive was tested and every manifest digest was verified against its ZIP contents.

## Duplication governance

The before-screen reproduced the inherited `audits/logs/b7-fill-3-screen-after.txt` **byte for byte**: 317 declarations, 72 pairs, 19,550 reproduced characters.

The final after-screen has **363 declarations, 75 pairs, 20,607 reproduced characters**. Every inherited pair is unchanged. There are exactly three new pairs, all in `QueryReshape.lean`:

| Target reproduces source | Match | Justification |
|---|---:|---|
| `CompState` reproduces `DropState` | 356/667 = 53% | The two finite controls use conventional names for instances of the same received validation and decoding fragments; the new control adds the polynomial arithmetic, independent inner canonicality, and capped lifted-length states. The generic transition proofs are reused through their public loops. |
| `comp_seek_run` reproduces `drop_seek_run` | 221/428 = 52% | Both discharge endpoint transition equations of the received `indexedSeek_loop`; this instance uses a virtual prefix and the composition program's 14-register physical suffix layout. The seek induction is cited, not copied. |
| `comp_multiply` reproduces `comp_factor_run` | 480/944 = 51% | Both save and clear the arithmetic accumulator through the received copy/transfer fragments. Multiplication iterates the variable base and restores iteration scratch; fixed coefficient scaling uses `registerScale_loop` directly. The shared polynomial routine calls each once, serving both cap evaluations. |

**New cross-file pairs involving owned declarations: none. New copies: none.**

An intermediate development screen identified duplicate trivial decoder-control and vector-update normalizations, and duplicated reach/halt guards. These were factored before delivery: the decoder control reuses `dropDecodeAdvance`; vector updates use the received finite-vector update identities; the initial zero vector uses that same vector update theorem; and both run abbreviations share `CompGood`. No new pair at or above 90% remains. The final comparison contains no new ARM assembly / `UnaryLogspace::ltLang_mem` pair and no new reachability-relation copy.

Exact screen command (before and after):

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py "$PWD" \
  TCSlib/Complexity/SpaceComplexity/Logspace/{InputAccess,PreimageHost,QueryReshape,Reductions,Mult}.lean \
  TCSlib/Complexity/SpaceComplexity/{ImplicitPoly,UnaryLogspace,CounterProgSim,CounterProgSimRun,ConfigCount,SpaceClasses,Basic}.lean \
  TCSlib/Complexity/SpaceComplexity/Machines/{DblLang,ARMKit,ARMProof,Compile,Lib,FragDec,Frag,Bank,ParsePlain,Parse}.lean
```

The parallel batch's unpublished `Mult.lean` work is not visible to this comparison. The delivered `Mult.lean` baseline is untouched; any integration-time match with that batch remains for the maintainer, per the brief.

## Delivery commit

Base: `0bf08187c1a8c24b3733b4300f3c0d00886dc109`. Delivery HEAD: `fe9b6ee31232aa573d2f5d89289e0f91a48c7b7b`.

One patch is supplied under `patches/`; it replays exactly to the delivery tree. The bundle carries `refs/heads/fill/ch34-b7-cont3` and requires the recorded base.

## Recorded base sorry-warning set

```text
# base sorry-warning set at the issue tree (integrate/b7-fill-3 on the campaign tip 635afc66) over briefs/orders/ch34-b7-cont3.txt: one entry per declaration whose comment-stripped text contains `sorry` (Lean warns once per such declaration)
SpaceComplexity/Constructible: 2: spaceConstructible_logSpace, spaceConstructible_linear
SpaceComplexity/ConfigGraph: 3: NSPACE_subset_exp_dtime, NL_subset_P, polyTimeReducible_of_mem_NL
SpaceComplexity/Savitch: 3: spaceConstructible_poly, savitch, PSPACE_eq_NPSPACE
SpaceComplexity/Hierarchy: 4: space_universal, space_hierarchy, LOGSPACE_ssubset_PSPACE, SPACE_linear_ne_NP
SpaceComplexity/Logspace/QueryReshape: 1: ImplicitlyLogspaceComputable.compQ
SpaceComplexity/Logspace/Reductions: 2: ImplicitlyLogspaceComputable.comp, LogspaceReducible.trans
SpaceComplexity/Logspace/Path: 2: PATH_mem_NL, PATH_NLComplete
SpaceComplexity/Logspace/ImmermanSzelepcsenyi: 3: compl_PATH_mem_NL, NL_eq_coNL, NSPACE_compl_eq
SpaceComplexity/Logspace/Mult: 1: multLang_mem_LOGSPACE
TOTAL 21
```

## Final verification summary

```text
PASS base bootstrap: 105 modules, 0 errors, exactly 21 base sorry warnings
PASS final sweep: 8 modules, 0 errors; owned files 0 sorry warnings; Path 2, ImmermanSzelepcsenyi 3, Mult 1
PASS combined closure: 18 remaining original admissions = 12 frozen upstream + 6 final-eight
PASS unchanged pre-ship probe: 0 errors, no sorry of its own, target 12 alone still prints sorryAx
PASS all twelve axiom prints: targets 1–11 within the standard triple; target 12 retains its frozen sorryAx
style_lint: 0 FAIL, 3 WARN over 45 files
PASS duplication: inherited pairs unchanged; 3 new in-file pairs below 90%; 0 new cross-file pairs; new copies: none
declarations screened: 363; copy pairs (target reproduces >= half of source): 75; reproduced text: 20,607 chars
PASS git diff --check
```

## Final sweep log

```text
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess
EXIT 0 TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost
EXIT 0 TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
EXIT 0 TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
EXIT 0 TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/Path
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:104:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:133:8: warning: declaration uses 'sorry'
EXIT 0 TCSlib/Complexity/SpaceComplexity/Logspace/Path
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:80:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:93:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:112:8: warning: declaration uses 'sorry'
EXIT 0 TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
CHECK TCSlib/Complexity/SpaceComplexity/Logspace/Mult
TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean:71:8: warning: declaration uses 'sorry'
EXIT 0 TCSlib/Complexity/SpaceComplexity/Logspace/Mult
CHECK TCSlib/Complexity/SpaceComplexity
EXIT 0 TCSlib/Complexity/SpaceComplexity
PASS: final eight-module sweep completed.
```

## All twelve target axiom prints

```text
'Complexity.LogProg.OIS.run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.compile_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_of_logspaceReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.readIn_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_dropIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.compQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogspaceReducible.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.multLang_mem_LOGSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Pre-ship probe rerun

```text
'Complexity.LogProg.readIn_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.compile_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_dropIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.compQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.pairEncode_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.indicator_indexLang_pairEncode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.vword_whole₁' depends on axioms: [propext]
'Complexity.dropIdx_pairEncode' depends on axioms: [propext, Quot.sound]
'Complexity.dropIdx_length_le' depends on axioms: [propext, Quot.sound]
'Complexity.compQ_pairEncode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_indexLang_compQ_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.compQ_length_le' depends on axioms: [propext, Quot.sound]
'Complexity.inputBitLang_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.inputLenLang_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogspaceReducible.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_of_logspaceReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.multLang_mem_LOGSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogProg.compile_space' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.bank_cleanRun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.arm_decides_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.inc_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.dec_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.eq_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.clr_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.rewind_x' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.canon_eq_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.MultiTapeTM.abs_pos_lt_card_visited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LOGSPACE_subset_NL' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Before-screen — exact output

```text
declarations screened: 317; copy pairs (target reproduces >= half of source): 72; reproduced text: 19,550 chars
   ARMKit.lean::vword_unary₂  reproduces  ARMKit.lean::vword_unary₁: 176/176 = 100%
   ARMKit.lean::vword_unary₁  reproduces  ARMKit.lean::vword_unary₂: 176/176 = 100%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.trans: 200/202 = 99%
   ARMProof.lean::AReach.trans  reproduces  DblLang.lean::Rch.trans: 200/202 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   ImplicitPoly.lean::regCfg_cfg  reproduces  DblLang.lean::regCfg_K: 121/124 = 98%
   ARMProof.lean::AReach.halt  reproduces  ARMProof.lean::AReach.trans: 197/202 = 98%
   ARMProof.lean::AReach.halt  reproduces  DblLang.lean::Rch.trans: 185/202 = 92%
   ParsePlain.lean::validPlain_iff  reproduces  ARMKit.lean::takeWhile_pairEncode_replicate: 94/105 = 90%
   QueryReshape.lean::drop_u_prepare  reproduces  QueryReshape.lean::drop_lookup_prepare: 311/349 = 89%
   CounterProgSimRun.lean::Bd  reproduces  CounterProgSim.lean::cf: 190/220 = 86%
   DblLang.lean::regCfg_K  reproduces  ImplicitPoly.lean::regCfg_cfg: 121/143 = 85%
   ARMProof.lean::AReach.trans  reproduces  ARMProof.lean::AReach.halt: 197/236 = 83%
   QueryReshape.lean::drop_z_prepare  reproduces  QueryReshape.lean::drop_lookup_prepare: 291/349 = 83%
   InputAccess.lean::access_reject  reproduces  InputAccess.lean::access_jump: 93/113 = 82%
   DblLang.lean::sym_lt  reproduces  DblLang.lean::sym_eq: 83/101 = 82%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_eq: 82/101 = 81%
   CounterProgSim.lean::pr_halt  reproduces  CounterProgSim.lean::pr_reach: 836/1033 = 81%
   ParsePlain.lean::rrun_one_x  reproduces  Frag.lean::rrun_one_eq: 67/84 = 80%
   Frag.lean::rrun_one_eq  reproduces  ParsePlain.lean::rrun_one_x: 67/85 = 79%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.halt: 185/236 = 78%
   InputAccess.lean::access_clear  reproduces  InputAccess.lean::access_inc: 212/271 = 78%
   FragDec.lean::rrun_one_reg  reproduces  Frag.lean::rrun_one_eq: 64/84 = 76%
   QueryReshape.lean::drop_u_prepare  reproduces  QueryReshape.lean::drop_z_prepare: 442/584 = 76%
   FragDec.lean::decDAct  reproduces  Lib.lean::incCAct: 61/82 = 74%
   DblLang.lean::sym_eq  reproduces  DblLang.lean::sym_lt: 83/112 = 74%
   CounterProgSim.lean::cf  reproduces  CounterProgSimRun.lean::Bd: 190/257 = 74%
   InputAccess.lean::access_answer  reproduces  InputAccess.lean::access_jump: 83/113 = 73%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_lt: 81/112 = 72%
   Frag.lean::half_run  reproduces  FragDec.lean::clr_run: 375/520 = 72%
   Frag.lean::eqB_run  reproduces  Parse.lean::regBack_x: 617/864 = 71%
   InputAccess.lean::access_inc  reproduces  InputAccess.lean::access_clear: 212/299 = 71%
   CounterProgSimRun.lean::ans_append  reproduces  CounterProgSimRun.lean::ans_of_le: 60/86 = 70%
   Lib.lean::incB_run  reproduces  Frag.lean::eqB_run: 654/938 = 70%
   FragDec.lean::decD_run  reproduces  Lib.lean::incC_run: 1179/1733 = 68%
   Frag.lean::halfL_run  reproduces  FragDec.lean::clrE_run: 928/1366 = 68%
   CounterProgSimRun.lean::ans_of_le  reproduces  CounterProgSimRun.lean::ans_append: 60/90 = 67%
   ImplicitPoly.lean::rounds  reproduces  DblLang.lean::Rch.trans: 134/202 = 66%
   CounterProgSim.lean::pr_reach  reproduces  CounterProgSim.lean::pr_halt: 836/1262 = 66%
   Parse.lean::regBack_x  reproduces  Frag.lean::eqB_run: 617/938 = 66%
   InputAccess.lean::access_bump  reproduces  InputAccess.lean::access_inc: 177/271 = 65%
   QueryReshape.lean::drop_inner_run  reproduces  QueryReshape.lean::drop_nested_run: 895/1388 = 64%
   FragDec.lean::clrEAct  reproduces  FragDec.lean::toEndAct: 144/229 = 63%
   Lib.lean::incB_run  reproduces  Parse.lean::regBack_x: 536/864 = 62%
   InputAccess.lean::readFrame  reproduces  InputAccess.lean::readAt: 66/107 = 62%
   Frag.lean::eqB_run  reproduces  Lib.lean::incB_run: 654/1066 = 61%
   Lib.lean::incB_run  reproduces  FragDec.lean::toEnd_run: 582/951 = 61%
   QueryReshape.lean::dropIdx_prefix_address  reproduces  QueryReshape.lean::dropIdx_suffix_address: 256/420 = 61%
   InputAccess.lean::readIn_run  reproduces  InputAccess.lean::read_one: 81/135 = 60%
   Frag.lean::rrun_one_eq  reproduces  FragDec.lean::rrun_one_reg: 64/110 = 58%
   QueryReshape.lean::dropIdx_suffix_address  reproduces  QueryReshape.lean::dropIdx_prefix_address: 256/443 = 58%
   FragDec.lean::clr_run  reproduces  Frag.lean::half_run: 375/653 = 57%
   InputAccess.lean::access_jump  reproduces  InputAccess.lean::access_reject: 93/167 = 56%
   Lib.lean::inc_run  reproduces  FragDec.lean::dec_run: 372/670 = 56%
   CounterProgSimRun.lean::UnaryLogspace.counterProg  reproduces  UnaryLogspace.lean::ltLang_mem: 580/1051 = 55%
   InputAccess.lean::read_cleanup  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   Lib.lean::incCAct  reproduces  FragDec.lean::decDAct: 61/111 = 55%
   FragDec.lean::toEnd_run  reproduces  Lib.lean::incB_run: 582/1066 = 55%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::read_cleanup: 523/993 = 53%
   FragDec.lean::dec_run  reproduces  Lib.lean::inc_run: 372/707 = 53%
   InputAccess.lean::access_bump  reproduces  InputAccess.lean::access_clear: 157/299 = 53%
   QueryReshape.lean::drop_z_prepare  reproduces  QueryReshape.lean::drop_u_prepare: 442/871 = 51%
   DblLang.lean::dblLang_mem  reproduces  UnaryLogspace.lean::orc_eq: 76/150 = 51%
   Parse.lean::regBack_x  reproduces  Lib.lean::incB_run: 536/1066 = 50%
   Lib.lean::update_bufferTape_cons  reproduces  FragDec.lean::bufferTape_erase_last: 137/273 = 50%
```

## After-screen — exact output

```text
declarations screened: 363; copy pairs (target reproduces >= half of source): 75; reproduced text: 20,607 chars
   ARMKit.lean::vword_unary₂  reproduces  ARMKit.lean::vword_unary₁: 176/176 = 100%
   ARMKit.lean::vword_unary₁  reproduces  ARMKit.lean::vword_unary₂: 176/176 = 100%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.trans: 200/202 = 99%
   ARMProof.lean::AReach.trans  reproduces  DblLang.lean::Rch.trans: 200/202 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   ImplicitPoly.lean::regCfg_cfg  reproduces  DblLang.lean::regCfg_K: 121/124 = 98%
   ARMProof.lean::AReach.halt  reproduces  ARMProof.lean::AReach.trans: 197/202 = 98%
   ARMProof.lean::AReach.halt  reproduces  DblLang.lean::Rch.trans: 185/202 = 92%
   ParsePlain.lean::validPlain_iff  reproduces  ARMKit.lean::takeWhile_pairEncode_replicate: 94/105 = 90%
   QueryReshape.lean::drop_u_prepare  reproduces  QueryReshape.lean::drop_lookup_prepare: 311/349 = 89%
   CounterProgSimRun.lean::Bd  reproduces  CounterProgSim.lean::cf: 190/220 = 86%
   DblLang.lean::regCfg_K  reproduces  ImplicitPoly.lean::regCfg_cfg: 121/143 = 85%
   ARMProof.lean::AReach.trans  reproduces  ARMProof.lean::AReach.halt: 197/236 = 83%
   QueryReshape.lean::drop_z_prepare  reproduces  QueryReshape.lean::drop_lookup_prepare: 291/349 = 83%
   InputAccess.lean::access_reject  reproduces  InputAccess.lean::access_jump: 93/113 = 82%
   DblLang.lean::sym_lt  reproduces  DblLang.lean::sym_eq: 83/101 = 82%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_eq: 82/101 = 81%
   CounterProgSim.lean::pr_halt  reproduces  CounterProgSim.lean::pr_reach: 836/1033 = 81%
   ParsePlain.lean::rrun_one_x  reproduces  Frag.lean::rrun_one_eq: 67/84 = 80%
   Frag.lean::rrun_one_eq  reproduces  ParsePlain.lean::rrun_one_x: 67/85 = 79%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.halt: 185/236 = 78%
   InputAccess.lean::access_clear  reproduces  InputAccess.lean::access_inc: 212/271 = 78%
   FragDec.lean::rrun_one_reg  reproduces  Frag.lean::rrun_one_eq: 64/84 = 76%
   QueryReshape.lean::drop_u_prepare  reproduces  QueryReshape.lean::drop_z_prepare: 442/584 = 76%
   FragDec.lean::decDAct  reproduces  Lib.lean::incCAct: 61/82 = 74%
   DblLang.lean::sym_eq  reproduces  DblLang.lean::sym_lt: 83/112 = 74%
   CounterProgSim.lean::cf  reproduces  CounterProgSimRun.lean::Bd: 190/257 = 74%
   InputAccess.lean::access_answer  reproduces  InputAccess.lean::access_jump: 83/113 = 73%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_lt: 81/112 = 72%
   Frag.lean::half_run  reproduces  FragDec.lean::clr_run: 375/520 = 72%
   Frag.lean::eqB_run  reproduces  Parse.lean::regBack_x: 617/864 = 71%
   InputAccess.lean::access_inc  reproduces  InputAccess.lean::access_clear: 212/299 = 71%
   CounterProgSimRun.lean::ans_append  reproduces  CounterProgSimRun.lean::ans_of_le: 60/86 = 70%
   Lib.lean::incB_run  reproduces  Frag.lean::eqB_run: 654/938 = 70%
   FragDec.lean::decD_run  reproduces  Lib.lean::incC_run: 1179/1733 = 68%
   Frag.lean::halfL_run  reproduces  FragDec.lean::clrE_run: 928/1366 = 68%
   CounterProgSimRun.lean::ans_of_le  reproduces  CounterProgSimRun.lean::ans_append: 60/90 = 67%
   ImplicitPoly.lean::rounds  reproduces  DblLang.lean::Rch.trans: 134/202 = 66%
   CounterProgSim.lean::pr_reach  reproduces  CounterProgSim.lean::pr_halt: 836/1262 = 66%
   Parse.lean::regBack_x  reproduces  Frag.lean::eqB_run: 617/938 = 66%
   InputAccess.lean::access_bump  reproduces  InputAccess.lean::access_inc: 177/271 = 65%
   QueryReshape.lean::drop_inner_run  reproduces  QueryReshape.lean::drop_nested_run: 895/1388 = 64%
   FragDec.lean::clrEAct  reproduces  FragDec.lean::toEndAct: 144/229 = 63%
   Lib.lean::incB_run  reproduces  Parse.lean::regBack_x: 536/864 = 62%
   InputAccess.lean::readFrame  reproduces  InputAccess.lean::readAt: 66/107 = 62%
   Frag.lean::eqB_run  reproduces  Lib.lean::incB_run: 654/1066 = 61%
   Lib.lean::incB_run  reproduces  FragDec.lean::toEnd_run: 582/951 = 61%
   QueryReshape.lean::dropIdx_prefix_address  reproduces  QueryReshape.lean::dropIdx_suffix_address: 256/420 = 61%
   InputAccess.lean::readIn_run  reproduces  InputAccess.lean::read_one: 81/135 = 60%
   Frag.lean::rrun_one_eq  reproduces  FragDec.lean::rrun_one_reg: 64/110 = 58%
   QueryReshape.lean::dropIdx_suffix_address  reproduces  QueryReshape.lean::dropIdx_prefix_address: 256/443 = 58%
   FragDec.lean::clr_run  reproduces  Frag.lean::half_run: 375/653 = 57%
   InputAccess.lean::access_jump  reproduces  InputAccess.lean::access_reject: 93/167 = 56%
   Lib.lean::inc_run  reproduces  FragDec.lean::dec_run: 372/670 = 56%
   CounterProgSimRun.lean::UnaryLogspace.counterProg  reproduces  UnaryLogspace.lean::ltLang_mem: 580/1051 = 55%
   InputAccess.lean::read_cleanup  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::readFrame_at: 86/156 = 55%
   Lib.lean::incCAct  reproduces  FragDec.lean::decDAct: 61/111 = 55%
   FragDec.lean::toEnd_run  reproduces  Lib.lean::incB_run: 582/1066 = 55%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   QueryReshape.lean::CompState  reproduces  QueryReshape.lean::DropState: 356/667 = 53%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::read_cleanup: 523/993 = 53%
   FragDec.lean::dec_run  reproduces  Lib.lean::inc_run: 372/707 = 53%
   InputAccess.lean::access_bump  reproduces  InputAccess.lean::access_clear: 157/299 = 53%
   QueryReshape.lean::comp_seek_run  reproduces  QueryReshape.lean::drop_seek_run: 221/428 = 52%
   QueryReshape.lean::comp_multiply  reproduces  QueryReshape.lean::comp_factor_run: 480/944 = 51%
   QueryReshape.lean::drop_z_prepare  reproduces  QueryReshape.lean::drop_u_prepare: 442/871 = 51%
   DblLang.lean::dblLang_mem  reproduces  UnaryLogspace.lean::orc_eq: 76/150 = 51%
   Parse.lean::regBack_x  reproduces  Lib.lean::incB_run: 536/1066 = 50%
   Lib.lean::update_bufferTape_cons  reproduces  FragDec.lean::bufferTape_erase_last: 137/273 = 50%
```

