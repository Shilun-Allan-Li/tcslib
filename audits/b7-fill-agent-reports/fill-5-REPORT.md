# B7 multiplication fill — target 12

**Complete: 1/1 owned target.** `Complexity.multLang_mem_LOGSPACE` is proved by a finite abstract register machine over `![inputBitLang, inputLenLang]`, with a proved column/carry invariant and bounded halting on every input. Its axiom print is exactly `[propext, Classical.choice, Quot.sound]`. There are no admitted private helpers and the proved-modulo set is empty.

The final eight-module sweep passed with zero errors and exactly the eight specified out-of-scope sorry warnings. `Mult.lean` itself has zero errors and zero warnings. The unchanged pre-ship probe passed, and campaign lint reports `0 FAIL, 4 WARN`.

**Scope qualification on the all-twelve axiom requirement:** targets 1–8 and 12 have only the standard triple. Targets 9–11 still print `sorryAx` at this base because their frozen bodies belong to the parallel batch. The literal “all twelve: no `sorryAx`” condition cannot be met in this isolated delivery while also obeying the ownership and frozen-body requirements. The complete twelve-target log is included without filtering. No proof here depends on targets 9–11. Their removal is an integration check after the parallel delivery lands, not an unproved part of target 12.

## Provenance and scope

| Item | Value |
| --- | --- |
| Repository | `https://github.com/Shilun-Allan-Li/tcslib` |
| Starting campaign branch | `complexity/arora-barak-ch3-4` |
| Base | `0bf08187c1a8c24b3733b4300f3c0d00886dc109` |
| Required ancestor | `aa2373fe57b1b83407bec0ca70d0dbf0d2b9924c` |
| Working branch | `fill/ch34-b7-mult` |
| Delivery commit | `e685dd851be58a61e55e5bc799391d94a01c4579` |
| Owned and only changed tracked file | `TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean` |
| Final owned-file size | 1,463 lines (base: 74 lines) |
| Diff | 1 file, 1,392 insertions, 3 deletions |

The required `git merge-base --is-ancestor aa2373fe57b1b83407bec0ca70d0dbf0d2b9924c HEAD` check succeeded before proof work. The ancestor is also checked against the recorded base in the supplied scope-check script. No rebase, push, pull request, or edit to another tracked file was performed.

The first reads were `fill-3-REPORT.md` and `fill-2-REPORT.md`. The continuation brief's substrate description, P4.4 findings (including T11 and Q8), resolutions and addendum, B7 statement findings and resolutions, `policy.md`, `workflow.md` §4, and plan §4e were read and applied.

Freeze check: removing the new private block, restoring the target body to its original `sorry`, and reverting exactly the two authorized status labels reproduces the entire base `Mult.lean` byte for byte. All original definitions, imports, options, signatures, attributions, and remaining docstring text are unchanged. All 62 explicitly added declarations are private; generated constructors, recursors, projections and deriving instances belong to those private declarations. There is no new public declaration.

## Completed construction

The machine has 13 natural-number registers and a finite control type. All input access uses the two proved input-access languages. It never decodes or stores an operand or result as a natural-number value.

1. The public `inputLength_loop` obtains the physical input length.
2. Two applications of the public `alignedPair_loop` validate the outer pair and its nested suffix pair, at stride one. The suffix correspondence and the three field addresses come from the public `pairEncode_getD`; there is no reimplementation of aligned scanning.
3. The public `registerCopy_loop` preserves the two field starts and prepares the field ends and column count. A single field-parametrized last-bit path checks each field: it must be empty or end in `true`. Canonicality is checked without numerical decoding.
4. For each column below the sum of the operand lengths, two nested loops enumerate the two operand positions. The first operand is read at `2p`; the second is read at `2|a| + 2 + 2q`. A contribution is added only when `p + q` equals the current column and both bits are true. Each first-operand row contributes at most one, so the accumulator and carry remain bounded.
5. The accumulator parity is compared with the result bit. The result pointer saturates at the physical input end, where subsequent bits are treated as zero. It is advanced only while within the result field.
6. After exactly `|a| + |b|` columns, the pointer must have reached the physical end and the carry must be zero. The final pointer test rejects an excessively long result even if all earlier bits matched. Malformed shapes, noncanonical fields and bit mismatches reject through proved bounded paths.

The physical starts are `2|a| + 2` and `2|a| + 2 + 2|b| + 2`. Subtracting the separators produces the two operand ends. Halving the result start and subtracting two produces the column count. The result field is an undoubled suffix, as required by the actual nested `pairEncode` representation.

The pure proof defines a convolution column and a carry recurrence:

```text
column(j) = Σ p < |a|, if p ≤ j then a[p] · b[j-p] else 0
carry(0) = 0
carry(j+1) = (carry(j) + column(j)) / 2
```

`mult_carry_invariant` proves Q8's weighted invariant, for every natural `n`:

```text
Σ j < n, 2^j · column(j)
  = Σ j < n, 2^j · ((carry(j) + column(j)) % 2) + 2^n · carry(n).
```

`mult_columns_value` identifies the full column sum with `bitsVal a * bitsVal b`. Binary digit uniqueness, the invariant and the zero-padded result expansion yield `mult_columns_correct`: for a result of length at most the column count, the product equation is equivalent to every parity comparison and final zero carry. `mult_product_length` proves the canonical product length bound, including zero. `mult_membership` uses `pairEncode_injective` twice and the received canonical binary uniqueness/value laws (`canon_eq_bits`, `canon_bits`, `bitsVal_bits`) to identify the frozen existential language with the product equation. These received inverse laws supply the canonical uniqueness step without reproving binary injectivity.

`MultGood` carries the actual syntactic `PreS` obligation and the bound `∀ r, v r ≤ 4 * (x.length + 1)`. Every path lemma uses the received `AReach` or `AHalt` at that same predicate, so the bound covers intermediate states and temporary registers, not merely loop endpoints. `mult_inner_loop`, `mult_outer_loop`, and `mult_columns_run` give terminating bounded paths for all iterations; `mult_run` assembles parsing, canonicality and arithmetic for every physical input, including malformed words and empty fields. The final theorem applies `arm_decides_poly` with coefficient 4 and exponent 1, using `inputBitLang_mem` and `inputLenLang_mem` for the bank.

### Reuse of the inherited frontier

The implementation directly cites `pairEncode_getD`, `inputLength_loop`, `alignedPair_loop`, `register_update_le`, and `registerCopy_loop`. It also uses the public ARM reachability/halting combinators, oracle indicator law, pair decoding/injectivity and binary/canonicality lemmas. Neither the target-7 private program nor target-8's private program is copied or referenced. The six exports documented by `fill-3-REPORT.md` were examined; scaling, indexed seeking and bounded numerical decoding are not required by this construction. In particular, `canonicalTail_loop`'s numerical-cap premise is not imposed on the unbounded operand fields. Their canonicality is checked from emptiness and the last bit.

No declaration from `ConfigGraph`, `Path`, or `ImmermanSzelepcsenyi` is cited. No admitted out-of-scope theorem is used. No imports were added, including Mathlib imports.

## New declarations and roles

Every declaration listed below is private and proved or defined without admissions.

| Declaration | Role |
| --- | --- |
| `multColumn` | Convolution column, with absent operand bits read as zero. |
| `multColumn_nil` | Empty first operand gives zero column. |
| `multColumn_cons` | Split the first operand's leading bit out of a column. |
| `multColumn_le` | A column is at most the first operand length. |
| `mult_bits_prefix` | Weighted bit sum equals the value of a prefix, including padding. |
| `mult_column_prefix_cons` | Weighted column-prefix recurrence under a first-operand cons. |
| `mult_columns_value` | Sufficiently many weighted columns give the product of `bitsVal`s. |
| `multCarry` | Carry recurrence starting at zero. |
| `multCarry_le` | Carry is at most the first operand length. |
| `mult_carry_invariant` | Exact weighted column/carry invariant required by Q8. |
| `mult_digits_unique` | Uniqueness of bounded binary digits and final carry. |
| `mult_columns_correct` | Product equation iff the finite parity checks and zero carry. |
| `mult_product_length` | Canonical product length bound, including zero operands. |
| `mult_column_row` | A row's double-loop sum has at most one possible contribution. |
| `mult_column_double` | Double-loop sum equals the convolution column. |
| `multRow` | Remaining inner-loop sum from a given index sum. |
| `multRow_cons` | Inner-loop recurrence consuming a second-operand bit. |
| `multRow_le_one` | A remaining row contributes at most one. |
| `multRows` | Remaining outer-loop sum from a given first-operand index. |
| `multRows_cons` | Outer-loop recurrence consuming a first-operand bit. |
| `multRows_bound` | Remaining outer-loop sum is at most the remaining row count. |
| `multRows_column` | Initial double loop computes the desired column. |
| `mult_canonical_last` | Canonicality iff the word is empty or its last bit is true. |
| `mult_membership` | Frozen language membership iff canonical fields and the product equation. |
| `mult_acceptance` | Membership iff canonicality, result-length bound, parities and zero carry. |
| `MultState` | Finite ARM control; derived decidable equality and finite enumeration. |
| `multPairNext` | Shared continuation table for the two received aligned scans. |
| `multCopy` | Sources, destinations and continuations of the received copy fragment. |
| `multARM` | Complete 13-register multiplication verifier over the input-access bank. |
| `mult_addresses` | Physical addresses for both operands and the padded result. |
| `MultRemaining` | Arithmetic obligation for the unprocessed columns and final checks. |
| `mult_remaining_step` | Split that obligation into current parity and later columns. |
| `multOracle` | The two-language bank's indicator functions. |
| `mult_queries` | Whole-input bit and length query answers. |
| `mult_preconditions` | Every control state satisfies the syntactic ARM preconditions. |
| `MultGood` | Shared `PreS` and linear register-bound predicate. |
| `MultReach` | Received bounded path relation specialized to this machine and guard. |
| `MultHalt` | Received bounded halting relation specialized to the same guard. |
| `mult_copy` | Instantiation of the public bounded register-copy fragment. |
| `mult_scan` | Instantiation of the public aligned-pair fragment, for either scan. |
| `mult_contribution` | Bounded path for one tested bit-pair contribution. |
| `mult_inner_loop` | Terminating bounded inner loop and exact row increment. |
| `mult_row_start` | Shared-copy setup of the second pointer and index sum for a row. |
| `mult_outer_loop` | Terminating bounded outer loop and exact column increment. |
| `mult_return` | Bounded return at either Boolean answer. |
| `mult_finish` | Final pointer and carry tests, including overlong-result rejection. |
| `mult_parity` | Parity comparison, with rejection on mismatch. |
| `mult_result_read` | Result-bit access, reading zero after the field ends. |
| `mult_next_column` | Halve the accumulator and advance column/result pointers safely. |
| `mult_columns_run` | All remaining columns halt with exactly the arithmetic answer. |
| `multCanonSource` | Source register for each of the three last-bit checks. |
| `multCanonCopy` | Shared-copy stage for each of the three last-bit checks. |
| `multCanonNext` | Successful continuation after each canonical field. |
| `mult_last_bit` | One field-parametrized bounded path to its physical last bit. |
| `mult_validate_field` | Empty-field acceptance or last-bit canonicality check. |
| `MultReady` | Prepared field metadata and zeroed loop-register invariant. |
| `mult_ready_frame` | Canonicality setup preserves the prepared metadata. |
| `mult_canonical_run` | Three canonicality checks followed by the column machine. |
| `mult_sub_two` | Two bounded decrements used in metadata preparation. |
| `mult_prepare_run` | Shared copies and separator arithmetic prepare the canonicality phase. |
| `mult_bad_decode` | Either failed pair decode excludes multiplication-language membership. |
| `mult_run` | Complete all-input bounded halting proof from the initial zero registers. |

`multLang_mem_LOGSPACE` is the existing public target; only its body and authorized status tag changed.

## Flags, promotion candidates and remaining obligations

- **Imports:** unchanged. No additional TCSlib or Mathlib edge.
- **Shared-file changes requested for correctness:** none; `InputAccess.lean` remains byte-identical to base.
- **Promotion candidates for serial maintainer review:** the two-step bounded decrement argument `mult_sub_two` (currently machine-specialized); the pure word-prefix expansion `mult_bits_prefix`, binary digit uniqueness `mult_digits_unique`, canonical product-length bound `mult_product_length`, and last-bit characterization `mult_canonical_last`. These remain private here as the brief requires. No promotion is needed to check or integrate this proof.
- **Status update 1:** module heading `Main results (sorried; phase-P4.4 statement)` becomes `Main results (proved; phase-P4.4 statement)`.
- **Status update 2:** target docstring `spec, fill pending — phase P4.4` becomes `proved — phase P4.4`. The rest of the original docstring, including its proof sketch, is unchanged.
- **Appendices:** the new private-construction section documents the implementation and its invariant; no frozen attribution or sketch was rewritten.
- **Size:** 1,463 lines. The new size warning is accepted under ground rule 8, which explicitly removes the size cap and prohibits splitting into new source files. The other three size warnings are unchanged out-of-scope files.
- **Escalations concerning the owned theorem:** none. The only cross-batch verification qualification is the all-twelve axiom condition explained at the start.
- **Partial frontier:** none. No private `sorry`, no proved-modulo helper and no incomplete target-12 obligation remains.

## Duplication governance

**new copies: none**

The before-screen is byte-identical to `audits/logs/b7-fill-3-screen-after.txt`: 317 declarations, 72 pairs, 19,550 reproduced characters. The final screen has 370 screened declarations, 75 pairs and 21,295 reproduced characters. The count of screened declarations is the screen's filtered population, not the count of all 62 added declarations.

There are exactly three new directed pairs, all within `Mult.lean`, all below 90%. No baseline pair disappeared and no new cross-file pair touches the owned file. The 1,745 additional matched characters are the three measurements below; they are similarity measurements, not copied-material claims. The cumulative copied-material ledger for `Mult.lean` is **0 characters, 0%**.

| New directed pair | Screen result | Justification |
| --- | --- | --- |
| `multRows_cons` reproduces `multRow_cons` | 77/95 = 81% | Two different sums consume different operand lists; both cite the same existing `Finset.sum_range_succ'` and addition normalization to unfold their respective definitions. |
| `multRow_cons` reproduces `multRows_cons` | 77/96 = 80% | Reverse measurement of that same short pair of distinct inner/outer recurrence lemmas; no duplicated arithmetic invariant or machine proof. |
| `mult_outer_loop` reproduces `mult_inner_loop` | 1,591/2,947 = 54% | Distinct nested inductions on the first and second operand lists share endpoint/update normalization; the outer proof invokes the proved inner loop and shared row setup without repeating the inner correctness argument. |

The shared guard was factored into `MultGood` so the two specialized path abbreviations do not repeat it. Common copying, scanning, per-contribution, row setup and canonicality paths are each proved once and reused. The prescribed screen's complete before and after outputs are quoted below. The parallel batch's private helpers are absent from this base and remain an integration-time comparison as the brief specifies.

## Verification and environment

Every Lean check used the unchanged `scripts/lean_check_tree.sh`. No `lake build` was run. The toolchain is Lean 4.25.0; mathlib is pinned at `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

The complete 105-module bootstrap was run once successfully before proof work, with the required 21 base sorry warnings. The supplied base inventory names every declaration. The final eight-module sweep ran after the proof edits and produced zero errors, zero owned-file warnings, and exactly the expected eight other sorry warnings: QueryReshape 1, Reductions 2, Path 2 and ImmermanSzelepcsenyi 3. Thus the unchanged upstream closure plus the final suffix has 20 remaining out-of-scope sorry warnings over the whole order list; the whole list was not redundantly rerun after the suffix.

The pre-ship probe was copied byte for byte from `audits/evidence/b7/B7StatementsProbe.lean.txt` into ignored `.lake/b7-verification/B7StatementsProbe.lean` and checked through the script. It has zero errors and no warnings of its own; target 12's print is now the standard triple. A separate ignored probe prints all twelve targets in numerical order. Both probe sources and their complete logs are supplied as evidence, not new tracked modules or imports.

The sandbox needed the available compatibility launcher to tell the stock Lean executable its own path. The launcher sets `S128_EXECUTABLE_PATH` and preloads a small `readlink` shim that supplies that path only for the current process's `/proc/<pid>/exe`; all other `readlink` calls are delegated. Its source and the exact launcher are included for transparency. It changes executable-location discovery, not elaboration, kernel checking or trust. The actual compiler binary was the installed stock Lean 4.25.0.

Pinned pre-existing Mathlib package/cache files were reused; a network cache download was unnecessary. All 105 TCSlib modules were nevertheless freshly checked by the required script. To avoid exhausting the shared workspace disk, 102 byte-identical generated `.olean` files in this checkout were later hardlinked to already-present cache files; no source or reference-cache file was changed. The check script unlinks its output before every compile, and the final sweep created fresh outputs for its modules.

All final commands returned exit 0: eight-module sweep, unchanged pre-ship probe, all-twelve axiom probe, lint, duplication screen, scope/freeze check and `git diff --check`. Lint's four warnings are only the documented file-size warnings. The patch is also replayed against the base in an isolated Git index and its tree compared exactly with the delivery commit; bundle verification is included in the packaging evidence. All payload checksums and ZIP CRCs are verified after final packaging.

## Archive and integration

The ZIP contains this report, the full owned source at its original path, a one-commit format-patch series against the recorded base, an incremental Git bundle, all required logs, probe and scope-check sources, runtime compatibility source, and `SHA256SUMS`. It contains no generated `.olean` files or unrelated repository sources. Nothing was pushed.

From the extracted archive, verify `sha256sum -c SHA256SUMS`. In a campaign checkout containing the recorded base, review and integrate the patch with `git am -3 /path/to/extracted/patches/*.patch`. The incremental bundle requires the recorded base and advertises `refs/heads/fill/ch34-b7-mult`; it is a second transport of the same commit, not a separate change series. The maintainer should combine this with the parallel batch and rerun the joint duplication and all-twelve axiom checks.

The exact logs below are also present individually under `evidence/`.

## Base sorry inventory (verbatim)

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

## Complete final sweep output

```text
Checking TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess
Checking TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost
Checking TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean:1204:8: warning: declaration uses 'sorry'
Checking TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:95:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:105:8: warning: declaration uses 'sorry'
Checking TCSlib/Complexity/SpaceComplexity/Logspace/Path
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:104:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:133:8: warning: declaration uses 'sorry'
Checking TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:80:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:93:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:112:8: warning: declaration uses 'sorry'
Checking TCSlib/Complexity/SpaceComplexity/Logspace/Mult
Checking TCSlib/Complexity/SpaceComplexity
```

## All twelve axiom prints (complete)

```text
'Complexity.LogProg.OIS.run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.compile_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_of_logspaceReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.readIn_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_dropIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.compQ' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.comp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogspaceReducible.trans' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.multLang_mem_LOGSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Re-run pre-ship probe (complete output)

```text
'Complexity.LogProg.readIn_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.compile_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_dropIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.compQ' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
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
'Complexity.ImplicitlyLogspaceComputable.comp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogspaceReducible.trans' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_of_logspaceReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.multLang_mem_LOGSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
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

## Scope and freeze check (complete output)

```text
Required ancestor aa2373fe57b1b83407bec0ca70d0dbf0d2b9924c is an ancestor of base 0bf08187c1a8c24b3733b4300f3c0d00886dc109: PASS
Only tracked change: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean
Removing new private block, restoring target body and two allowed status labels exactly reproduces base: PASS
All original definitions, imports, options, docstrings, attributions and target signature frozen: PASS
New explicit declarations: 62; every one private; public declaration drift: none
Generated constructors, recursors, projections and deriving instances stay under the private declarations.
No admission, new axiom, unsafe/native proof shortcut, or forbidden out-of-scope dependency in owned source: PASS
Owned file: 1463 lines
New declarations (source order):
  def multColumn
  lemma multColumn_nil
  lemma multColumn_cons
  lemma multColumn_le
  lemma mult_bits_prefix
  lemma mult_column_prefix_cons
  lemma mult_columns_value
  def multCarry
  lemma multCarry_le
  lemma mult_carry_invariant
  lemma mult_digits_unique
  lemma mult_columns_correct
  lemma mult_product_length
  lemma mult_column_row
  lemma mult_column_double
  def multRow
  lemma multRow_cons
  lemma multRow_le_one
  def multRows
  lemma multRows_cons
  lemma multRows_bound
  lemma multRows_column
  lemma mult_canonical_last
  lemma mult_membership
  lemma mult_acceptance
  inductive MultState
  def multPairNext
  def multCopy
  def multARM
  lemma mult_addresses
  def MultRemaining
  lemma mult_remaining_step
  def multOracle
  lemma mult_queries
  lemma mult_preconditions
  abbrev MultGood
  abbrev MultReach
  abbrev MultHalt
  lemma mult_copy
  lemma mult_scan
  lemma mult_contribution
  lemma mult_inner_loop
  lemma mult_row_start
  lemma mult_outer_loop
  lemma mult_return
  lemma mult_finish
  lemma mult_parity
  lemma mult_result_read
  lemma mult_next_column
  lemma mult_columns_run
  def multCanonSource
  def multCanonCopy
  def multCanonNext
  lemma mult_last_bit
  lemma mult_validate_field
  structure MultReady
  lemma mult_ready_frame
  lemma mult_canonical_run
  lemma mult_sub_two
  lemma mult_prepare_run
  lemma mult_bad_decode
  lemma mult_run
```

## Lint (complete output)

```text
WARN  TCSlib/Complexity/SpaceComplexity/Inclusions.lean                     2880 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean           2016 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean                  1463 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean          1208 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/SpaceComplexity/Basic.lean                          191 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean                    493 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    612 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    612 lines; 16 public / 12 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean                  95 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean                 495 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean              246 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Examples.lean                       147 lines; 4 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean                      234 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean                   416 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Inclusions.lean                     2880 lines; 4 public / 64 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean  116 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean           2016 lines; 20 public / 58 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean                  1463 lines; 2 public / 62 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean                  136 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean          822 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean          822 lines; 13 public / 16 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean          1208 lines; 9 public / 57 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean            153 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean                   307 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean                93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean              333 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean                285 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean                551 lines; 30 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean                  226 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean                   176 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Call.lean                  360 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean            495 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean                 438 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean            508 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean               266 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean               358 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean                  455 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean               479 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean                423 lines; 29 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean                   333 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean                 376 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean              445 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean            571 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Program.lean               347 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean                   564 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/NSPACE.lean                         136 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Savitch.lean                        131 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean                   86 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean                  319 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean                      264 lines; 11 public / 2 private declarations

style_lint: 0 FAIL, 4 WARN over 45 files
```

## Before duplication screen (verbatim)

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

## After duplication screen (verbatim)

```text
declarations screened: 370; copy pairs (target reproduces >= half of source): 75; reproduced text: 21,295 chars
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
   Mult.lean::multRows_cons  reproduces  Mult.lean::multRow_cons: 77/95 = 81%
   CounterProgSim.lean::pr_halt  reproduces  CounterProgSim.lean::pr_reach: 836/1033 = 81%
   Mult.lean::multRow_cons  reproduces  Mult.lean::multRows_cons: 77/96 = 80%
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
   Mult.lean::mult_outer_loop  reproduces  Mult.lean::mult_inner_loop: 1591/2947 = 54%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   InputAccess.lean::read_advance  reproduces  InputAccess.lean::read_cleanup: 523/993 = 53%
   FragDec.lean::dec_run  reproduces  Lib.lean::inc_run: 372/707 = 53%
   InputAccess.lean::access_bump  reproduces  InputAccess.lean::access_clear: 157/299 = 53%
   QueryReshape.lean::drop_z_prepare  reproduces  QueryReshape.lean::drop_u_prepare: 442/871 = 51%
   DblLang.lean::dblLang_mem  reproduces  UnaryLogspace.lean::orc_eq: 76/150 = 51%
   Parse.lean::regBack_x  reproduces  Lib.lean::incB_run: 536/1066 = 50%
   Lib.lean::update_bufferTape_cons  reproduces  FragDec.lean::bufferTape_erase_last: 137/273 = 50%
```

## Duplication delta

```text
Before output is byte-identical to the brief's baseline: PASS
declarations screened: 317; copy pairs (target reproduces >= half of source): 72; reproduced text: 19,550 chars
declarations screened: 370; copy pairs (target reproduces >= half of source): 75; reproduced text: 21,295 chars
New pairs:
   Mult.lean::multRows_cons  reproduces  Mult.lean::multRow_cons: 77/95 = 81%
   Mult.lean::multRow_cons  reproduces  Mult.lean::multRows_cons: 77/96 = 80%
   Mult.lean::mult_outer_loop  reproduces  Mult.lean::mult_inner_loop: 1591/2947 = 54%
Removed pairs: none
New cross-file pairs touching Mult.lean: none
New pairs at or above 90 percent: none
new copies: none
```

## Patch and bundle verification

```text
Base: 0bf08187c1a8c24b3733b4300f3c0d00886dc109
Delivery commit: e685dd851be58a61e55e5bc799391d94a01c4579
Working branch: fill/ch34-b7-mult
Only changed tracked path: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean
Working tree clean after local commit: PASS
git diff --check BASE HEAD: PASS
Full source byte equality with committed checkout: PASS
Source git blob: 0610c9ef5189b864a2c36cd4b3d9a49b7f3f479d
Pre-ship source byte equality with maintainer probe: PASS

Format-patch series (one commit):
patches/0001-Prove-logspace-multiplication-with-a-bounded-input-a.patch

Isolated-index patch replay:
git read-tree BASE: PASS
git apply --cached --check PATCH: PASS
git apply --cached PATCH: PASS
Replay tree: 62c34f1fe013aa8b00368fdacff0d97d6d9edb73
Commit tree: 62c34f1fe013aa8b00368fdacff0d97d6d9edb73
Exact replay tree equality: PASS

git bundle verify:
/workspace/scratch/d0021d076cf3/delivery/fill-ch34-b7-mult.bundle is okay
The bundle contains this ref:
e685dd851be58a61e55e5bc799391d94a01c4579 refs/heads/fill/ch34-b7-mult
The bundle requires this ref:
0bf08187c1a8c24b3733b4300f3c0d00886dc109 
The bundle uses this hash algorithm: sha1

git bundle list-heads:
e685dd851be58a61e55e5bc799391d94a01c4579 refs/heads/fill/ch34-b7-mult

```
