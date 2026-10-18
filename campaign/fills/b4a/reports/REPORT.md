# B4a: packaged TQBF configuration codec and CNFs

**Complete: 1/1 target proved.** `Complexity.exists_adjacency_codec_cnf` is proved without `sorryAx` or any proved-modulo dependency. All 119 new explicit declarations are private; none contains `sorry`. The other three TQBF targets are untouched.

## Provenance and scope

| Item | Value |
| --- | --- |
| Repository | https://github.com/Shilun-Allan-Li/tcslib |
| Campaign branch | `complexity/arora-barak-ch3-4` |
| Working branch | `fill/b4a-codec` |
| Base | `1e9361b5fe2022594f5b62d6d48b629d88214794` |
| Required ancestor | `78116c5d5db075c9ce46ecec0b56735d1c600bef` |
| Ancestor check | `git merge-base --is-ancestor 78116c5d5db075c9ce46ecec0b56735d1c600bef HEAD`, exit 0 before editing |
| Delivery commit | `f5449004fc762b3a9b8cf65d704b963ec62da3da` |
| Owned source | `TCSlib/Complexity/ClassPSPACE/TQBF.lean` |
| Changed tracked files | Exactly the owned source |
| Remote writes | None; delivery is by ZIP |

The attached brief was read locally. The branch was created from the campaign branch and never rebased. No parallel-batch source was edited. The base has the brief's exact ten-warning admission set, with no additional landed-fill drift.

## Proof and size accounting

1. `CodecRow` factors its state, head positions, and window symbols through `ConfigCount.coreCode`, carrying the input contents and `outSummary` separately. `CodecBit` gives the required input, one-hot position/state, work-symbol/head, and summary tracks.
2. `configurationCodec` pads the finite coordinates to exactly `C (s+n+1)`. Wrong-length inputs receive a zero word of that same length. Input separation and fixed-input vertex equivalence use the shared bit-injectivity argument and cite the public `ConfigCount.coreCode_inj`.
3. Validity conjoins exactly-one marker constraints, the two-flag symbol/summary ranges, and zero padding. Decoding a valid assignment produces a finite row; extending its cells by blanks realizes a genuine windowed configuration. Both directions of the image characterization are proved.
4. Acceptance is the conjunction of the halt marker and the accepting-summary marker.
5. Adjacency includes carried-input equality and a family indexed by the joint head positions, finite state/scanned-symbol cases, and output coordinates. Each gate has exactly `3k+7` Boolean ports, independent of `n` and `s`. `exists_cnf_boolFun` is applied only to these individual gates. Unmarked symbols are copied, marked symbols are written, marker positions use the native action's shifts, and state and summary are updated. Halt is a silent identity action. Exact integer successor markers reject exterior work heads. Output normalization before stepping cites `NDTM.coreSum_stepWith`, and the observation equivalence proves the required quotient adjacency.
6. `codecCnfCost` counts literal occurrences **plus one per clause**, so empty clauses and delimiters are included. The serialization bound uses the public chapter-2 grammar (`serializeLit`, `serializeClause`, `serialize`), with a final terminator. The single polynomial absorption lemma supplies one constant for every width and formula bound.

Notation: `k = M.k`, `u = s+n+2`, `Aᵥ = codecValidityCoefficient M`, and `Aₜ = codecTransitionCoefficient M`. The ledgers before the final absorption are:

| Formula | Serialized-length bound |
| --- | --- |
| Validity | `(3 Aᵥ + 7) C² u³` |
| Adjacency | `(5 (6 + Aₜ) + 1) C² u^(k+3)` |
| Acceptance | `13 C² u³` |

The guarded position count is bounded by `2^k u^(k+1)`. The transition coefficient includes the fixed state/scanned-symbol case count and per-gate bound `2^(3k+7) (3k+8)`. This is a polynomial gate enumeration, never a whole-row truth table. As in the frozen statement, the package is existence only; a uniform emitter remains outside this target.

## Freeze, status, imports, and file size

`logs/freeze-audit.txt` records a byte-level reconstruction of the original file: remove the new private-helper block, restore the target body, and undo the two permitted status changes; the result equals the base exactly. The target signature is byte-identical. There are no renamed, removed, or re-signed existing declarations, and no public declaration drift.

- **Fill appendix:** the inserted appendix before the private row definitions explains numbering, exact successor markers, fixed gate arity, the quotient bridge, and the size ledgers. The original target sketch is retained.
- **Status edits:** the module's count changes from four remaining phase-P4.3 statements to three; the owned target's `spec, fill pending` tag becomes `proved`.
- **Imports:** unchanged; no TCSlib or Mathlib import was added.
- **File size:** 1,902 lines; 8 public and 119 private explicit declarations, counted on the same basis as the campaign lint. Generated constructor/projection/deriving declarations are excluded from these source counts.
- **Length warning justification:** the brief's ground rules 1 and 8 require all new helpers to remain private in this sole owned file and explicitly impose no cap. A split would violate ownership during this batch. Generic promotion candidates are recorded below for a future shared-file window.

**Escalations: none. Proved-modulo targets: none. New private admissions: none.**

## Requested shared lemmas / promotion candidates

These are proved privately here, as the ownership rule requires; no shared file was changed.

| Candidate family | Possible shared home | Purpose |
| --- | --- | --- |
| `codecCnfCost`, its relabel/append/flatMap lemmas, `codecCnf_numVars`, `codecCnf_serialize` | `Formulas/CNF` / `CNFEncoding` | Reusable clause-and-literal and serialization ledgers, including empty clauses. |
| `codecOneHot`, `codecOneHot_eval`, `codecOneHot_cost` | Formula gadgets | Exactly-one markers and their quadratic cost. |
| `codecWord` and its length/read/equality/padding/reconstruction lemmas | Finite bit-codec utility | Fixed-width encodings without auxiliary variables. |
| `codecLocalCheck` | Formula gadgets | Fixed-arity universality followed by arbitrary wiring, with a common cost bound. |
| `codec_step_blank` | Turing-machine configuration/action utilities | Writes at windowed old heads preserve blank exterior cells. |
| `codec_square_le_pow`, `codec_absorb` | Arithmetic bounds | Absorb width-dependent polynomial coefficients into the package's one constant. |

## Every new declaration

All entries below are private and proved/defined without admissions.

| Declaration | Kind | Role |
| --- | --- | --- |
| `CodecRow` | structure | The finite fields of a windowed configuration, together with its input. |
| `CodecBit` | inductive | One coordinate for each bit in the marker discipline of Claim 4.4(2). |
| `codecBit_card` | theorem | The unpadded track width, with three bits for every work cell. |
| `codecCoefficient` | def | A machine-dependent linear coefficient sufficient for all raw tracks. |
| `codecBit_card_le` | theorem | The raw tracks fit every requested width with coefficient at least this one. |
| `codecRowBits` | def | Marker encoding of a finite row. Blank symbols and the empty summary use `00`; false/true symbols and accept/dead summaries use the two singleton patterns. |
| `codec_symbol_ext` | theorem | Two singleton flags distinguish all three values of an optional bit. |
| `codecRowBits_injective` | theorem | Marker equality recovers every field of a finite row. |
| `codecRowOf` | def | Restriction of a configuration to its finite core code, with input and summary. |
| `codec_core_window` | theorem | Translate the public window predicate into the hypotheses of `coreCode_inj`. |
| `codecRowOf_input_eq` | theorem | Equality of the finite rows recovers the input content. |
| `codecRowOf_eq_iff` | theorem | The finite row identifies exactly the configuration-graph vertex at a fixed input. |
| `codecWord` | def | Pad an arbitrary finite bit assignment to exactly `L` bits (truncate if necessary). The application below always proves that truncation cannot occur. |
| `codecWord_length` | theorem | The padded word has its prescribed length on all arguments. |
| `codecWord_get` | theorem | Reading the coordinate of a finite bit assignment after sufficient padding. |
| `codecWord_eq_iff` | theorem | Sufficiently padded words agree exactly when their underlying bits agree. |
| `configurationCodec` | def | The total configuration codec. Wrong-length inputs receive the all-zero word. |
| `configurationCodec_length` | theorem | Exact length holds even for wrong-length inputs and nonwindowed configurations. |
| `configurationCodec_input_eq` | theorem | The codec separates inputs of the prescribed length. |
| `configurationCodec_eq_iff` | theorem | The padded codec factors through, and separates, the windowed vertex quotient. |
| `codecCnf_eval_flatMap` | theorem | A flattened family conjoins exactly its member formulas. |
| `codecCnf_eval_map` | theorem | A list of clauses conjoins their individual evaluations. |
| `codecOneHot` | def | Exactly one positive marker, expressed by one positive clause and pairwise exclusions. |
| `codecOneHot_eval` | theorem | Pairwise exclusions give precisely a one-hot assignment. |
| `codecBitsValid` | def | Valid marker assignments consist of one-hot heads and state, with the forbidden `11` pattern excluded from each symbol and summary pair. |
| `codecRowBits_valid` | theorem | Every finite row produces a valid marker assignment. |
| `codecBitsValid_iff` | theorem | Every valid marker assignment is the encoding of a finite row. |
| `codecValidity` | def | The validity CNF on unpadded tracks. Input contents are unrestricted. |
| `codecValidity_eval` | theorem | The unpadded validity formula recognizes exactly the finite-row encodings. |
| `codec_posCode` | theorem | The finite position code decodes the designated cell of the window. |
| `codecRow_realize` | theorem | Every finite row is realized by a genuine windowed configuration. |
| `codecWord_padding` | theorem | A padded word's unused suffix is zero. |
| `codecWord_reconstruct` | theorem | A word of length `L` with zero padding is recovered from its finite coordinates. |
| `codecPadding` | def | The padding clauses fix every unused coordinate to false. |
| `codecPadding_eval` | theorem | Evaluation of the padding clauses states exactly that the unused suffix is zero. |
| `configurationValidity` | def | Number the finite validity formula inside the prescribed width and add zero padding. |
| `configurationValidity_eval` | theorem | Validity recognizes exactly the padded codes of windowed configurations. |
| `codecAcceptance` | def | Acceptance reads the halt marker and the accepting summary marker. |
| `codecAcceptance_eval` | theorem | The acceptance formula has the required meaning on every finite row. |
| `configurationAcceptance` | def | Number the two acceptance tests at their actual code positions. |
| `configurationAcceptance_eval` | theorem | The numbered acceptance CNF recognizes halted configurations with accepting summary. |
| `codecCnfCost` | def | Clause count plus literal occurrences; empty clauses still cost one unit. |
| `codecCnfCost_relabel` | theorem | Renumbering variables preserves the clause-and-literal cost. |
| `codecCnfCost_append` | theorem | Conjoining CNFs adds their clause-and-literal costs. |
| `codecCnfCost_flatMap_le` | theorem | A family of bounded-cost checks has at most its length times the common cost. |
| `codecOneHot_cost` | theorem | The exactly-one constraint has a quadratic cost, including its positive clause. |
| `codecCnf_numVars` | theorem | A variable bound for an explicitly bounded relabeling of a finite formula. |
| `codecCnf_serialize` | theorem | The chapter-2 grammar bounds serialization by the cost times the index bound. |
| `codecValidityCoefficient` | def | Explicit polynomial coefficient for the unpadded validity clauses. |
| `codecValidity_cost_raw` | theorem | Counting one-hot exclusions and trit ranges gives the raw validity cost. |
| `codecValidity_cost` | theorem | The raw validity cost is bounded quadratically in `s+n+2`. |
| `codecPadding_cost` | theorem | The padding contributes at most two cost units per code position. |
| `configurationValidity_literals` | theorem | All validity literals lie strictly inside the prescribed code width. |
| `configurationValidity_numVars` | theorem | The validity CNF's variable count is inside the code width. |
| `configurationValidity_size_raw` | theorem | A preliminary serialized-size ledger, before choosing the common theorem constant. |
| `configurationAcceptance_bounds` | theorem | The acceptance CNF has two unit clauses and all its indices are inside the code. |
| `codec_size_normalize` | theorem | Normalize the validity serialization ledger to one cubic polynomial. |
| `configurationValidity_size` | theorem | Validity has a polynomial serialized-size bound uniform in the width coefficient. |
| `configurationAcceptance_size` | theorem | Acceptance also fits a cubic ledger, uniformly over all sufficient code widths. |
| `codecLocalCheck` | theorem | A fixed-arity Boolean check becomes a CNF of bounded cost after arbitrary wiring. This applies the chapter-2 universality theorem to a single gate, never to a row. |
| `CodecPositions` | abbrev | Positions jointly guarded by one local transition check. |
| `codecPositions_card_le` | theorem | The joint head-position enumeration has polynomial size for a fixed machine. |
| `codecPairBits` | def | Source and target bit tracks for a pair of finite rows. |
| `codecPairWire` | def | Place the target coordinates after one full padded source block. |
| `codecPairWire_lt` | theorem | Every pair coordinate lies inside the concatenation of the two code blocks. |
| `configurationCodec_pair_get` | theorem | Numbered pair coordinates read exactly the source or target finite-row bit. |
| `codecInputEquality` | def | Two clauses per input bit require equality of the carried input contents. |
| `codecInputEquality_eval` | theorem | The input-equality conjunct compares exactly the input-content fields. |
| `codecInputEquality_cost` | theorem | Input equality costs six units per input position: two clauses of width two. |
| `configurationInputEquality` | def | Number the cross-input rejection conjunct in the two padded code blocks. |
| `configurationInputEquality_reject` | theorem | Distinct carried inputs fail the equality conjunct, independently of transition checks. |
| `configurationInputEquality_bounds` | theorem | The cross-input equality conjunct has bounded indices and polynomial serialization. |
| `configurationCodec_step_congr` | theorem | Equal windowed codes have equal successor vertices, through the public quotient bridge. This is the deterministic instance of `NDTM.coreSum_stepWith`, not a second step proof. |
| `codec_square_le_pow` | theorem | Beyond four, the exponential pays for a quadratic coefficient. |
| `codec_absorb` | theorem | One constant can simultaneously dominate the width and the polynomial ledgers. |
| `codec_posCode_eq_iff` | theorem | Exact window markers recover integer positions without clamping. |
| `codecObserve` | def | Observe the row coordinates using exact integer head markers. An exterior head has no true marker; this prevents clamping from admitting an overflowing step. |
| `codecObserve_eq` | theorem | On windowed configurations, exact observations agree with the padded codec's row. |
| `codecObserve_congr` | theorem | Exact observations depend only on the public configuration-graph vertex. |
| `codec_step_blank` | theorem | Applying a transition cannot write outside a window containing its old heads. |
| `codecObserve_step_iff` | theorem | Equality of exact successor observations with a valid target is adjacency. |
| `codecSummaryWord` | def | A canonical representative of each of the three output summaries. |
| `codecSummaryWord_summary` | theorem | The chosen representative has the prescribed output summary. |
| `codecObserve_step_normalize` | theorem | Output histories may be normalized before taking a step, through the public `coreSum_stepWith` bridge; the exact observed successor bits are unchanged. |
| `CodecCase` | abbrev | The finite transition-table cases: control, scanned input, and scanned work symbols. |
| `codecAction` | def | Include a silent identity action for the halted case. |
| `codecAction_apply` | theorem | The case action computes the native step, including halted self-edges. |
| `CodecPort` | inductive | The constant number of Boolean ports read by a single guarded update gate. |
| `codecPort_card` | theorem | Gate arity is independent of the input length and window radius. |
| `codecReadSymbol` | def | A two-flag decoder for optional work symbols, with an arbitrary value on `11`. |
| `codecReadSymbol_flags` | theorem | The symbol decoder recovers every legal two-flag encoding. |
| `codecReadSummary` | def | Decode the two summary flags; `11` is irrelevant on encoded configurations. |
| `codecReadSummary_flags` | theorem | Summary decoding recovers the three canonical flag patterns. |
| `codecInputWire` | def | Wire one input-symbol port; boundary cases ignore the arbitrary fallback wire. |
| `codecInputRead` | def | The physical input boundaries read blank; interior positions read the wired bit. |
| `codecGateWire` | def | Wire the guard, scanned symbols, summary, and one old/new bit pair. |
| `codecGuard` | def | A joint position/table guard. All quantification is over the machine's fixed tapes. |
| `codecInputRead_wire` | theorem | Under the input-position guard, the input-symbol port reads the actual input. |
| `codecGuard_rows` | theorem | On encoded rows, the gate guard tests exactly the selected positions and reads. |
| `codecGuard_spec` | theorem | Native meaning of a true guard on a windowed configuration. |
| `codecExpected` | def | One output bit of the selected action: copy unmarked cells, write at old heads, shift markers, rewrite the state, and update the output summary. |
| `codecGate` | def | The guarded single-bit predicate compiled by per-gate Boolean universality. |
| `codecExpected_apply` | theorem | Each expected bit is the exact bit of the action applied to the canonical output representative; only the guard's positions and a constant number of bits enter. |
| `codecExpected_step` | theorem | A true transition guard makes its expected bit the actual successor bit. Output normalization is justified by `NDTM.coreSum_stepWith`. |
| `codecGate_cnf` | theorem | Compile one finite-port gate, retaining a machine-only cost bound. |
| `codecGateCNF` | def | Choose the per-gate CNF from the proved constant-arity universality bound. |
| `codecGateCNF_spec` | theorem | The chosen gate formula has exactly its local semantics and machine-only cost. |
| `CodecGateIndex` | abbrev | Enumerate the guarded positions, finite table cases, and updated coordinates. |
| `codecTransitionCNF` | def | Conjoin one constant-arity gate for each guarded coordinate update. |
| `codecTransitionCNF_eval` | theorem | The transition conjunction enforces exactly all of its local update gates. |
| `codecTransitionCNF_step_iff` | theorem | The local conjunction is equivalent to adjacency on windowed same-input pairs. |
| `codecTransitionCNF_cost` | theorem | Counting local gates multiplies positions, fixed machine cases, coordinates, and the constant per-gate cost; no row truth table appears. |
| `configurationAdjacency` | def | The numbered adjacency formula includes the separate carried-input equality conjunct. |
| `configurationAdjacency_eval` | theorem | The numbered adjacency formula has the required quotient-step interpretation. |
| `configurationAdjacency_reject` | theorem | Different carried inputs fail the adjacency formula's equality conjunct. |
| `codecTransitionCoefficient` | def | Machine-only coefficient for the joint transition enumeration. |
| `codecTransitionCNF_cost_poly` | theorem | The transition gates have polynomial cost, of degree `k+2` before serialization. |
| `codecAdjacency_cost` | theorem | Input equality and transition gates share the degree-`k+2` cost ledger. |
| `configurationAdjacency_bounds` | theorem | Adjacency uses only the two code blocks and has a polynomial serialized length. |

## Verification

Lean is pinned to `leanprover/lean4:v4.25.0`; mathlib is pinned to `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The existing cache at that exact pin was reused. Every Lean check used the unchanged `scripts/lean_check_tree.sh`, including scratch elaboration, the bootstrap, the final 73-module sweep, the probe, and axiom printing. `lake build` was never run.

The container's virtual PID made the toolchain launcher unable to find its executable. Verification used a narrowly scoped `readlink` shim redirecting only the process's own `/proc/<pid>/exe` lookup to `/proc/self/exe`, plus a direct-toolchain wrapper with `-j1`. This changes executable discovery, not Lean source or proof checking. The shim source and wrapper are included under `verification/`; they are not repository changes. The copied scratch checker and repository checker have the same SHA256, recorded in `logs/freeze-audit.txt`.

Bootstrap: all 73 modules passed with zero errors and exactly the ten baseline admitted declarations:

```text
# base sorry-warning set at the issue tree (the campaign tip 0bf08187) over briefs/orders/b4a-fill.txt: one entry per declaration whose comment-stripped text contains `sorry` (Lean warns once per such declaration)
SpaceComplexity/Constructible: 2: spaceConstructible_logSpace, spaceConstructible_linear
SpaceComplexity/ConfigGraph: 3: NSPACE_subset_exp_dtime, NL_subset_P, polyTimeReducible_of_mem_NL
TuringMachine/Build/CfgRecord: 1: exists_recordStepTM
ClassPSPACE/TQBF: 4: exists_adjacency_codec_cnf, TQBF_mem_PSPACE, TQBF_PSPACEHard, TQBF_PSPACEComplete
TOTAL 10
```

Final results:

```text
Final sweep: PASS
Command: while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < briefs/orders/b4a-fill.txt
Checker exit: 0
Modules: 73/73, in the brief order
Errors: 0
Sorry warnings: 9, exactly the baseline minus exists_adjacency_codec_cnf
Owned file: 3 sorry warnings, all three out-of-scope TQBF summit declarations
New private sorry declarations: 0
Public target axioms: propext, Classical.choice, Quot.sound
Pre-ship probe: checker exit 0, zero errors
Lint: 0 FAIL, 1 WARN (file length, justified in REPORT.md)
Checked commit: f5449004fc762b3a9b8cf65d704b963ec62da3da
Source SHA256: 1fb912da948e7e4cfa04fed07a58d3deb3bb6f3bd0dccaf75a650b7505c7a8c3
```

The remaining nine warnings are exactly `spaceConstructible_logSpace`, `spaceConstructible_linear`, `NSPACE_subset_exp_dtime`, `NL_subset_P`, `polyTimeReducible_of_mem_NL`, `exists_recordStepTM`, `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, and `TQBF_PSPACEComplete`. They are all out of scope and unchanged.

The maintainer's pre-ship probe was copied byte-for-byte from `audits/evidence/b4a/TQBFCodecProbe.lean.txt` into a scratch Lean module and checked through the same script. It passed with zero errors; see `logs/probe.log` and `verification/TQBFCodecProbe.lean`.

Target axiom print:

```text
'Complexity.exists_adjacency_codec_cnf' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lint:

```text
WARN  TCSlib/Complexity/ClassPSPACE/TQBF.lean   1902 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/ClassPSPACE/Games.lean  175 lines; 4 public / 7 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBF.lean   1902 lines; 8 public / 119 private declarations

style_lint: 0 FAIL, 1 WARN over 2 files
```

Final sweep tail (the full log is included):

```text
Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:10950:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
CHECK TCSlib/Complexity/TuringMachine/Build/Scan
TCSlib/Complexity/TuringMachine/Build/Scan.lean:108:68: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Scan.lean:210:67: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Scan.lean:252:74: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Scan.lean:257:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Scan.lean:364:78: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Scan.lean:450:77: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Scan.lean:467:66: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Scan.lean:521:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Scan.lean:660:46: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
CHECK TCSlib/Complexity/TuringMachine/SymbolLift
CHECK TCSlib/Complexity/TuringMachine/Build/CounterLoop
CHECK TCSlib/Complexity/TuringMachine/Build/VirtualInput
CHECK TCSlib/Complexity/SpaceComplexity/Inclusions
CHECK TCSlib/Complexity/TuringMachine/Build/InputCall
CHECK TCSlib/Complexity/TuringMachine/Build/CfgRecord
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:2908:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassPSPACE/TQBF
TCSlib/Complexity/ClassPSPACE/TQBF.lean:1839:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:1891:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:1899:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassPSPACE/Games
CHECK TCSlib/Complexity/ClassPSPACE
```

## Duplication ledger

**new copies: none**. The exact twelve-file screen from the brief was run before editing and after the completed proof. Baseline: 758 screened declarations, 358 pairs, 75,613 reproduced characters. Final: 853 screened declarations, 363 pairs, 76,157 reproduced characters. Existing pairs are unchanged. There are **no new cross-file pairs involving the owned file**, and no new in-file pair reaches 90%.

All five new in-file pairs, totaling 544 measured reproduced characters, are disclosed below. They reuse projection or theorem-instantiation text; the underlying shared arguments are already factored. There is no newly copied proof body under the brief's threshold, hence no new copied-material debt.

| Target reproduces | Source | Measurement | Justification |
| --- | --- | --- | --- |
| `codecCnf_numVars` | `codecCnfCost_relabel` | 61/82 (74%) | Both simplify relabel/map structure. The index-bound proof and cost-preservation proof establish different facts; neither repeats the other argument. |
| `configurationValidity_size_raw` | `configurationValidity_numVars` | 68/96 (71%) | Both instantiate the shared literal-bound lemma, once for serialization and once for numVars. Their common premise is already factored. |
| `configurationAdjacency_bounds` | `configurationInputEquality_bounds` | 169/297 (57%) | Both apply the shared pair-wire bound and generic CNF ledgers. The former bounds the full transition family, the latter only the input-equality conjunct. |
| `configurationCodec_input_eq` | `configurationCodec_eq_iff` | 81/146 (55%) | Both remove padding through codecWord_eq_iff and use the single bit-injectivity proof; the conclusions recover different components. |
| `codecRowOf_eq_iff` | `codecObserve_congr` | 165/326 (51%) | Shared text projects the public coreSum fields. The first uses coreCode_inj to recover a windowed core; the second transports exact observations forward. |

Both complete screen outputs follow, as required.

### Before

```text
declarations screened: 758; copy pairs (target reproduces >= half of source): 358; reproduced text: 75,613 chars
   SAT.lean::sat_bridge_bound  reproduces  Hardness.lean::clA5_bridge_bound: 452/452 = 100%
   Hardness.lean::clA5_bridge_bound  reproduces  SAT.lean::sat_bridge_bound: 452/452 = 100%
   SAT.lean::sat_call_first_halt  reproduces  Hardness.lean::clA5_call_first_halt: 330/330 = 100%
   Hardness.lean::clA5_call_first_halt  reproduces  SAT.lean::sat_call_first_halt: 330/330 = 100%
   SAT.lean::SatClean  reproduces  Hardness.lean::CLA5Clean: 257/257 = 100%
   Hardness.lean::CLA5Clean  reproduces  SAT.lean::SatClean: 257/257 = 100%
   SAT.lean::satStopTM  reproduces  Hardness.lean::clA5StopTM: 180/180 = 100%
   Hardness.lean::clA5StopTM  reproduces  SAT.lean::satStopTM: 180/180 = 100%
   SAT.lean::sat_live_prefix  reproduces  Hardness.lean::clA5_live_prefix: 152/152 = 100%
   Hardness.lean::clA5_live_prefix  reproduces  SAT.lean::sat_live_prefix: 152/152 = 100%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clLoad_idle: 147/147 = 100%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clInput_idle: 142/142 = 100%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clWipe_idle: 142/142 = 100%
   SAT.lean::satPadCfg  reproduces  Hardness.lean::clA5PadCfg: 134/134 = 100%
   Hardness.lean::clA5PadCfg  reproduces  SAT.lean::satPadCfg: 134/134 = 100%
   SAT.lean::sat_guard_add  reproduces  Hardness.lean::clA5_guard_add: 127/127 = 100%
   SAT.lean::satMapTM  reproduces  Hardness.lean::clA5MapTM: 127/127 = 100%
   Hardness.lean::clA5_guard_add  reproduces  SAT.lean::sat_guard_add: 127/127 = 100%
   Hardness.lean::clA5MapTM  reproduces  SAT.lean::satMapTM: 127/127 = 100%
   SAT.lean::satPadAction  reproduces  Hardness.lean::clA5PadAction: 84/84 = 100%
   Hardness.lean::clA5PadAction  reproduces  SAT.lean::satPadAction: 84/84 = 100%
   Hardness.lean::clWipeCfg  reproduces  Hardness.lean::clReadCfg: 72/72 = 100%
   Hardness.lean::clReadCfg  reproduces  Hardness.lean::clWipeCfg: 72/72 = 100%
   SAT.lean::satStopCfg  reproduces  Hardness.lean::clA5StopCfg: 64/64 = 100%
   Hardness.lean::clA5StopCfg  reproduces  SAT.lean::satStopCfg: 64/64 = 100%
   Hardness.lean::clA5Clean_install  reproduces  SAT.lean::satClean_install: 614/623 = 99%
   Hardness.lean::clA5Clean_emit  reproduces  SAT.lean::satClean_emit: 595/604 = 99%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clOutput_compute: 1751/1778 = 98%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clOutputAt_compute: 1751/1782 = 98%
   SAT.lean::satClean_install  reproduces  Hardness.lean::clA5Clean_install: 614/626 = 98%
   SAT.lean::satClean_emit  reproduces  Hardness.lean::clA5Clean_emit: 595/607 = 98%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clRow_idle: 143/146 = 98%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clRow_idle: 143/146 = 98%
   Hardness.lean::clCount_size_budget  reproduces  Hardness.lean::clRecord_size_budget: 305/312 = 98%
   Hardness.lean::clA5Host_clean  reproduces  SAT.lean::satHost_clean: 130/133 = 98%
   Hardness.lean::clA5Clean_install  reproduces  Hardness.lean::clA5Clean_emit: 592/607 = 98%
   SAT.lean::satClean_install  reproduces  SAT.lean::satClean_emit: 589/604 = 98%
   Hardness.lean::clA5PadTM  reproduces  SAT.lean::satPadTM: 117/120 = 98%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clLoad_idle: 143/147 = 97%
   SAT.lean::satHost_clean  reproduces  Hardness.lean::clA5Host_clean: 130/134 = 97%
   Hardness.lean::clA5_pt_eq  reproduces  SAT.lean::sat_pt_eq: 186/192 = 97%
   SAT.lean::satRed_maxFormula  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_maxClause  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_counterBack  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satPair_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clReplay_back  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clRead_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clInput_backward  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clCopy_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clCmp_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satPadTM  reproduces  Hardness.lean::clA5PadTM: 117/121 = 97%
   Hardness.lean::clMatch_tick  reproduces  Hardness.lean::clMatch_stop: 288/298 = 97%
   Hardness.lean::clRecord_size_budget  reproduces  Hardness.lean::clCount_size_budget: 305/316 = 97%
   Hardness.lean::clA5Map_run  reproduces  SAT.lean::satMap_run: 878/911 = 96%
   Hardness.lean::clA5MapWord  reproduces  SAT.lean::satMapWord: 79/82 = 96%
   Hardness.lean::clA5_pt_head  reproduces  SAT.lean::sat_pt_head: 382/397 = 96%
   Hardness.lean::clA5_pt_tail  reproduces  SAT.lean::sat_pt_tail: 380/395 = 96%
   Hardness.lean::clA5_pt_head  reproduces  Hardness.lean::clA5_pt_tail: 384/400 = 96%
   SAT.lean::sat_pt_head  reproduces  SAT.lean::sat_pt_tail: 379/395 = 96%
   SAT.lean::sat_pt_eq  reproduces  Hardness.lean::clA5_pt_eq: 186/194 = 96%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clWipe_idle: 136/142 = 96%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clInput_idle: 136/142 = 96%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clWipe_idle: 136/142 = 96%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clInput_idle: 136/142 = 96%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clWipe_idle: 136/142 = 96%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clInput_idle: 136/142 = 96%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clWipe_idle: 136/142 = 96%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clInput_idle: 136/142 = 96%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clA5_pt_tail  reproduces  Hardness.lean::clA5_pt_head: 384/402 = 96%
   SAT.lean::sat_pt_tail  reproduces  SAT.lean::sat_pt_head: 379/397 = 95%
   SAT.lean::satMap_run  reproduces  Hardness.lean::clA5Map_run: 878/920 = 95%
   SAT.lean::satDrop_skip  reproduces  SAT.lean::satRed_one: 60/63 = 95%
   SAT.lean::satMapWord  reproduces  Hardness.lean::clA5MapWord: 79/83 = 95%
   SAT.lean::sat_pt_head  reproduces  Hardness.lean::clA5_pt_head: 382/402 = 95%
   SAT.lean::sat_pt_tail  reproduces  Hardness.lean::clA5_pt_tail: 380/400 = 95%
   Hardness.lean::clReplay_run  reproduces  Hardness.lean::clReplay_from: 398/419 = 95%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clFresh_idle: 145/153 = 95%
   Hardness.lean::clA5Clean_emit  reproduces  Hardness.lean::clA5Clean_install: 592/626 = 95%
   SAT.lean::satClean_emit  reproduces  SAT.lean::satClean_install: 589/623 = 95%
   SAT.lean::satVerdict_true_poly  reproduces  SAT.lean::satVerdict_false_poly: 378/400 = 94%
   Hardness.lean::clRec_track_inactive  reproduces  Hardness.lean::clRec_row_inactive: 177/188 = 94%
   Hardness.lean::clA5Stop_clean  reproduces  SAT.lean::satStop_clean: 754/801 = 94%
   Hardness.lean::clA5Map_poly  reproduces  SAT.lean::satMap_poly: 300/321 = 93%
   Hardness.lean::clA5Pad_run  reproduces  SAT.lean::satPad_run: 406/435 = 93%
   SAT.lean::satStop_clean  reproduces  Hardness.lean::clA5Stop_clean: 754/809 = 93%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clCmp_idle: 137/147 = 93%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clCmp_idle: 137/147 = 93%
   Hardness.lean::clA5Host_seam  reproduces  SAT.lean::satHost_seam: 163/175 = 93%
   SAT.lean::satHost_seam  reproduces  Hardness.lean::clA5Host_seam: 163/176 = 93%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clCmp_idle: 136/147 = 93%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clCmp_idle: 136/147 = 93%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clCmp_idle: 136/147 = 93%
   SAT.lean::satMap_poly  reproduces  Hardness.lean::clA5Map_poly: 300/325 = 92%
   SAT.lean::satPad_run  reproduces  Hardness.lean::clA5Pad_run: 406/441 = 92%
   Hardness.lean::clA5Clean_stop  reproduces  SAT.lean::satClean_stop: 336/365 = 92%
   Hardness.lean::clA5StoredRound_native  reproduces  Hardness.lean::clA5Sizes_native: 196/214 = 92%
   Hardness.lean::clA5Clean_install  reproduces  SAT.lean::satClean_emit: 552/604 = 91%
   SAT.lean::satClean_stop  reproduces  Hardness.lean::clA5Clean_stop: 336/369 = 91%
   SAT.lean::satClean_install  reproduces  Hardness.lean::clA5Clean_emit: 552/607 = 91%
   Hardness.lean::clRowCfg  reproduces  Hardness.lean::clLoadCfg: 116/128 = 91%
   SAT.lean::satPairCfg  reproduces  SAT.lean::satEvalCfg: 131/146 = 90%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clFresh_idle: 137/153 = 90%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clFresh_idle: 136/153 = 89%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clFresh_idle: 136/153 = 89%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clFresh_idle: 136/153 = 89%
   Hardness.lean::clA5Clean_emit  reproduces  SAT.lean::satClean_install: 552/623 = 89%
   SAT.lean::satEvalCfg  reproduces  SAT.lean::satPairCfg: 131/148 = 89%
   Hardness.lean::clMatch_stop  reproduces  Hardness.lean::clMatch_tick: 288/326 = 88%
   Hardness.lean::clReplay_from  reproduces  Hardness.lean::clReplay_run: 398/451 = 88%
   SAT.lean::satClean_emit  reproduces  Hardness.lean::clA5Clean_install: 552/626 = 88%
   Hardness.lean::clA5Pad_seam  reproduces  SAT.lean::satPad_seam: 208/239 = 87%
   SAT.lean::satPad_seam  reproduces  Hardness.lean::clA5Pad_seam: 208/242 = 86%
   Hardness.lean::clA5_pt_head  reproduces  SAT.lean::sat_pt_tail: 339/395 = 86%
   Hardness.lean::clA5Host_call  reproduces  SAT.lean::satHost_call: 777/909 = 85%
   Hardness.lean::clA5_pt_tail  reproduces  SAT.lean::sat_pt_head: 339/397 = 85%
   Hardness.lean::clA5Stop_step  reproduces  SAT.lean::satStop_step: 175/205 = 85%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clWipe_idle: 121/142 = 85%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clInput_idle: 121/142 = 85%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clCopy_idle: 121/142 = 85%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clCmp_idle: 125/147 = 85%
   SAT.lean::sat_pt_head  reproduces  Hardness.lean::clA5_pt_tail: 339/400 = 85%
   SAT.lean::satStop_step  reproduces  Hardness.lean::clA5Stop_step: 175/207 = 85%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clCmp_idle: 124/147 = 84%
   SAT.lean::sat_pt_tail  reproduces  Hardness.lean::clA5_pt_head: 339/402 = 84%
   SAT.lean::satHost_call  reproduces  Hardness.lean::clA5Host_call: 777/926 = 84%
   Hardness.lean::clNative_pair  reproduces  SAT.lean::sat_pt_fields: 78/93 = 84%
   Hardness.lean::clRec_copy  reproduces  Hardness.lean::clTrack_dispatch: 88/105 = 84%
   Hardness.lean::clRec_advance  reproduces  Hardness.lean::clTrack_dispatch: 88/105 = 84%
   Hardness.lean::clRec_row_frame  reproduces  Hardness.lean::clRec_row_inactive: 156/188 = 83%
   Hardness.lean::clNative_append  reproduces  SAT.lean::sat_pt_append: 107/129 = 83%
   Hardness.lean::clLoadCfg  reproduces  Hardness.lean::clRowCfg: 116/140 = 83%
   SAT.lean::satDrop_rewind  reproduces  SAT.lean::satDrop_dispatch: 256/311 = 82%
   Hardness.lean::clRec_prepared  reproduces  Hardness.lean::clRepeat_initial: 100/122 = 82%
   Hardness.lean::clRec_track_frame  reproduces  Hardness.lean::clRec_row_inactive: 154/188 = 82%
   Hardness.lean::clCmp_rewind  reproduces  Hardness.lean::clCmp_forward_step: 185/226 = 82%
   Hardness.lean::clRecords_native  reproduces  Hardness.lean::clTrajectory_native: 157/193 = 81%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clWipe_idle: 115/142 = 81%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clInput_idle: 115/142 = 81%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clCopy_idle: 115/142 = 81%
   SAT.lean::satReq_round  reproduces  SAT.lean::satReq_fields: 93/115 = 81%
   Hardness.lean::clRead_separator  reproduces  Hardness.lean::clRead_pair: 953/1182 = 81%
   SAT.lean::sat_pt_append  reproduces  Hardness.lean::clNative_append: 107/133 = 80%
   Hardness.lean::clRead_pair  reproduces  Hardness.lean::clRead_separator: 953/1186 = 80%
   Hardness.lean::clRec_tick  reproduces  Hardness.lean::clRec_stop: 248/310 = 80%
   CNFEncoding.lean::parseClauses_bounds  reproduces  CNFEncoding.lean::parseClause_bounds: 731/920 = 79%
   SAT.lean::satMax_prefix  reproduces  SAT.lean::satMax_finish: 428/540 = 79%
   Hardness.lean::clA5StoredRound_native  reproduces  Hardness.lean::clA5Cursor_native: 103/130 = 79%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clFresh_idle: 121/153 = 79%
   SAT.lean::satSplitClause_width  reproduces  SAT.lean::satSplitClause_vars: 67/85 = 79%
   Hardness.lean::clA5Fuel  reproduces  Hardness.lean::clA5Cursor_install: 61/78 = 78%
   Hardness.lean::clA5DecodeStep_state  reproduces  Hardness.lean::clVisitStep_state: 93/119 = 78%
   SAT.lean::satPairAction_apply  reproduces  SAT.lean::satEvalAction_apply: 121/157 = 77%
   SAT.lean::satEvalAction_apply  reproduces  SAT.lean::satPairAction_apply: 121/157 = 77%
   Hardness.lean::clRecordOutputTM  reproduces  Hardness.lean::clCountOutputTM: 84/109 = 77%
   Hardness.lean::clLoadTM  reproduces  Hardness.lean::clRowTM: 223/293 = 76%
   Hardness.lean::clA5Field_native  reproduces  Hardness.lean::clA5Decode_orbit: 70/92 = 76%
   Hardness.lean::clBank_run  reproduces  Hardness.lean::clCount_idle_run: 69/91 = 76%
   SAT.lean::sat_parseClauses_repr  reproduces  SAT.lean::sat_parseClause_repr: 400/529 = 76%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clFresh_idle: 115/153 = 75%
   SAT.lean::satReqStep_poly  reproduces  SAT.lean::satReqEmit_poly: 333/446 = 75%
   Hardness.lean::clLeft_until  reproduces  Hardness.lean::clCmp_forward: 105/141 = 74%
   Hardness.lean::clA5Next_pack  reproduces  Hardness.lean::clVisitStep_state: 88/119 = 74%
   CNFEncoding.lean::parseClause_bounds  reproduces  CNFEncoding.lean::parseClauses_bounds: 731/992 = 74%
   Hardness.lean::clCount_idle_run  reproduces  Hardness.lean::clBank_run: 69/94 = 73%
   Hardness.lean::clCount_idle  reproduces  Hardness.lean::clTrack_dispatch: 77/105 = 73%
   Hardness.lean::clInput_forward  reproduces  Hardness.lean::clCmp_forward: 103/141 = 73%
   Hardness.lean::clCmp_finish_scan  reproduces  Hardness.lean::clCmp_forward_step: 165/226 = 73%
   CNFEncoding.lean::numVars_le_of_literal_bounds  reproduces  CNF.lean::foldr_max_le_of_forall: 97/133 = 73%
   Hardness.lean::clReplay_forward  reproduces  Hardness.lean::clReplay_back: 514/705 = 73%
   SAT.lean::sat_parseClause_repr  reproduces  SAT.lean::sat_parseClauses_repr: 400/549 = 73%
   Hardness.lean::clA5Iter_shrinking  reproduces  Hardness.lean::clA5Decode_orbit: 67/92 = 73%
   SAT.lean::satSyntaxSuffix_cons  reproduces  SAT.lean::sat_clause_measure: 79/109 = 72%
   Hardness.lean::clMatchCfg  reproduces  Hardness.lean::clQueryWords: 91/128 = 71%
   Hardness.lean::clTrajectory_native  reproduces  Hardness.lean::clFinalCount_native: 137/193 = 71%
   Hardness.lean::clFinalCount_native  reproduces  Hardness.lean::clTrajectory_native: 137/193 = 71%
   Hardness.lean::clA5Data_exact  reproduces  Hardness.lean::clA5Stored_exact: 159/224 = 71%
   Hardness.lean::clHeaderLayout  reproduces  Hardness.lean::clRecWords: 75/107 = 70%
   SAT.lean::satReqStep  reproduces  SAT.lean::satReqEmit: 159/229 = 69%
   MeyerTableau.lean::wstep_some_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 79/114 = 69%
   Hardness.lean::clA5HostTM  reproduces  SAT.lean::satHostTM: 146/211 = 69%
   SAT.lean::satSplitClause_vars  reproduces  SAT.lean::satSplitClause_width: 67/97 = 69%
   Hardness.lean::clRead_run  reproduces  Hardness.lean::clCopy_run: 195/283 = 69%
   Hardness.lean::clRepeat_frame  reproduces  Hardness.lean::clRepeat_initial: 84/122 = 69%
   Hardness.lean::clCountOutput_quadratic  reproduces  Hardness.lean::clRecordOutput_quadratic: 509/741 = 69%
   Hardness.lean::clRec_track_frame  reproduces  Hardness.lean::clRec_track_inactive: 194/283 = 69%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clRow_idle: 100/146 = 68%
   Hardness.lean::clCountInc_bits  reproduces  Hardness.lean::clNum_bits: 89/130 = 68%
   Hardness.lean::clA5Pad_apply  reproduces  SAT.lean::satPad_apply: 117/171 = 68%
   Hardness.lean::clRowTM  reproduces  Hardness.lean::clLoadTM: 223/328 = 68%
   SAT.lean::satHostTM  reproduces  Hardness.lean::clA5HostTM: 146/216 = 68%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clLoad_idle: 99/147 = 67%
   Hardness.lean::clPrepared_run  reproduces  Hardness.lean::clRepeat_initial: 82/122 = 67%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clRepeat_initial: 82/122 = 67%
   SAT.lean::satPad_apply  reproduces  Hardness.lean::clA5Pad_apply: 117/175 = 67%
   CNFEncoding.lean::parseClauses  reproduces  CNFEncoding.lean::parseClause: 117/175 = 67%
   Hardness.lean::clCopy_pair  reproduces  Hardness.lean::clCopy_separator: 443/668 = 66%
   SAT.lean::satEval_double  reproduces  SAT.lean::satEval_skip: 137/207 = 66%
   Hardness.lean::clRepeat_initial  reproduces  Hardness.lean::clRepeat_frame: 84/128 = 66%
   Hardness.lean::clPrepared_run  reproduces  Hardness.lean::clRepeat_frame: 84/128 = 66%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clRepeat_frame: 84/128 = 66%
   Hardness.lean::clCopy_rewind  reproduces  Hardness.lean::clRead_rewind: 524/803 = 65%
   SAT.lean::satMax_finish  reproduces  SAT.lean::satMax_prefix: 428/656 = 65%
   Hardness.lean::clHeaderLayout_native  reproduces  Hardness.lean::clRecordWords_native: 553/849 = 65%
   Hardness.lean::clRecordCfg  reproduces  Hardness.lean::clPreparedCfg: 91/140 = 65%
   SAT.lean::sat_pt_append  reproduces  SAT.lean::sat_pt_pair: 65/100 = 65%
   SAT.lean::satStream_parseLit  reproduces  SAT.lean::satWidth_index: 62/96 = 65%
   Hardness.lean::clA5Fuel  reproduces  SAT.lean::sat_pt_fields: 60/93 = 65%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clPrepare_idle: 147/228 = 64%
   Hardness.lean::clCmp_forward_step  reproduces  Hardness.lean::clCmp_finish_scan: 165/256 = 64%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clWipe_idle: 91/142 = 64%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clInput_idle: 91/142 = 64%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clCopy_idle: 91/142 = 64%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clWipe_idle: 91/142 = 64%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clInput_idle: 91/142 = 64%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clCopy_idle: 91/142 = 64%
   Hardness.lean::clLastCode_native  reproduces  Hardness.lean::clNative_append: 85/133 = 64%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clPrepare_idle: 145/228 = 64%
   SAT.lean::satAppend_copy  reproduces  SAT.lean::satAppend_seek: 528/832 = 63%
   Hardness.lean::clRec_row_frame  reproduces  Hardness.lean::clRec_track_inactive: 179/283 = 63%
   Hardness.lean::clRecordWords_native  reproduces  Hardness.lean::clRepeatArgument_native: 271/430 = 63%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clPrepare_idle: 143/228 = 63%
   SAT.lean::satEval_start  reproduces  SAT.lean::satPair_start: 1086/1733 = 63%
   Hardness.lean::clRec_row_inactive  reproduces  Hardness.lean::clRec_track_inactive: 177/283 = 63%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   CNFEncoding.lean::parseClause  reproduces  CNFEncoding.lean::parseClauses: 117/189 = 62%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clCmp_idle: 91/147 = 62%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clCmp_idle: 91/147 = 62%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Snapshot.lean::prevVisit_some_last  reproduces  Hardness.lean::clPrev_spec: 82/133 = 62%
   SAT.lean::satRed_maxClause  reproduces  SAT.lean::sat_clause_measure: 67/109 = 61%
   SAT.lean::satEval_clause  reproduces  SAT.lean::sat_clause_measure: 67/109 = 61%
   Hardness.lean::clCountOutputTM  reproduces  Hardness.lean::clRecordOutputTM: 84/138 = 61%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clRow_idle: 88/146 = 60%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clPrepare_idle: 137/228 = 60%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clLoad_idle: 88/147 = 60%
   SAT.lean::satDrop_skip  reproduces  SAT.lean::satDrop_dispatch: 186/311 = 60%
   Hardness.lean::clLastCode_native  reproduces  SAT.lean::sat_pt_append: 77/129 = 60%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clPrepare_idle: 136/228 = 60%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clPrepare_idle: 136/228 = 60%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clPrepare_idle: 136/228 = 60%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clFresh_idle: 91/153 = 59%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clFresh_idle: 91/153 = 59%
   Hardness.lean::clCopy_rewind  reproduces  Hardness.lean::clCopy_write: 98/165 = 59%
   SAT.lean::sat_pt_unaryLength  reproduces  SAT.lean::sat_takeTrues_repr: 76/128 = 59%
   Hardness.lean::clRecords_native  reproduces  Hardness.lean::clFinalCount_native: 114/193 = 59%
   Hardness.lean::clA5Sizes_native  reproduces  Hardness.lean::clA5Cursor_native: 76/130 = 58%
   Hardness.lean::clRepeat_round  reproduces  Hardness.lean::clTrack_dispatch: 61/105 = 58%
   Hardness.lean::clMatch_load  reproduces  Hardness.lean::clTrack_dispatch: 61/105 = 58%
   SAT.lean::satPair_start  reproduces  SAT.lean::satEval_start: 1086/1871 = 58%
   SAT.lean::satPair_replay  reproduces  SAT.lean::satPair_rewind: 542/938 = 58%
   Hardness.lean::clA5WorkFragment  reproduces  Hardness.lean::clA5InputFragment: 112/194 = 58%
   Hardness.lean::clReplay_back  reproduces  Hardness.lean::clReplay_forward: 514/891 = 58%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clFresh_idle: 88/153 = 58%
   SAT.lean::satScanTM  reproduces  SAT.lean::satMapTM: 73/127 = 57%
   SAT.lean::satScanTM  reproduces  Hardness.lean::clA5MapTM: 73/127 = 57%
   Hardness.lean::clA5InputFragment_native  reproduces  Hardness.lean::clA5IfLt_native: 81/141 = 57%
   Hardness.lean::clA5Fuel  reproduces  Hardness.lean::clNative_append: 76/133 = 57%
   SAT.lean::satStreamStep_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 65/114 = 57%
   SAT.lean::satPair_rewind  reproduces  SAT.lean::satEval_rewind: 446/785 = 57%
   Hardness.lean::clMatch_cmp_frame  reproduces  Hardness.lean::clQuery_initial: 101/178 = 57%
   SAT.lean::satMax_finish  reproduces  SAT.lean::satDrop_dispatch: 176/311 = 57%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clWipe_idle: 80/142 = 56%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clInput_idle: 80/142 = 56%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clCopy_idle: 80/142 = 56%
   Hardness.lean::clCmp_rewind  reproduces  Hardness.lean::clCmp_finish_scan: 144/256 = 56%
   Hardness.lean::clRecordWords_native  reproduces  Hardness.lean::clHeaderLayout_native: 553/985 = 56%
   Hardness.lean::clSearchArg_native  reproduces  Hardness.lean::clRepeatArgument_native: 241/430 = 56%
   SAT.lean::satMapTM  reproduces  SAT.lean::satScanTM: 73/131 = 56%
   Hardness.lean::clA5MapTM  reproduces  SAT.lean::satScanTM: 73/131 = 56%
   SAT.lean::sat_pt_mapSnd  reproduces  Hardness.lean::clNative_map: 279/502 = 56%
   CNFEncoding.lean::parseClause_bounds  reproduces  SAT.lean::sat_parseClause_repr: 294/529 = 56%
   Hardness.lean::clRead_rewind  reproduces  Hardness.lean::clReplay_back: 391/705 = 55%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clPrepare_idle: 126/228 = 55%
   Hardness.lean::clCopy_rewind  reproduces  Hardness.lean::clReplay_back: 388/705 = 55%
   Hardness.lean::clQuery_initial  reproduces  Hardness.lean::clRepeat_initial: 67/122 = 55%
   Hardness.lean::clMatch_cmp_frame  reproduces  Hardness.lean::clRepeat_initial: 67/122 = 55%
   CNFEncoding.lean::parseClauses_serialize  reproduces  CNFEncoding.lean::parseClause_serializeClause: 402/733 = 55%
   Hardness.lean::clA5Field_native  reproduces  Hardness.lean::clA5Drop_native: 123/225 = 55%
   Hardness.lean::clCopy_separator  reproduces  Hardness.lean::clCopy_pair: 443/811 = 55%
   Hardness.lean::clA5Stop_clean  reproduces  Hardness.lean::clCmp_forward: 77/141 = 55%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clCmp_idle: 80/147 = 54%
   Hardness.lean::clRec_track_inactive  reproduces  Hardness.lean::clRec_row_frame: 179/330 = 54%
   SAT.lean::satAppend_rewind  reproduces  SAT.lean::satAppend_seek: 450/832 = 54%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clRecord_prepare_frame: 151/280 = 54%
   SAT.lean::satStreamRead_word  reproduces  SAT.lean::satReq_fields: 62/115 = 54%
   SAT.lean::satMap_run  reproduces  SAT.lean::satScan_run: 269/499 = 54%
   MeyerTableau.lean::RW_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   MeyerTableau.lean::RI_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   CNFEncoding.lean::parseClause_serializeClause  reproduces  CNFEncoding.lean::parseClauses_serialize: 402/747 = 54%
   Hardness.lean::clRead_separator  reproduces  Hardness.lean::clRead_rewind: 432/803 = 54%
   CNFEncoding.lean::parseClauses_bounds  reproduces  SAT.lean::sat_parseClauses_repr: 295/549 = 54%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   SAT.lean::satReq_fields_poly  reproduces  SAT.lean::sat_pt_append: 69/129 = 53%
   Hardness.lean::clA5Map_run  reproduces  SAT.lean::satScan_run: 266/499 = 53%
   SAT.lean::satStreamRound  reproduces  SAT.lean::satStreamTail: 65/122 = 53%
   Hardness.lean::clRecord_prepare_frame  reproduces  Hardness.lean::clRepeat_initial: 65/122 = 53%
   SAT.lean::sat_run_agree  reproduces  Hardness.lean::clCmp_forward: 75/141 = 53%
   SAT.lean::satStop_clean  reproduces  Hardness.lean::clCmp_forward: 75/141 = 53%
   Hardness.lean::clRec_track_inactive  reproduces  Hardness.lean::clRec_track_frame: 194/366 = 53%
   Hardness.lean::clRead_rewind  reproduces  Hardness.lean::clCopy_rewind: 524/991 = 53%
   Hardness.lean::clRec_prepared  reproduces  Hardness.lean::clQuery_initial: 94/178 = 53%
   Snapshot.lean::workCell_succ  reproduces  Snapshot.lean::snapshotAt_state_succ: 77/146 = 53%
   MeyerTableau.lean::incFixed_enumWord  reproduces  MeyerTableau.lean::ctrVal_enumWord: 98/186 = 53%
   SAT.lean::satDrop_rewind  reproduces  SAT.lean::satDrop_skip: 269/512 = 53%
   SAT.lean::satMax_prefix  reproduces  Hardness.lean::clCmp_forward: 74/141 = 52%
   Hardness.lean::clWipe_forward  reproduces  Hardness.lean::clRead_rewind: 421/803 = 52%
   Hardness.lean::clRec_prepared  reproduces  Hardness.lean::clRepeat_frame: 67/128 = 52%
   Hardness.lean::clQuery_initial  reproduces  Hardness.lean::clRepeat_frame: 67/128 = 52%
   Hardness.lean::clMatch_cmp_frame  reproduces  Hardness.lean::clRepeat_frame: 67/128 = 52%
   SAT.lean::satMax_prefix  reproduces  SAT.lean::satDrop_skip: 267/512 = 52%
   SAT.lean::satStop_clean  reproduces  SAT.lean::sat_run_agree: 111/213 = 52%
   Hardness.lean::clA5Stop_clean  reproduces  SAT.lean::sat_run_agree: 111/213 = 52%
   Hardness.lean::clA5InputFragment  reproduces  Hardness.lean::clA5WorkFragment: 112/215 = 52%
   Hardness.lean::clA5Run_output  reproduces  Snapshot.lean::snapshotAt_state_succ: 76/146 = 52%
   Hardness.lean::clHeaderLayout_native  reproduces  Hardness.lean::clRepeatArgument_native: 222/430 = 52%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clWipe_idle: 73/142 = 51%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clInput_idle: 73/142 = 51%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clCopy_idle: 73/142 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clWipe_idle: 73/142 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clInput_idle: 73/142 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clCopy_idle: 73/142 = 51%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clRow_idle: 75/146 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clRow_idle: 75/146 = 51%
   Hardness.lean::clLeft_until  reproduces  SAT.lean::sat_run_agree: 109/213 = 51%
   Hardness.lean::clPrepHeader_native  reproduces  Hardness.lean::clNative_append: 68/133 = 51%
   Hardness.lean::clRead_forward  reproduces  Hardness.lean::clCopy_forward: 138/270 = 51%
   Hardness.lean::clRecWords  reproduces  Hardness.lean::clHeaderLayout: 75/147 = 51%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clLoad_idle: 75/147 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clLoad_idle: 75/147 = 51%
   Hardness.lean::clWipe_backward  reproduces  Hardness.lean::clWipe_forward: 435/855 = 51%
   Hardness.lean::clRepeatCfg  reproduces  Hardness.lean::clLoadCfg: 65/128 = 51%
   Hardness.lean::clRecord_prepare_frame  reproduces  Hardness.lean::clRepeat_frame: 65/128 = 51%
   Hardness.lean::clInputTM  reproduces  Hardness.lean::clReplayTM: 137/270 = 51%
   Hardness.lean::clRead_pair  reproduces  Hardness.lean::clRead_rewind: 406/803 = 51%
   Hardness.lean::clNative_map  reproduces  SAT.lean::sat_pt_mapSnd: 279/552 = 51%
   SAT.lean::sat_pt_pair  reproduces  SAT.lean::sat_pt_append: 65/129 = 50%
   Hardness.lean::clReplay_back  reproduces  Hardness.lean::clCmp_forward: 71/141 = 50%
   Hardness.lean::clRepeat_complete  reproduces  Hardness.lean::clCmp_forward: 71/141 = 50%
   Hardness.lean::clInput_backward  reproduces  Hardness.lean::clCmp_forward: 71/141 = 50%
   SAT.lean::satRed_maxLiteral  reproduces  SAT.lean::satRed_maxOnes: 505/1003 = 50%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clPrepare_idle: 114/228 = 50%
   Hardness.lean::clA5Next_pack  reproduces  Hardness.lean::clA5Stored_exact: 112/224 = 50%
   Hardness.lean::clPreparedCfg  reproduces  Hardness.lean::clRecordCfg: 91/182 = 50%
   Hardness.lean::clA5Count_native  reproduces  Hardness.lean::clA5Address_native: 74/148 = 50%
   SAT.lean::satReq_fields  reproduces  SAT.lean::satStreamRead_word: 62/124 = 50%
```

### After

```text
declarations screened: 853; copy pairs (target reproduces >= half of source): 363; reproduced text: 76,157 chars
   SAT.lean::sat_bridge_bound  reproduces  Hardness.lean::clA5_bridge_bound: 452/452 = 100%
   Hardness.lean::clA5_bridge_bound  reproduces  SAT.lean::sat_bridge_bound: 452/452 = 100%
   SAT.lean::sat_call_first_halt  reproduces  Hardness.lean::clA5_call_first_halt: 330/330 = 100%
   Hardness.lean::clA5_call_first_halt  reproduces  SAT.lean::sat_call_first_halt: 330/330 = 100%
   SAT.lean::SatClean  reproduces  Hardness.lean::CLA5Clean: 257/257 = 100%
   Hardness.lean::CLA5Clean  reproduces  SAT.lean::SatClean: 257/257 = 100%
   SAT.lean::satStopTM  reproduces  Hardness.lean::clA5StopTM: 180/180 = 100%
   Hardness.lean::clA5StopTM  reproduces  SAT.lean::satStopTM: 180/180 = 100%
   SAT.lean::sat_live_prefix  reproduces  Hardness.lean::clA5_live_prefix: 152/152 = 100%
   Hardness.lean::clA5_live_prefix  reproduces  SAT.lean::sat_live_prefix: 152/152 = 100%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clLoad_idle: 147/147 = 100%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clInput_idle: 142/142 = 100%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clWipe_idle: 142/142 = 100%
   SAT.lean::satPadCfg  reproduces  Hardness.lean::clA5PadCfg: 134/134 = 100%
   Hardness.lean::clA5PadCfg  reproduces  SAT.lean::satPadCfg: 134/134 = 100%
   SAT.lean::sat_guard_add  reproduces  Hardness.lean::clA5_guard_add: 127/127 = 100%
   SAT.lean::satMapTM  reproduces  Hardness.lean::clA5MapTM: 127/127 = 100%
   Hardness.lean::clA5_guard_add  reproduces  SAT.lean::sat_guard_add: 127/127 = 100%
   Hardness.lean::clA5MapTM  reproduces  SAT.lean::satMapTM: 127/127 = 100%
   SAT.lean::satPadAction  reproduces  Hardness.lean::clA5PadAction: 84/84 = 100%
   Hardness.lean::clA5PadAction  reproduces  SAT.lean::satPadAction: 84/84 = 100%
   Hardness.lean::clWipeCfg  reproduces  Hardness.lean::clReadCfg: 72/72 = 100%
   Hardness.lean::clReadCfg  reproduces  Hardness.lean::clWipeCfg: 72/72 = 100%
   SAT.lean::satStopCfg  reproduces  Hardness.lean::clA5StopCfg: 64/64 = 100%
   Hardness.lean::clA5StopCfg  reproduces  SAT.lean::satStopCfg: 64/64 = 100%
   Hardness.lean::clA5Clean_install  reproduces  SAT.lean::satClean_install: 614/623 = 99%
   Hardness.lean::clA5Clean_emit  reproduces  SAT.lean::satClean_emit: 595/604 = 99%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clOutput_compute: 1751/1778 = 98%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clOutputAt_compute: 1751/1782 = 98%
   SAT.lean::satClean_install  reproduces  Hardness.lean::clA5Clean_install: 614/626 = 98%
   SAT.lean::satClean_emit  reproduces  Hardness.lean::clA5Clean_emit: 595/607 = 98%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clRow_idle: 143/146 = 98%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clRow_idle: 143/146 = 98%
   Hardness.lean::clCount_size_budget  reproduces  Hardness.lean::clRecord_size_budget: 305/312 = 98%
   Hardness.lean::clA5Host_clean  reproduces  SAT.lean::satHost_clean: 130/133 = 98%
   Hardness.lean::clA5Clean_install  reproduces  Hardness.lean::clA5Clean_emit: 592/607 = 98%
   SAT.lean::satClean_install  reproduces  SAT.lean::satClean_emit: 589/604 = 98%
   Hardness.lean::clA5PadTM  reproduces  SAT.lean::satPadTM: 117/120 = 98%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clLoad_idle: 143/147 = 97%
   SAT.lean::satHost_clean  reproduces  Hardness.lean::clA5Host_clean: 130/134 = 97%
   Hardness.lean::clA5_pt_eq  reproduces  SAT.lean::sat_pt_eq: 186/192 = 97%
   SAT.lean::satRed_maxFormula  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_maxClause  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satRed_counterBack  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satPair_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clReplay_back  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clRead_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clInput_backward  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clCopy_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   Hardness.lean::clCmp_rewind  reproduces  SAT.lean::satRed_one: 61/63 = 97%
   SAT.lean::satPadTM  reproduces  Hardness.lean::clA5PadTM: 117/121 = 97%
   Hardness.lean::clMatch_tick  reproduces  Hardness.lean::clMatch_stop: 288/298 = 97%
   Hardness.lean::clRecord_size_budget  reproduces  Hardness.lean::clCount_size_budget: 305/316 = 97%
   Hardness.lean::clA5Map_run  reproduces  SAT.lean::satMap_run: 878/911 = 96%
   Hardness.lean::clA5MapWord  reproduces  SAT.lean::satMapWord: 79/82 = 96%
   Hardness.lean::clA5_pt_head  reproduces  SAT.lean::sat_pt_head: 382/397 = 96%
   Hardness.lean::clA5_pt_tail  reproduces  SAT.lean::sat_pt_tail: 380/395 = 96%
   Hardness.lean::clA5_pt_head  reproduces  Hardness.lean::clA5_pt_tail: 384/400 = 96%
   SAT.lean::sat_pt_head  reproduces  SAT.lean::sat_pt_tail: 379/395 = 96%
   SAT.lean::sat_pt_eq  reproduces  Hardness.lean::clA5_pt_eq: 186/194 = 96%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clWipe_idle: 136/142 = 96%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clInput_idle: 136/142 = 96%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clWipe_idle: 136/142 = 96%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clInput_idle: 136/142 = 96%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clWipe_idle: 136/142 = 96%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clInput_idle: 136/142 = 96%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clWipe_idle: 136/142 = 96%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clInput_idle: 136/142 = 96%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clCopy_idle: 136/142 = 96%
   Hardness.lean::clA5_pt_tail  reproduces  Hardness.lean::clA5_pt_head: 384/402 = 96%
   SAT.lean::sat_pt_tail  reproduces  SAT.lean::sat_pt_head: 379/397 = 95%
   SAT.lean::satMap_run  reproduces  Hardness.lean::clA5Map_run: 878/920 = 95%
   SAT.lean::satDrop_skip  reproduces  SAT.lean::satRed_one: 60/63 = 95%
   SAT.lean::satMapWord  reproduces  Hardness.lean::clA5MapWord: 79/83 = 95%
   SAT.lean::sat_pt_head  reproduces  Hardness.lean::clA5_pt_head: 382/402 = 95%
   SAT.lean::sat_pt_tail  reproduces  Hardness.lean::clA5_pt_tail: 380/400 = 95%
   Hardness.lean::clReplay_run  reproduces  Hardness.lean::clReplay_from: 398/419 = 95%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clFresh_idle: 145/153 = 95%
   Hardness.lean::clA5Clean_emit  reproduces  Hardness.lean::clA5Clean_install: 592/626 = 95%
   SAT.lean::satClean_emit  reproduces  SAT.lean::satClean_install: 589/623 = 95%
   SAT.lean::satVerdict_true_poly  reproduces  SAT.lean::satVerdict_false_poly: 378/400 = 94%
   Hardness.lean::clRec_track_inactive  reproduces  Hardness.lean::clRec_row_inactive: 177/188 = 94%
   Hardness.lean::clA5Stop_clean  reproduces  SAT.lean::satStop_clean: 754/801 = 94%
   Hardness.lean::clA5Map_poly  reproduces  SAT.lean::satMap_poly: 300/321 = 93%
   Hardness.lean::clA5Pad_run  reproduces  SAT.lean::satPad_run: 406/435 = 93%
   SAT.lean::satStop_clean  reproduces  Hardness.lean::clA5Stop_clean: 754/809 = 93%
   Hardness.lean::clPrepare_idle  reproduces  Hardness.lean::clCmp_idle: 137/147 = 93%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clCmp_idle: 137/147 = 93%
   Hardness.lean::clA5Host_seam  reproduces  SAT.lean::satHost_seam: 163/175 = 93%
   SAT.lean::satHost_seam  reproduces  Hardness.lean::clA5Host_seam: 163/176 = 93%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clCmp_idle: 136/147 = 93%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clCmp_idle: 136/147 = 93%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clCmp_idle: 136/147 = 93%
   SAT.lean::satMap_poly  reproduces  Hardness.lean::clA5Map_poly: 300/325 = 92%
   SAT.lean::satPad_run  reproduces  Hardness.lean::clA5Pad_run: 406/441 = 92%
   Hardness.lean::clA5Clean_stop  reproduces  SAT.lean::satClean_stop: 336/365 = 92%
   Hardness.lean::clA5StoredRound_native  reproduces  Hardness.lean::clA5Sizes_native: 196/214 = 92%
   Hardness.lean::clA5Clean_install  reproduces  SAT.lean::satClean_emit: 552/604 = 91%
   SAT.lean::satClean_stop  reproduces  Hardness.lean::clA5Clean_stop: 336/369 = 91%
   SAT.lean::satClean_install  reproduces  Hardness.lean::clA5Clean_emit: 552/607 = 91%
   Hardness.lean::clRowCfg  reproduces  Hardness.lean::clLoadCfg: 116/128 = 91%
   SAT.lean::satPairCfg  reproduces  SAT.lean::satEvalCfg: 131/146 = 90%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clFresh_idle: 137/153 = 90%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clFresh_idle: 136/153 = 89%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clFresh_idle: 136/153 = 89%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clFresh_idle: 136/153 = 89%
   Hardness.lean::clA5Clean_emit  reproduces  SAT.lean::satClean_install: 552/623 = 89%
   SAT.lean::satEvalCfg  reproduces  SAT.lean::satPairCfg: 131/148 = 89%
   Hardness.lean::clMatch_stop  reproduces  Hardness.lean::clMatch_tick: 288/326 = 88%
   Hardness.lean::clReplay_from  reproduces  Hardness.lean::clReplay_run: 398/451 = 88%
   SAT.lean::satClean_emit  reproduces  Hardness.lean::clA5Clean_install: 552/626 = 88%
   Hardness.lean::clA5Pad_seam  reproduces  SAT.lean::satPad_seam: 208/239 = 87%
   SAT.lean::satPad_seam  reproduces  Hardness.lean::clA5Pad_seam: 208/242 = 86%
   Hardness.lean::clA5_pt_head  reproduces  SAT.lean::sat_pt_tail: 339/395 = 86%
   Hardness.lean::clA5Host_call  reproduces  SAT.lean::satHost_call: 777/909 = 85%
   Hardness.lean::clA5_pt_tail  reproduces  SAT.lean::sat_pt_head: 339/397 = 85%
   Hardness.lean::clA5Stop_step  reproduces  SAT.lean::satStop_step: 175/205 = 85%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clWipe_idle: 121/142 = 85%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clInput_idle: 121/142 = 85%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clCopy_idle: 121/142 = 85%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clCmp_idle: 125/147 = 85%
   SAT.lean::sat_pt_head  reproduces  Hardness.lean::clA5_pt_tail: 339/400 = 85%
   SAT.lean::satStop_step  reproduces  Hardness.lean::clA5Stop_step: 175/207 = 85%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clCmp_idle: 124/147 = 84%
   SAT.lean::sat_pt_tail  reproduces  Hardness.lean::clA5_pt_head: 339/402 = 84%
   SAT.lean::satHost_call  reproduces  Hardness.lean::clA5Host_call: 777/926 = 84%
   Hardness.lean::clNative_pair  reproduces  SAT.lean::sat_pt_fields: 78/93 = 84%
   Hardness.lean::clRec_copy  reproduces  Hardness.lean::clTrack_dispatch: 88/105 = 84%
   Hardness.lean::clRec_advance  reproduces  Hardness.lean::clTrack_dispatch: 88/105 = 84%
   Hardness.lean::clRec_row_frame  reproduces  Hardness.lean::clRec_row_inactive: 156/188 = 83%
   Hardness.lean::clNative_append  reproduces  SAT.lean::sat_pt_append: 107/129 = 83%
   Hardness.lean::clLoadCfg  reproduces  Hardness.lean::clRowCfg: 116/140 = 83%
   SAT.lean::satDrop_rewind  reproduces  SAT.lean::satDrop_dispatch: 256/311 = 82%
   Hardness.lean::clRec_prepared  reproduces  Hardness.lean::clRepeat_initial: 100/122 = 82%
   Hardness.lean::clRec_track_frame  reproduces  Hardness.lean::clRec_row_inactive: 154/188 = 82%
   Hardness.lean::clCmp_rewind  reproduces  Hardness.lean::clCmp_forward_step: 185/226 = 82%
   Hardness.lean::clRecords_native  reproduces  Hardness.lean::clTrajectory_native: 157/193 = 81%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clWipe_idle: 115/142 = 81%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clInput_idle: 115/142 = 81%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clCopy_idle: 115/142 = 81%
   SAT.lean::satReq_round  reproduces  SAT.lean::satReq_fields: 93/115 = 81%
   Hardness.lean::clRead_separator  reproduces  Hardness.lean::clRead_pair: 953/1182 = 81%
   SAT.lean::sat_pt_append  reproduces  Hardness.lean::clNative_append: 107/133 = 80%
   Hardness.lean::clRead_pair  reproduces  Hardness.lean::clRead_separator: 953/1186 = 80%
   Hardness.lean::clRec_tick  reproduces  Hardness.lean::clRec_stop: 248/310 = 80%
   CNFEncoding.lean::parseClauses_bounds  reproduces  CNFEncoding.lean::parseClause_bounds: 731/920 = 79%
   SAT.lean::satMax_prefix  reproduces  SAT.lean::satMax_finish: 428/540 = 79%
   Hardness.lean::clA5StoredRound_native  reproduces  Hardness.lean::clA5Cursor_native: 103/130 = 79%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clFresh_idle: 121/153 = 79%
   SAT.lean::satSplitClause_width  reproduces  SAT.lean::satSplitClause_vars: 67/85 = 79%
   Hardness.lean::clA5Fuel  reproduces  Hardness.lean::clA5Cursor_install: 61/78 = 78%
   Hardness.lean::clA5DecodeStep_state  reproduces  Hardness.lean::clVisitStep_state: 93/119 = 78%
   SAT.lean::satPairAction_apply  reproduces  SAT.lean::satEvalAction_apply: 121/157 = 77%
   SAT.lean::satEvalAction_apply  reproduces  SAT.lean::satPairAction_apply: 121/157 = 77%
   Hardness.lean::clRecordOutputTM  reproduces  Hardness.lean::clCountOutputTM: 84/109 = 77%
   Hardness.lean::clLoadTM  reproduces  Hardness.lean::clRowTM: 223/293 = 76%
   Hardness.lean::clA5Field_native  reproduces  Hardness.lean::clA5Decode_orbit: 70/92 = 76%
   Hardness.lean::clBank_run  reproduces  Hardness.lean::clCount_idle_run: 69/91 = 76%
   SAT.lean::sat_parseClauses_repr  reproduces  SAT.lean::sat_parseClause_repr: 400/529 = 76%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clFresh_idle: 115/153 = 75%
   SAT.lean::satReqStep_poly  reproduces  SAT.lean::satReqEmit_poly: 333/446 = 75%
   Hardness.lean::clLeft_until  reproduces  Hardness.lean::clCmp_forward: 105/141 = 74%
   TQBF.lean::codecCnf_numVars  reproduces  TQBF.lean::codecCnfCost_relabel: 61/82 = 74%
   Hardness.lean::clA5Next_pack  reproduces  Hardness.lean::clVisitStep_state: 88/119 = 74%
   CNFEncoding.lean::parseClause_bounds  reproduces  CNFEncoding.lean::parseClauses_bounds: 731/992 = 74%
   Hardness.lean::clCount_idle_run  reproduces  Hardness.lean::clBank_run: 69/94 = 73%
   Hardness.lean::clCount_idle  reproduces  Hardness.lean::clTrack_dispatch: 77/105 = 73%
   Hardness.lean::clInput_forward  reproduces  Hardness.lean::clCmp_forward: 103/141 = 73%
   Hardness.lean::clCmp_finish_scan  reproduces  Hardness.lean::clCmp_forward_step: 165/226 = 73%
   CNFEncoding.lean::numVars_le_of_literal_bounds  reproduces  CNF.lean::foldr_max_le_of_forall: 97/133 = 73%
   Hardness.lean::clReplay_forward  reproduces  Hardness.lean::clReplay_back: 514/705 = 73%
   SAT.lean::sat_parseClause_repr  reproduces  SAT.lean::sat_parseClauses_repr: 400/549 = 73%
   Hardness.lean::clA5Iter_shrinking  reproduces  Hardness.lean::clA5Decode_orbit: 67/92 = 73%
   SAT.lean::satSyntaxSuffix_cons  reproduces  SAT.lean::sat_clause_measure: 79/109 = 72%
   Hardness.lean::clMatchCfg  reproduces  Hardness.lean::clQueryWords: 91/128 = 71%
   Hardness.lean::clTrajectory_native  reproduces  Hardness.lean::clFinalCount_native: 137/193 = 71%
   Hardness.lean::clFinalCount_native  reproduces  Hardness.lean::clTrajectory_native: 137/193 = 71%
   Hardness.lean::clA5Data_exact  reproduces  Hardness.lean::clA5Stored_exact: 159/224 = 71%
   TQBF.lean::configurationValidity_size_raw  reproduces  TQBF.lean::configurationValidity_numVars: 68/96 = 71%
   Hardness.lean::clHeaderLayout  reproduces  Hardness.lean::clRecWords: 75/107 = 70%
   SAT.lean::satReqStep  reproduces  SAT.lean::satReqEmit: 159/229 = 69%
   MeyerTableau.lean::wstep_some_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 79/114 = 69%
   Hardness.lean::clA5HostTM  reproduces  SAT.lean::satHostTM: 146/211 = 69%
   SAT.lean::satSplitClause_vars  reproduces  SAT.lean::satSplitClause_width: 67/97 = 69%
   Hardness.lean::clRead_run  reproduces  Hardness.lean::clCopy_run: 195/283 = 69%
   Hardness.lean::clRepeat_frame  reproduces  Hardness.lean::clRepeat_initial: 84/122 = 69%
   Hardness.lean::clCountOutput_quadratic  reproduces  Hardness.lean::clRecordOutput_quadratic: 509/741 = 69%
   Hardness.lean::clRec_track_frame  reproduces  Hardness.lean::clRec_track_inactive: 194/283 = 69%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clRow_idle: 100/146 = 68%
   Hardness.lean::clCountInc_bits  reproduces  Hardness.lean::clNum_bits: 89/130 = 68%
   Hardness.lean::clA5Pad_apply  reproduces  SAT.lean::satPad_apply: 117/171 = 68%
   Hardness.lean::clRowTM  reproduces  Hardness.lean::clLoadTM: 223/328 = 68%
   SAT.lean::satHostTM  reproduces  Hardness.lean::clA5HostTM: 146/216 = 68%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clLoad_idle: 99/147 = 67%
   Hardness.lean::clPrepared_run  reproduces  Hardness.lean::clRepeat_initial: 82/122 = 67%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clRepeat_initial: 82/122 = 67%
   SAT.lean::satPad_apply  reproduces  Hardness.lean::clA5Pad_apply: 117/175 = 67%
   CNFEncoding.lean::parseClauses  reproduces  CNFEncoding.lean::parseClause: 117/175 = 67%
   Hardness.lean::clCopy_pair  reproduces  Hardness.lean::clCopy_separator: 443/668 = 66%
   SAT.lean::satEval_double  reproduces  SAT.lean::satEval_skip: 137/207 = 66%
   Hardness.lean::clRepeat_initial  reproduces  Hardness.lean::clRepeat_frame: 84/128 = 66%
   Hardness.lean::clPrepared_run  reproduces  Hardness.lean::clRepeat_frame: 84/128 = 66%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clRepeat_frame: 84/128 = 66%
   Hardness.lean::clCopy_rewind  reproduces  Hardness.lean::clRead_rewind: 524/803 = 65%
   SAT.lean::satMax_finish  reproduces  SAT.lean::satMax_prefix: 428/656 = 65%
   Hardness.lean::clHeaderLayout_native  reproduces  Hardness.lean::clRecordWords_native: 553/849 = 65%
   Hardness.lean::clRecordCfg  reproduces  Hardness.lean::clPreparedCfg: 91/140 = 65%
   SAT.lean::sat_pt_append  reproduces  SAT.lean::sat_pt_pair: 65/100 = 65%
   SAT.lean::satStream_parseLit  reproduces  SAT.lean::satWidth_index: 62/96 = 65%
   Hardness.lean::clA5Fuel  reproduces  SAT.lean::sat_pt_fields: 60/93 = 65%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clPrepare_idle: 147/228 = 64%
   Hardness.lean::clCmp_forward_step  reproduces  Hardness.lean::clCmp_finish_scan: 165/256 = 64%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clWipe_idle: 91/142 = 64%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clInput_idle: 91/142 = 64%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clCopy_idle: 91/142 = 64%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clWipe_idle: 91/142 = 64%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clInput_idle: 91/142 = 64%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clCopy_idle: 91/142 = 64%
   Hardness.lean::clLastCode_native  reproduces  Hardness.lean::clNative_append: 85/133 = 64%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clPrepare_idle: 145/228 = 64%
   SAT.lean::satAppend_copy  reproduces  SAT.lean::satAppend_seek: 528/832 = 63%
   Hardness.lean::clRec_row_frame  reproduces  Hardness.lean::clRec_track_inactive: 179/283 = 63%
   Hardness.lean::clRecordWords_native  reproduces  Hardness.lean::clRepeatArgument_native: 271/430 = 63%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clPrepare_idle: 143/228 = 63%
   SAT.lean::satEval_start  reproduces  SAT.lean::satPair_start: 1086/1733 = 63%
   Hardness.lean::clRec_row_inactive  reproduces  Hardness.lean::clRec_track_inactive: 177/283 = 63%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clRow_idle: 91/146 = 62%
   CNFEncoding.lean::parseClause  reproduces  CNFEncoding.lean::parseClauses: 117/189 = 62%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clCmp_idle: 91/147 = 62%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clCmp_idle: 91/147 = 62%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Hardness.lean::clFresh_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clLoad_idle: 91/147 = 62%
   Snapshot.lean::prevVisit_some_last  reproduces  Hardness.lean::clPrev_spec: 82/133 = 62%
   SAT.lean::satRed_maxClause  reproduces  SAT.lean::sat_clause_measure: 67/109 = 61%
   SAT.lean::satEval_clause  reproduces  SAT.lean::sat_clause_measure: 67/109 = 61%
   Hardness.lean::clCountOutputTM  reproduces  Hardness.lean::clRecordOutputTM: 84/138 = 61%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clRow_idle: 88/146 = 60%
   Hardness.lean::clCmp_idle  reproduces  Hardness.lean::clPrepare_idle: 137/228 = 60%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clLoad_idle: 88/147 = 60%
   SAT.lean::satDrop_skip  reproduces  SAT.lean::satDrop_dispatch: 186/311 = 60%
   Hardness.lean::clLastCode_native  reproduces  SAT.lean::sat_pt_append: 77/129 = 60%
   Hardness.lean::clWipe_idle  reproduces  Hardness.lean::clPrepare_idle: 136/228 = 60%
   Hardness.lean::clInput_idle  reproduces  Hardness.lean::clPrepare_idle: 136/228 = 60%
   Hardness.lean::clCopy_idle  reproduces  Hardness.lean::clPrepare_idle: 136/228 = 60%
   Hardness.lean::clRow_idle  reproduces  Hardness.lean::clFresh_idle: 91/153 = 59%
   Hardness.lean::clLoad_idle  reproduces  Hardness.lean::clFresh_idle: 91/153 = 59%
   Hardness.lean::clCopy_rewind  reproduces  Hardness.lean::clCopy_write: 98/165 = 59%
   SAT.lean::sat_pt_unaryLength  reproduces  SAT.lean::sat_takeTrues_repr: 76/128 = 59%
   Hardness.lean::clRecords_native  reproduces  Hardness.lean::clFinalCount_native: 114/193 = 59%
   Hardness.lean::clA5Sizes_native  reproduces  Hardness.lean::clA5Cursor_native: 76/130 = 58%
   Hardness.lean::clRepeat_round  reproduces  Hardness.lean::clTrack_dispatch: 61/105 = 58%
   Hardness.lean::clMatch_load  reproduces  Hardness.lean::clTrack_dispatch: 61/105 = 58%
   SAT.lean::satPair_start  reproduces  SAT.lean::satEval_start: 1086/1871 = 58%
   SAT.lean::satPair_replay  reproduces  SAT.lean::satPair_rewind: 542/938 = 58%
   Hardness.lean::clA5WorkFragment  reproduces  Hardness.lean::clA5InputFragment: 112/194 = 58%
   Hardness.lean::clReplay_back  reproduces  Hardness.lean::clReplay_forward: 514/891 = 58%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clFresh_idle: 88/153 = 58%
   SAT.lean::satScanTM  reproduces  SAT.lean::satMapTM: 73/127 = 57%
   SAT.lean::satScanTM  reproduces  Hardness.lean::clA5MapTM: 73/127 = 57%
   Hardness.lean::clA5InputFragment_native  reproduces  Hardness.lean::clA5IfLt_native: 81/141 = 57%
   Hardness.lean::clA5Fuel  reproduces  Hardness.lean::clNative_append: 76/133 = 57%
   SAT.lean::satStreamStep_iterate  reproduces  MeyerTableau.lean::wstep_none_iterate: 65/114 = 57%
   TQBF.lean::configurationAdjacency_bounds  reproduces  TQBF.lean::configurationInputEquality_bounds: 169/297 = 57%
   SAT.lean::satPair_rewind  reproduces  SAT.lean::satEval_rewind: 446/785 = 57%
   Hardness.lean::clMatch_cmp_frame  reproduces  Hardness.lean::clQuery_initial: 101/178 = 57%
   SAT.lean::satMax_finish  reproduces  SAT.lean::satDrop_dispatch: 176/311 = 57%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clWipe_idle: 80/142 = 56%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clInput_idle: 80/142 = 56%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clCopy_idle: 80/142 = 56%
   Hardness.lean::clCmp_rewind  reproduces  Hardness.lean::clCmp_finish_scan: 144/256 = 56%
   Hardness.lean::clRecordWords_native  reproduces  Hardness.lean::clHeaderLayout_native: 553/985 = 56%
   Hardness.lean::clSearchArg_native  reproduces  Hardness.lean::clRepeatArgument_native: 241/430 = 56%
   SAT.lean::satMapTM  reproduces  SAT.lean::satScanTM: 73/131 = 56%
   Hardness.lean::clA5MapTM  reproduces  SAT.lean::satScanTM: 73/131 = 56%
   SAT.lean::sat_pt_mapSnd  reproduces  Hardness.lean::clNative_map: 279/502 = 56%
   CNFEncoding.lean::parseClause_bounds  reproduces  SAT.lean::sat_parseClause_repr: 294/529 = 56%
   TQBF.lean::configurationCodec_input_eq  reproduces  TQBF.lean::configurationCodec_eq_iff: 81/146 = 55%
   Hardness.lean::clRead_rewind  reproduces  Hardness.lean::clReplay_back: 391/705 = 55%
   Hardness.lean::clRecord_idle  reproduces  Hardness.lean::clPrepare_idle: 126/228 = 55%
   Hardness.lean::clCopy_rewind  reproduces  Hardness.lean::clReplay_back: 388/705 = 55%
   Hardness.lean::clQuery_initial  reproduces  Hardness.lean::clRepeat_initial: 67/122 = 55%
   Hardness.lean::clMatch_cmp_frame  reproduces  Hardness.lean::clRepeat_initial: 67/122 = 55%
   CNFEncoding.lean::parseClauses_serialize  reproduces  CNFEncoding.lean::parseClause_serializeClause: 402/733 = 55%
   Hardness.lean::clA5Field_native  reproduces  Hardness.lean::clA5Drop_native: 123/225 = 55%
   Hardness.lean::clCopy_separator  reproduces  Hardness.lean::clCopy_pair: 443/811 = 55%
   Hardness.lean::clA5Stop_clean  reproduces  Hardness.lean::clCmp_forward: 77/141 = 55%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clCmp_idle: 80/147 = 54%
   Hardness.lean::clRec_track_inactive  reproduces  Hardness.lean::clRec_row_frame: 179/330 = 54%
   SAT.lean::satAppend_rewind  reproduces  SAT.lean::satAppend_seek: 450/832 = 54%
   Hardness.lean::clPrepare_start  reproduces  Hardness.lean::clRecord_prepare_frame: 151/280 = 54%
   SAT.lean::satStreamRead_word  reproduces  SAT.lean::satReq_fields: 62/115 = 54%
   SAT.lean::satMap_run  reproduces  SAT.lean::satScan_run: 269/499 = 54%
   MeyerTableau.lean::RW_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   MeyerTableau.lean::RI_step  reproduces  MeyerTableau.lean::SS_step: 63/117 = 54%
   CNFEncoding.lean::parseClause_serializeClause  reproduces  CNFEncoding.lean::parseClauses_serialize: 402/747 = 54%
   Hardness.lean::clRead_separator  reproduces  Hardness.lean::clRead_rewind: 432/803 = 54%
   CNFEncoding.lean::parseClauses_bounds  reproduces  SAT.lean::sat_parseClauses_repr: 295/549 = 54%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   SAT.lean::satReq_fields_poly  reproduces  SAT.lean::sat_pt_append: 69/129 = 53%
   Hardness.lean::clA5Map_run  reproduces  SAT.lean::satScan_run: 266/499 = 53%
   SAT.lean::satStreamRound  reproduces  SAT.lean::satStreamTail: 65/122 = 53%
   Hardness.lean::clRecord_prepare_frame  reproduces  Hardness.lean::clRepeat_initial: 65/122 = 53%
   SAT.lean::sat_run_agree  reproduces  Hardness.lean::clCmp_forward: 75/141 = 53%
   SAT.lean::satStop_clean  reproduces  Hardness.lean::clCmp_forward: 75/141 = 53%
   Hardness.lean::clRec_track_inactive  reproduces  Hardness.lean::clRec_track_frame: 194/366 = 53%
   Hardness.lean::clRead_rewind  reproduces  Hardness.lean::clCopy_rewind: 524/991 = 53%
   Hardness.lean::clRec_prepared  reproduces  Hardness.lean::clQuery_initial: 94/178 = 53%
   Snapshot.lean::workCell_succ  reproduces  Snapshot.lean::snapshotAt_state_succ: 77/146 = 53%
   MeyerTableau.lean::incFixed_enumWord  reproduces  MeyerTableau.lean::ctrVal_enumWord: 98/186 = 53%
   SAT.lean::satDrop_rewind  reproduces  SAT.lean::satDrop_skip: 269/512 = 53%
   SAT.lean::satMax_prefix  reproduces  Hardness.lean::clCmp_forward: 74/141 = 52%
   Hardness.lean::clWipe_forward  reproduces  Hardness.lean::clRead_rewind: 421/803 = 52%
   Hardness.lean::clRec_prepared  reproduces  Hardness.lean::clRepeat_frame: 67/128 = 52%
   Hardness.lean::clQuery_initial  reproduces  Hardness.lean::clRepeat_frame: 67/128 = 52%
   Hardness.lean::clMatch_cmp_frame  reproduces  Hardness.lean::clRepeat_frame: 67/128 = 52%
   SAT.lean::satMax_prefix  reproduces  SAT.lean::satDrop_skip: 267/512 = 52%
   SAT.lean::satStop_clean  reproduces  SAT.lean::sat_run_agree: 111/213 = 52%
   Hardness.lean::clA5Stop_clean  reproduces  SAT.lean::sat_run_agree: 111/213 = 52%
   Hardness.lean::clA5InputFragment  reproduces  Hardness.lean::clA5WorkFragment: 112/215 = 52%
   Hardness.lean::clA5Run_output  reproduces  Snapshot.lean::snapshotAt_state_succ: 76/146 = 52%
   Hardness.lean::clHeaderLayout_native  reproduces  Hardness.lean::clRepeatArgument_native: 222/430 = 52%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clWipe_idle: 73/142 = 51%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clInput_idle: 73/142 = 51%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clCopy_idle: 73/142 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clWipe_idle: 73/142 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clInput_idle: 73/142 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clCopy_idle: 73/142 = 51%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clRow_idle: 75/146 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clRow_idle: 75/146 = 51%
   Hardness.lean::clLeft_until  reproduces  SAT.lean::sat_run_agree: 109/213 = 51%
   Hardness.lean::clPrepHeader_native  reproduces  Hardness.lean::clNative_append: 68/133 = 51%
   Hardness.lean::clRead_forward  reproduces  Hardness.lean::clCopy_forward: 138/270 = 51%
   Hardness.lean::clRecWords  reproduces  Hardness.lean::clHeaderLayout: 75/147 = 51%
   Hardness.lean::clOutput_compute  reproduces  Hardness.lean::clLoad_idle: 75/147 = 51%
   Hardness.lean::clOutputAt_compute  reproduces  Hardness.lean::clLoad_idle: 75/147 = 51%
   Hardness.lean::clWipe_backward  reproduces  Hardness.lean::clWipe_forward: 435/855 = 51%
   Hardness.lean::clRepeatCfg  reproduces  Hardness.lean::clLoadCfg: 65/128 = 51%
   Hardness.lean::clRecord_prepare_frame  reproduces  Hardness.lean::clRepeat_frame: 65/128 = 51%
   Hardness.lean::clInputTM  reproduces  Hardness.lean::clReplayTM: 137/270 = 51%
   TQBF.lean::codecRowOf_eq_iff  reproduces  TQBF.lean::codecObserve_congr: 165/326 = 51%
   Hardness.lean::clRead_pair  reproduces  Hardness.lean::clRead_rewind: 406/803 = 51%
   Hardness.lean::clNative_map  reproduces  SAT.lean::sat_pt_mapSnd: 279/552 = 51%
   SAT.lean::sat_pt_pair  reproduces  SAT.lean::sat_pt_append: 65/129 = 50%
   Hardness.lean::clReplay_back  reproduces  Hardness.lean::clCmp_forward: 71/141 = 50%
   Hardness.lean::clRepeat_complete  reproduces  Hardness.lean::clCmp_forward: 71/141 = 50%
   Hardness.lean::clInput_backward  reproduces  Hardness.lean::clCmp_forward: 71/141 = 50%
   SAT.lean::satRed_maxLiteral  reproduces  SAT.lean::satRed_maxOnes: 505/1003 = 50%
   Hardness.lean::clPrepared_idle  reproduces  Hardness.lean::clPrepare_idle: 114/228 = 50%
   Hardness.lean::clA5Next_pack  reproduces  Hardness.lean::clA5Stored_exact: 112/224 = 50%
   Hardness.lean::clPreparedCfg  reproduces  Hardness.lean::clRecordCfg: 91/182 = 50%
   Hardness.lean::clA5Count_native  reproduces  Hardness.lean::clA5Address_native: 74/148 = 50%
   SAT.lean::satReq_fields  reproduces  SAT.lean::satStreamRead_word: 62/124 = 50%
```

## Archive contents and integration

- `REPORT.md`: this report, including the complete duplication outputs and declaration ledger.
- `TCSlib/Complexity/ClassPSPACE/TQBF.lean`: the complete modified source.
- `patches/0001-Prove-the-packaged-TQBF-configuration-codec-and-CNFs.patch`: the one-commit `git format-patch` series against the recorded base.
- `b4a-codec.bundle`: the delivery branch with the base as its prerequisite; `git bundle verify` passes.
- `logs/`: bootstrap and final sweep, target axioms, the probe, lint, freeze and duplication evidence, and delivery verification.
- `verification/`: probe and axiom sources, the exact order list, and environment wrapper/shim source.
- `SHA256SUMS`: SHA256 of every other archive file, using paths relative to the archive root.

Integration is the campaign's `git am -3` workflow. The patch and full source are checked against one another, and the bundle records the same delivery commit. No push or PR was created.
