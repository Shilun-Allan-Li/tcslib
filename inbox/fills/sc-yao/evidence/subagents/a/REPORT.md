# Decoder and Alice garbling sub-agent handoff

Agent: `/root/decoder` (slot tag `sc-yao-a`), branch `fill/sc-yao-a`, worktree
`/Users/seyoonr/.codex/worktrees/sc-yao-a/tcslib-exchange`.
Base: `6ce4658db08a1dc2a03a149987197660db078011`. No sub-agent commits or pushes.
The lead owns the three frozen source files and final integration/checks.

## Completed proof contracts

All ten owned modules check with zero errors, zero warnings, and no admissions.

| Module | Final semantic check log | Main result |
|---|---|---|
| ChunkScanner | `logs/chunk-scanner-04.log` | Generic finite word-emission scanner; same clean machine with polynomial time/head envelope |
| DescriptionDecoder | `logs/description-decoder-05.log` | Total decoder and canonical circuit/output-word correctness; same clean machine with time/head envelope |
| CoinGarbling | `logs/coin-garbling-01.log` | Polynomial-time key/row-nonce/shift addressing from supplied equations |
| Garbling | `logs/garbling-03.log` | Total nested-encryption adapter; bounded gate/argument-key computation; arbitrary constant enumerations |
| WordLists | `logs/word-lists-02.log` | Encoded vectors from total indexed word adapters using the existing public loop |
| RowFromCoins | `logs/row-from-coins-09.log` | Complete raw row machine, arbitrary output-bit core, seed-reader semantic bridge and pointwise normalization |
| TablesFromCoins | `logs/tables-from-coins-03.log` | Guarded table assembly, arbitrary row-family core, exact garbled-table bridge |
| AllTables | `logs/all-tables-04.log` | Complete raw all-table program, indexed context transport, exact outer table-vector bridge |
| GarblingProgram | `logs/garbling-program-02.log` | Actual garbled-table vector polynomial-time from circuit/seed readers, with no indexed reconstruction hypothesis |
| AliceProgram | `logs/alice-program-04.log` | Actual selected-key vector, output-key-pair vector and complete first-message polynomial time |

After the listed semantic checks, only line wrapping changed in DescriptionDecoder and
RowFromCoins. The supporting ChunkScanner host was strengthened and checked after all other
modules: its value function and polynomial-time theorem remain identical. The lead runs the
final sweep on the merged tree.

`AliceProgram.message_poly` is the integration interface. It takes polynomial-time raw
width/bound/input-count/Alice-count/output-count/description/input/coin maps, the circuit and
seed families, canonical description shape, input/output vertex bounds, fan-in two, and the
key/nonce/XOR-shift equations. Its conclusion is exactly the pair of encoded actual garbled
tables and the pair of selected keys and output decoding pairs. No polynomial-time garbling,
row reconstruction, or indexed transport hypothesis remains for the consumer to prove.

The key and nonce equations hold on arbitrary short tapes through false padding. Zero key
width, zero input/output counts, constant gates, one-argument gates and arbitrary constant
assignment enumerations are covered. Raw table adapters guard arity greater than two; this
keeps malformed description words inside the polynomial-time contract.

## Rule 10 and overlap/reuse

Consumers use public readers throughout. The lead must run the required whole-file seals,
axiom/dependency closure trace, header checks and global clash scans. This handoff does not
claim those lead-only final checks have already passed.

Searches used `rg` over TCSlib and the pinned Mathlib tree for polynomial-time decoders,
finite-list/table maps, `dbl_append`, `getD`/`ofFn` readers, word-list encoding, bit/address
maps, transducers and loop contracts. Canonical reuse includes:

- `DAGCircuit.decode_encode` is the existing validating decoder. The new host recodes gate
  records for computation, is total on arbitrary words and does not duplicate validity checks.
- `DescriptionDecoder.dbl_pair` uses `MultiMsg.dbl_append`,
  `Encryption/PrivateKey/FromPRF/ReductionMachine.lean:235`. The initially drafted local
  `dbl_append` was removed before any decoder check. The import was explicitly approved.
- `Garbling.fixedTable_poly` re-derives the finite native-function list assembly of private
  `Complexity.clNative_fields`, `Complexity/CookLevin/Hardness.lean:4000`. The private function
  uses `clFields`; it is inaccessible and outside the allowed import closure. The new generic
  proof uses public `PolyTimeComputable.pairEncode` and `BinArith.encWords` readers. This
  private overlap must remain explicitly disclosed in the lead report.
- `WordLists.rangeTable_poly` directly reuses
  `ColMachines.polyTimeComputable_flatMap_range`; `ofFnTable_poly` directly reuses
  `TCSlib.Cryptography.ofFn_eq_map_range`. The ThreeColoring.Machines import was approved.
- `Garbling.spEncStr_poly` directly reuses `polyTimeComputable_spEncFun` and NUPPT layout
  readers. The total word-list nested adapter is identified with `nestedSpecial_enc`.
- `Garbling.gateOut_small` specializes `gateOut_eq_eval` and `DAGGate.eval_eq` at arity at
  most two. Its nearest private relative is the upstream `map_range_getD_ofFn` bridge in
  Garbling.lean, but this proof uses the public gate readers and core Boolean/list equations
  rather than copying the general private lemma.
- `Garbling.argKeys_small` uses `argKeys_eq`; its private keyList_small bridge uses the
  public word-list encoder and core finite-vector readers at the three bounded arities.
- `ChunkScanner.flatMap_scan` is a stateful-control analogue of BitLists.flatMap_range_drop;
  the latter cannot express the changing finite phase. The scanner's state envelope reuses
  the projection bounds and the public emitting-loop assembly.
- `RowFromCoins.assignmentFold_eq_two` gives the exact two-bit fold formula. Its unmerged
  relative is `GarblingProbability.assignmentFold_small`, sc-garble
  `Garbling/CoinBlocks.lean:38`, which instead proves a bound and injectivity. No sc-garble
  declaration is imported or used. The remaining coin-address lemmas do not reproduce
  sc-garble's independence/injectivity statements.
- No PRF hybrid, B1 proof, probability-switch lemma or list-window identity is re-derived.
  The current modules do not use sc-ot or sc-compose helpers.

`rowWordWith_poly` takes an arbitrary polynomial-time output-key selection bit. The real
row wrapper supplies its computed gate bit; fake rows can supply false. `tableWordWith_poly`
accepts any polynomial-time row family at each of the three arities, so simulators can reuse
both the coin-addressing core and the guarded constant-enumeration layer.

## Host promotion and draft registry row

Request promotion of DescriptionDecoder to the circuit-complexity construction layer and
registry review with this unit, per SY-4. The supporting generic ChunkScanner is public and
also exposes a clean-machine/head-envelope contract. Neither is a private host.

Draft row in machine-library-design.md section 14's four-column format:

| ID | Host | Status / provenance | Consumers |
|---|---|---|---|
| H-SY-decoder (draft) | Circuit-description recoder: DescriptionDecoder.decodeDescription_host. One H14 clean-install machine maps a paired circuit description/output word to the unary input count, encoded gate records (kind plus encoded unary arguments) and unchanged output word. Canonical correctness holds for every DAGCircuit, without a fan-in restriction. The same machine has a polynomial first-halt time bound and all-time work-head envelope. | Proved in sc-yao; public generic contract under SY-4. Promotion requested to Complexity/CircuitComplexity; registration and landing gate pending. Built from the public emitting loop, finite Boolean branching, pairing, and H14 clean_install/Clean.envelope. | Actual Alice garbling and output decoding; garbled-evaluation program; simulator/reduction reconstruction. |

## Evidence and provenance

Every Lean/check invocation used the shared slot wrapper and tag `sc-yao-a`; no Lake command
was run by this sub-agent. `.lake/packages` is linked to the lead and this worktree has its
own APFS-seeded TCSlib olean tree. The host-wide cap is three Lean processes, shared with all
other jobs. The lead supplied and checked macOS preflight/cache/bootstrap evidence.

Raw logs and error summaries count both diagnostic forms `error:` and `error(...)`.
`check-module.sh` snapshots each source before checking it and logs UTC start/end/status.
The initial ChunkScanner/CoinRead/CoinGarbling checks and the first two Garbling checks
predate that runner; their retained source versions are under versions/. `chunk-scanner-01.reconstructed.lean` and `garbling-01.reconstructed.lean` are
explicitly labelled deterministic reconstructions made by reversing the recorded edits from
the saved second versions. Their raw failing-log line anchors agree, as recorded in
logs/initial-version-reconstruction.log. They are not represented as original byte snapshots.
All later failed source versions are direct pre-check snapshots beside the logs.

The long AllTables-02 attempt finished itself with a dependent-domain matching error after
137.54 seconds. Its process sample is retained. Resource sampling showed about 2.17 GB RSS
and 5.66 GiB host headroom. An intended own-PID interrupt found that PID already absent;
no process was killed. The repair names the natural arity before comparing dependent
enumerations and freezes row data pointwise. AllTables-04 passes in 6.31 seconds. This was
not an E-RES result or a timeout-based proof claim.
