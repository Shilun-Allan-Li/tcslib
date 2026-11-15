# seq-zk-a status

Agent: `/root/zk_route`, host slot tag `seq-zk-a`, local branch `fill/seq-zk-a`.
Worktree: `/Users/seyoonr/.codex/worktrees/seq-zk-a/tcslib-exchange`.
Own olean tree: `.lake/seq-zk-a-oleans` (empty; no Lean command has run).
Packages: `.lake/packages` is a symlink to the lead's exact-pin packages, read-only for this agent.

## Source

`TCSlib/Cryptography/Composability/SequentialZK/Normalization.lean` is 98 lines, at most 94
characters per line. It contains no admissions and no new simp attributes. Its proofs remain
unchecked while the lead bootstraps the import closure. Only the lead may commit or deliver.

The new declarations are:

- `encodeMsgs_eq_encWords`: general bridge, re-derived from published nil/cons readers.
- `normalizeMsgs`, with `normalizeMsgs_eq`: exactly p slots decoded with empty defaults and
  truncated to B bits.
- `length_normalizeMsgs`: exactly p output slots.
- `length_le_of_mem_normalizeMsgs`: each output message has at most B bits.
- `normalizeMsgs_encodeMsgs`: fixed point for canonical bounded p-slot inputs.
- `length_encodeMsgs_normalizeMsgs_le`: encoding size at most p*(2*B+2).

## Overlap and reuse

The encoding bridge exactly matches the local `have henc` inside
`SecureComputation/Yao.lean:352`. That provider is outside the allowed supplied closure;
this helper derives the general statement from the public equations of both encodings.
The same representation occurs as `ThreeColoring/Machines.lean:911`'s
`encodeMsgs_eq_flatMap`; using the generic Words module avoids graph-specific imports.
Requested eventual promotion: place a general Strategy/BinArith encoding bridge beside
Strategy.encodeMsgs in ZeroKnowledge/Interaction.lean during a shared-file window.

The size bound specializes public `BinaryArith/Words.lean:81 length_encWords_le`, which the
proof directly reuses. Its count and per-message prerequisites are the new normalization
invariants. The pre-existing `CommitmentLemmas.lean:241 length_encodeMsgs_le` gives the
same generic bound for Strategy.encodeMsgs but introduces a larger cryptographic dependency.
The per-message bound uses List.length_take and Nat.min_le_left (the same arithmetic as
List.length_take_le). This is the normalization-specific consequence, not a replacement
for a generic take lemma. The fixed-point theorem reuses decWords_encWords and
List.take_of_length_le; no decoder or list host is copied.

## Scope

The un-applied `scope-StatZK-iff.patch` was requested by the lead after independent discovery
of a missing StatZK reader. The lead reports Seyoon has approved and the lead has applied
that reader. This agent edited no frozen file.

## Assessment

No mathematical counterexample was found in static review. `route-assessment.md` records
phase reconstruction, normalization, an explicit phase-auxiliary polynomial bound, advice,
and edge cases. It is an assessment, not a checked proof.

## Evidence

`searches.log` records repeated key source searches, including Mathlib source read-only.
`searches.md` records the API review. `width.log` records the helper's size and width.
No Lean/Lake/probe/check/seal logs exist because none has run yet.

## NormalizationMachine continuation

The lead approved `NormalizationMachine.lean` and its precise import of the public
`ColMachines.polyTimeComputable_flatMap_range` from ThreeColoring/Machines.lean:159.
The helper now has three untested theorem blocks and no admissions:

- `polyTimeComputable_encWords_decWords` directly specializes BinArith's mapW host to the
  identity payload. Nearest published relative: BinaryArith/Words.lean:221
  polyTimeComputable_mapW, with its arbitrary-raw-word reader at line 208. No host is copied.
- `polyTimeComputable_decWords_getD` directly composes that canonicalization with
  BinaryArith/Loops.lean:391 polyTimeComputable_getW and line 375 getW_pairEncode.
- `polyTimeComputable_encode_normalizeMsgs` uses these lookup operations, the public
  EncodingMachines.lean:459 truncate_poly, and ThreeColoring/Machines.lean:159's counted
  emitter. Its loop proof is reused, not duplicated. The only hypotheses are polynomial-time
  raw data and unary-computable slot count and bit cap. No extra size premise is needed.

Potential promotion request: the generic canonicalization and decoded-lookup statements
belong beside the BinaryArith word-list hosts at a future shared-file window. The generic
counted emitter already has a public provider, so no reimplementation is requested.

`normalization-machine-searches.log` records searches across TCSlib and Mathlib before
implementation. `normalization-machine-width.log` records its width/size check. Still no
Lean command has run; lead bootstrap readiness is pending.

## Checked results

After the lead seeded the prerequisite oleans into this agent's private olean tree:

- Normalization.lean passed its first check, with no diagnostics; maximum RSS 1,564,000,256
  bytes and 1.80 seconds wall time for compilation. A normal shared-slot wait preceded it.
- NormalizationMachine.lean's first check found one proof error: the lambda identity map
  requires the published core lemma List.map_id' instead of List.map_id. It also reported
  two unused simp arguments. Both source blocks were corrected individually.
- NormalizationMachine.lean passed check 02 with no diagnostics; maximum RSS 2,213,593,088
  bytes and 2.31 seconds compilation wall time.

Every check used LEAN_SLOT_TAG=seq-zk-a, the assigned TCSLIB_OLEANS, the issued host wrapper,
/usr/bin/time -l and scripts/lean_check_tree.sh for exactly one module. No lake command ran.
The raw failed attempt is retained. check-summary.json counts both error: and error(...) forms;
slots.log records this tag's acquisitions and releases, including timestamps for the first
normalization check whose raw log contains only the time report. Source widths and SHA-256
are in final-width-and-hashes.log. Axiom, seal and campaign-lint checks remain the lead's
final merged-branch responsibility.
