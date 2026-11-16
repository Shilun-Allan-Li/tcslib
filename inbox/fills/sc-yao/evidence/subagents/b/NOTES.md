# Evaluation worker notes

Worker `/root/evaluation` owns the six new files `RunWithHost.lean`, `Decryption.lean`,
`FirstTagged.lean`, `EvalGate.lean`, `GarbledRun.lean`, and `BobTables.lean` under
`TCSlib/Cryptography/SecureComputation/Yao/HybridProof/`. The lead owns all other files,
including the copied `CoinRead.lean`; this worker did not change those.

No commit was made. The local branch is `fill/sc-yao-b` at the issue base.
The Mathlib package tree is the lead's read-only symlink. The TCSlib olean tree is this
worker's `.lake/sc-yao-oleans`, initially seeded by the lead with APFS clones.
Every Lean command used `/private/tmp/sc-yao-lean-slot.sh`, tag `sc-yao-b`, under the shared host cap of at most three Lean processes.

## Proved interfaces

- `RunWithHost.orbit_eq` proves the encoded state of every gate prefix.
- `RunWithHost.polyTimeComputable_runWith` proves a generic traversal with an input-dependent
  value type and encoding, a polynomial-time leaf and polynomial state envelope.
- `RunWithHost.exists_machine` gives one clean machine with a polynomial time budget and
  an all-time work-head envelope for that same machine, using H14.
- `specialDecTagged_poly` handles separate unary key and message lengths, hence both
  `n` and `4n+2` message lengths in nested special encryption.
- `nestedDecTagged_encoded` and `nestedDecTagged_poly` give exact semantics and total
  polynomial time for nested special decryption, with an unambiguous success marker.
- `firstTagged_encoded` and `firstTagged_poly` implement the first successful row by the
  existing bounded first-index host, without a new traversal implementation.
- `evalGateWord_encoded` and `evalGateWord_poly` give exact generic garbled-gate semantics
  and total polynomial time, including malformed ciphertexts and missing vertex values.
- `evalGateAppendWord_encoded` supplies the exact append contract needed by `runWith`.
- `garbledRunWith_poly` composes the leaf and traversal. Its caller supplies polynomial-time
  parameter, gate-list and initial-key maps and a polynomial-time current-table selector,
  plus the gate-argument and table-selector equations. All state and round envelopes are
  derived from these polynomial-time maps; no separate orbit-bound hypothesis is required.

- `BobTables.tableSelector_poly` reconstructs the current table on arbitrary raw host words;
  `tableSelector_host` supplies its exact canonical-host equation, without a Yao definition.

## Reuse and overlap

Searches included `runWith.*polyTime`, `polyTime.*runWith`, stateFind/iterate/blockMap,
word lookup/count/map, firstIdx/findSome, encWords/decWords normalization, getD map/default,
and tagged decryption. Sources and search commands are recorded in the raw tool history and
`reuse-search.log`; final signatures and dependency traces are in the probe outputs.

- The host reuses `Randomized/Repetition.lean:241` (`polyTimeComputable_stateFind`) and
  `DAGCircuit.lean:153-175` (nil, append, singleton, length readers). No CVAL machine is used:
  it is a language decider and cannot return generic data-dependent vertex values.
- The machine contract reuses `Build/ModuleHost.lean:319` (`clean_install`) and `:244`
  (`Clean.envelope`) directly, rather than copying their time-to-space arguments.
- `specialDecTagged_poly` generalizes the existing `SpecialEncryption.lean:214`
  `polyTimeComputable_spDecFun`, whose published statement fixes message length to key length.
  Its three length tests and prefix/XOR closure shape are the nearest relative; the existing
  fixed-length adapter cannot implement the outer `4n+2` layer. The new adapter uses
  `spDecStr_eq`, pairing, length, prefix/suffix and XOR contracts. No private lemma is copied.
- The key checker uses `Asymptotic/Adversary.lean:197` (`decodeFin_eq_some_iff`).
- First-success search reuses `ZeroKnowledge/EncodingMachines.lean:324`
  (`polyTimeComputable_firstIdx`) and its first-index characterizations, plus
  `BinaryArith/Loops.lean:375` (`getW_pairEncode`) and `Words.lean:361` (`countW_eq`).
  The inline prefix argument specializes `List.findSome?_eq_some_iff`; it does not
  reimplement a scan. Canonicalization uses the public `mapW_pairEncode` contract.
- `keyLookup_encoded` has an inline alternate-default argument for `List.getD_map`'s shape.
  It splits the public optional lookup reader, uses `padFin_ofFn` on an available key,
  and reuses `Games/BitCodec.lean:151` (`padFin_nil`) and `zeroBits_apply` otherwise.
  This is necessary because encoded-word lookup defaults to `[]`, whereas vertex lookup
  defaults to the zero vector. No getD/ofFn/window lemma is copied.
- Encoded append and list lengths reuse `BinArith.encWords_append_singleton` and
  `length_encWords_le`. Suffix lengths reuse `iterate_pairSndD_encWords` and
  `length_iterate_pairSndD_le`. Polynomial envelopes reuse `output_length_le`.
- The raw `BobTables` selector is the generic machine-side reconstruction corresponding
  to `Yao.lean:425` (`yaoBobTables_eq`). It is not a semantic circuit-family definition:
  it takes polynomial-time input-count/message selectors, counts an encoded host value list,
  normalizes the selected raw table, and returns encoded rows. Its canonical-host equation
  lets the owned target body connect the machine to the frozen Yao reader. It reuses
  `polyTimeComputable_reencodeWords`, `countW`, `getW` and `unarySub_poly`.
- No declaration was rederived from the unmerged sc-garble, #318, or sc-compose helpers.
  The evidence seal generator is adapted from sc-garble's evidence tool at exchange
  commit `8313d3d29df28270e956b67379b927c18475b873` (the path's last change); this is tool
  reuse, not a Lean proof copy. The generator changes the issue base and output directory.

## Host promotion and draft registry row

Request promotion of `RunWithHost` and the garbled-evaluation specialization to the shared
circuit/randomized construction layer after the unit gate. Proposed row:

| Row | Contract | Status | Consumers |
|---|---|---|---|
| H-SY-eval (draft) | Encoded topological gate evaluation, generic in gate records, input-dependent value types, leaf step, initial values and polynomial round/state envelopes. `RunWithHost.exists_machine` supplies one clean machine, its uniform polynomial time envelope, and an all-time work-head envelope for the same machine. `garbledRunWith_poly` derives the envelopes for fixed-width keys from the polynomial-time input constructors. | Proved in sc-yao; request promotion and registry review at landing. | Yao's Bob evaluator, fake-garbling simulator and reduction reconstruction. |

## Validation

The passing development logs are `runwithhost-03.log`, `decryption-02.log`,
`firsttagged-03.log`, `evalgate-03.log`, `garbledrun-02.log`, and `bobtables-02.log`. The intermediate
failed logs are retained, and both `error:` and `error(...)` forms are counted.
The final whole-file seals, paired controls, signatures, axioms and dependency trace
are recorded separately under this evidence directory. All six files are new at the
issue base, so their base seal manifest records `ABSENT_AT_BASE`.

Final evidence: 24 current-source whole-file seals (A/B, strict/coe) pass with zero errors.
The retained history has 28 successful seal runs, including the four refreshed after a
docstring-only variable-name correction. All eight paired controls behave as required:
four unsealed controls pass; each of four sealed controls fails exactly once. The complete
83-constant signature/axiom/closure probe finds only `propext`, `Classical.choice`, and
`Quot.sound`, and no sorry dependency for any stored constant. The six-file source scan
finds no admission, explicit unfold/delta, width violation, or size violation. Its only
`dsimp only` reduces local let/beta expressions without naming a foreign definition.
See `verification-summary.json`, `current-source-seals.json`, `source-scan.json`, and the
complete raw logs and source snapshots under `probe-runs/`.
