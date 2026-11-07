# Branch reader proposal: bounded pre-ship evidence

2026-11-07. **Not yet clear to merge.** This folder tests an API proposal and a conditional
consumer; it adds no library API and does not accept cp02 or close its `branchTM` exclusion.
Seyoon's approval remains required before publishing a new public reader.

The useful result is concrete: explicit `k`/`State` reader transport works with `branchTM`
sealed. A run-independence contract stated over the explicitly transported raw machine
then supports a sealed conditional right-bank consumer without reducing a foreign
transition table. The actual `condTM`/`timedCondTM` host premise and complete cp02 consumer
chain have **not** been discharged here.

## Context and execution

- Import context: `TCSlib.Complexity.TuringMachine.Simulation`, Lean `v4.25.0`.
- Complete snapshot: `oleans-mac2`, adopted at
  `3555163f40d9c101a2ef4e81407c1bda58fe5ca4`; adoption receipt is
  `campaign/status/2026-11-07-natbits-merge/receipt.json`.
- `context.json` records full Git/object pins, source SHA-256 values and compiled module
  hashes. Current `Simulation.lean` and `Deterministic.lean` match that snapshot's source
  base byte for byte.
- Each `.lean.txt` was read before running. `run_probe.py` copied it to a unique
  `/private/tmp/tcslib-branch-reader-*/*.lean`, then invoked only the repository's
  `devtools/seyoon/leanelab.sh` against that full snapshot. One Lean process at a time,
  local slot budget three, shared slot locks, four Lean threads and `nice 10`.
- Every run has its original `.out` and `-run.json`, including actual command, timing,
  exit, diagnostic count and input/output hashes. `results.json` checks those hashes and
  records all outcomes. No source, API, Git, compiled snapshot, cache, or screen mutation
  was made. Only this output folder and unique temporary probe files were written.

## Actual results

| Probe | Exit / errors | Meaning |
| --- | --- | --- |
| `Contracts-v1` | 1 / 1 | Preserved first attempt: the state equality needed parentheses around the sum type. |
| `Contracts-v2` | 0 / 0 | Original shape and raw run-independence statements prove in the proposed home context with `runFrom` sealed. |
| `TypeTransport-v1` | 1 / 1 | Explicit transports elaborate, but their round trip fails at bare `rfl`. |
| `TypeTransport-v2` | 0 / 0 | The round trip closes with `eq_mpr_eq_cast`, `cast_cast`, and `cast_eq`, keeping `branchTM` sealed. |
| `TransportedConsumer-v1` | 0 / 0 | Primary refined run statement and sealed conditional consumer pass. |
| `Controls-unsealed` | 0 / 0 | Eight direct-definition controls all pass without the seals. |
| `Controls-sealed` | 1 / 8 | The same controls all fail, exactly two per sealed definition. |

All five named declarations printed by `TransportedConsumer-v1` depend only on
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom is present.
These include the three proposal theorems and the two probe-only consumer theorems.

## Concrete proposal and the necessary refinement

Proposed home: beside `branchTM` in `Simulation.lean`, without definition/import changes or
new `simp` attributes. The three proposed names are:

1. `Turing.FinTM.branchTM_k`, giving `(branchTM M₁ M₂ b).k = M₁.k + M₂.k`.
2. `Turing.FinTM.branchTM_State`, giving
   `(branchTM M₁ M₂ b).State = (M₁.State ⊕ M₂.State)`.
3. `Turing.FinTM.branchTM_runFrom_independent`, giving equality of arbitrary-start runs at
   every finite time for any two Boolean tags, **after explicit transport of each bundled
   machine to the shared tape/state carrier**.

The exact tested declaration and proof are in `TransportedConsumer-v1.lean.txt:25`.
Its statement binds a local `view` by rewriting the tape/state types with the first two
readers. That is a `let` inside the theorem statement, not a new public definition. The
statement therefore exposes the required dependent conversion instead of relying on a
consumer to treat an opaque bundled projection as its implementation type. Its proof
uses the existing `agreeOn_iff` and `runFrom_eq_of_agreeOn` equations; it never unfolds
`runFrom`. The Boolean changes the initial state, and an arbitrary-start run depends on
the transition table, which is independent of that Boolean.

`Contracts-v2` preserves the earlier untransported statement and its proof. That proof
alone is not the consumer pre-ship result. Use the explicitly transported statement when
reviewing this proposal. `TypeTransport-v2` also proves that explicit configuration
transports cancel using published core cast equations; no unsafe reducibility override
or relaxed transparency option was used.

## Sealed consumer scope and limits

`TransportedConsumer-v1.lean.txt:43` seals `branchTM`, `runFrom`, `rightCfg`, and
`rightAction` **before** the consumer helpers and theorem headers. The probe-local
`branchView` is precisely the statement's explicit carrier transport. It is evidence
plumbing, not an additional proposed public API.

The conditional consumer's sole table-agreement premise says that the actual host
agrees, on the embedded states, with the **fixed false-tag transported machine**. It uses
the published `rightCfg_run` to obtain that fixed-tag run, then the proposed independence
contract and `congrArg` to replace the tag by the selected one. The conclusion is equality
of complete configurations for arbitrary start data, inactive tapes/heads, selected tag,
and time. This preserves the branch semantics conditional on that stated premise.

This establishes that a branch definition occurring in dependent types can be handled by
published shape equations and explicit transport. It does **not** establish that the
existing `condTM` proof can retain its header or table premise unchanged. Instantiating
the real host, its prefix/start configuration, and all downstream Composition/Wrappers
uses remains necessary before calling the final API sufficient or closing the exclusion.
The ten separate configuration-field readers in `checkpoints-2026-11-07/API-REVIEW.md`
remain a separate approval scope.

## Seal inventory and argument inspection

The four effective consumer seals are `MultiTapeTM.runFrom`, `FinTM.branchTM`,
`FinTM.rightCfg`, and `FinTM.rightAction`. None has a definition-level `simp` attribute to
remove. Controls give a direct delta goal and its complete defining equation for each;
the negative diagnostic lines are 11, 13, 17, 27, 32, 38, 42, and 47 in
`Controls-sealed.lean.txt`.

In the proposed home section, `branchTM` and the same-home table/embedding declarations
may be read; `runFrom` remains sealed. The public agreement theorem is an opaque existing
theorem, so its internal proof is not re-audited as a new definition read. In the consumer,
only the probe's own `branchView` may reduce. No other-file TCSlib definition occurs in a
`simp`, `rw`, or `unfold` argument. `rw` names only the two proposed shape lemmas or the
existing `agreeOn_iff`; the transport round-trip's `simp only` names only core cast
equations. The only new-home `rfl` proofs compare the branch shape or identical transition
tables; the primary sealed consumer contains no `rfl`.

No reducible TCSlib abbreviation is reached by these probes. `step`, initial-configuration
definitions, and space/visited-set definitions are not directly read by the conditional
consumer and are outside this bounded seal. This is not a global Simulation or cp02 seal.
