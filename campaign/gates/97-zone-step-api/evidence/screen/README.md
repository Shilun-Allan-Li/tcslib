# Gate 97's copy-text screen (v3, restricted)

- **Script:** `screen-zonestep-pairs.py.txt`, the head's `scripts/copy-text-screen-v3.py` with one
  line added: only pairs with a `Build/ZoneStep` declaration on one side are kept (as gate 95's NF
  screen kept `NDNormalForm`'s). `ZoneStep` is new, so every such pair is new.
- **Population:** `population.txt`, 20 files: `ZoneStep`, the zone layer, the contract library,
  the state-renaming and configuration facts, G5's consumer `Robustness/TwoTapes`, and the files
  with time-bound arithmetic or contract compositions (`TimeConstructible`, the clock machines,
  `StepClock`, `CounterLoop`, `Loop`, `Catalog`, `Primitives`, `CodeSimulator`).
- **At the first head `6b989e08`** (`superseded-6b989e08/`): one pair, `ZoneStep`'s private
  zero-time contract against `ZoneRebalance`'s private `zr_anchorContract` (99%). Fixed by the
  public `Turing.Contract.zero`, which both now use.
- **At the final head:** `screen-head-zonestep-pairs.txt`, 1,991 declarations, **no pair**.
- `status.txt`: each run's exit status, commit and time.
