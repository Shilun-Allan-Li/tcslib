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

## The changed-files screen (`changed-files/`)

The screen above keeps only `ZoneStep`'s pairs, so it does not cover `Contract.zero` in
`Contract/Basic` or the new equations in `ZoneRebalance`. This one widens both the restriction
and the population:
- **Restriction:** pairs with a declaration of any of the three changed Lean files on one side
  (`screen-changed-pairs.py.txt`).
- **Population:** 22 files, the 20 above and the cited `Deterministic` (`runFrom_zero`) and
  `Configuration`.
- **Commits:** base `683e2adf`, head `0a1b64d5`.

**Result** (`pairdiff.txt`): 562 pairs at base and 559 at head, **no new pair**. Three pairs are
gone, all inside `ZoneRebalance`. The anchor's re-point shortened `zr_pinAnchorContract` and
`zr_host_dispatch_run`, which had paired with `zr_pinTestContract` and `zr_scan_round`.
