# Reproduction and execution record

Every shell command sourced `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/env.sh` first. All Python used `python3 -I`. Wrapper executions used authorized scratch access for the managed slot locks, with `TCSLIB_LEAN_SLOTS=3` and no nested lock.

The clone command is recorded exactly in `clone-receipt.json`:

```sh
/bin/cp -cR /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-msg4/. /private/tmp/tcslib-g106-r3-integrated-4trrpdy7/overlay
```

After verifying all clone hashes, these driver calls ran sequentially:

```sh
source /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/env.sh
TCSLIB_LEAN_SLOTS=3 python3 -I campaign/gates/106-sg1-dedup/review/round3-integrated/compile-module.py TCSlib/Complexity/ClassNP/SAT.lean
TCSLIB_LEAN_SLOTS=3 python3 -I campaign/gates/106-sg1-dedup/review/round3-integrated/compile-module.py TCSlib/Complexity/CookLevin/Hardness.lean
```

Each driver unlinks that module's existing overlay output, records its old hash, then executes `leanelab-o.sh WORKTREE OVERLAY SOURCE OVERLAY`. `SAT-compile-run.json` and `Hardness-compile-run.json` retain the complete expanded argument lists, timings, source hashes, output hashes and log hashes. This writes only to the private complete overlay.

```sh
source /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/env.sh
TCSLIB_LEAN_SLOTS=3 python3 -I campaign/gates/106-sg1-dedup/review/round3-integrated/run-metadata.py Metadata-roots-census-v1
TCSLIB_LEAN_SLOTS=3 python3 -I campaign/gates/106-sg1-dedup/review/round3-integrated/run-metadata.py Metadata-whole9-axioms-v1
```

These plain probes ran `leanelab.sh WORKTREE OVERLAY TEMP_SOURCE`, with no compiled output. Full expanded commands and input/output hashes are in their `*-run.json` receipts. Probe sources are archived as `.lean.txt`; no additional `eq_def` materialization or private-name alias is added.

```sh
source /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/env.sh
python3 -I campaign/gates/106-sg1-dedup/review/round3-integrated/parse-metadata.py
python3 -I campaign/gates/106-sg1-dedup/review/round3-integrated/verify-artifacts.py
```

No Lean attempt failed in this folder. A standalone read-only inventory preview mistakenly treated the saved dictionary as a list, producing the retained `inspection-failure.txt`; it was corrected to inspect dictionary keys. It ran no Lean and mutated no artifact.
