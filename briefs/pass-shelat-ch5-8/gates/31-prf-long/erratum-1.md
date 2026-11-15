# Gate 31 · erratum 1

The pack is shipped and is not edited; this records one correction. The records pin stays
`9cc4db6204a9965da907471603993e9c24d105d2`, and the exchange outbox `outbox/gates/31-prf-long-gate/` is unchanged.

| # | Pack location | Erratum | Found |
|---|---|---|---|
| E1 | Target and base, the PR-base-to-tip bullet ("138 tip modules are downstream of both a #314 module and a PR module"; `pack-checks/deltacheck-tip.txt` in `verification.zip`) | The count of 138 included `briefs/` evidence `.lean` files: `deltacheck.py` builds its import graph from every `.lean` file in the tip tree, so evidence probes that import TCSlib modules were counted as downstream. Restricted to `TCSlib/` and `audits/` modules, by the corrected method used for Gate 32 (`gates/32-headd-promote/`, `pack-checks/downstream314.txt`), the count is **85** (138 = 85 + 53 `briefs/` files). Nothing else in the pack changes: the merge tree, the closure statements and the pending merge condition are unaffected. | 2026-11-15, Gate 32 staging |
