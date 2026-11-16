# Gate 36 · erratum 1 to the round-2 pack (G36-02)

The paired-control summaries in `pack-r2.md` (lines 104–106) and in `landing-r1/PROVENANCE.txt` (lines 80–83, and its
archived copy) state 7 sealed negatives for coe and 9 for strict. The correct counts, from `controls-plan.json`,
`mkctl-{coe,strict}.log`, `ctlcheck-{coe,strict}.log` and the raw diagnostics, are:

| Variant | Sealed A negatives | Sealed B negatives | Total negatives | Positive-reader failures |
|---|---:|---:|---:|---:|
| coe | 2 | 3 | **5** | 0 |
| strict | 3 | 4 | **7** | 2 (both `ctlCoeReader`, disclosed) |

That gives 9 diagnostics in total for strict. Each variant has four probes, two sealed and two unsealed. Every sealed
negative fails exactly once, every unsealed control passes, and there are no unattributed errors. The pinned files
are not rewritten; this erratum supersedes their counts.
