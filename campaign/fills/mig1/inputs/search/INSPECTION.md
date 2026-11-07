# Forwarding API candidate inspection

The fresh search enumerated **104 refs / 76 distinct TCSlib trees**, covering both open PRs,
prepared local/remote Lean heads and available delivery refs. Every ref/full commit/tree was
resolved and checked with Git. The three proposed full public names have **zero declaration
collisions** in those searched trees. This is candidate enumeration and inspection, not a
claim of semantic exhaustiveness.

The broad raw pattern deliberately overselects ordinary pairEncode uses, FP closure,
projections, padding and other unrelated formulas. All raw results are retained. Focused
formal-header candidates and the explicitly inspected existing time-only row are in
`formal-shape-candidates.json`.

| Actual reusable material | Disposition |
|---|---|
| Primitives' `computesFunInTime_pairMapSnd` | Existing existential time-only row; it supplies no named witness with the intrinsic space contract. The approved consolidation repoints this row. |
| Catalog's `computesFunInTime_pairMapSnd_spaceUsed` and private `a2_mapTM` | The canonical forwarding implementation and its time/space arguments; move these to the named witness's approved Primitives home, then make the existing row a corollary. No third implementation. |
| Catalog's strip-last candidates | Different function, with final-marker search and rejection; keep/use their existing named spec, not a second forwarding-map API. |
| Higher-level polynomial-time pairing/closure and ordinary pair-encoding applications | Consumers or different formulas; they are not another named forwarding machine or a proof of the two proposed same-witness specifications. No extra cleanup or new debt acknowledgment is inferred. |

The two open PRs add no forwarding API. NatBits overlaps Encoding and Catalog mechanically;
its diff does not implement the forwarding controller. SG-1 has no owned-file overlap. The
separate prepared Hierarchy consumer changes only Hierarchy's import/proof, with no forwarding
name or contract. The worker remains pinned; the maintainer handles later integration.
