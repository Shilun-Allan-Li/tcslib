# Gate 106 round-two current evidence

**Not yet clear to merge: #215.** Fresh repaired-source evidence is complete and stable for the selected Codex follow-up. Source/probe/census/replay crosschecks and the fresh complete nine-file screens pass their stated checks. This is maintainer evidence, not an audit verdict, new debt acknowledgment, or gate closure.

The supplied current base is `e3adffac67377a8b6e23bed74bfdbb44a123dd86`; the frozen PR head is `478cd3a8dfb46094b9d8b971662f2ddadb1eccdb`. No Git command was used. `context.json` and `tree-hashes.json` pin the actual source bytes and selected compiled modules independently; `POPULATION.md` and `population.txt` define the same nine-file population for source freeze, compiled census and both screens.

The full TCSlib path/hash comparison finds exactly five changed Lean files: SAT, Tautology, Hardness, CounterLoop and SingleTape. The four originally audited bodies, including Frag, independently match their original/msg3 Git-blob SHA1 and SHA256. Frag's common repair is already in the base; it is not a current sixth diff. The three original Segment-consumer bodies have not changed since their executed seals, so their old seals are retained by identity, not rerun or claimed executed here. Their target remains Segment; the old isolated Frag probe concerns its exact cell-read step, not all unrelated foreign reads.

The source comparison reads every declaration's full balanced header, including private declarations, and compares visibility, order, executable definitions and imports. There are no public additions/removals/header changes, visibility changes, surviving private header changes, or executable definition changes. Source counts remain 1,984 across the population: SAT 270, Tautology 93, Hardness 544, Frag 15, Catalog 505, Basic 93, CounterLoop 79, Primitives 285 and SingleTape 100. The only current public proof changes are the five previously audited CounterLoop proofs; `halfL_run` is now identical to base. The three original private concatenation helpers are replaced by their already audited private Segment bridges. Both SAT/Hardness guard declarations retain their exact headers and surrounding bytes, with proof-body changes only. Imports differ only by the two previously approved Basic imports in Tautology/SingleTape.

New executed checks use plain managed `leanelab.sh`, complete `oleans-msg4`, local slot budget 3, one sequential Lean and no outer lock. The base compiler census uses complete `oleans-mac3`. No source, Git state, snapshot or compiled cache is changed.

| Check | Actual result |
| --- | --- |
| Exact `sat_guard_add`, SAT:4076 | Pass under Segment seal before header |
| Exact `clA5_guard_add`, Hardness:6395 | Pass under Segment seal before header |
| Segment controls, pointwise and fully abstracted | Both pass unsealed; exactly one intended `rfl` failure each sealed |
| Offline diagnostic-checker negatives | Duplicate, missing, and exit-0-with-errors rejected |
| Nine-module compiled census | Non-private 1,349 → 1,349, exact names/owner/kind/internal identity |
| Actual compiled private guard axioms | Both `[propext, Quot.sound]` before/after, exact IDs preserved |
| Six original public axiom prints | Standard three axioms only |

The new seal inputs contain each exact private declaration's original import list and verbatim header/proof body, not the earlier generic substitute proof. Segment is an ordinary `def`; `attribute [local irreducible]` precedes both headers and all controls. Definition-level simp unfolding is explicitly removed. Lean warns that Segment already has no `[simp]` attribute; this benign warning is preserved in the raw logs. Proof inspection finds no `simp [Segment]`, `rw [Segment]`, or `unfold Segment` escape. Both bodies construct and read through `segment_iff`, invoke `Segment.trans`, and use `Set.mem_singleton_iff`; the reflexive endpoint is the identical `runFrom d b` expression on both sides. There is no recreated time-splitting proof or new import/API.

The exact imported private proof IDs are:

```text
_private.TCSlib.Complexity.ClassNP.SAT.0.Complexity.sat_guard_add
_private.TCSlib.Complexity.CookLevin.Hardness.0.Complexity.clA5_guard_add
```

The complete compiled census, including private generated auxiliaries, is 7,099 → 7,087. The six private additions are the three bridge replacements and three generated helpers; the eighteen removals are the three retired concatenation bindings and fifteen generated proof auxiliaries. In particular, each repaired guard loses two arithmetic auxiliaries. This is distinct from both the unchanged non-private census and the unchanged source declaration count. `compiler-census-delta.json` gives every exact name.

The completed parent msg4 replay is **crosschecked, not rerun**: all archived artifact hashes match; the order file exactly matches 329 raw successful module entries; failures 0, static mismatches 0, static total 66. The earlier msg3 total 67 predates the merged Hierarchy proof. Raw current replay receipt and artifacts remain in `../../evidence/round2/current-replay/`; `checks.json` records their independent consistency checks.

Retained debt is separate from the F1 reuse repair. The canonical ledger records Seyoon's five adapter-kind acknowledgment, including correctness/frame companions, plus the separate finite-family shared-bank dispatcher acknowledgment. Current full-code rechecks still give 22 exact prefix-renaming pairs: clean 4, padding 6, release-stop 4, transducer 7 and bridge-overhead 1. Dispatcher correspondence has six non-abbreviation declarations plus one HostState alias per file, after the explicit module-count/routing parameters; concrete HostNext tables remain client data. Neither ruling publishes a new shared API.

The post-F1-repair named unions remain **SAT 34/270 and Hardness 32/544**, including notation and prior named acknowledgment/watch records. These are lower bounds, not an exhaustive cleared census. The old live-prefix watch, wider RO-1 and statement-specific candidates retain their separate status. The 86 historical directed SAT/Hardness candidate labels are preserved in the incoming review; screen edges and endpoint counts are not debt counts. The Segment source is not counted twice. F1's old re-derivations retire on merge; the retained public-API adapters do not reimplement composition.

SingleTape accounting is independently reconfirmed from the actual Segment expressions: six consumer declarations and twelve calls (`dg_init` 3, `dg_collect` 1, `dg_turn_with_growth` 2, `dg_end_with_growth` 2, `dg_step` 3, `dg_simulate` 1). `single-tape-call-quotes.json` preserves the exact closing expressions and line numbers. The immutable round-one pack is not rewritten; canonical erratum/dispositions remain the maintainer's separate records.

The two fresh screens ran serially under the shared `$TCSLIB_SCRATCH/locks/screen` lock, using every archived source byte from the same population. Results are **1,559 → 1,561 eligible declarations; 1,583 → 1,583 directed pairs; 492,990 → 494,807 reproduced normalized characters**. One edge disappears (Basic's `Segment.trans` reproducing retired `tautDual_segment_add`, 91/168); one appears (SingleTape's `dg_turn_with_growth` reproducing `dg_end_with_growth`, 784/1,564). This is the same old in-file near-match, from pre-existing transition scaffolding with public Segment composition substituted. It is not an exact in-file copy or a new composition proof. No new cross-file edge appears.

Against the immutable audited head screen, the entire 1,583-edge set is unchanged. Only the reciprocal SAT/Hardness guard edges' shared lengths rise from 127 to 525 characters each: the two existing adapters now construct/read the public Segment interface. Their bodies are exactly the newly executed seal targets, rather than a fresh time-splitting proof. The extra 796 reproduced characters are explicitly disclosed; a larger raw text overlap is not silently treated as cleared semantic debt. All 86 SAT/Hardness directed edges remain, with per-edge current dispositions and unchanged wider/watch statuses in `current-sat-hardness-candidates.json`. `screen/classification.md` separates metric changes, established reuse, accepted kinds and remaining candidates. No exhaustive census claim follows.

`checks.json`, request/run JSON, exact `.lean.txt` inputs and raw logs distinguish executed results from supplied replay evidence and source-only classifications. The synthetic checker-negative outputs are not additional Lean runs. `execution-notes.md` explains the benign no-simp warnings and a screen timing-field label. `SHA256SUMS` covers every archived file except itself. No broader semantic-reuse clearance or merge permission is inferred.
