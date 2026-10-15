# Extract: machine-library-design.md §14 (lines 3024-3086 at dc891632), verbatim, for brief point 5

## 14. Hosts first: the rule and the host registry (user, 2026-10-12)

**The rule** (`policy.md` §1, **Hosts come first**; `workflow.md` §2 and §4,
ground rule 4). A *host* is a control structure that drives other routines:
a search or traversal, a recursion or evaluation scheme, an interpreter step
block, a clocked or windowed runner, a dispatcher over a data structure, or an
input device. A host is never built `private` inside the proof that first
needs it. Its public contract is designed and statement-gated first, generic
in what its consumers vary, with time and head-envelope clauses; consumers
cite it, proved modulo while its fill runs. Leaf rows (copy, compare, seek,
arithmetic) are not hosts and keep the §4 rule of admission.

**Why** (the library-reuse assessment of 2026-10-12, four read-only reviews of
the tip `3462c1b4`). The configuration-level calculus (§12–§13: framed sweeps,
`scanTM`, seams, the phase host, R1 embedding, symbol lifts, counter loops,
configuration records) is general: alphabet-generic, with exact time, framing
and head envelopes. Overfitting entered one level up, where every theorem got
its own private host, because the briefs' ground rule 1 made new helpers
private by default:
- NP ⊆ PSPACE's evaluation host (`SpaceComplexity/Inclusions.lean`, about 70
  privates), S1b's BFS and windowed pieces (private by `briefs/ch34-s1b.md`,
  which lists three promotion candidates), B4 membership's assignment walker
  (private by `briefs/ch34-b4-mem.md`), and Cook–Levin's machine-to-formula
  kit (private in `CookLevin/Hardness.lean`);
- four configuration encodings (`coreCode`, `cfgRecord`, B4a's bit rows,
  Cook–Levin's snapshot blocks) and three reachability notions (configuration
  reachability in `ConfigGraph`, `Complexity.GraphReach`, `Kruskal.Reach`),
  none linked to Mathlib's `Digraph`/`SimpleGraph`;
- about 300 `f2_` private copies in `Build/Catalog.lean`, there only to attach
  space bounds to rows exported as existentials (the §2 design rule, *named*
  machines with spec theorems, was not followed by those rows).

**The registry.** Status as of 2026-10-12. Each entry gets a public contract
and a statement gate before a second consumer is briefed.

| # | Host | Status | Named consumers |
|---|---|---|---|
| 0 | **Framed-contract structure**: machine, entry/exit states, precondition, endpoint as a function of the start configuration, time, no-earlier-exit cut, head envelope; sequencing, phase host, R1 embedding, lift and counter loop as structure-to-structure theorems, space derived | to design; **requirements revised by §16** (exact time and cut first-class) | every host below; removes the inline restatements of the delimited-word precondition |
| H1 | **AND/OR evaluator**: a depth-first odometer over a path word of per-depth records with node kinds (AND/OR), a pluggable leaf-verdict module with its own framed contract, short-circuit semantics as a pure function; space = path + leaf + O(1) | the pure core is proved, private, in B4 membership's partial (`b4mValue`, `b4mValue_truth`, `b4mWalk_value`; fills-6); no machine walker was built. **Language first (user, 2026-10-12):** the general evaluator is written as a recursive program of §15's language, not as a machine host, and `TQBF_mem_PSPACE` follows as a program over that core (backlog MIG-22) | `TQBF_mem_PSPACE`; Savitch (midpoint records as digits); NP ⊆ PSPACE (re-derivation); `ClassPSPACE/Games.lean`'s game values; backtracking in the §15 layer |
| H2 | **Step block**: one simulated transition of a `k`-tape coded table, relation-level, with per-round time `B·(\|table\| + 1)` and a head envelope | **the complete step block is proved, private, in B5a H1's continuation (fills-7):** `h1RoundTM k`, one finite machine per `k` whose control does not depend on the state count, with `h1Round_effect` (`0 < T ≤ 50·(\|table\| + 1)`, strict interior, silent, head envelope). Promotion by PR and gate before a second consumer is briefed (backlog F7-1(a)) | H1 (`exists_uniformSimulator`); U-1; B6's self-application universal; C1 (with a choice-bit-indexed table); EXPCOM |
| H3 | **Windowed runner**: run a fixed machine on a windowed record, exiting on window exit, simulated halt, or a configuration-count clock | parts exist privately in S1b's partial (radius phase, records-to-runs bridge, the general-`S` count). S1b stopped (fills-6); B6's window route is the next consumer (adopted, §16b item 3) | S1b; B6 (the window route); Savitch; NL = coNL |
| H4 | **Search over a graph presented by rows** (enumerate, equality, adjacency, start, target), visited table, BFS | not built: S1b's partial has the record graph (records, edges, path lifting, counts) but no search machine, and it stopped there (user, fills-6). **Language first:** the general search is a program of §15's language, and `NSPACE ⊆ DTIME(2^O(S))` is re-derived through it (backlog MIG-19) | `NL ⊆ P`, `NSPACE ⊆ DTIME(2^O(S))`; `PATH ∈ P`; Immerman–Szelepcsényi counting; §15 graph algorithms |
| H5 | **Input devices** behind one interface: native, buffered (Z1, exists), unary marker, binary position (from `exists_inputSeekTM`), computed input | partial | B6 / `space_universal`; U-1 and H2 (backlog); C1 |
| H6 | **Machine-to-formula kit**: closed-form variable indexing, snapshot-keyed local gates, ordered emission by `exists_emitLoopTM`, Tseitin on `Std.Sat.CNF ℕ` correct for every prefix assignment | pattern private in `CookLevin/Hardness.lean`; B4a's codec is non-uniform (its orderings range over index types depending on `n` and `s`, and its public statement is `∀ n s, ∃ …`). **B4a is restated in place over this kit's indexing** (user, 2026-10-12; §16b item 2) | TQBF hardness; Cook–Levin deduplication; later machine-to-formula reductions |

Pure-Lean kits that the hosts' semantics share (not machines, so not hosts,
but designed with them): bounded reachability (`ReachWithin`, the midpoint
lemma, pigeonhole shortening) with bridges from configuration reachability,
`GraphReach` and `Kruskal.Reach` to Mathlib's `Digraph`/`SimpleGraph`.
Consumers: Savitch, TQBF hardness, Immerman–Szelepcsényi, PATH, §15.

**Work in flight when the rule was adopted.** No in-flight brief is withdrawn.
B4 membership and B5a H1 received addenda (`briefs/ch34-b4-mem-addendum-1.md`,
`briefs/b5a-fill-h1-addendum-1.md`): their hosts stay private for now, as
their ownership requires, but are written generic, with self-contained
statements, and listed as promotion candidates. They and S1b's candidates are
promoted, by PR and gate, before any second consumer is briefed.

**Proposed sequencing** (maintainer; for the user): item 0, then H1 (two
consumers ready: TQBF membership and Savitch), then H3/H4 from S1b's delivery,
then H5 with H2's self-application universal for B6, then H6 for TQBF
hardness. Each is a statement phase plus its gate, then a fill.

