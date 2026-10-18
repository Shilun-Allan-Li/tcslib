# Extract of machine-library-design.md at 947158e9: §14 (hosts first; item 0) lines 3010–3072, and §16 with §16a (the migration; MIG-0) lines 3462–end

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
| H2 | **Step block**: one simulated transition of a `k`-tape coded table, relation-level, with per-round time `B·(\|table\| + 1)` and a head envelope | one component proved, private, in B5a H1's partial (fills-6): `h1RecordTM`, which executes a selected record's fixed fields, with addendum 1's envelope for that component. Lookup, successor installation and the round seam remain | H1 (`exists_uniformSimulator`); U-1; B6's self-application universal; C1 (with a choice-bit-indexed table); EXPCOM |
| H3 | **Windowed runner**: run a fixed machine on a windowed record, exiting on window exit, simulated halt, or a configuration-count clock | parts exist privately in S1b's partial (radius phase, records-to-runs bridge, the general-`S` count). S1b stopped (fills-6); B6's window route is the next consumer | S1b; B6 (the window route); Savitch; NL = coNL |
| H4 | **Search over a graph presented by rows** (enumerate, equality, adjacency, start, target), visited table, BFS | not built: S1b's partial has the record graph (records, edges, path lifting, counts) but no search machine, and it stopped there (user, fills-6). **Language first:** the general search is a program of §15's language, and `NSPACE ⊆ DTIME(2^O(S))` is re-derived through it (backlog MIG-19) | `NL ⊆ P`, `NSPACE ⊆ DTIME(2^O(S))`; `PATH ∈ P`; Immerman–Szelepcsényi counting; §15 graph algorithms |
| H5 | **Input devices** behind one interface: native, buffered (Z1, exists), unary marker, binary position (from `exists_inputSeekTM`), computed input | partial | B6 / `space_universal`; U-1 and H2 (backlog); C1 |
| H6 | **Machine-to-formula kit**: closed-form variable indexing, snapshot-keyed local gates, ordered emission by `exists_emitLoopTM`, Tseitin on `Std.Sat.CNF ℕ` correct for every prefix assignment | pattern private in `CookLevin/Hardness.lean`; B4a's codec is non-uniform (its orderings range over index types depending on `n` and `s`, and its public statement is `∀ n s, ∃ …`) | TQBF hardness; Cook–Levin deduplication; later machine-to-formula reductions |

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


## 16. The foundation migration (user decisions, 2026-10-12)

**Why.** The user: "I really think we should invest effort into building code in the right way,
especially in this foundational stage." Seven read-only reviews of the tip `9827cc99` costed a
retroactive migration onto the §14/§15 style:
- the Build foundation and the machine core;
- the machine-level files that stay on Turing machines;
- the algorithm files that could become programs.

Their per-file figures are the restyling backlog (`backlog.md` §2, MIG/RS).

**Decisions (user, 2026-10-12).**
1. **The no-retroactive-migration rules are lifted for this migration**: §8's byte-identity
   bullet and decision 12.2's byte-identical `Primitives.lean`.
2. **Scenario B.** Proof bodies are swapped onto contracts, and in addition the duplicate
   statement families are retired: the R3 canonical `_run` rows, `counterLoopTM` next to
   `counterLoopTMVia`, `EmitIterEmbed`'s embedding, and `Codes2Tape`'s mirror. Their consumers are
   edited. Proof-body swaps under unchanged statements are gated by a freeze check, a replay and
   a fidelity gate. Each retired or changed statement needs a full statement gate.
3. **Savitch and `NSPACE ⊆ DTIME(2^O(S))` are algorithms at heart.** They are written as programs
   of the §15 language and converted by the RAM-to-`FinTM` compiler (stage 2). TM-intrinsic
   results are *not* recast as programs: Cook–Levin, TMSAT, NP ⊆ PSPACE's machine,
   Nondeterminism, the oblivious and hierarchy constructions, and the universal machine.
   **S1b**, in flight at machine level and proving `NSPACE ⊆ DTIME(2^O(S))`, `NL ⊆ P` and Ex 4.3,
   **finishes as briefed** (user, 2026-10-12: "Let it finish"). Once stage 2 and the
   configuration routines exist, it is re-derived as a program and its private host retired,
   with its public statements unchanged (MIG-19).
   *Outcome (fills-6, user: "Stop at this partial"):* S1b landed `NL ⊆ P` and Ex 4.3 proved
   modulo `NSPACE ⊆ DTIME(2^O(S))`, without a search host. MIG-19 is now the route for the
   simulation itself.
4. **Restyling is opportunistic, with a clear backlog** to chip away at: the RS items. Each
   row has its estimate, prerequisites and gate.

**The estimate** (ranges are the reviewers'; ESTIMATED unless marked):

| Bucket | Today | Net change |
|---|---|---|
| Foundation: Build (43,143) and the core (3,887), MEASURED | 47,030 | about −12.5k (−8k to −17.5k). That includes the `f2_` deletion, −7.6k to −8.3k at high confidence, and about 3.6k of new infrastructure |
| Machine-level files staying on TMs: universal, robustness, Nondeterminism, diagonalization and time hierarchy, oracle model, Mathlib bridge | 26.3k | about −4k to −5k: −3.7k from restyling, −1.7k to −2.1k from duplicates found, and +0.5k to 1.5k of extra infrastructure |
| Scenario B's statement retirements | | about −1k more |
| **Total** | **73k** | **about −17k (−12k to −23k)**. About 30k lines of proofs are touched and 4–5k are written new |

**What the contract structure must support** (§14 item 0). The survey revises the "time within
`T`" default taken from [AFM26]'s program logic:
- **exact time, with a no-earlier-exit cut, as first-class fields**, and "within `T`" derived
  from them. About 34 public Build statements carry cuts and about 33 state exact times. Seams,
  counter loops and the zone layer's `2p + 2` compose exact times;
- a **positive-duration field**, for the universal machine's block converse;
- an **endpoint function and a frame predicate**, with tape-indexed `SameOn`-style frames and
  `.keep` lemmas;
- **head envelopes**, both radius and interval forms, with space derived from them;
- the **input tape** (clamped moves, virtual input) and **output appends**;
- **transports**: state renaming (`Sum`/`Sigma`), R1 embedding, symbol lift, alphabet reduction,
  and the lockstep combinators of the robustness layer (decoration, parallel coding, folding);
- **later**, nondeterministic (`runWith`) and oracle-step variants.

From [AFM26] the design takes framing, spec-only calls and default-argument tactics; it does not
take the treatment of time.

**Programs for Savitch and `NSPACE ⊆ DTIME`** (decision 3) need one more planned component:
**machine-configuration routines in the language**. A configuration of a given (nondeterministic)
machine is encoded in memory, and routines enumerate its successors, or test the step relation,
from the machine's finite table. This is narrower than a general machine interpreter, since the
programs are built per machine.

There is also an open question for stage 2: Savitch's `O(S²)` space. Two routes give it:
- configurations held as single words, with word size `Θ(S)`, so that `O(S)` frames times
  `O(S)`-bit words fits the planned bound of cells times word size;
- a bit-accounted space bound in the compile theorem.

`NSPACE ⊆ DTIME(2^O(S))` is unaffected, since polynomial overhead on `2^O(S)` stays `2^O(S)`.

**Order of work:**
1. Item 0's statement phase and gate, with the requirements above.
2. The certain savings, which need no new infrastructure: named witnesses and the `f2_` deletion
   (MIG-1), then the known duplicates (MIG-2 to MIG-10).
3. Contract instances and tactics, grown against the first migrated file; then rebasing the
   composition-heavy files (MIG-11 to MIG-17).
4. The asymptotics port (MIG-18).
5. The RS items, opportunistically.

**12.2c** (plan §4e) is folded into this migration. Its items are subsumed, moved, kept as MIG-20
and MIG-21, or lapsed, as recorded at the head of the 12.2c tasklist. **MIG-0 and MIG-1 now
precede §13d G2** (user, 2026-10-12), reversing "G2 comes before the Catalog split".

New and unfinished work is written in the new style from the start. Deliveries now in flight
in the old style (record tables, W2-S, B5a canonizer and H1, B4, S1b) join step 3.

### 16a. MIG-0, the contract structure: statement draft and decisions (2026-10-12)

**A sorried statement draft of `Build/Contract.lean` was written and fit-tested** (maintainer,
2026-10-12). It was informed by a read-only inventory of every public contract in `Build/`
(about 150 run statements: 24 exact closed-form times; about 45 cuts that include time `0` and
4 that do not; 25 interval and 12 radius envelopes; no frame predicate anywhere, and frames
written in four idioms).

**The structure** `Turing.Contract M entry exits ι x`:
- a precondition, an **exact time**, an **endpoint function** and per-tape head intervals
  `[lo, hi]`, all functions of a data index `i : ι` (the word or fields the module reads) and the
  start configuration;
- proofs: the run reaches the endpoint at that time; the endpoint is at an exit; **no exit is
  reached earlier, with the cut including time `0`**; and the heads stay in their intervals.
  Exits form a set, so single anchors, verdict pairs, loop exits and halting are one structure;
- derived: "within `B`" (`within`) and the per-tape space bound (`spaceUsedByTape_le`, through
  `spaceUsedByTape_le_card_Icc`); positivity is a predicate.

**Decisions (user, 2026-10-12):**
1. **Universe `Type`** for the alphabet, the states and the data index: the universe of
   `FinTM`, `phaseHostTM` and `counterLoopTMVia`. UNIV-1(a) stays an optional generalization.
2. **Frames are a derived layer**, not a field. The endpoint already states the frame as
   `{ d with … }`. The layer adds `Cfg.SameOutside` (a per-tape footprint), its composition,
   `.keep` lemmas for stored words and blank tapes, and `Contract.Frames`.

**Compositions, as thin wrappers over the existing rows:**
- `trans`: sequencing on one machine, the private `RecordRun` pattern;
- `seq`: the R2 seam, time `t₁ + 1 + t₂`;
- `inPhase`: one phase inside the phase host, whose redirect targets lie in other phases;
- `embed`: the R1 embedding, with unselected tapes framed and output appended;
- `branch`: the two-way seam;
- `ReturnContract` with `release`: for the four rows whose entry is also their exit (the install
  and emit calls and the advancing writer), whose cut starts at time `1`.

**Fit test.** `trans`, `seq`, `inPhase`, `embed` and `embedEmitCfg_select` are proved with no
statement change and no extra hypothesis, on the standard three axioms. So is the instance
`clearTM_contract`, R3 clear repackaged from `clearTM_run_ofCfg`. A second fit test then
proved the rest: the frames layer (the `SameOutside` lemmas are nearly definitional),
`clearTM_contract_frames` (the footprint is exactly where the endpoint writes blanks), `release`
and `branch`. **The whole MIG-0a draft is proved: 837 lines, 0 errors, 0 warnings**
(`audits/evidence/mig0/Contract-draft.lean.txt`).

Further observations from the fit tests:
- **Liveness is a lemma.** A contract's run is live strictly before its time, from the cut and
  `exit_mem`, since a halt would persist to the endpoint. `branch` needs it; promote it as
  `Contract.live`.
- **`branch`'s halting exit is untagged.** If both continuations may halt, a halted endpoint
  does not say which ran. The statement is still correct.
- **A third export:** a pointwise `seamReleaseTM_runFrom_pos`. The release's envelope went
  through `seamReleaseTM_visitedByTapeHead`, because the pointwise lemma is private.
- **Ergonomics:** a `@[simp]` unfolding lemma for `Frames` and `SameOutside`, so that `rw` sees
  a footprint's `if` without a `show`.

The test found two missing public exports, both additive:
- `embedEmitCfg_unselected_tape` and `_pos` (`Build/Embed.lean`). The proof of
  `embedEmitCfg_select` worked around their absence through `embedEmitTM_frame` and a trivial
  machine;
- a right-segment seam lemma (`Build/Seam.lean`), to replace the private `seamComp_right`. It is
  needed for set-valued exits; `seamCompTM_firstReturn_ofCfg` excludes only one target.

**Scope, in two increments:**
- **MIG-0a:** the structure, the derived lemmas, the frames layer, `trans`, `seq`, `inPhase`,
  `embed`, `branch`, `ReturnContract` with `release`, `Contract.live`, and the three exports;
- **MIG-0b:** the symbol lift (through `Cfg.decodeSymbols`), the counter loop (rounds as
  `ReturnContract`s), state renaming along an embedding (`runFrom_mapState_of_agreeOn`), and
  the tactics.

The next step is MIG-0a's statement gate. The draft's proofs exist, so the gate can audit
statements and proofs together.
