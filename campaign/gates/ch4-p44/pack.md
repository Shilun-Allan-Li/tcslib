# External audit pack — Chapter 4, phase P4.4 (logspace reductions, PATH, Immerman-Szelepcsényi), statement gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase P4.4 —
logspace reducibility `≤ₗ` and `NL`-completeness with the general Lemma 4.17,
the campaign's first graph encoding and `PATH` (membership and Theorem 4.18),
the Immerman-Szelepcsényi theorem (Theorem 4.20, Corollary 4.21), and
Example 4.7's `MULT` — **the chapter-4 statement program's final phase**.
Statement phase per `workflow.md` §2-3; the gate closes on a round with zero
blockers and zero majors.

Audited at commit `200f4693` (branch `complexity/arora-barak-ch3-4`); the four
Lean modules under audit are byte-identical to their landing commit `ec400dc5`
(the auditor can verify:
`git diff ec400dc5 200f4693 -- TCSlib/Complexity/SpaceComplexity/Logspace/`
is empty). Under audit:
`TCSlib/Complexity/SpaceComplexity/Logspace/{Reductions,Path,ImmermanSzelepcsenyi,Mult}.lean`
— **11 sorried statements (Reductions 5, Path 2, ImmermanSzelepcsenyi 3,
Mult 1), 6 definitions plus the scoped `≤ₗ` notation.**

**Layering caveat, stated plainly**: `Path.lean` and
`ImmermanSzelepcsenyi.lean` import the **phase-P4.2 surface**
(`SpaceComplexity/ConfigGraph.lean` — `Turing.NDTM.coreSum`,
`Turing.FinNDTM.configBound`, the packaged
`DecidesInSpace.mem_iff_acceptsWithin_configBound` iff, and the graph
dictionary `Turing.NDTM.reflTransGen_cfgStep_iff`), whose own statement gate
runs **concurrently** (`audits/ch4-p42-pack.md`). Audit P4.4's statements
against that surface as given; findings against the P4.2 definitions
themselves are welcome and are filed to that round, labeled as such — they do
not block this gate unless they falsify a P4.4 statement. Also concurrent:
the §12 routine layer (`audits/routine-infra-pack.md`) and the P4.3 pack
(disjoint files). **Closed context**: the P4.1 gate
(`audits/ch4-p41-resolutions.md` — `NL`/`coNL`/`NSPACE`/`SpaceConstructible`)
and the P0 reception gate (`audits/ch34-p0-resolutions.md` — the received
implicit-logspace layer `ImplicitPoly.lean` sitting on
`Complexity.ImplicitlyLogspaceComputable`, with its received divergences:
`0`-based indices and the campaign polynomial normal form `C·(n+1)^c`; and
the `LogProg`/ARM machine layer the sketches cite as engines). The P0 round's
note 10 recorded, of the received surface: "General Lemma 4.17 is not
delivered and the plan says so. […] Do not treat these results as the missing
general composition theorem" (`audits/ch34-p0-findings.md`, note 10) —
`Reductions.lean`'s `ImplicitlyLogspaceComputable.comp` is exactly that
recorded debt coming due. One more deferral to keep in view: the plan's
**nondeterministic-ARM extension** (deferred to the §12 gate and the
colleague sync) gains its first two named customers here — the `PATH` walk
and the counting verifier, declared as fill obligations in the sketches; the
extension itself is not under audit in this round.

## Brief for the auditor

Definitions, statements, docstrings. Failure modes per `audits/TEMPLATE.md`,
plus this phase's own two: **an instance encoding whose non-injectivity or
fallback polarity makes `PATH` (and hence `PATH`-complement) a different
language than the book's**, and **a reducibility notion that silently fails
transitivity-relevant closure (output-length bounds, index conventions) so
Lemma 4.17 is false as stated**. Blind restatements for all 6 definitions —
with special care on `Complexity.ImplicitlyLogspaceComputable` *as received*
(`SpaceComplexity/Basic.lean`): restate exactly what `≤ₗ` and the `comp`
statement inherit from its three conjuncts (the polynomial output-length
bound `∃ C c, ∀ x, |f x| ≤ C·(|x|+1)^c`; the bit language
`indexLang (fun x i => (f x).getD i false = true) ∈ LOGSPACE`; the length
language `indexLang (fun x i => i < (f x).length) ∈ LOGSPACE`; queries
carried as `Turing.pairEncode x (Nat.bits i)`, indices `0`-based,
little-endian). True-as-stated arguments for all 11 sorried statements; at
least **5 adversarial instantiations**; no blanket approvals. Sources: [AB09]
§4.3 (Definition 4.16, Lemma 4.17, Figure 4.3, Theorem 4.18), §4.1.2 ((4.1)
and the `PATH ∈ NL` paragraph; Example 4.7's `MULT`), §4.3.1-4.3.2
(Definition 4.19, Theorem 4.20, Corollary 4.21); [Imm88]/[Sze87] are cited
through [AB09] — no external text required.

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch4-p44-sweep.log`, revision recorded at
  start: `200f4693`): 5 modules (the four under audit plus the
  `SpaceComplexity` facade), 0 `error:` lines, fresh `.olean`s, exactly
  **11** `declaration uses 'sorry'` warnings (Reductions 5, Path 2,
  ImmermanSzelepcsenyi 3, Mult 1).
* Style lint (`audits/logs/ch4-p42-p44-stylelint.log`, shared with the
  concurrent P4.2/P4.3 packs): `SpaceComplexity` 0 FAIL / 0 WARN over
  42 files.
* Statement-freeze baseline: commit `200f4693`.
* Drafting provenance: maintainer-drafted; landing commit `ec400dc5`.

## Known deviations and design decisions (declared — verify each, flag others)

1. **`≤ₗ` is rendered through the received implicitly-logspace layer**, as
   the book itself does (a logspace machine cannot store its output):
   `B ≤ₗ C` is `∃ f, ImplicitlyLogspaceComputable f ∧ ∀ x, x ∈ B ↔ f x ∈ C`.
   The received divergences are inherited and named: **`0`-based indices**
   (`i < |f(x)|` for the book's `1`-based `i ≤ |f(x)|`) and the **campaign
   polynomial normal form** (`|f x| ≤ C·(|x|+1)^c`), both documented at the
   `Basic.lean` definition site since P0.
2. **`GraphReach` is in-house** — `Relation.ReflTransGen` over the decoded
   adjacency relation on `Fin n`. The plan's §2.6 target,
   `GraphTheory`'s `Digraph.Reachable`, lives in a tree currently carrying
   admissions outside the audited closure; the campaign keeps the relation
   local and records the bridging lemma as future work (plan decision log,
   the P4.4 row) — a declared deviation.
3. **The `PATH` instance encoding is layered aligned pairs** — unary vertex
   count `1ⁿ`, row-major adjacency matrix
   (`(List.finRange n).flatMap fun u => (List.finRange n).map (A u)`), binary
   endpoints (`Nat.bits`), each layer a `Turing.pairEncode` — with
   membership by **existential witness over genuine encodings** (the
   `EXPCOM`/`dblLang` house pattern; no total decode). Consequence, stated
   bluntly: **every malformed string is OUT of `PATH` and therefore IN
   `PATH`-complement**, so `compl_PATH_mem_NL`'s verifier must *accept*
   malformed shapes — the flipped validator, declared in that sketch.
4. **No read-once certificate model**: the book proves Theorem 4.20 in the
   Definition-4.19 certificate view (a read-once certificate tape); the
   campaign's binary-choice NDTM consumes choice bits one per step, never
   re-readable, so certificates ARE choice words and Definition 4.19 is not
   formalized — a declared simplification (the
   `ImmermanSzelepcsenyi.lean` module docstring).
5. **Corollary 4.21 is rendered as the set equality**
   `{L | Lᶜ ∈ NSPACE S} = NSPACE S` for space-constructible `S`
   (`Complexity.SpaceConstructible`, the P4.1-closed bundled form with the
   `logSpace` floor as data).
6. **`MULT`'s number-triple encoding is fixed here** — little-endian
   `Nat.bits`, nested aligned pairs
   (`pairEncode (bits a) (pairEncode (bits b) (bits (a·b)))`), existential
   witness over genuine encodings — the encoding conventions P4.1 recorded
   as deferred to this phase (P4.1 pack, deviation 7).
7. **`NL`'s downward closure under `≤ₗ` appears as a NAMED FILL OBLIGATION**
   inside `NL_eq_coNL`'s sketch ("the logspace analogue of
   `mem_LOGSPACE_of_logspaceReducible`"), not as a standalone sorried
   statement — **seeded question 7 asks whether the gate should demand its
   promotion to a statement.**

## Specific questions (prioritized)

1. **`LogspaceReducible`**: blind-restate against [AB09, Definition 4.16]
   *through* the received `ImplicitlyLogspaceComputable` — does the received
   shape bundle the polynomial output-length bound and **both** query
   languages the composition needs? Where exactly do the received
   divergences (`0`-based indices, the `C·(n+1)^c` normal form) surface in
   `≤ₗ`, and can either make `B ≤ₗ C` hold or fail against the book's
   reading?
2. **`ImplicitlyLogspaceComputable.comp`**: is `g ∘ f` implicitly logspace
   computable TRUE AS STATED given the received shape? [AB09, Figure 4.3]'s
   virtual-input-tape argument needs `f`'s *length* queries to manage the
   virtual head — check the received surface supplies them (the length
   `indexLang` conjunct), and check the index-bookkeeping ledger (binary
   counters within `logSpace`, the `Machines/Bin` layer; the composite's
   polynomial bound as the composition of the two bounds).
3. **`LogspaceReducible.trans` / `mem_LOGSPACE_of_logspaceReducible` /
   `LogspaceReducible.polyTimeReducible`**: statement shapes against
   [AB09, Lemma 4.17(1)(2)] and the `≤ₚ` refinement via the received
   `ImplicitlyLogspaceComputable.polyTimeComputable`. In the
   `L`-downward-closure sketch, the final step is a **fixed-index
   specialization** of the `indexLang` conjunct (deciding `B` as the bit
   query at index `0` — note `Nat.bits 0 = []`, so `⟨x, 0⟩` is
   `pairEncode x []`): is that obligation sound as sketched? Also the
   collapse statement `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` against
   the book's remark after Lemma 4.17.
4. **`encodePATH`/`PATH`**: is the existential-witness membership sound —
   can two distinct `(n, A, s, t)` produce one string (encoding injectivity:
   the aligned-pair layout is self-delimiting and `Nat.bits` is injective —
   does anything in `PATH`'s consumers *need* injectivity, and does it
   hold)? Row-major order via `finRange` `flatMap`; endpoints via `Nat.bits`
   (`Nat.bits 0 = []` — vertex `0`'s code is the empty string; harmless
   under the pair alignment?); `n = 0` is impossible (`Fin 0` is empty, so
   no instance has zero vertices) — faithful to the book's graphs?;
   `GraphReach` is reflexive, so genuine instances with `s = t` are always
   members — the book's reading of "there is a path"?
5. **`PATH_mem_NL` / `PATH_NLComplete`**: the guessed-walk sketch's budget
   (`n` rounds, two `logSpace n`-bit registers and a counter) and the shape
   validation. For hardness: the reduction through the P4.2 vertex layer at
   window `c₀ · logSpace` (`coreSum`/`configBound`), the single-target
   accepting normalization — the sketch claims the **P0 unique-terminal
   caveat is discharged exactly here** (the erase-and-park normalization,
   `Machines/Clean`'s `cleanTM` discipline as model): check that claim — and
   the implicit-logspace computability of the reduction itself (bit-query
   locality: one matrix bit from one local transition-table check; the
   length query pure arithmetic in `i`), assembled by the received
   `arm_decides`.
6. **`compl_PATH_mem_NL`**: the inductive-counting sketch — ascending-order
   enumeration, exact counts `cᵢ`, and the **two-level certificate layout on
   ONE choice word**. The campaign's choice words are natively read-once
   (deviation 4): is that claim airtight, i.e. can the verifier of [AB09]'s
   proof ever need to *revisit* a certificate bit (path replays are re-made
   by fresh guessing, not re-reading — does the sketch's layout deliver
   that)? And the malformed-shape acceptance (deviation 3's flipped
   validator): is the stated language `PATHᶜ` — all non-encodings included —
   exactly what the verifier sketch accepts?
7. **`NL_eq_coNL` / `NSPACE_compl_eq`**: the complement bookkeeping (`coNL`
   as defined in P4.1's `SpaceClasses.lean`: `{L | Lᶜ ∈ NL}`), the
   `NL`-downward-closure fill obligation (deviation 7 — should it be a
   statement?), and for Corollary 4.21 the configuration-graph variant: the
   window radius computed from the `SpaceConstructible` witness — is
   constructibility used anywhere beyond the window computation, and is the
   two-sided set equality the book's statement?
8. **`multLang`**: does the existential capture the book's `MULT` exactly —
   all `a, b : ℕ` including `0` (`Nat.bits 0 = []`: zero components encode
   as empty strings inside the pairs — still genuine encodings)? And the
   column-sum/carry sketch's space ledger (carry of `O(logSpace n)` bits
   since a column sum is at most the input length; two index counters; the
   `Parse2`/`ParseCmp` toolkit on `⟨u, ⟨v, w⟩⟩` inputs).

Adversarial instantiations to attempt: the empty string in `PATH`, `PATHᶜ`,
and `multLang`; `s = t` instances (reflexivity); the one-vertex graph
(`n = 1`, empty endpoint codes); `a = 0` or `b = 0` triples in `multLang`;
`B = ∅` and `B = Σ*` in `NLComplete`'s hardness quantifier; a reduction `f`
with `f x = []` for all `x` in `≤ₗ` (the length language is empty — which
languages does it relate?).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; P4.2-surface findings: same table,
prefixed "[P4.2]". Findings go verbatim into `audits/ch4-p44-findings.md`;
the gate closes on zero blockers and majors.
