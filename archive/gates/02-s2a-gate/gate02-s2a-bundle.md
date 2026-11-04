## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/pack.md =====

# Gate 02 (Pass–shelat ch. 5–8, S2a): external API audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#185](https://github.com/Shilun-Allan-Li/tcslib/pull/185)
into `cryptography/pass-shelat-ch2-4`, at its head `597eef43ccd3c8bfafe0c0c16a2444b12adc1644`.
- **The change:** the core of a new framework for security games and two-party protocols,
  `TCSlib/Cryptography/Games/` (six modules and a facade, 1,325 lines), plus one import line in
  `TCSlib.lean`.
- **Gate type:** an **API gate** (user's ruling, 2026-11-04). The definitions are new, every
  lemma is proved, and there is no `sorry`. The statements of the six chapters' prongs will be
  written against this API, so its definitions are what matter most.
- **The deliverable:** **`gate02-s2a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*,
3rd ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. You need
it for question 9: §4.4 (book pp. 114–116), and the definitions of ch. 5–7 (book pp. 133–175).

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 framework: definitions, theorem statements,
docstrings and proof sketches. The proofs are machine-checked; do not review tactic scripts. Hunt
for:
1. **Wrong semantics:** a definition that does not compute what its docstring says. For example,
   probabilities that are not those of uniform sampling, a simulation that threads state wrongly, a
   log in the wrong order, or an execution that misroutes messages.
2. **Trivialization:** hypotheses that are vacuous or too strong to be met by the games they are
   meant for, or definitions satisfiable for degenerate reasons.
3. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases.
4. **Unfitness for purpose:** this API must express the security games and protocols of [PS10]
   ch. 5–8 (question 9). A definition that cannot express one of them is a finding.
5. **Debt and duplication:** see the attestations; the framework generalizes three existing
   pieces, with bridges scheduled for the next PR (S2b).
6. **Attribution:** `policy.md` §2 (in the bundle), including its *design adaptation* rule. The
   framework adapts VCVio's design, and the citation block is
   `briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md` (in the bundle).

For **every definition**, restate it in your own mathematical English before reading its
docstring, and report any daylight. For **every theorem**, say in 1–3 sentences whether its
statement is what the docstring claims. Attempt at least **three adversarial instantiations**.
Propose missing sanity theorems. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit (all declarations) | `TCSlib/Cryptography/Games/{OracleComp,Probability,Simulate,Advantage,Hopping,Protocols}.lean`, `TCSlib/Cryptography/Games.lean` |
| Design documents (context; they state the intent) | `briefs/pass-shelat-ch5-8/design/S2-game-framework.md`, `briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md` |
| Context, not under audit | `TCSlib/InformationTheory/FinDist.lean` (on `main`); the concrete layer of the ch. 2–4 branch that the framework generalizes: `TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean` (`QueryTree`), `TCSlib/Cryptography/Foundations/Probability.lean` (`uprob`), `TCSlib/Cryptography/Foundations/Experiments.lean` (`distAdv`, `acceptProb`) |
| Source | [PS10] §4.4; ch. 5–7 definitions (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the S2b layer (bridges to the ch. 2–4 layer, the machine model), which is not written yet |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

1. **Elaboration.** `scripts/lean_check_tree.sh`, one module at a time into a fresh olean tree,
   over the 8 modules of the closure (`InformationTheory/FinDist`, the six modules, the facade):
   8/8 pass, 0 errors, 0 warnings, 0 `sorry` (`replay-head.log`).
2. **Axioms.** `#print axioms` for all 68 theorems: only `propext`, `Classical.choice` and
   `Quot.sound` (`axioms.log`).
3. **Lint.** `scripts/style_lint.py`: 0 findings on the 7 files; no line over 100 characters
   (`style-lint.log`).
4. **Imports.** `Mathlib.Data.Nat.Notation`, `TCSlib.InformationTheory.FinDist` and the
   framework's own modules. No ch. 2–4 module is imported.
5. **Names** (`name-screen.log`).
   - No short name of `TCSlib.Cryptography.Games` is declared elsewhere in `TCSlib.Cryptography`.
     The one clash found, `distAdv`, was renamed `advantage` before this head.
   - The pinned Mathlib has no `OracleComp`, `OracleSpec`, `ProbComp` or `QueryImpl`.
6. **Generalizations of existing code, disclosed as planned debt.** Each is resolved by a bridge
   in S2b (design note §8). None is a copy: the framework's definitions are new and more general.
   - B1: `Games.OracleComp` with one oracle and `Games.simulate` generalize the concrete layer's
     `QueryTree` and `QueryTree.simulate`.
   - B2: `Games.ProbComp.prob` over finite samples generalizes `uprob` over finite seed types, as
     the user's ruling R-1 decided (sampling as an oracle). A route probe proved the concrete
     layer's `invProb f A` equal to the probability of a one-line game (design note, probe
     P-S2-1).
   - `Games.advantage` and `Games.accept` correspond to `distAdv` and `acceptProb` over
     samplers.

## Known deviations and design choices (declared; verify they are benign)

- **Universe 0.** The framework lives in `Type`; [PS10]'s objects are all finite strings or
  finite structures.
- **Probability.** A real-valued finite sum over each sampling step: sampling oracle `m` is uniform
  on `Fin (m + 1)`, and other finite types are sampled through `Fintype.equivFin`. There are no
  measures (VCVio's semantics is measure-valued; this one is not).
- **Query bounds.** `CostBoundedBy cost c q`: total cost along every run at most `q`, oracle `i`
  costing `cost i`. "At most `q` queries to oracle `i`" is cost 1 on `i` and 0 elsewhere.
- **Identical until bad.**
  - The two implementations must be *equal as computations* on good states, and keep bad states
    bad (every possible new state of a bad state is bad).
  - The bound is the first simulation's probability of ending bad.
  - The lemma also proves the two simulations' bad probabilities equal.
- **Protocols.**
  - A party's exchange query is answered with `Option In`, where `none` means the other party has
    returned.
  - The first mover is the first argument of `Party.exec`.
  - Execution stops with `none` when the fuel runs out.
  - Views are not yet defined as objects; they come from logging, in S2b.

## Specific questions

1. **Sampling.** Is `ProbComp.expect` exactly the expectation under uniform, independent answers
   at every sampling step? Is `ProbComp.sample T` uniform for every nonempty finite `T`?
2. **Simulation and logging.** Is `simulate`'s threading of state right, and does
   `QueryImpl.withLog` log in chronological order? Is `simulate_withLog` the right "logging is
   harmless" statement?
3. **Composition.** Does `simulate_comp` say what a reduction needs: running a reduction against
   implemented oracles is one implementation of its adversary's oracles?
4. **Costs.** Does `simulate_costBoundedBy` capture "the reduction asks at most `q` queries if its
   adversary does and each answer costs at most one query"? Any boundary problem with cost-0
   oracles?
5. **Identical until bad.** Are the hypotheses usable for the bad-event hops of [PS10]'s proofs
   (for example the repeated-nonce event in Thm 168.2, or a forger querying the challenge)? Is
   requiring *equal computations* on good states too strong, or the stickiness hypothesis
   unnecessary? Is the conclusion the standard one?
6. **The collision bound** (`prob_mem_le`). Does the statement capture independence of the fresh
   sample from the list, and the right bound `q/|T|`?
7. **Guessing versus distinguishing** (`guessAdv_eq_half_advantage`). Is it the standard factor
   of two?
8. **Executions.**
   - Does `Party.exec` implement [PS10] §4.4's alternating execution?
   - Is the `Option` reply sound, or can it hide a party's misbehaviour?
   - Does the fuel bound lose anything for protocols with a fixed number of rounds?
9. **Expressiveness for [PS10] ch. 5–8.** Check whether each of the following can be expressed
   with this API, in a sentence each:
   - MAC and signature forgery (Defs 134.2, 136.2), with "`m` was not queried" read from the
     log;
   - collision resistance (Def 140.1);
   - IND-CPA/CCA1/CCA2 (Def 168.1), with CCA2's refusal to decrypt the challenge;
   - non-malleability (Def 172.6);
   - honest-but-curious two-party security (Def 155.1), with views and outputs;
   - sequential composition of zero knowledge (Thm 175.1).

   Report any that cannot be expressed as findings.
10. **The VCVio citation.** Is it adequate under `policy.md`'s design-adaptation rule?
    - Check the project, authors, modules, commit, licence, and a tag usable at declaration
      level.
    - Are the declarations that follow a VCVio construction tagged
      (`[VCVio, OracleComp/OracleSpec]`, `[VCVio, SimSemantics]`, …)?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream phase would build on a wrong definition or statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The gate closes at **0 blockers and 0 majors**.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.

## ===== briefs/pass-shelat-ch5-8/design/S2-game-framework.md =====

# S2 design note: one framework for security games and two-party protocols

Status: **draft, 2026-11-04.** It implements the user's rulings of 2026-11-04:
- S2 is home-built at TCSlib's pins, adapting VCVio's design, and **VCVio is cited**;
- two-party protocols are carried by the same framework ("protocols unified");
- D-2: a common base, with `OracleEnsemble` restated over it, by agreement with Frederick.

Open decisions for the user are marked **R-n**; points needing Frederick's agreement are marked
**F-n**.

## Citation (policy.md §2, design adaptation)

```
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
```

The source of every mathematical notion stays [PS10] (with [KL] and [Gol04] where [PS10] is
silent). The game-playing method is from [BR06] M. Bellare, P. Rogaway, "The security of triple
encryption and a framework for code-based game-playing proofs", EUROCRYPT 2006 (the fundamental
lemma), and [Sho04] V. Shoup, "Sequences of games", ePrint 2004/332. The rule for when each tag
is used is in `CITATION-VCVio.md`.

## Why (the finding behind the ruling)

Ch. 2–4 expresses each security notion by hand:
- the fixed functionals `invProb`, `predProb`, `acceptProb`, `distAdv` over uniform seeds;
- one deterministic oracle `I → O` with a Boolean output (`QueryTree`, `OracleAdversary`);
- a custom NUPPT decoder per notion (`inverter`, `distinguisherL`, `toOracleAdversary`).

Ch. 5–8 needs several things that model cannot express directly:
- **randomized, stateful oracles:** CPA's `Enc_k` draws fresh coins per query;
- **oracle families:** CCA's `Enc` and `Dec`;
- **non-Boolean adversary outputs:** forgeries, collisions, message pairs;
- **phases with adversary state:** CPA/CCA, non-malleability;
- **transcript predicates:** "`m` was not queried", "the challenge was not decrypted";
- **two-party executions with views:** Def 155.1, OT, Yao, ZK composition.

## Design

### 1. Oracle specifications and computations (after [VCVio, OracleComp/OracleSpec])

```lean
/-- A family of oracles named by `ι`: oracle `i` takes a query in `dom i` and answers in `rng i`. -/
structure OracleSpec (ι : Type) where
  dom : ι → Type
  rng : ι → Type

/-- Computations with access to the oracles of `spec`, returning an `α`: a free monad. -/
inductive OracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type
  | pure : α → OracleComp spec α
  | query (i : ι) : spec.dom i → (spec.rng i → OracleComp spec α) → OracleComp spec α
```

- `Monad` and `LawfulMonad` instances, with bind by structural recursion.
- Disjoint union of specs, `spec₁ + spec₂` (index `ι₁ ⊕ ι₂`), and the lifts `liftLeft`/`liftRight`.
- Garg's `QueryTree I O α` is the one-oracle case: there is a bijection
  `QueryTree I O α ≃ OracleComp (singleSpec I O) α` that commutes with `eval` and `simulate`
  (bridge B1).
- The whole framework lives in `Type` (universe 0), as `QueryTree`'s uses do. VCVio's universe
  polymorphism is not needed for [PS10].

### 2. Probability (TCSlib's: finite, uniform, real-valued)

Sampling is the oracle `unifSpec : OracleSpec ℕ` with `dom _ = Unit` and `rng m = Fin (m + 1)`
(after VCVio's uniform-selection oracle). Other finite types are sampled through an equivalence
with `Fin`: `$ᵗ T` for `[Fintype T] [Nonempty T]` (`Fintype.equivFin`). Write
`ProbComp α := OracleComp unifSpec α`.

**Semantics, by structural recursion, real-valued, with finite branching (no PMF, no `ℝ≥0∞`):**

```lean
noncomputable def ProbComp.prob (c : ProbComp α) (p : α → Prop) : ℝ   -- written Pr[p | c]
--   Pr[p | pure a]          = if p a then 1 else 0
--   Pr[p | query m () k]    = (m + 1)⁻¹ * ∑ j : Fin (m + 1), Pr[p | k j]
```

For finite `α` this gives a `FinDist α` (`ProbComp.dist`), which connects to `main`'s `statDist`,
`EpsClose` and extractors (#183).

**Bridge to `uprob` (B2):** a computation that samples `x ← $ᵗ σ`, `r ← $ᵗ ρ` and then decides
`P x r` has `Pr = uprob (fun z : σ × ρ => P z.1 z.2)`. So Garg's `invProb`, `predProb`,
`acceptProb` and `distAdv` are exactly the probabilities of four one-line games, and every
ch. 2–4 result stated through them transfers.

- **R-1 (ruled 2026-11-04: (a), the sampling oracle):**
  - (a) sampling as an oracle in the monad, as above (recommended): games read as programs, as in
    [PS10]'s experiments, and the semantics is a finite sum;
  - (b) all randomness as external finite seeds (`ρ → OracleComp spec α`, handlers reading coin
    tables): closest to today's code, but every game must declare and thread its product of
    seeds by hand.

  Both are finite, uniform and real-valued; the bridge B2 makes (a) agree with today's `uprob`.

### 3. Oracle implementations, simulation, logging (after [VCVio, SimSemantics, QueryTracking])

```lean
/-- Implement the oracles of `spec` by computations over `spec'`, with state `σ`. -/
def QueryImpl (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') :=
  ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)

def simulate (impl : QueryImpl spec σ spec') : OracleComp spec α → σ → OracleComp spec' (α × σ)
```

- **Stateful, randomized oracles** are handlers into `spec' = unifSpec` (or `unifSpec + …`). For
  example, `Enc_k` draws its coins with `$ᵗ` on each query; the state holds the key, counters and
  flags.
- **Logging** is a handler transformer `withLog impl`, which appends `⟨i, x, y⟩` to a
  `QueryLog spec` in the state. Win conditions and oracle restrictions are predicates on the log:
  - "`m` was never queried to `Tag`";
  - CCA2's refusal to decrypt the challenge is a handler that answers `⊥` on it.
- **Reductions** are `simulate` with a handler that answers the adversary's oracles by querying
  the reduction's own oracles. This generalizes `QueryTree.simulate` (`eval_simulate`) to
  families and to state.
- **Query bounds** are a structural predicate `IsQueryBound c (qb : ι → ℕ)`, preserved by
  `simulate` with a per-query cost, generalizing `QueryTree.BoundedBy`.

### 4. Games and advantages (concrete level, one security parameter value)

- A **search game** is a `ProbComp Bool` built from the adversary: forgery, collision, inversion.
  Its advantage is `Pr[= true]`.
- A **distinguishing pair** is `G₀ G₁ : ProbComp Bool`, with advantage `|Pr[G₀] − Pr[G₁]|`.
- A **guess-the-bit game** has advantage `|Pr[b' = b] − ½|`, with the standard lemma relating it
  to the distinguishing form (factor 2).

[PS10]'s definitions are then short programs over these. Examples:
- **MAC forgery** (Def 134.2): `k ← Gen; (m, σ) ← simulate (withLog (tagImpl k)) A; return
  (Ver k m σ ∧ m ∉ log)`.
- **IND-CCA2** (Def 168.1): phase 1 with `(encImpl k + decImpl k)`, then the challenge, then
  phase 2 with `decImpl` refusing `c*`. The adversary's state between phases is the value it
  returns.

### 5. Game hopping (the generic lemmas, proved once)

1. `Pr` respects bind (total probability), `map` and relabelling of finite samples.
2. **Hybrids:** advantages add along a chain of games (the triangle inequality), with the standard
   `k`-step form used by the hybrid lemma.
3. **Identical until bad** [BR06]: two games written over the same code that differ only after a
   flag is set satisfy `|Pr[G₀] − Pr[G₁]| ≤ Pr[bad]`. Here this is a lemma about two handlers that
   agree while a state flag is clear.
4. **Oracle substitution:** if two oracle implementations are indistinguishable to every
   `q`-query adversary, then a game using one is close to the game using the other. The proof is
   by `simulate`. This is the step "replace the PRF by a random function" used in
   Thms 135.4, 168.2, 170.4 and 179.1.
5. **Lazy sampling** of a random function: a handler that samples on first query and caches gives
   the same distribution as a function table sampled up front. Garg's `LazySampling.lean` proves
   this for `QueryTree`; it is re-derived through B1/B2, not re-proved, where possible.
6. **Collision and union bounds** over `q` queries: for example, the `r` collisions of Thm 168.2.

### 6. Two-party protocols in the same framework ("protocols unified")

```lean
/-- A party that sends messages of type `Out`, receives messages of type `In`, and draws coins. -/
abbrev Party (Out In α : Type) := OracleComp (exchangeSpec Out In + unifSpec) α
--   exchangeSpec Out In has one oracle: query = outgoing message,
--   answer = the other party's next message, or `none` once the other party has returned
```

- **Execution** `exec (fuel : ℕ) (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
  ProbComp (Option (α × β))` (probed in P-S2-4; the transcript comes from logging handlers) is the
  coroutine interleaving: A's exchange query is answered by running B until
  B's next exchange query, and so on. The fuel is the protocol's message count, as in
  Frederick's fixed alternation.
- **A party's view** is (its input, its coins, the messages it received), read off the log of its
  `exchangeSpec` queries and its `unifSpec` answers. Def 155.1's joint distribution
  `{(view_A, out_B)}` is then a `ProbComp` directly.
- **Simulation-based security** (Def 155.1, ZK) compares two such `ProbComp`s, or two ensembles
  of them asymptotically, through the same distinguishing advantage.
- **OT inside Yao** (the composition step [PS10] omits): a party whose sub-protocol is run by a
  handler. Sequential composition is `simulate` of the outer party's calls to an inner
  protocol's ideal functionality, so the hybrid "real OT → simulated OT" is the oracle
  substitution lemma (§5.4) applied to a protocol.
- **Bridge B4 to Frederick's model:** every `Strategy` with a fixed alternation of `rounds`
  moves induces a `Party` (a loop that keeps the history and calls `next`). `exec` of the
  induced parties gives his `Protocol.exec`, `View`, `outP`/`outV` and transcript. His ZK
  definitions (`ZK`, `PerfectZK`, `PerfectZKAbort`) then transfer, and Thm 175.1 (sequential
  composition) is stated in the framework with a proved equivalence to his `ZK`. **F-2:** whether
  his ZK layer is later restated over `Party`, or only bridged (our recommendation: bridged now,
  restated at integration, by him).

### 7. The machine layer (asymptotic security)

- **Codecs.** A `SpecCodec spec` gives, per security parameter, string encodings of oracle
  names, queries, answers and the output, with `decode (encode a) = some a` and polynomial length
  bounds. It reuses Frederick's `pairEncode`, `decodeFin` and `encodeHist`.
- **The generic decoder.** `NUPPT.toComp (A : NUPPT) (codec) (n q : ℕ) : (A.Coins n) →
  OracleComp spec α` iterates `A`'s next-query activation on the encoded history, decoding a query
  or a final output, with budget `q`. It generalizes his `toOracleAdversary`, which is its
  one-oracle, Boolean-output instance (**bridge B3, which is also the D-2 restatement of
  `OracleEnsemble.Indist`**).
- **Security, uniformly:** `Secure G := ∀ (A : NUPPT) (q : PolyExpr), Negligible fun n =>
  adv (G n) (A.toComp codec n (q.eval n))`. The same shape covers search, distinguishing and
  guess-bit games, with fixed or adversary-chosen messages.
- **The efficiency lemma (the machine-level crux, proved once).** If a reduction is a NUPPT
  adversary run under a handler whose per-query work is a `PolyTimeComputable` function of the
  encoded state and query, with a polynomial query bound and polynomial state size, then the
  composite is `NUPPT.toComp` of a single NUPPT. It is built from Frederick's closure calculus
  (`Complexity/Randomized/Closure`). Every reduction of prongs A–D then needs only its handler's
  poly-time computability, never a machine construction of its own.

### 8. Bridges to existing code (all in our files; nothing of his edited without agreement)

| Bridge | Relates | Purpose |
|---|---|---|
| B1 | `QueryTree I O α` ≃ one-oracle `OracleComp`; `eval`, `simulate`, `BoundedBy` | reuse Garg's PRF/GGM/lazy-sampling results |
| B2 | `uprob`-functionals (`invProb`, `predProb`, `acceptProb`, `distAdv`) = `Pr` of one-line games | reuse every ch. 2–4 concrete result |
| B3 | `NUPPT.toOracleAdversary` = one-oracle instance of `NUPPT.toComp`; `OracleEnsemble.Indist` = a one-oracle distinguishing `Secure` | D-2's restatement (**F-1**) |
| B4 | `Strategy`/`Protocol.exec`/`View` = induced `Party`s and `exec` | reuse his ZK layer (**F-2**) |
| B5 | `PrivateKeyScheme.SingleMessageSecure`/`MultiMessageSecure`, `PublicKeyScheme.Secure` = games with fixed message vectors | Thm 168.2, Claim 172.a |

### 9. Layout (new directory, on `cryptography/pass-shelat-ch2-4` per D-0)

`TCSlib/Cryptography/Games/`:
- `OracleSpec.lean`, `OracleComp.lean` (monad, sums of specs, query bounds);
- `Probability.lean` (`unifSpec`, `$ᵗ`, `Pr`, `dist`);
- `Simulate.lean` (handlers, `simulate`, logging);
- `Advantage.lean` (game shapes);
- `Hopping.lean` (§5);
- `Protocols.lean` (`Party`, `exec`, views);
- `Machines.lean` (codecs, `NUPPT.toComp`, the efficiency lemma);
- `Bridges/` (B1–B5);
- the facade `Games.lean`.

The namespace is `TCSlib.Cryptography`, with the framework's types `OracleSpec`, `OracleComp`,
`ProbComp`, `QueryImpl` and `Party`. Each module docstring's `## References` carries [VCVio] (the
block above), plus [BR06]/[Sho04] for `Hopping.lean`, and [PS10] for the protocol layer's §4.4
and §6.2.

**Size estimate:** 3–5k lines, including the protocol layer and the machine layer (the plan's
1–2k for S2 assumed the narrower design). The machine layer (§7) is the largest risk.

## Route probes before the statement phase (pre-ship, run in Lean)

| Probe | Shows |
|---|---|
| P-S2-1 | the monad, `Pr`, and B2 on `invProb` (one ch. 2–4 functional, transferred). **Passed 2026-11-04** (`probes/P-S2-1-monad-prob-bridge.lean.txt`): the free monad, `unifSpec` sampling, the finite-sum `expect`/`prob`, total expectation (`expect_bind`), `expect_sample`, and `invProb f A = Pr[game]`, with standard axioms. It reads `invProb` and `uexp` by their bodies, for want of published equations (F-3) |
| P-S2-2 | Thm 135.4's concrete reduction: a forger, run under a handler that answers `Tag` with a PRF-or-random oracle, gives a distinguisher with advantage `≥ ε − 2^{-n}` |
| P-S2-3 | the CPA game for Alg 99.1 with a stateful, fresh-coin `Enc` oracle, and one hop of Thm 168.2's proof. **Passed in part, 2026-11-04** (`probes/P-S2-3-handlers-log-cpa.lean.txt`). Done: sums of specs and of handlers, `simulate` with state, logging, `simulate_withLog` (logging is conservative; proved), the fresh-coin `encImpl`, the IND-CPA experiment as a program (phases, adversary state, challenge), `cpaAdv`, and the bad event of Thm 168.2 as a log predicate. **Not yet:** the hop itself, which needs the oracle-substitution and identical-until-bad lemmas (§5) and is scheduled for the statement-phase probes |
| P-S2-4 | one OT execution (Prot 160.4) through `exec`, with the receiver's view read from the log. **Passed in part, 2026-11-04** (`probes/P-S2-4-protocol-exec.lean.txt`): `Party` over `exchangeSpec` + `unifSpec`, `step`/`finish`, `exec` with fuel and role swap, a toy protocol executing by `rfl`. Design fix found: an exchange answers `Option In`, where `none` means the other party has returned, so a waiting party can finish. **Not yet:** OT itself and views from logs |
| P-S2-5 | B3: his `toOracleAdversary` as an instance of `NUPPT.toComp`, at the level of definitions |

## Coordination with Frederick (adds to the S1 note)

- **F-1 (D-2):** `OracleEnsemble` and `toOracleAdversary` restated over `Games`, or bridged by
  B3; who does it, and when relative to his external gate.
- **F-2 (protocols unified):** his `Strategy`/`View`/`ZK` bridged by B4 now, and restated at
  integration.
- **F-3:** the framework adapts his `encodeHist`/`pairEncode` codecs and cites his closure
  calculus; any machine lemma we need in his `Closure.lean` is requested, not added.
  It also requests published equations for `invProb`, `predProb`, `acceptProb` and `uexp`
  (`Foundations/`): bridge B2 reads them by their bodies today (P-S2-1).

## Decisions for the user (ruled 2026-11-04: R-1 (a) the sampling oracle; R-2 reuse via bridges)

- **R-1:** sampling as an oracle inside the monad (recommended), or external finite seeds (§2).
- **R-2:** the generic lemmas of §5, re-derived through B1/B2 from Garg's concrete layer where
  possible (recommended), or proved fresh in the framework (simpler proofs, more duplication;
  each duplicate goes to the ledger).

## ===== briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md =====

# Citation for the S2 game framework's design source

Ruled 2026-11-04 (user): S2 is home-built at TCSlib's pins, **adapting VCVio's design**, and VCVio
**must be cited**. `policy.md` (§2, *Design adaptation*) requires the citation even though no code
is transcribed: in the `## References` of every module that uses the adapted design, with a short
tag usable at declaration level, and in every design document and blueprint entry built on it.

## The reference block (use verbatim in module docstrings)

```
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
```

## Declaration level

A declaration whose shape follows a VCVio construction carries `[VCVio, <module>]` in its
docstring, for example `[VCVio, OracleComp/OracleSpec]`, after the source citation ([PS10], [KL],
[Gol04]) that the mathematics comes from.

## What is and is not taken

- **Taken (design):** the three ideas above.
- **Not taken:**
  - no code, and no proof;
  - not VCVio's probability semantics: TCSlib keeps real-valued probabilities over finite uniform
    seeds (`uprob`) and `FinDist`;
  - not its notion of polynomial time: TCSlib keeps the Turing-machine `Complexity.NUPPT`;
  - not its program logic or tactics.
- **Why not a dependency:** VCVio pins Lean 4.35.0 with Mathlib v4.35.0, while TCSlib pins Lean
  4.25.0. Its polynomial time is a backend-relative cost model, and its probability semantics is
  measure-valued (the decision log of `PassShelatChapter5-8Plan.md`, 2026-11-04).

## Authors seen in the consulted modules (from their headers)

Devon Tuma (most of `OracleComp`, `OracleSpec`), with Quang Dao, Alexander Hicks and James Waters
in neighbouring modules. The file headers say "VCVio Contributors".

## ===== TCSlib/Cryptography/Games.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Games.Protocols

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Security games and protocols as oracle computations

One framework for the security games and the two-party protocols of [PS10] chapters 5–8:
- oracle computations, a free monad over an indexed family of oracles;
- uniform sampling as an oracle, with a real-valued, finite-sum probability;
- stateful oracle implementations with query logging, and simulation;
- the shapes of security advantages;
- the game-hopping lemmas;
- two-party executions.

It lives in the namespace `TCSlib.Cryptography.Games`. Its connections to the ch. 2–4 layer are
the next layer (S2b): the concrete layer's `QueryTree` and `uprob`, the machine model `NUPPT`, and
the interaction model `Strategy`.

## Contents

* `TCSlib.Cryptography.Games.OracleComp`: oracle specifications, oracle computations, unions,
  query costs.
* `TCSlib.Cryptography.Games.Probability`: the sampling oracle, expectations, probabilities,
  output distributions.
* `TCSlib.Cryptography.Games.Simulate`: oracle implementations, simulation, logging, composition.
* `TCSlib.Cryptography.Games.Advantage`: acceptance, distinguishing and guess-the-bit
  advantages, the hybrid argument.
* `TCSlib.Cryptography.Games.Hopping`: the difference lemma, identical until bad, the collision
  bound.
* `TCSlib.Cryptography.Games.Protocols`: parties, the message exchange, executions.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
* [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
  code-based game-playing proofs*, EUROCRYPT 2006.
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
  ePrint 2004/332.
-/

## ===== TCSlib/Cryptography/Games/OracleComp.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Notation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle computations

The syntax of security games and protocols. An *oracle specification* names a family of oracles,
each with a type of queries and a type of answers. An *oracle computation* over it asks one
oracle a query, looks at the answer, chooses what to do next, and eventually returns a value. It
is the free monad over the specification: a finite tree whose inner nodes are queries, with one
subtree per possible answer.

Everything else in the framework is built on this file:
- uniform sampling is one more oracle (`TCSlib.Cryptography.Games.Probability`);
- running a computation against implementations of its oracles is `simulate`
  (`TCSlib.Cryptography.Games.Simulate`);
- a two-party protocol is a pair of computations whose oracle is the message exchange
  (`TCSlib.Cryptography.Games.Protocols`).

With one oracle, an oracle computation is a `TCSlib.Cryptography.QueryTree` of the concrete
layer ([Gar26]); the bridge between the two is in the S2b layer.

## Main definitions

* `Games.OracleSpec ι`: a family of oracles named by `ι`.
* `Games.OracleComp spec α`: computations with access to the oracles of `spec`, returning an `α`;
  a `Monad` and a `LawfulMonad`.
* `Games.OracleComp.call i x`: ask oracle `i` the query `x` and return the answer.
* `Games.OracleSpec.add`: the disjoint union of two oracle families;
  `OracleComp.liftLeft`/`liftRight` run a computation over one part in the union.
* `Games.OracleComp.CostBoundedBy cost c q`: every run of `c` spends at most `q`, oracle `i`
  costing `cost i` per query (for example, 1 for the oracle under attack and 0 for coin draws).

## Main results

* `Games.OracleComp.instLawfulMonad`: the monad laws.
* `Games.OracleComp.CostBoundedBy.bind`: costs add under sequencing.
* `Games.OracleComp.costBoundedBy_liftLeft`, `costBoundedBy_liftRight`: lifting into a union of
  specifications keeps the cost.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (oracle adversaries).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games

/-- A **family of oracles** named by `ι`: oracle `i` accepts queries in `dom i` and answers in
`rng i`. [VCVio, OracleComp/OracleSpec] -/
structure OracleSpec (ι : Type) where
  /-- The queries oracle `i` accepts. -/
  dom : ι → Type
  /-- The answers oracle `i` gives. -/
  rng : ι → Type

/-- **Oracle computations** over `spec` returning an `α`: either return a value, or ask oracle
`i` the query `x` and continue with `k` applied to the answer. This is the free monad over
`spec`; an oracle adversary of [Gar26, Definition 3.9] or [PS10, §3.8.1] with fixed coins is the
one-oracle case. [VCVio, OracleComp/OracleComp] -/
inductive OracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type where
  /-- Return `a` without further queries. -/
  | pure : α → OracleComp spec α
  /-- Ask oracle `i` the query `x`, and continue with `k` on the answer. -/
  | query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α) : OracleComp spec α

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {α β γ : Type}

/-- Sequencing: run `c`, then `f` on its result. Queries of `c` come first. -/
def bind : OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
  | .pure a, f => f a
  | .query i x k, f => .query i x (fun y => bind (k y) f)

instance : Monad (OracleComp spec) where
  pure := .pure
  bind := bind

/-- `>>=` is `OracleComp.bind`. -/
theorem bind_eq_bind (c : OracleComp spec α) (f : α → OracleComp spec β) :
    (c >>= f) = c.bind f := rfl

/-- `pure` is the constructor `OracleComp.pure`. -/
theorem pure_eq_pure (a : α) : (Pure.pure a : OracleComp spec α) = .pure a := rfl

/-- `<$>` is sequencing with a return. -/
theorem map_eq_bind (h : α → β) (c : OracleComp spec α) :
    (h <$> c) = c.bind (fun a => .pure (h a)) := rfl

/-- Returning first, then continuing, is continuing. -/
@[simp] theorem pure_bind (a : α) (f : α → OracleComp spec β) : (OracleComp.pure a).bind f = f a :=
  rfl

/-- A query followed by `f` is the query whose continuation is followed by `f`. -/
@[simp] theorem query_bind (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (f : α → OracleComp spec β) :
    (OracleComp.query i x k).bind f = .query i x (fun y => (k y).bind f) := rfl

/-- Continuing with a return changes nothing. -/
@[simp] theorem bind_pure (c : OracleComp spec α) : c.bind .pure = c := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- Sequencing is associative. -/
theorem bind_assoc (c : OracleComp spec α) (f : α → OracleComp spec β)
    (g : β → OracleComp spec γ) : (c.bind f).bind g = c.bind (fun a => (f a).bind g) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- The monad laws. -/
instance instLawfulMonad : LawfulMonad (OracleComp spec) :=
  LawfulMonad.mk' _
    (id_map := fun c => bind_pure c)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun c f g => bind_assoc c f g)

/-- Ask oracle `i` the query `x` and return the answer. -/
def call (i : ι) (x : spec.dom i) : OracleComp spec (spec.rng i) :=
  .query i x .pure

/-- Asking and then continuing with `f` is the query with continuation `f`. -/
@[simp] theorem call_bind (i : ι) (x : spec.dom i) (f : spec.rng i → OracleComp spec α) :
    (call i x).bind f = .query i x f := rfl

/-! ### Unions of oracle families -/

end OracleComp

/-- The **disjoint union** of two oracle families: oracle `.inl i` is oracle `i` of `s₁`, and
oracle `.inr j` is oracle `j` of `s₂`. [VCVio, OracleComp/OracleSpec] -/
def OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :
    OracleSpec (ι₁ ⊕ ι₂) :=
  ⟨Sum.elim s₁.dom s₂.dom, Sum.elim s₁.rng s₂.rng⟩

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {α β : Type}

/-- Run a computation over `s₁` inside the union `s₁.add s₂`, asking only oracles of `s₁`. -/
def liftLeft {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₁ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query i x k => .query (.inl i) x (fun y => liftLeft (k y))

/-- Run a computation over `s₂` inside the union `s₁.add s₂`, asking only oracles of `s₂`. -/
def liftRight {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₂ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query j x k => .query (.inr j) x (fun y => liftRight (k y))

/-- Lifting commutes with sequencing. -/
theorem liftLeft_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₁ α)
    (f : α → OracleComp s₁ β) :
    (liftLeft (s₂ := s₂) (c.bind f)) = (liftLeft c).bind (fun a => liftLeft (f a)) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, liftLeft, ih]

/-- Lifting commutes with sequencing. -/
theorem liftRight_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₂ α)
    (f : α → OracleComp s₂ β) :
    (liftRight (s₁ := s₁) (c.bind f)) = (liftRight c).bind (fun a => liftRight (f a)) := by
  induction c with
  | pure a => rfl
  | query j x k ih => simp only [query_bind, liftRight, ih]

/-! ### Query costs -/

variable {spec : OracleSpec ι₁}

/-- `c` is **cost-bounded by `q`**: along every run, the total cost of its queries, oracle `i`
costing `cost i` per query, is at most `q`. With `cost` equal to 1 on the oracle under attack and
0 elsewhere, this is "at most `q` queries to that oracle", the query bound of
[Gar26, Definition 3.9]. -/
def CostBoundedBy (cost : ι₁ → ℕ) : OracleComp spec α → ℕ → Prop
  | .pure _, _ => True
  | .query i _ k, q => cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i)

/-- A return costs nothing. -/
@[simp] theorem costBoundedBy_pure (cost : ι₁ → ℕ) (a : α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.pure (spec := spec) a) q :=
  trivial

/-- A query is within budget `q` exactly when its cost fits and every continuation fits in what
is left. -/
@[simp] theorem costBoundedBy_query (cost : ι₁ → ℕ) (i : ι₁) (x : spec.dom i)
    (k : spec.rng i → OracleComp spec α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.query i x k) q ↔
      cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i) :=
  Iff.rfl

/-- A larger budget is still a bound. -/
theorem CostBoundedBy.mono {cost : ι₁ → ℕ} {c : OracleComp spec α} {q q' : ℕ}
    (h : CostBoundedBy cost c q) (hq : q ≤ q') : CostBoundedBy cost c q' := by
  induction c generalizing q q' with
  | pure a => trivial
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := h
    exact ⟨Nat.le_trans hi hq, fun y => ih y (hk y) (Nat.sub_le_sub_right hq _)⟩

/-- **Costs add under sequencing:** if `c` fits in `q₁` and every continuation `f a` fits in
`q₂`, then `c` followed by `f` fits in `q₁ + q₂`.

**Proof sketch.** Induction on `c`. At a query of cost `cost i ≤ q₁`, the continuation fits in
`q₁ - cost i` by hypothesis, so by induction it fits in `(q₁ - cost i) + q₂`, which is
`(q₁ + q₂) - cost i`. -/
theorem CostBoundedBy.bind {cost : ι₁ → ℕ} {c : OracleComp spec α} {f : α → OracleComp spec β}
    {q₁ q₂ : ℕ} (hc : CostBoundedBy cost c q₁) (hf : ∀ a, CostBoundedBy cost (f a) q₂) :
    CostBoundedBy cost (c.bind f) (q₁ + q₂) := by
  induction c generalizing q₁ with
  | pure a => exact (hf a).mono (Nat.le_add_left _ _)
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := hc
    refine ⟨Nat.le_trans hi (Nat.le_add_right _ _), fun y => ?_⟩
    rw [Nat.sub_add_comm hi]
    exact ih y (hk y)

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
left part. -/
theorem costBoundedBy_liftLeft {s₂ : OracleSpec ι₂} {cost : ι₁ ⊕ ι₂ → ℕ} {c : OracleComp spec α}
    {q : ℕ} (h : CostBoundedBy (fun i => cost (.inl i)) c q) :
    CostBoundedBy cost (liftLeft (s₂ := s₂) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query i x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
right part. -/
theorem costBoundedBy_liftRight {s₁ : OracleSpec ι₂} {cost : ι₂ ⊕ ι₁ → ℕ}
    {c : OracleComp spec α} {q : ℕ} (h : CostBoundedBy (fun j => cost (.inr j)) c q) :
    CostBoundedBy cost (liftRight (s₁ := s₁) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query j x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

end OracleComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic computations

Randomness enters the framework as one more oracle: oracle `m` of `unifSpec` answers a uniformly
random element of `Fin (m + 1)`, and a uniform element of any nonempty finite type is obtained
through an enumeration. A *probabilistic computation* (`ProbComp`) is an oracle computation whose
only oracle is this one. Security games, once their adversary is plugged in and their oracles
implemented, are probabilistic computations.

The semantics is elementary and real-valued. The expectation of `g` over the output of a
computation is defined by recursion on the computation: a return contributes `g a`, and a sampling
step averages over its `m + 1` equally likely answers. There are no measures and no extended
reals: every computation is a finite tree with finite branching, so every probability is a finite
sum of rationals. The probability of an event is the expectation of its indicator. For a
computation with a finite output type, its output distribution is a `FinDist` of the library's
information-theory layer, so statistical distance and closeness (`EpsClose`) apply directly.

## Main definitions

* `Games.unifSpec`: the uniform-sampling oracles; `Games.ProbComp`: computations over them.
* `Games.ProbComp.sampleFin m`, `Games.ProbComp.sample T`: a uniform element of `Fin (m + 1)`, and
  of a nonempty finite type `T`.
* `Games.ProbComp.expect c g`: the expectation of `g` over the output of `c`.
* `Games.ProbComp.prob c p`: the probability that the output of `c` satisfies `p`.
* `Games.ProbComp.dist c`: the output distribution of `c`, for a finite output type.

## Main results

* `ProbComp.expect_bind`: **total expectation**; sequencing averages the continuations.
* `ProbComp.expect_sample`: sampling a finite type is the uniform average.
* `ProbComp.expect_add`, `expect_const_mul`, `expect_sum`, `expect_mono`: linearity and
  monotonicity.
* `ProbComp.prob_nonneg`, `prob_le_one`, `prob_mono`, `prob_or_le` (the union bound),
  `prob_not`, `prob_bind`.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
  Uniform sampling as an oracle follows VCVio's uniform-selection oracle; the real-valued
  finite-sum semantics here is not VCVio's (which is measure-valued).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (probabilistic algorithms; the uniform distribution over coin strings).
-/

namespace TCSlib.Cryptography.Games

open Finset TCSlib.InformationTheory

/-- The **uniform-sampling oracles**: oracle `m` takes no query and answers a uniformly random
element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp] -/
abbrev unifSpec : OracleSpec ℕ := ⟨fun _ => Unit, fun m => Fin (m + 1)⟩

/-- **Probabilistic computations**: oracle computations whose only oracles draw uniform samples.
-/
abbrev ProbComp := OracleComp unifSpec

namespace ProbComp

variable {α β : Type}

/-- A uniformly random element of `Fin (m + 1)`. -/
def sampleFin (m : ℕ) : ProbComp (Fin (m + 1)) := .query m () .pure

/-- A uniformly random element of the nonempty finite type `T`, through its enumeration
`Fintype.equivFin`. -/
noncomputable def sample (T : Type) [Fintype T] [Nonempty T] : ProbComp T :=
  (fun j : Fin (Fintype.card T - 1 + 1) =>
    (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
      sampleFin (Fintype.card T - 1)

/-- The **expectation** of `g` over the output of `c`: `g a` for a return, and the average over
the `m + 1` equally likely answers at a sampling step. -/
noncomputable def expect : ProbComp α → (α → ℝ) → ℝ
  | .pure a, g => g a
  | .query m _ k, g => ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g

/-- The **probability** that the output of `c` satisfies `p`: the expectation of the indicator
of `p`. -/
noncomputable def prob (c : ProbComp α) (p : α → Prop) : ℝ := by
  classical exact expect c (fun a => if p a then 1 else 0)

/-- A return is its own expectation. -/
@[simp] theorem expect_pure (a : α) (g : α → ℝ) : expect (.pure a) g = g a := rfl

/-- A sampling step averages over its answers. -/
theorem expect_query (m : ℕ) (x : Unit) (k : Fin (m + 1) → ProbComp α) (g : α → ℝ) :
    expect (.query m x k) g = ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g := rfl

/-- **Total expectation:** the expectation over `c` followed by `f` is the expectation over `c`
of the expectation over `f a`.

**Proof sketch.** Induction on `c`: a return is immediate, and at a sampling step both sides
average the same continuations. -/
theorem expect_bind (c : ProbComp α) (f : α → ProbComp β) (g : β → ℝ) :
    expect (c.bind f) g = expect c (fun a => expect (f a) g) := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [OracleComp.query_bind, expect_query, ih]

/-- The expectation over a mapped computation is the expectation of the composite. -/
theorem expect_map (h : α → β) (c : ProbComp α) (g : β → ℝ) :
    expect (h <$> c) g = expect c (fun a => g (h a)) := by
  rw [OracleComp.map_eq_bind, expect_bind]; rfl

/-- Sampling `Fin (m + 1)` is the uniform average over it. -/
theorem expect_sampleFin (m : ℕ) (g : Fin (m + 1) → ℝ) :
    expect (sampleFin m) g = ((m : ℝ) + 1)⁻¹ * ∑ j, g j := rfl

/-- Sampling a nonempty finite type is the uniform average over it.

**Proof sketch.** The sample is the image of a uniform element of `Fin |T|` under the bijection
`Fintype.equivFin`, and a sum is invariant under reindexing by a bijection. -/
theorem expect_sample (T : Type) [Fintype T] [Nonempty T] (g : T → ℝ) :
    expect (sample T) g = (Fintype.card T : ℝ)⁻¹ * ∑ t, g t := by
  have hc : Fintype.card T - 1 + 1 = Fintype.card T := Nat.sub_add_cancel Fintype.card_pos
  rw [sample, expect_map, expect_sampleFin]
  congr 1
  · congr 1
    exact_mod_cast hc
  · exact Fintype.sum_equiv ((finCongr hc).trans (Fintype.equivFin T).symm) _ _
      (fun j => by simp)

/-- Expectation is additive. -/
theorem expect_add (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a + g a) = expect c f + expect c g := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [expect_query, ih, sum_add_distrib, mul_add]

/-- Expectation commutes with scaling by a constant. -/
theorem expect_const_mul (c : ProbComp α) (r : ℝ) (f : α → ℝ) :
    expect c (fun a => r * f a) = r * expect c f := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, ← mul_sum]
    ring

/-- The expectation of a constant is that constant. -/
theorem expect_const (c : ProbComp α) (r : ℝ) : expect c (fun _ => r) = r := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

/-- Expectation commutes with finite sums. -/
theorem expect_sum {ι : Type} (c : ProbComp α) (s : Finset ι) (f : ι → α → ℝ) :
    expect c (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect c (f i) := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, mul_sum]
    exact sum_comm

/-- Expectation is monotone. -/
theorem expect_mono (c : ProbComp α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expect c f ≤ expect c g := by
  induction c with
  | pure a => exact h a
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j) (by positivity)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (c : ProbComp α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ expect c f := by
  simpa [expect_const] using expect_mono c (f := fun _ => 0) h

/-! ### Probabilities of events -/

/-- The probability of `p` is the expectation of its indicator (any decidability instance). -/
theorem prob_eq_expect (c : ProbComp α) (p : α → Prop) [DecidablePred p] :
    prob c p = expect c (fun a => if p a then 1 else 0) := by
  unfold prob
  congr 1
  funext a
  congr 1

/-- A return satisfies `p` with probability one or zero. -/
theorem prob_pure (a : α) (p : α → Prop) [Decidable (p a)] :
    prob (.pure a) p = if p a then 1 else 0 := by
  classical
  rw [prob_eq_expect, expect_pure]
  congr 1

/-- **Total probability:** the probability over `c` followed by `f` is the expectation over `c`
of the probability over `f a`. -/
theorem prob_bind (c : ProbComp α) (f : α → ProbComp β) (p : β → Prop) :
    prob (c.bind f) p = expect c (fun a => prob (f a) p) := by
  classical
  simp only [prob_eq_expect, expect_bind]

/-- Probabilities are nonnegative. -/
theorem prob_nonneg (c : ProbComp α) (p : α → Prop) : 0 ≤ prob c p := by
  classical
  rw [prob_eq_expect]
  exact expect_nonneg c fun a => by split_ifs <;> norm_num

/-- Probabilities are at most one. -/
theorem prob_le_one (c : ProbComp α) (p : α → Prop) : prob c p ≤ 1 := by
  classical
  rw [prob_eq_expect]
  calc expect c (fun a => if p a then (1 : ℝ) else 0) ≤ expect c (fun _ => 1) :=
        expect_mono c fun a => by split_ifs <;> norm_num
    _ = 1 := expect_const c 1

/-- An event implied by another has at least its probability. -/
theorem prob_mono (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    prob c p ≤ prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_mono c fun a => by
    by_cases hp : p a
    · simp [hp, h a hp]
    · simp only [hp, if_false]; split_ifs <;> norm_num

/-- Events that agree on every output have the same probability. -/
theorem prob_congr (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    prob c p = prob c q :=
  le_antisymm (prob_mono c fun a => (h a).1) (prob_mono c fun a => (h a).2)

/-- **The union bound** for two events. -/
theorem prob_or_le (c : ProbComp α) (p q : α → Prop) :
    prob c (fun a => p a ∨ q a) ≤ prob c p + prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  exact expect_mono c fun a => by
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- The complement of an event has one minus its probability. -/
theorem prob_not (c : ProbComp α) (p : α → Prop) :
    prob c (fun a => ¬ p a) = 1 - prob c p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, eq_sub_iff_add_eq, ← expect_add]
  calc expect c (fun a => (if ¬ p a then (1 : ℝ) else 0) + if p a then 1 else 0)
      = expect c (fun _ => 1) := by
        congr 1; funext a; by_cases hp : p a <;> simp [hp]
    _ = 1 := expect_const c 1

/-! ### Output distributions -/

/-- The **output distribution** of a computation with a finite output type: the probability of
each outcome. -/
noncomputable def dist [Fintype α] [DecidableEq α] (c : ProbComp α) : FinDist α where
  prob a := prob c (· = a)
  nonneg a := prob_nonneg c _
  sum_prob := by
    simp only [prob_eq_expect]
    rw [← expect_sum]
    calc expect c (fun x => ∑ a, if x = a then (1 : ℝ) else 0) = expect c (fun _ => 1) := by
          congr 1; funext x; simp
      _ = 1 := expect_const c 1

/-- The output distribution gives each outcome its probability. -/
theorem dist_apply [Fintype α] [DecidableEq α] (c : ProbComp α) (a : α) :
    dist c a = prob c (· = a) := rfl

end ProbComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Simulate.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implementing oracles: simulation and logging

An oracle computation only *asks* its oracles. A security game decides how they answer: with a
keyed function, with fresh coins on every query (a randomized encryption oracle), refusing some
queries (a CCA2 decryption oracle that will not decrypt the challenge), or by asking other
oracles (a reduction that answers its adversary's queries with queries of its own). All of these
are *implementations*: for each oracle and query, a computation over a target specification that
returns the answer and updates a state. `simulate` runs a computation with every query answered
by an implementation, threading the state.

Logging is an implementation transformer: it answers as before and also appends every query and
its answer to a log kept in the state. Win conditions such as "the forged message was never
queried" are predicates on that log. Logging never changes the computation
(`simulate_withLog`).

## Main definitions

* `Games.QueryImpl spec σ spec'`: implementations of the oracles of `spec` by computations over
  `spec'`, with state `σ`.
* `Games.simulate impl c s`: run `c` from state `s`, answering its queries with `impl`.
* `Games.QueryImpl.ofComp`, `QueryImpl.passthrough`, `QueryImpl.sum`: stateless implementations,
  forwarding queries unchanged, and implementing two oracle families side by side.
* `Games.QueryLog spec`, `Games.QueryImpl.withLog`: the record of a run's queries and answers, and
  the logging transformer.
* `Games.QueryImpl.comp`: answering one implementation's queries with another.

## Main results

* `Games.simulate_bind`: simulation commutes with sequencing.
* `Games.simulate_withLog`: forgetting the log of a logged simulation gives the plain simulation.
* `Games.simulate_comp`: simulation composes; a reduction run against an implementation of its
  oracles is a single implementation of its adversary's oracles.
* `Games.simulate_costBoundedBy`: if each query of `c` to oracle `i` is answered by a computation
  of cost at most `b i`, and `c` is cost-bounded by `q` when oracle `i` costs `b i`, then the
  simulation is cost-bounded by `q`.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (answering an adversary's queries in a reduction).
-/

namespace TCSlib.Cryptography.Games

variable {ι ι' ι₁ ι₂ : Type} {α β σ : Type}

/-- An **implementation** of the oracles of `spec` by computations over `spec'`, with state `σ`:
on oracle `i`, query `x` and state `s`, a computation returning the answer and the new state.
[VCVio, SimSemantics] -/
def QueryImpl {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') : Type :=
  ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)

/-- **Simulation:** run `c` from state `s`, answering each of its queries with `impl` and
threading the state; return `c`'s result and the final state. [VCVio, SimSemantics] -/
def simulate {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec') :
    OracleComp spec α → σ → OracleComp spec' (α × σ)
  | .pure a, s => .pure (a, s)
  | .query i x k, s => (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2)

section Simulate

variable {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec')

/-- Simulating a return returns it with the state unchanged. -/
@[simp] theorem simulate_pure (a : α) (s : σ) :
    simulate impl (OracleComp.pure a) s = .pure (a, s) := rfl

/-- Simulating a query runs the implementation, then simulates the continuation. -/
@[simp] theorem simulate_query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (s : σ) :
    simulate impl (OracleComp.query i x k) s =
      (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2) := rfl

/-- **Simulation commutes with sequencing:** simulating `c` followed by `f` is simulating `c`,
then simulating `f` on its result from the state it reached.

**Proof sketch.** Induction on `c`; at a query, both sides run the implementation first, and the
monad's associativity lines up the continuations. -/
theorem simulate_bind (c : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
    simulate impl (c.bind f) s = (simulate impl c s).bind (fun p => simulate impl (f p.1) p.2) := by
  induction c generalizing s with
  | pure a => rfl
  | query i x k ih => simp only [OracleComp.query_bind, simulate_query, OracleComp.bind_assoc, ih]

/-- Simulating a single call is running the implementation. -/
theorem simulate_call (i : ι) (x : spec.dom i) (s : σ) :
    simulate impl (OracleComp.call i x) s = impl i x s := by
  simp only [OracleComp.call, simulate_query, simulate_pure]
  exact OracleComp.bind_pure _

end Simulate

namespace QueryImpl

/-- A **stateless** implementation: oracle `i` answers query `x` by running `f i x`. -/
def ofComp {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) : QueryImpl spec σ spec' :=
  fun i x s => (f i x).bind (fun y => .pure (y, s))

/-- **Forwarding:** every query is passed unchanged to the same oracle of the target. -/
def passthrough {spec : OracleSpec ι} : QueryImpl spec σ spec :=
  ofComp (fun i x => OracleComp.call i x)

/-- Implement two oracle families **side by side**, sharing one state: `.inl i` is answered by
`impl₁`, and `.inr j` by `impl₂`. -/
def sum {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') :
    QueryImpl (s₁.add s₂) σ spec'
  | .inl i => impl₁ i
  | .inr j => impl₂ j

end QueryImpl

/-! ### Composing implementations -/

/-- **Composition:** answer the queries of `spec` with `impl₁`, whose own queries (to `spec'`)
are answered by `impl₂`; the state is the pair of the two states. This is how a reduction that
answers its adversary's queries by querying its own oracles becomes, after its oracles are
implemented, a single implementation of the adversary's oracles. -/
def QueryImpl.comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') : QueryImpl spec (σ₁ × σ₂) spec'' :=
  fun i x s => (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))

/-- **Simulation composes:** simulating with `impl₂` a simulation by `impl₁` is simulating once
with the composed implementation, up to regrouping the states.

**Proof sketch.** Induction on the computation. At a query, both sides first run `impl₁`'s answer
under `impl₂` (`simulate_bind` on the left, the definition of `comp` on the right), and the
continuations agree by induction after associativity. -/
theorem simulate_comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (c : OracleComp spec α) (s₁ : σ₁) (s₂ : σ₂) :
    simulate impl₂ (simulate impl₁ c s₁) s₂ =
      (simulate (impl₂.comp impl₁) c (s₁, s₂)).bind (fun p => .pure ((p.1, p.2.1), p.2.2)) := by
  induction c generalizing s₁ s₂ with
  | pure a => rfl
  | query i x k ih =>
    simp only [simulate_query, simulate_bind, QueryImpl.comp, OracleComp.bind_assoc,
      OracleComp.pure_bind]
    congr 1
    funext p
    exact ih p.1.1 p.1.2 p.2

/-! ### Logging -/

/-- The **log** of a run: the list of its queries, each with the oracle asked, the query and the
answer, in order. [VCVio, QueryTracking/LoggingOracle] -/
abbrev QueryLog {ι : Type} (spec : OracleSpec ι) : Type :=
  List (Σ i, spec.dom i × spec.rng i)

/-- **Logging:** answer as `impl` does, and append each query and its answer to the log kept
beside the state. [VCVio, QueryTracking/LoggingOracle] -/
def QueryImpl.withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') : QueryImpl spec (σ × QueryLog spec) spec' :=
  fun i x s => (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))

/-- **Logging is conservative:** forgetting the log of a logged simulation gives the plain
simulation, whatever the initial log.

**Proof sketch.** Induction on the computation: at a query, the logged implementation is the
plain one followed by a return that only extends the log, and the continuations agree by
induction. -/
theorem simulate_withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (c : OracleComp spec α) (s : σ) (log : QueryLog spec) :
    (simulate impl.withLog c (s, log)).bind (fun p => .pure (p.1, p.2.1)) =
      simulate impl c s := by
  induction c generalizing s log with
  | pure a => rfl
  | query i x k ih =>
    simp only [simulate_query, QueryImpl.withLog, OracleComp.bind_assoc, OracleComp.pure_bind]
    congr 1
    funext ys
    exact ih ys.1 ys.2 _

/-! ### Costs under simulation -/

/-- **Costs under simulation:** if every call to oracle `i` is answered by a computation of cost
at most `b i` (target costs `cost'`), and `c` is cost-bounded by `q` when oracle `i` costs
`b i`, then the simulation of `c` is cost-bounded by `q`. With `b i = 1` for every oracle the
reduction asks once per query, the reduction makes no more target queries than its adversary
makes queries.

**Proof sketch.** Induction on `c`. At a query to oracle `i` with budget `q ≥ b i`, the
implementation fits in `b i`, and the simulated continuation fits in `q - b i` by induction, so
the sequence fits in `b i + (q - b i) = q` (`CostBoundedBy.bind`). -/
theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {impl : QueryImpl spec σ spec'} {cost' : ι' → ℕ} {b : ι → ℕ}
    (himpl : ∀ i x s, OracleComp.CostBoundedBy cost' (impl i x s) (b i))
    {c : OracleComp spec α} {q : ℕ} (hc : OracleComp.CostBoundedBy b c q) (s : σ) :
    OracleComp.CostBoundedBy cost' (simulate impl c s) q := by
  induction c generalizing q s with
  | pure a => trivial
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := hc
    have h := OracleComp.CostBoundedBy.bind (himpl i x s) (fun ys => ih ys.1 (hk ys.1) ys.2)
    rwa [Nat.add_sub_cancel' hi] at h

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Advantage.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advantages of game-playing adversaries

Security definitions come in three shapes, each measured at one value of the security parameter:
- a **search game** (forge a tag, find a collision, invert a function): its advantage is the
  probability that the game, run with the adversary, outputs `true`;
- a **distinguishing pair** (real versus random, left versus right): its advantage is the
  difference of the two games' acceptance probabilities;
- a **guess-the-bit game**: a bit `b` is drawn, the game runs on `b`, and the adversary wins if it
  outputs `b`. Its advantage is the distance of the winning probability from `½`, which is half
  the distinguishing advantage of the two games (`guessAdv_eq_half_advantage`).

Games are `ProbComp Bool`s built from the adversary; these shapes are what asymptotic security
definitions wrap with "negligible for every efficient adversary".

## Main definitions

* `Games.accept G`: the probability that `G` outputs `true`.
* `Games.advantage G₀ G₁`: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
* `Games.guessGame G`, `Games.guessAdv G`: the guess-the-bit game over `G : Bool → ProbComp Bool`
  and its advantage `|Pr[win] − ½|`.

## Main results

* `advantage_triangle`, `advantage_hybrid`: the hybrid argument; the advantage between the ends of a
  chain of games is at most the sum of the advantages between neighbours.
* `guessAdv_eq_half_advantage`: the guess-the-bit advantage is half the distinguishing advantage
  between the games for `b = 1` and `b = 0`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.1 (computational indistinguishability) and Lemma 70.2 (the hybrid lemma).
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*,
  IACR ePrint 2004/332, §3.
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset ProbComp

/-- The probability that the game `G` outputs `true`. -/
noncomputable def accept (G : ProbComp Bool) : ℝ := prob G (· = true)

/-- The **distinguishing advantage** between two games: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
[PS10, §3.1] -/
noncomputable def advantage (G₀ G₁ : ProbComp Bool) : ℝ := |accept G₀ - accept G₁|

/-- An acceptance probability is between zero and one. -/
theorem accept_nonneg (G : ProbComp Bool) : 0 ≤ accept G := prob_nonneg G _

/-- An acceptance probability is at most one. -/
theorem accept_le_one (G : ProbComp Bool) : accept G ≤ 1 := prob_le_one G _

/-- The distinguishing advantage is nonnegative. -/
theorem advantage_nonneg (G₀ G₁ : ProbComp Bool) : 0 ≤ advantage G₀ G₁ := abs_nonneg _

/-- The distinguishing advantage is symmetric. -/
theorem advantage_comm (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ = advantage G₁ G₀ :=
  abs_sub_comm _ _

/-- A game has no advantage against itself. -/
@[simp] theorem advantage_self (G : ProbComp Bool) : advantage G G = 0 := by simp [advantage]

/-- The distinguishing advantage is at most one. -/
theorem advantage_le_one (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ ≤ 1 := by
  unfold advantage
  rw [abs_le]
  constructor <;> linarith [accept_nonneg G₀, accept_nonneg G₁, accept_le_one G₀, accept_le_one G₁]

/-- **One game hop:** the advantage between `G₀` and `G₂` is at most the sum of the advantages
through `G₁`. -/
theorem advantage_triangle (G₀ G₁ G₂ : ProbComp Bool) :
    advantage G₀ G₂ ≤ advantage G₀ G₁ + advantage G₁ G₂ :=
  abs_sub_le _ _ _

/-- **The hybrid argument:** along a chain of games `G 0, …, G n`, the advantage between the ends
is at most the sum of the advantages between neighbours. [PS10, Lemma 70.2], [Sho04, §3]

**Proof sketch.** Induction on `n`, one game hop (`advantage_triangle`) per step. -/
theorem advantage_hybrid (G : ℕ → ProbComp Bool) (n : ℕ) :
    advantage (G 0) (G n) ≤ ∑ i ∈ range n, advantage (G i) (G (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    exact (advantage_triangle _ (G n) _).trans (by linarith)

/-! ### Guess-the-bit games -/

/-- The **guess-the-bit game** over `G`: draw a uniform bit `b`, run `G b`, and win if its output
is `b`. -/
noncomputable def guessGame (G : Bool → ProbComp Bool) : ProbComp Bool :=
  (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))

/-- The **guess-the-bit advantage**: how far the winning probability is from `½`. -/
noncomputable def guessAdv (G : Bool → ProbComp Bool) : ℝ := |accept (guessGame G) - 1 / 2|

/-- The winning probability of the guess-the-bit game is the average of `Pr[G 1 = 1]` and
`Pr[G 0 = 0]`.

**Proof sketch.** Total probability over the uniform bit (two equally likely values), and
`Pr[G 0 = 0] = 1 − Pr[G 0 = 1]`. -/
theorem accept_guessGame (G : Bool → ProbComp Bool) :
    accept (guessGame G) = (accept (G true) + (1 - accept (G false))) / 2 := by
  classical
  have hnot : prob (G false) (· = false) = 1 - accept (G false) := by
    rw [accept, ← prob_not]
    exact prob_congr _ fun b => by cases b <;> simp
  unfold accept guessGame
  rw [prob_bind, expect_sample]
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton, Fintype.card_bool, prob_bind]
  have h1 : expect (G true) (fun b' => prob (OracleComp.pure (decide (b' = true))) (· = true)) =
      prob (G true) (· = true) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  have h0 : expect (G false) (fun b' => prob (OracleComp.pure (decide (b' = false))) (· = true)) =
      prob (G false) (· = false) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  rw [h1, h0, hnot]
  simp only [accept]
  push_cast
  ring

/-- **Guessing versus distinguishing:** the guess-the-bit advantage is half the distinguishing
advantage between `G 1` and `G 0`. -/
theorem guessAdv_eq_half_advantage (G : Bool → ProbComp Bool) :
    guessAdv G = advantage (G true) (G false) / 2 := by
  unfold guessAdv advantage
  rw [accept_guessGame]
  rw [show (accept (G true) + (1 - accept (G false))) / 2 - 1 / 2 =
      (accept (G true) - accept (G false)) / 2 by ring, abs_div, abs_two]

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Hopping.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Advantage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Game hopping

The steps of a game-based security proof, proved once:
- **the difference lemma**: two events that agree unless a "bad" event happens differ in
  probability by at most the probability of the bad event;
- **identical until bad**: two oracle implementations that answer identically until a flag in
  their state is raised, and never lower it, give simulations whose outputs differ in probability
  by at most the probability that the flag is raised;
- **a collision bound**: a fresh uniform sample lands in a list of at most `q` earlier values with
  probability at most `q / |T|`. This is the "bad event" of most PRF-based proofs, for example a
  repeated nonce in [PS10, Thm 168.2].

The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Advantage`).

## Main definitions

* `Games.OracleComp.AllOutputs P c`: every possible output of `c` satisfies `P`.

## Main results

* `ProbComp.prob_eq_one_of_allOutputs`, `ProbComp.expect_mono_of_allOutputs`: reasoning on the
  possible outputs only.
* `ProbComp.abs_prob_sub_le_of_agree`: the difference lemma [Sho04, Lemma 1].
* `ProbComp.prob_mem_le`: the collision bound.
* `Games.prob_eq_until_bad`, `Games.identical_until_bad`: the code-based fundamental lemma
  [BR06, Lemma 2].

## References

* [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
  code-based game-playing proofs*, EUROCRYPT 2006, §2 (Lemma 2, the fundamental lemma).
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*,
  IACR ePrint 2004/332, §4 (Lemma 1, the difference lemma).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Thm 168.2 (proof sketch: the bad events of the CPA analysis).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset

variable {ι : Type} {α β σ : Type}

/-- **Every possible output** of `c` satisfies `P`: a return satisfies it, and every
continuation of a query does, whatever the answer. -/
def OracleComp.AllOutputs {spec : OracleSpec ι} (P : α → Prop) : OracleComp spec α → Prop
  | .pure a => P a
  | .query _ _ k => ∀ y, AllOutputs P (k y)

/-- `AllOutputs` is monotone in the predicate. -/
theorem OracleComp.AllOutputs.mono {spec : OracleSpec ι} {P Q : α → Prop} (hPQ : ∀ a, P a → Q a)
    {c : OracleComp spec α} (h : c.AllOutputs P) : c.AllOutputs Q := by
  induction c with
  | pure a => exact hPQ a h
  | query i x k ih => exact fun y => ih y (h y)

/-- Every possible output of `c` followed by `f` satisfies `Q` when every possible output `a`
of `c` satisfies `P` and every possible output of `f a` with `P a` satisfies `Q`. -/
theorem OracleComp.AllOutputs.bind {spec : OracleSpec ι} {P : α → Prop} {Q : β → Prop}
    {c : OracleComp spec α} {f : α → OracleComp spec β} (hc : c.AllOutputs P)
    (hf : ∀ a, P a → (f a).AllOutputs Q) : (c.bind f).AllOutputs Q := by
  induction c with
  | pure a => exact hf a hc
  | query i x k ih => exact fun y => ih y (hc y)

namespace ProbComp

/-- An event splits by a second event: `Pr[A] = Pr[A ∧ ¬F] + Pr[A ∧ F]`. -/
theorem prob_split (c : ProbComp α) (A F : α → Prop) :
    prob c A = prob c (fun a => A a ∧ ¬ F a) + prob c (fun a => A a ∧ F a) := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  congr 1
  funext a
  by_cases hA : A a <;> by_cases hF : F a <;> simp [hA, hF]

/-- An expectation only depends on the function's values at the possible outputs. -/
theorem expect_mono_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
    {f g : α → ℝ} (h : ∀ a, P a → f a ≤ g a) : expect c f ≤ expect c g := by
  induction c with
  | pure a => exact h a hc
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j (hc j)) (by positivity)

/-- An event holding at every possible output has probability one. -/
theorem prob_eq_one_of_allOutputs {c : ProbComp α} {p : α → Prop} (hc : c.AllOutputs p) :
    prob c p = 1 := by
  classical
  refine le_antisymm (prob_le_one c p) ?_
  rw [prob_eq_expect]
  calc (1 : ℝ) = expect c (fun _ => 1) := (expect_const c 1).symm
    _ ≤ _ := expect_mono_of_allOutputs hc fun a ha => by simp [ha]

/-- An event failing at every possible output has probability zero. -/
theorem prob_eq_zero_of_allOutputs {c : ProbComp α} {p : α → Prop}
    (hc : c.AllOutputs fun a => ¬ p a) : prob c p = 0 := by
  have h := prob_not c p
  rw [prob_eq_one_of_allOutputs hc] at h
  linarith

/-- **The difference lemma:** if the events `A` and `B` agree at every output where `F` fails,
their probabilities differ by at most the probability of `F`. [Sho04, Lemma 1]

**Proof sketch.** Pointwise, the indicators of `A` and `B` differ by at most the indicator of
`F`; take expectations in both directions (linearity and monotonicity). -/
theorem abs_prob_sub_le_of_agree (c : ProbComp α) {A B F : α → Prop}
    (h : ∀ a, ¬ F a → (A a ↔ B a)) : |prob c A - prob c B| ≤ prob c F := by
  classical
  have key : ∀ (A B : α → Prop), (∀ a, ¬ F a → (A a ↔ B a)) →
      prob c A ≤ prob c B + prob c F := by
    intro A B hAB
    rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
    exact expect_mono c fun a => by
      by_cases hF : F a
      · by_cases hA : A a <;> by_cases hB : B a <;> simp [hA, hB, hF]
      · have := hAB a hF
        by_cases hA : A a
        · simp [hA, this.1 hA, hF]
        · simp [hA, hF]; split_ifs <;> norm_num
  rw [abs_le]
  constructor
  · linarith [key B A fun a ha => (h a ha).symm]
  · linarith [key A B h]

/-- **The collision bound:** if every possible output list has length at most `q`, a fresh
uniform element of `T` lies in the list with probability at most `q / |T|`.

**Proof sketch.** By total probability over the list, it suffices that a fixed list `L` of length
at most `q` is hit with probability `#{t ∈ L} / |T| ≤ q / |T|`; average over the possible lists
with `expect_mono_of_allOutputs`. -/
theorem prob_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (c : ProbComp (List T))
    {q : ℕ} (hc : c.AllOutputs fun L => L.length ≤ q) :
    prob (c.bind fun L => (sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1) ≤
      q / Fintype.card T := by
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  rw [prob_bind]
  calc expect c (fun L => prob ((sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1))
      ≤ expect c (fun _ => (q : ℝ) / Fintype.card T) := by
        refine expect_mono_of_allOutputs hc fun L hL => ?_
        rw [prob_bind, expect_sample]
        have hsum : ∑ t : T, prob (OracleComp.pure (L, t)) (fun p : List T × T => p.2 ∈ p.1) =
            (L.toFinset.card : ℝ) := by
          simp only [prob_pure, Finset.sum_boole]
          congr 2
          ext t
          simp
        rw [hsum, inv_mul_eq_div]
        refine div_le_div_of_nonneg_right ?_ hT.le
        exact_mod_cast (List.toFinset_card_le L).trans hL
    _ = q / Fintype.card T := expect_const c _

end ProbComp

/-- From a bad state, every possible final state of the simulation is bad, when the
implementation never leaves a bad state. -/
theorem simulate_allOutputs_bad {spec : OracleSpec ι} {impl : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) (hstick : ∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) {s : σ} (hs : bad s) :
    (simulate impl c s).AllOutputs fun r => bad r.2 := by
  induction c generalizing s with
  | pure a => exact hs
  | query i x k ih =>
    rw [simulate_query]
    exact OracleComp.AllOutputs.bind (hstick i x s hs) fun ys hys => ih ys.1 hys

/-- **Equal until bad:** from a good state, two implementations that agree on good states and
keep bad states bad give the same probability to "`Q` holds and the final state is good", and the
same probability to "the final state is bad".

**Proof sketch.** Induction on the computation. At a query from a good state both implementations
are the same computation; for each of its outputs, a good new state is the induction hypothesis,
and a bad new state makes the first event impossible and the second certain on both sides
(`simulate_allOutputs_bad`). -/
theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) (hagree : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s)
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (Q : α → Prop) {s : σ} (hs : ¬ bad s) :
    ProbComp.prob (simulate impl₀ c s) (fun r => Q r.1 ∧ ¬ bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => Q r.1 ∧ ¬ bad r.2) ∧
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => bad r.2) := by
  induction c generalizing s with
  | pure a => exact ⟨rfl, rfl⟩
  | query i x k ih =>
    simp only [simulate_query, ProbComp.prob_bind, hagree i x s hs]
    constructor
    · congr 1
      funext ys
      by_cases hb : bad ys.2
      · rw [ProbComp.prob_eq_zero_of_allOutputs
            ((simulate_allOutputs_bad bad hstick₀ _ hb).mono fun r hr h => h.2 hr),
          ProbComp.prob_eq_zero_of_allOutputs
            ((simulate_allOutputs_bad bad hstick₁ _ hb).mono fun r hr h => h.2 hr)]
      · exact (ih ys.1 hb).1
    · congr 1
      funext ys
      by_cases hb : bad ys.2
      · rw [ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₀ _ hb),
          ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₁ _ hb)]
      · exact (ih ys.1 hb).2

/-- **Identical until bad** (the code-based fundamental lemma): let two implementations of the
same oracles agree on every query made from a state where `bad` fails, and let each keep `bad`
once it holds (every possible new state of a bad state is bad). Then, from a good state, for any
computation `c` and event `p` on its output, the probabilities of `p` under the two simulations
differ by at most the probability that the first simulation ends in a bad state.
[BR06, Lemma 2], [Sho04, §4]

**Proof sketch.**
1. *Sticky:* from a bad state, every possible final state of either simulation is bad
   (induction on `c`, from the hypothesis on each implementation).
2. *Equal until bad:* from a good state, the two simulations give the same probability to
   "`p` holds and the final state is good", and the same probability to "the final state is bad".
   Induction on `c`: at a query from a good state both implementations are the same computation;
   for each of its outputs, a good new state is the induction hypothesis, and a bad new state
   makes "good at the end" impossible and "bad at the end" certain on both sides (step 1,
   `prob_eq_zero_of_allOutputs`, `prob_eq_one_of_allOutputs`).
3. Write each probability of `p` as "`p` and good" plus at most "bad", and conclude with the
   difference lemma's arithmetic. -/
theorem identical_until_bad {spec : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop)
    (hagree : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s)
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (p : α → Prop) {s : σ} (hs : ¬ bad s) :
    |ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) -
        ProbComp.prob (simulate impl₁ c s) (fun r => p r.1)| ≤
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) := by
  obtain ⟨h1, h2⟩ := prob_eq_until_bad bad hagree hstick₀ hstick₁ c p hs
  rw [ProbComp.prob_split (simulate impl₀ c s) (fun r => p r.1) (fun r => bad r.2),
    ProbComp.prob_split (simulate impl₁ c s) (fun r => p r.1) (fun r => bad r.2), h1]
  have a0 := ProbComp.prob_nonneg (simulate impl₀ c s) (fun r => p r.1 ∧ bad r.2)
  have a1 := ProbComp.prob_nonneg (simulate impl₁ c s) (fun r => p r.1 ∧ bad r.2)
  have b0 := ProbComp.prob_mono (simulate impl₀ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  have b1 := ProbComp.prob_mono (simulate impl₁ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  rw [abs_le]
  constructor <;> linarith

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Protocols.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two-party protocols as oracle computations

A party of a two-party protocol is an oracle computation with two kinds of oracles: the message
exchange (send a message, receive the other party's next message) and its own coins. Running the
protocol interleaves the two parties as coroutines: the active party runs until it sends a
message, the other party resumes with that message and runs until it replies, and so on. When a
party returns its output, the other party's pending send is answered `none` ("the other party has
finished"), so it too can finish.

This is the same framework as security games: a party's view (its coins and the messages it
received) is the log of its own oracle answers, and simulation-based security compares two
`ProbComp`s with `advantage`. The bridge to the next-message strategies of the ch. 2–4 layer
(`TCSlib.Cryptography.Strategy`, `TCSlib.Cryptography.exec`) is part of the S2b layer.

## Main definitions

* `Games.exchangeSpec Out In`: the message-exchange oracle (send an `Out`, receive an `In` or
  `none`).
* `Games.Party Out In α`: a party sending `Out`, receiving `In`, drawing its own coins and returning
  an `α`.
* `Games.Party.step`: run a party until it returns or sends a message.
* `Games.Party.finish`: finish a party whose counterpart has returned.
* `Games.Party.exec fuel A B`: execute a protocol in which `A` moves first, with at most `fuel`
  messages.

## Main results

* `Games.Party.exec_zero`, `Party.exec_succ`: the execution equations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines, executions, views) and §6.2 (two-party secure computation).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

/-- The **message-exchange oracle**: the query is the message sent, and the answer is the other
party's next message, or `none` if the other party has returned. [PS10, §4.4] -/
abbrev exchangeSpec (Out In : Type) : OracleSpec Unit := ⟨fun _ => Out, fun _ => Option In⟩

/-- A **party** of a two-party protocol: sends messages of type `Out`, receives messages of type
`In`, draws its own coins, and returns an `α`. [PS10, §4.4] -/
abbrev Party (Out In α : Type) : Type := OracleComp ((exchangeSpec Out In).add unifSpec) α

namespace Party

variable {Out In α β : Type}

/-- Run a party until it returns or sends a message, passing its coin draws through. The result is
either its output, or the message it sends together with how it continues on the reply. -/
def step : Party Out In α → ProbComp (α ⊕ (Out × (Option In → Party Out In α)))
  | .pure a => .pure (.inl a)
  | .query (.inl ()) m k => .pure (.inr (m, k))
  | .query (.inr j) x k => .query j x (fun y => step (k y))

/-- Finish a party whose counterpart has returned: every further send is answered `none`. -/
def finish : Party Out In α → ProbComp α
  | .pure a => .pure a
  | .query (.inl ()) _ k => finish (k none)
  | .query (.inr j) x k => .query j x (fun y => finish (k y))

/-- **Execution** of a two-party protocol with at most `fuel` messages. `A` moves first, and `B`
waits for `A`'s first message (`none` if `A` returns at once). After each message the roles swap.
The result is both outputs, or `none` if the fuel runs out first. [PS10, §4.4] -/
def exec : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) → ProbComp (Option (α × β))
  | 0, _, _, _, _, _, _ => .pure none
  | fuel + 1, _, _, _, _, A, B =>
    (step A).bind (Sum.elim
      (fun a => (finish (B none)).bind fun b => .pure (some (a, b)))
      (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure (r.map Prod.swap)))

/-- Without fuel, the execution stops at once. -/
@[simp] theorem exec_zero {M₁ M₂ : Type} (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
    exec 0 A B = .pure none := rfl

/-- One move of the execution: `A` runs until it returns (then `B` finishes) or sends `m` (then
`B` resumes with `m` as the first mover, against `A`'s continuation). -/
theorem exec_succ {M₁ M₂ : Type} (fuel : ℕ) (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β) :
    exec (fuel + 1) A B =
      (step A).bind (Sum.elim
        (fun a => (finish (B none)).bind fun b => .pure (some (a, b)))
        (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure (r.map Prod.swap))) :=
  rfl

end Party

end TCSlib.Cryptography.Games

## ===== TCSlib/InformationTheory/FinDist.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Distributions on a finite type

A lightweight, real-valued model of a probability distribution on a finite type: a nonnegative
function summing to one. This is deliberately not `PMF`, whose `ℝ≥0∞` values make subtraction
truncated and Cauchy–Schwarz awkward — and the arguments this file supports (collision
probability, the `ℓ¹`–`ℓ²` bound, the leftover hash lemma) are all differences of real numbers.

## Main definitions

* `TCSlib.InformationTheory.FinDist α`: a distribution on a finite type.
* `FinDist.uniform`, `FinDist.map`, `FinDist.prod`: the uniform distribution, pushforward along a
  function, and the product (independent pair) of two distributions.
* `FinDist.collision`: the collision probability `∑ p a ^ 2`, i.e. the chance that two
  independent samples agree.
* `FinDist.HasMinEntropy p k`: every outcome has probability at most `2 ^ (-k)`.

## Main results

* `FinDist.collision_le_of_hasMinEntropy`: min-entropy `k` bounds the collision probability by
  `2 ^ (-k)`.
* `FinDist.collision_uniform`, `FinDist.inv_card_le_collision`: the uniform distribution
  minimizes collision probability.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.
* [Sho09] V. Shoup, *A Computational Introduction to Number Theory and Algebra*, 2nd ed., §8.
-/

namespace TCSlib.InformationTheory

open Finset

/-- A probability distribution on a finite type: nonnegative weights summing to one. -/
structure FinDist (α : Type*) [Fintype α] where
  /-- The probability assigned to each outcome. -/
  prob : α → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ a, 0 ≤ prob a
  /-- Probabilities sum to one. -/
  sum_prob : ∑ a, prob a = 1

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

instance : CoeFun (FinDist α) (fun _ => α → ℝ) := ⟨FinDist.prob⟩

@[simp] theorem coe_mk (f : α → ℝ) (h₁ : ∀ a, 0 ≤ f a) (h₂ : ∑ a, f a = 1) (a : α) :
    (⟨f, h₁, h₂⟩ : FinDist α) a = f a := rfl

@[ext] theorem ext {p q : FinDist α} (h : ∀ a, p a = q a) : p = q := by
  cases p; cases q; simpa using funext h

theorem le_one (p : FinDist α) (a : α) : p a ≤ 1 := by
  rw [← p.sum_prob]
  exact single_le_sum (fun b _ => p.nonneg b) (mem_univ a)

theorem card_pos (p : FinDist α) : 0 < Fintype.card α := by
  by_contra hcon
  have hzero : Fintype.card α = 0 := by omega
  haveI : IsEmpty α := Fintype.card_eq_zero_iff.1 hzero
  have hsum := p.sum_prob
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  norm_num at hsum

instance (p : FinDist α) : Nonempty α := Fintype.card_pos_iff.1 p.card_pos

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : FinDist α where
  prob _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_prob := by
    have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp

@[simp] theorem uniform_apply [Nonempty α] (a : α) :
    uniform α a = (Fintype.card α : ℝ)⁻¹ := rfl

/-- The pushforward of a distribution along a function. -/
def map [DecidableEq β] (f : α → β) (p : FinDist α) : FinDist β where
  prob b := ∑ a ∈ univ.filter (fun a => f a = b), p a
  nonneg _ := sum_nonneg fun a _ => p.nonneg a
  sum_prob := by
    rw [← p.sum_prob]
    exact sum_fiberwise_eq_sum_filter univ univ f p.prob ▸ (sum_fiberwise _ _ _)

@[simp] theorem map_apply [DecidableEq β] (f : α → β) (p : FinDist α) (b : β) :
    map f p b = ∑ a ∈ univ.filter (fun a => f a = b), p a := rfl

/-- The product of two distributions: an independent pair. -/
def prod (p : FinDist α) (q : FinDist β) : FinDist (α × β) where
  prob x := p x.1 * q x.2
  nonneg x := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, p.sum_prob, q.sum_prob]

@[simp] theorem prod_apply (p : FinDist α) (q : FinDist β) (x : α × β) :
    prod p q x = p x.1 * q x.2 := rfl

/-- The collision probability of `p`: the probability that two independent samples from `p`
are equal. [Vad12, §6.1] -/
def collision (p : FinDist α) : ℝ := ∑ a, p a ^ 2

theorem collision_nonneg (p : FinDist α) : 0 ≤ collision p :=
  sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem collision_uniform [Nonempty α] :
    collision (uniform α) = (Fintype.card α : ℝ)⁻¹ := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [collision, uniform_apply, Finset.sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- Uniform is the distribution of least collision probability. -/
theorem inv_card_le_collision (p : FinDist α) : (Fintype.card α : ℝ)⁻¹ ≤ collision p := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast p.card_pos
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := p.prob)
  rw [p.sum_prob, card_univ] at h
  have h2 : (1 : ℝ) ≤ (Fintype.card α : ℝ) * collision p := by
    simpa [collision] using h
  rw [inv_le_iff_one_le_mul₀ hc]
  linarith [mul_comm (Fintype.card α : ℝ) (collision p)]

/-- `p` has min-entropy at least `k` when no outcome has probability more than `2 ^ (-k)`.
Stated as this bound rather than as `-logb 2 (⨆ a, p a)` so that no logarithms appear in the
hypotheses of the results that use it. [Vad12, §6.2] -/
def HasMinEntropy (p : FinDist α) (k : ℝ) : Prop := ∀ a, p a ≤ (2 : ℝ) ^ (-k)

/-- Min-entropy `k` bounds the collision probability by `2 ^ (-k)`: the chance of a collision is
at most the chance of hitting any single most-likely point.

**Proof sketch.** `∑ p a ^ 2 ≤ (max p) · ∑ p a = max p ≤ 2 ^ (-k)`. -/
theorem collision_le_of_hasMinEntropy {p : FinDist α} {k : ℝ} (h : HasMinEntropy p k) :
    collision p ≤ (2 : ℝ) ^ (-k) := by
  calc collision p = ∑ a, p a * p a := by simp [collision, sq]
    _ ≤ ∑ a, (2 : ℝ) ^ (-k) * p a :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (h a) (p.nonneg a)
    _ = (2 : ℝ) ^ (-k) := by rw [← Finset.mul_sum, p.sum_prob, mul_one]

end FinDist

end TCSlib.InformationTheory

## ===== TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adaptive oracle adversaries as query trees

An oracle adversary asks its oracle a question, looks at the answer, chooses the next
question, and finally outputs a value. At one fixed value of the security parameter such
an adversary (for a fixed coin string) is exactly a finite tree: a leaf carries the output,
and an inner node carries a query `x : I` and one subtree for each possible answer `o : O`.
The coins are a uniform element of a finite type `ρ`, so a randomized oracle adversary is a
function `ρ → QueryTree I O α`.

Running the adversary against an oracle `f : I → O` follows the path chosen by the
answers `f x`. The adversary makes at most `q` queries when every root-to-leaf path has at
most `q` inner nodes. The cost of a query in [Gar26, Definition 3.9] ("each call to that
function costs 1 unit of time") is accounted by this bound; running time otherwise is the
business of the asymptotic layer.

Answering the queries of one adversary by a computation that itself asks queries to a
second oracle (`simulate`) is the basic reduction step: the simulated tree makes the same
number of queries.

## Main definitions

* `QueryTree I O α`: adaptive query trees with queries in `I`, answers in `O` and outputs
  in `α`.
* `QueryTree.eval f t`: the output of `t` run against the oracle `f`.
* `QueryTree.BoundedBy t q`: every path of `t` makes at most `q` queries.
* `QueryTree.simulate π ans t`: answer each query `x` of `t` by asking `π x` to a new oracle
  and post-processing the answer with `ans x`.
* `OracleAdversary ρ I O`: randomized Boolean oracle adversaries with coins in `ρ`.
* `oracleDist A`: the adversary viewed as a distinguisher for oracles.

## Main results

* `QueryTree.eval_simulate`: running the simulated tree against `g` is running the
  original tree against the oracle `x ↦ ans x (g (π x))`.
* `QueryTree.BoundedBy.simulate`: simulation preserves the query bound.
* `QueryTree.BoundedBy.mono`: query bounds are monotone.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 3.9 (oracle adversaries).
-/

namespace TCSlib.Cryptography

universe u v w u' v'

/-- An adaptive oracle algorithm with queries in `I`, answers in `O` and output in `α`,
as a decision tree: `ret a` stops and outputs `a`, and `query x k` asks the oracle at `x`
and continues with the subtree `k o` for the answer `o`. This is the concrete form of an
oracle adversary with fixed coins [Gar26, Definition 3.9]. -/
inductive QueryTree (I : Type u) (O : Type v) (α : Type w) : Type (max u v w)
  /-- Stop and output `a`. -/
  | ret : α → QueryTree I O α
  /-- Ask the oracle at `x` and continue with `k` applied to the answer. -/
  | query : I → (O → QueryTree I O α) → QueryTree I O α

namespace QueryTree

variable {I : Type u} {O : Type v} {α : Type w} {I' : Type u'} {O' : Type v'}

/-- The output of the query tree `t` when every query `x` is answered by `f x`. -/
def eval (f : I → O) : QueryTree I O α → α
  | ret a => a
  | query x k => eval f (k (f x))

/-- A leaf outputs its value. -/
@[simp] theorem eval_ret (f : I → O) (a : α) : (ret a : QueryTree I O α).eval f = a := rfl

/-- A query node continues with the subtree for the oracle's answer. -/
@[simp] theorem eval_query (f : I → O) (x : I) (k : O → QueryTree I O α) :
    (query x k).eval f = (k (f x)).eval f := rfl

/-- The query tree `t` makes at most `q` oracle queries along every path: a leaf is
bounded by every `q`, and `query x k` is bounded by `q + 1` when every continuation `k o`
is bounded by `q`. -/
def BoundedBy : QueryTree I O α → ℕ → Prop
  | ret _, _ => True
  | query _ _, 0 => False
  | query _ k, q + 1 => ∀ o, BoundedBy (k o) q

/-- A leaf makes no queries. -/
@[simp] theorem boundedBy_ret (a : α) (q : ℕ) : (ret a : QueryTree I O α).BoundedBy q :=
  trivial

/-- A query node makes at least one query. -/
@[simp] theorem boundedBy_query_zero (x : I) (k : O → QueryTree I O α) :
    ¬ (query x k).BoundedBy 0 := id

/-- A query node makes at most `q + 1` queries iff every continuation makes at most
`q`. -/
@[simp] theorem boundedBy_query_succ (x : I) (k : O → QueryTree I O α) (q : ℕ) :
    (query x k).BoundedBy (q + 1) ↔ ∀ o, (k o).BoundedBy q := Iff.rfl

/-- A tree making at most `q` queries makes at most `q'` queries for every `q' ≥ q`. -/
theorem BoundedBy.mono {t : QueryTree I O α} {q q' : ℕ} (h : t.BoundedBy q)
    (hq : q ≤ q') : t.BoundedBy q' := by
  induction t generalizing q q' with
  | ret a => trivial
  | query x k ih =>
    cases q with
    | zero => exact absurd h (boundedBy_query_zero x k)
    | succ q =>
      obtain ⟨q', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
      exact fun o => ih o (h o) (by omega)

/-- Simulation of oracle queries: each query `x` of `t` is replaced by the query `π x` to a
new oracle with answers in `O'`, whose answer `o'` is turned into the answer `ans x o'` for
`t`. The simulated tree asks exactly one new query per original query. -/
def simulate (π : I → I') (ans : I → O' → O) : QueryTree I O α → QueryTree I' O' α
  | ret a => ret a
  | query x k => query (π x) (fun o' => simulate π ans (k (ans x o')))

/-- Running the simulated tree against `g` is running the original tree against the
oracle that answers `x` by `ans x (g (π x))`. -/
@[simp] theorem eval_simulate (π : I → I') (ans : I → O' → O) (g : I' → O')
    (t : QueryTree I O α) :
    (t.simulate π ans).eval g = t.eval (fun x => ans x (g (π x))) := by
  induction t with
  | ret a => rfl
  | query x k ih => exact ih _

/-- Simulation does not increase the number of queries. -/
theorem BoundedBy.simulate {t : QueryTree I O α} {q : ℕ} (h : t.BoundedBy q)
    (π : I → I') (ans : I → O' → O) : (t.simulate π ans).BoundedBy q := by
  induction t generalizing q with
  | ret a => trivial
  | query x k ih =>
    cases q with
    | zero => exact absurd h (boundedBy_query_zero x k)
    | succ q => exact fun o' => ih _ (h _)

end QueryTree

/-- A randomized Boolean oracle adversary with coins in `ρ`: for every coin string a query
tree with queries in `I`, answers in `O` and a one-bit output. [Gar26, Definition 3.9]
at one value of the security parameter; the input `1^n` is implicit in the fixed types,
and the coins are uniform over the finite type `ρ`. -/
abbrev OracleAdversary (ρ : Type*) (I : Type u) (O : Type v) := ρ → QueryTree I O Bool

/-- The randomized oracle adversary `A` makes at most `q` queries on every coin string and
every path. -/
def OracleAdversary.BoundedBy {ρ : Type*} {I : Type u} {O : Type v}
    (A : OracleAdversary ρ I O) (q : ℕ) : Prop :=
  ∀ r, (A r).BoundedBy q

/-- The oracle adversary `A` as a distinguisher for oracles: on the oracle `f` and coins
`r` it outputs the result of running `A r` against `f`. With a sampler for the oracle,
`acceptProb` of this distinguisher is the probability `Pr[A^f = 1]` of
[Gar26, Definition 3.9]. -/
def oracleDist {ρ : Type*} {I : Type u} {O : Type v} (A : OracleAdversary ρ I O) :
    (I → O) → ρ → Bool :=
  fun f r => (A r).eval f

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Foundations/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform probability on finite types

Every probability in the concrete layer of the cryptography development is the
probability of an event under the uniform distribution on a finite type: inputs, keys
and coin strings are uniform, and an experiment's sample space is the product of their
types. So probabilities are exact counts, `uprob p = |{a | p a}| / |α|`, and
expectations are averages. Distributions that are not uniform arise as pushforwards
of uniform coins.

## Main definitions

* `uprob p`: the probability that a uniformly random element satisfies `p`.
* `uexp f`: the average of a real function over a finite type.

## Main results

* `uprob_nonneg`, `uprob_le_one`, `uprob_not`, `uprob_mono`, `uprob_or_le`,
  `uprob_exists_le`: basic laws and the union bound.
* `uprob_prod`: probability over a product is the average of the probabilities of
  the sections.
* `uprob_comp_equiv`: probability is invariant under relabelling by a bijection.
* `half_le_uprob_good`: the averaging argument — if an event has probability at least
  `ε`, then at least an `ε / 2` fraction of first coordinates have a section of
  probability at least `ε / 2`.
* `abs_sub_le_sum_hybrids`, `exists_hybrid_gap`: the hybrid argument for a chain of
  probabilities.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Lemma 2.1) and §3.2 (proof of Lemma 3.3).
-/

namespace TCSlib.Cryptography

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The probability that a uniformly random element of the finite type `α` satisfies `p`,
the number of elements satisfying `p` divided by the number of elements. -/
noncomputable def uprob (p : α → Prop) : ℝ :=
  (Nat.card {a // p a} : ℝ) / Fintype.card α

/-- The average of a real function over the finite type `α`, its expectation under the
uniform distribution. -/
noncomputable def uexp (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

/-- With decidable `p`, the probability counts the elements of the filter. -/
theorem uprob_eq_card_filter (p : α → Prop) [DecidablePred p] :
    uprob p = ((univ.filter p).card : ℝ) / Fintype.card α := by
  rw [uprob, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The probability of an event is the average of its indicator. -/
theorem uprob_eq_uexp (p : α → Prop) [DecidablePred p] :
    uprob p = uexp (fun a => if p a then (1 : ℝ) else 0) := by
  rw [uprob_eq_card_filter, uexp, Finset.sum_boole]

/-- Probabilities are nonnegative. -/
theorem uprob_nonneg (p : α → Prop) : 0 ≤ uprob p := by
  unfold uprob; positivity

/-- Probabilities are at most one. -/
theorem uprob_le_one (p : α → Prop) : uprob p ≤ 1 := by
  classical
  rw [uprob_eq_card_filter]
  exact div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (by positivity)

/-- The certain event has probability one on a nonempty type. -/
theorem uprob_true [Nonempty α] : uprob (fun _ : α => True) = 1 := by
  classical
  rw [uprob_eq_card_filter, filter_true, card_univ]
  exact div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/-- The impossible event has probability zero. -/
theorem uprob_false : uprob (fun _ : α => False) = 0 := by
  classical
  rw [uprob_eq_card_filter, filter_false, card_empty, Nat.cast_zero, zero_div]

/-- The complement of an event has probability one minus its probability.

**Proof sketch.** The elements satisfying `p` and those satisfying `¬ p` partition `α`, so
their counts add up to `|α|`. -/
theorem uprob_not [Nonempty α] (p : α → Prop) : uprob (fun a => ¬ p a) = 1 - uprob p := by
  classical
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h := filter_card_add_filter_neg_card_eq_card (s := univ) p
  rw [card_univ] at h
  rw [uprob_eq_card_filter, uprob_eq_card_filter, eq_sub_iff_add_eq, ← add_div,
    div_eq_one_iff_eq hc]
  exact_mod_cast (by omega : (univ.filter fun a => ¬ p a).card + (univ.filter p).card =
    Fintype.card α)

/-- An event implied by another has at least its probability. -/
theorem uprob_mono {p q : α → Prop} (h : ∀ a, p a → q a) : uprob p ≤ uprob q := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter]
  gcongr with a
  exact h a

/-- Union bound for two events. -/
theorem uprob_or_le (p q : α → Prop) : uprob (fun a => p a ∨ q a) ≤ uprob p + uprob q := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter, uprob_eq_card_filter, ← add_div, filter_or]
  gcongr
  exact_mod_cast card_union_le _ _

/-- Union bound for finitely many events.

**Proof sketch.** The set where some `p i` holds is the union over `i ∈ s` of the sets
where `p i` holds, and the size of a union is at most the sum of the sizes. -/
theorem uprob_exists_le {ι : Type*} (s : Finset ι) (p : ι → α → Prop) :
    uprob (fun a => ∃ i ∈ s, p i a) ≤ ∑ i ∈ s, uprob (p i) := by
  classical
  rw [uprob_eq_card_filter]
  simp_rw [uprob_eq_card_filter, ← sum_div]
  gcongr
  have : (univ.filter fun a => ∃ i ∈ s, p i a) = s.biUnion (fun i => univ.filter (p i)) := by
    ext a; simp
  rw [this]
  exact_mod_cast card_biUnion_le

/-- Probability over a product is the average over the first coordinate of the
probability of the section: Fubini for uniform distributions.

**Proof sketch.** Count the pairs satisfying `p` by first coordinate:
`|{z | p z}| / (|α| |β|) = (∑ a, |{b | p (a, b)}| / |β|) / |α|`. -/
theorem uprob_prod (p : α × β → Prop) :
    uprob p = uexp (fun a => uprob (fun b => p (a, b))) := by
  classical
  simp_rw [uexp, uprob_eq_card_filter, ← sum_div, div_div, Fintype.card_prod, Nat.cast_mul,
    mul_comm (Fintype.card β : ℝ)]
  congr 1
  simp_rw [card_filter]
  push_cast
  exact Fintype.sum_prod_type _

/-- Relabelling the sample space by a bijection preserves probabilities. In particular a
permutation of a uniform input is uniform. -/
theorem uprob_comp_equiv (e : α ≃ β) (p : β → Prop) : uprob (fun a => p (e a)) = uprob p := by
  rw [uprob, uprob, Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl)),
    Fintype.card_congr e]

/-- An event depending only on the first coordinate has the same probability on the
product.

**Proof sketch.** By `uprob_prod`, the section at `a` is the certain or the impossible
event according to `p a`, so its probability is the indicator of `p a`, whose average
is `uprob p`. -/
theorem uprob_fst [Nonempty β] (p : α → Prop) : uprob (fun z : α × β => p z.1) = uprob p := by
  classical
  rw [uprob_prod, uprob_eq_uexp]
  congr 1
  funext a
  by_cases h : p a <;> simp [h, uprob_true, uprob_false]

/-- The averaging argument: if an event on `α × β` has probability at least `ε`, then
the first coordinates whose section has probability at least `ε / 2` have probability
at least `ε / 2`. [Gar26, Lemma 2.1].

**Proof sketch.** For `ε < 0` the claim is trivial, and for empty `α` both sides vanish.
Otherwise every section has probability at most `[a is good] + ε / 2`: a good `a` has
section probability at most `1`, a bad one below `ε / 2`. Averaging over `a` with Fubini
(`uprob_prod`) gives `ε ≤ uprob p ≤ Pr[good] + ε / 2`. -/
theorem half_le_uprob_good (p : α × β → Prop) {ε : ℝ} (h : ε ≤ uprob p) :
    ε / 2 ≤ uprob (fun a => ε / 2 ≤ uprob (fun b => p (a, b))) := by
  classical
  rcases lt_or_ge ε 0 with hε | hε
  · linarith [uprob_nonneg (fun a => ε / 2 ≤ uprob (fun b => p (a, b)))]
  rcases isEmpty_or_nonempty α with hα | hα
  · have : uprob p = 0 := by
      rw [uprob, Fintype.card_eq_zero, Nat.cast_zero, div_zero]
    linarith [uprob_nonneg (fun a => ε / 2 ≤ uprob (fun b => p (a, b)))]
  have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  rw [uprob_prod, uexp] at h
  rw [uprob_eq_uexp, uexp]
  have hpt : ∀ a, uprob (fun b => p (a, b)) ≤
      (if ε / 2 ≤ uprob (fun b => p (a, b)) then (1 : ℝ) else 0) + ε / 2 := by
    intro a
    split_ifs with hg
    · linarith [uprob_le_one (fun b => p (a, b))]
    · linarith
  have hsum := sum_le_sum (fun a (_ : a ∈ univ) => hpt a)
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum
  rw [le_div_iff₀ hc] at h ⊢
  linarith

/-- The hybrid argument, telescoping form: the gap between the ends of a chain is at
most the sum of the gaps between neighbours. [Gar26, proof of Lemma 3.3].

**Proof sketch.** Induction on `t` with the triangle inequality
`|P 0 - P (t+1)| ≤ |P 0 - P t| + |P t - P (t+1)|`. -/
theorem abs_sub_le_sum_hybrids (P : ℕ → ℝ) (t : ℕ) :
    |P 0 - P t| ≤ ∑ i ∈ range t, |P i - P (i + 1)| := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ]
    exact (abs_sub_le _ _ _).trans (add_le_add_right ih _)

/-- The hybrid argument: in a chain of `t ≥ 1` steps some neighbouring pair is at least
a `1 / t` fraction of the end-to-end gap apart. [Gar26, proof of Lemma 3.3].

**Proof sketch.** Otherwise the telescoping bound gives a sum below `t · (gap / t)`. -/
theorem exists_hybrid_gap (P : ℕ → ℝ) {t : ℕ} (ht : 0 < t) :
    ∃ k < t, |P 0 - P t| / t ≤ |P k - P (k + 1)| := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ i ∈ range t, |P i - P (i + 1)| < ∑ _i ∈ range t, |P 0 - P t| / t :=
    sum_lt_sum_of_nonempty (nonempty_range_iff.2 ht.ne') fun i hi => hcon i (mem_range.1 hi)
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  rw [sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ htR] at hlt
  linarith [abs_sub_le_sum_hybrids P t]

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Foundations/Experiments.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.InformationTheory.StatisticalDistance

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete security experiments

The concrete layer fixes one value of the security parameter and quantifies over all
adversaries, given as functions of their input and of a uniformly random coin string
from a finite type `ρ`. No running time is imposed here; efficiency is the job of the
asymptotic layer. The experiments are:

* inversion: on `f x` for uniform `x`, output some preimage of `f x`;
* prediction: on `f x`, output the bit `B x`;
* distinguishing: tell apart samples `X s` and `Y t` from uniform seeds `s` and `t`.

Samplers `X : σ → γ` from a finite seed type `σ` describe exactly the distributions
that are pushforwards of uniform coins, which covers every efficiently samplable
ensemble at a fixed parameter.

## Main definitions

* `invProb f A`: the probability that `A` inverts `f`.
* `predProb f B A`: the probability that `A` predicts `B` from `f`.
* `acceptProb X D`: the probability that `D` accepts a sample of `X`.
* `distAdv X Y D`: the distinguishing advantage of `D` between `X` and `Y`.

## Main results

* `acceptProb_comp_equiv`: relabelling the seeds by a bijection preserves acceptance.
* `abs_sum_sub_le_statDist`: a test set distinguishes two distributions by at most
  their statistical distance.
* `distAdv_le_statDist`: the distinguishing advantage of any distinguisher is at most
  the statistical distance of the sampled distributions.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (inversion), Definition 2.3 (prediction),
  Definitions 3.2–3.4 and Lemma 3.1 (distinguishing).
-/

namespace TCSlib.Cryptography

open Finset TCSlib.InformationTheory

variable {α β ρ σ τ γ : Type*} [Fintype α] [Fintype ρ] [Fintype σ] [Fintype τ]

/-- The probability that the adversary `A`, given `f x` for uniform `x` and uniform coins
`r`, outputs a preimage of `f x`. [Gar26, Definition 2.1, Equation (2.1)], at one value of
the security parameter; the input `1^n` is implicit in the fixed types. -/
noncomputable def invProb (f : α → β) (A : β → ρ → α) : ℝ :=
  uprob fun z : α × ρ => f (A (f z.1) z.2) = f z.1

/-- The probability that the adversary `A`, given `f x` for uniform `x` and uniform coins
`r`, outputs the bit `B x`. [Gar26, Definition 2.3], at one value of the security
parameter. -/
noncomputable def predProb (f : α → β) (B : α → Bool) (A : β → ρ → Bool) : ℝ :=
  uprob fun z : α × ρ => A (f z.1) z.2 = B z.1

/-- The probability that the distinguisher `D` with uniform coins accepts a sample `X s`
for a uniform seed `s`. [Gar26, Definitions 3.2 and 3.4], the quantities `p(n)` and
`q(n)`. -/
noncomputable def acceptProb (X : σ → γ) (D : γ → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => D (X z.1) z.2 = true

/-- The distinguishing advantage of `D` between the sampled distributions `X` and `Y`,
`|Pr[D(X) = 1] - Pr[D(Y) = 1]|`. [Gar26, Definitions 3.2 and 3.4], the quantity
`Δ_A(n)`. -/
noncomputable def distAdv (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) : ℝ :=
  |acceptProb X D - acceptProb Y D|

/-- Relabelling the seed space of a sampler by a bijection does not change the probability
that a distinguisher accepts: a bijective image of a uniform seed is uniform. -/
theorem acceptProb_comp_equiv (e : σ ≃ τ) (X : τ → γ) (D : γ → ρ → Bool) :
    acceptProb (fun s => X (e s)) D = acceptProb X D :=
  uprob_comp_equiv (e.prodCongr (Equiv.refl ρ)) (fun z : τ × ρ => D (X z.1) z.2 = true)

/-- The probability that a uniform seed `s` has `X s` in an event `q` is the mass of `q` under
the pushforward of the uniform distribution along `X`. Technical glue between `uprob` and
`FinDist.map`.

**Proof sketch.** Both sides equal `∑ s, [q (X s)] / |σ|`: on the right, group the seeds
by their image under `X`. -/
theorem uprob_comp_eq_sum_map [Nonempty σ] [Fintype γ] [DecidableEq γ] (X : σ → γ)
    (q : γ → Prop) [DecidablePred q] :
    uprob (fun s => q (X s)) = ∑ g ∈ univ.filter q, (FinDist.uniform σ).map X g := by
  rw [uprob_eq_card_filter, sum_filter]
  have h := Finset.sum_fiberwise' univ X
    (fun g => if q g then (Fintype.card σ : ℝ)⁻¹ else 0)
  have h2 : ∑ s, (if q (X s) then (Fintype.card σ : ℝ)⁻¹ else 0) =
      ((univ.filter fun s => q (X s)).card : ℝ) / Fintype.card σ := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [← h2, ← h]
  refine sum_congr rfl fun g _ => ?_
  split_ifs <;> simp [FinDist.map_apply]

/-- The acceptance probability of `D` on samples of `X` is the average over the coins `r` of
the mass, under the distribution of `X`, of the set of samples that `D` accepts with coins
`r`. Technical glue for `distAdv_le_statDist`.

**Proof sketch.** Swap the two coordinates of the sample space, apply Fubini
(`uprob_prod`) to average over the coins first, and rewrite each section with
`uprob_comp_eq_sum_map`. -/
theorem acceptProb_eq_uexp_sum_map [Nonempty σ] [Fintype γ] [DecidableEq γ] (X : σ → γ)
    (D : γ → ρ → Bool) :
    acceptProb X D = uexp (fun r : ρ => ∑ g ∈ univ.filter (fun g => D g r = true),
        (FinDist.uniform σ).map X g) := by
  rw [acceptProb, ← uprob_comp_equiv (Equiv.prodComm ρ σ), uprob_prod]
  congr 1
  funext r
  exact uprob_comp_eq_sum_map X (fun g => D g r = true)

/-- For any set `T` of outcomes, `|p(T) - q(T)|` is at most the statistical distance of `p`
and `q`. This is the deterministic case of [Gar26, Lemma 3.1].

**Proof sketch.** The differences `d = p - q` sum to zero, so the sum of `d` over the
complement of `T` is `-d(T)`. Splitting `∑ |d|` over `T` and its complement and applying
the triangle inequality to each part gives `∑ |d| ≥ 2 |d(T)|`. -/
theorem abs_sum_sub_le_statDist [Fintype γ] (p q : FinDist γ) (T : Finset γ) :
    |∑ g ∈ T, (p g - q g)| ≤ statDist p q := by
  classical
  have h0 : ∑ g, (p g - q g) = 0 := by
    rw [sum_sub_distrib, p.sum_prob, q.sum_prob, sub_self]
  have hsplit := sum_add_sum_compl T (fun g => p g - q g)
  have habs := sum_add_sum_compl T (fun g => |p g - q g|)
  have h1 := abs_sum_le_sum_abs (fun g => p g - q g) T
  have h2 := abs_sum_le_sum_abs (fun g => p g - q g) Tᶜ
  have hneg : ∑ g ∈ Tᶜ, (p g - q g) = -∑ g ∈ T, (p g - q g) := by linarith
  rw [hneg, abs_neg] at h2
  rw [statDist]
  linarith

/-- The distinguishing advantage of any distinguisher, deterministic or with coins, is at
most the statistical distance of the two sampled distributions. [Gar26, Lemma 3.1].

**Proof sketch.** Average over the coins (`acceptProb_eq_uexp_sum_map`): for fixed coins
`r` the distinguisher is a test set `T_r`, whose advantage is `|X(T_r) - Y(T_r)|`. By
`abs_sum_sub_le_statDist` each of these is at most the statistical distance, and the
absolute value of an average is at most the average of the absolute values. -/
theorem distAdv_le_statDist [Nonempty σ] [Nonempty τ] [Nonempty ρ] [Fintype γ]
    [DecidableEq γ] (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    distAdv X Y D ≤
      statDist ((FinDist.uniform σ).map X) ((FinDist.uniform τ).map Y) := by
  have hρ : (0 : ℝ) < Fintype.card ρ := Nat.cast_pos.2 Fintype.card_pos
  rw [distAdv, acceptProb_eq_uexp_sum_map X, acceptProb_eq_uexp_sum_map Y, uexp, uexp,
    ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_comm, ← nsmul_eq_mul, ← card_univ, ← sum_const]
  refine sum_le_sum fun r _ => ?_
  rw [← sum_sub_distrib]
  exact abs_sum_sub_le_statDist _ _ _

end TCSlib.Cryptography

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence/replay-head.log =====

# replay of PR #185 head 597eef43ccd3c8bfafe0c0c16a2444b12adc1644, 2026-11-04T23:24:09Z, fresh olean tree, 8 modules
=== TCSlib/InformationTheory/FinDist start 23:24:09
=== TCSlib/InformationTheory/FinDist end 23:24:13 rc=0
=== TCSlib/Cryptography/Games/OracleComp start 23:24:13
=== TCSlib/Cryptography/Games/OracleComp end 23:24:13 rc=0
=== TCSlib/Cryptography/Games/Probability start 23:24:13
=== TCSlib/Cryptography/Games/Probability end 23:24:16 rc=0
=== TCSlib/Cryptography/Games/Simulate start 23:24:16
=== TCSlib/Cryptography/Games/Simulate end 23:24:17 rc=0
=== TCSlib/Cryptography/Games/Advantage start 23:24:17
=== TCSlib/Cryptography/Games/Advantage end 23:24:19 rc=0
=== TCSlib/Cryptography/Games/Hopping start 23:24:19
=== TCSlib/Cryptography/Games/Hopping end 23:24:22 rc=0
=== TCSlib/Cryptography/Games/Protocols start 23:24:22
=== TCSlib/Cryptography/Games/Protocols end 23:24:25 rc=0
=== TCSlib/Cryptography/Games start 23:24:25
=== TCSlib/Cryptography/Games end 23:24:27 rc=0
pass 8/8 errors 0 warnings 0 sorry 0

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence/replay-order.txt =====

TCSlib/InformationTheory/FinDist
TCSlib/Cryptography/Games/OracleComp
TCSlib/Cryptography/Games/Probability
TCSlib/Cryptography/Games/Simulate
TCSlib/Cryptography/Games/Advantage
TCSlib/Cryptography/Games/Hopping
TCSlib/Cryptography/Games/Protocols
TCSlib/Cryptography/Games

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence/axioms.log =====

# axioms at PR #185 head 597eef43ccd3c8bfafe0c0c16a2444b12adc1644
'TCSlib.Cryptography.Games.OracleComp.bind_eq_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.pure_eq_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.map_eq_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.pure_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.query_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.bind_pure' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.bind_assoc' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.call_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.liftLeft_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.liftRight_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_query' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.mono' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.bind' depends on axioms: [propext]
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_liftLeft' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_liftRight' does not depend on any axioms
'TCSlib.Cryptography.Games.ProbComp.expect_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_query' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sampleFin' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_or_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_not' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.dist_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.simulate_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_query' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_call' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_comp' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_withLog' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_costBoundedBy' depends on axioms: [propext]
'TCSlib.Cryptography.Games.accept_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.accept_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.accept_guessGame' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.guessAdv_eq_half_advantage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.AllOutputs.mono' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.AllOutputs.bind' does not depend on any axioms
'TCSlib.Cryptography.Games.ProbComp.prob_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_mono_of_allOutputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_one_of_allOutputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_zero_of_allOutputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.abs_prob_sub_le_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.simulate_allOutputs_bad' does not depend on any axioms
'TCSlib.Cryptography.Games.prob_eq_until_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.identical_until_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Party.exec_zero' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.exec_succ' does not depend on any axioms
# exit 0

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence/style-lint.log =====

# scripts/style_lint.py at PR #185 head 597eef43ccd3c8bfafe0c0c16a2444b12adc1644

0 findings in 7 files







# line widths: no line over 100 characters (checked by script)

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence/name-screen.log =====

# name screen at PR #185 head 597eef43ccd3c8bfafe0c0c16a2444b12adc1644
## short names declared both in TCSlib.Cryptography.Games and elsewhere in TCSlib.Cryptography (ambiguous under both opens): none (distAdv renamed to advantage in 597eef43)
## related existing concepts (generalized, not copied; bridges scheduled in S2b):
TCSlib/Cryptography/Foundations/Experiments.lean:72:noncomputable def acceptProb (X : σ → γ) (D : γ → ρ → Bool) : ℝ :=
TCSlib/Cryptography/Foundations/Experiments.lean:78:noncomputable def distAdv (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) : ℝ :=
TCSlib/Cryptography/Foundations/Probability.lean:59:noncomputable def uprob (p : α → Prop) : ℝ :=
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean:64:inductive QueryTree (I : Type u) (O : Type v) (α : Type w) : Type (max u v w)
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean:122:def simulate (π : I → I') (ans : I → O' → O) : QueryTree I O α → QueryTree I' O' α
TCSlib/Cryptography/SchnorrProtocol.lean:58:def simulate (pk : G) (c s : ZMod q) : Transcript G q :=
## Mathlib at the pinned rev: OracleComp/OracleSpec/ProbComp/QueryImpl names
(none listed = no hit)
