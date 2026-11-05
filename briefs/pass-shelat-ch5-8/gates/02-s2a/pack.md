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
