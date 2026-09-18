# Formalization Plan: Arora-Barak Chapter 2 — NP and NP-completeness

Continuation of the Chapter 1 campaign (`AroraBarakChapter1Plan.md`, complete and
audited end to end), on the same branch `complexity/arora-barak-ch1`, under the same
methodology: audited statement phases with proof sketches, cross-vendor LLM audit
gates between phases, then a fill campaign in epochs of parallel disjoint-ownership
batches (zip delivery), verification through `scripts/lean_check_tree.sh` (**`lake
build` stays banned**), `scripts/style_lint.py` conformance, drift attestations
(ordered + multiset, per the epoch-4 methodology), and a blueprint-extraction
increment at closure. Audit artifacts are named `audits/ch2-phase*` /
`audits/ch2-epoch*`; briefs `briefs/ch2-*`.

## 1. Scope: what Chapter 2 contains

[AB09, ch. 2, pp. 38-67.] The mandatory core of this campaign:

* **§2.1** — `NP` via polynomial-time verifiers (Definition 2.1); Claim 2.4
  (`P ⊆ NP ⊆ EXP`); nondeterministic TMs, `NTIME`, and Theorem 2.6
  (`NP = ⋃ c, NTIME (n^c)`).
* **§2.2** — Karp reductions, `NP`-hardness/completeness (Definition 2.7);
  Theorem 2.8 (transitivity; the collapse consequences); Theorem 2.9 (`TMSAT` is
  `NP`-complete).
* **§2.3** — CNF formulas, `SAT`, `3SAT`; Claim 2.13 (CNF universality);
  **Theorem 2.10 (Cook-Levin)** via Lemma 2.11 (`SAT` is `NP`-hard, by the
  oblivious-machine tableau) and Lemma 2.14 (`SAT ≤ₚ 3SAT`).
* **§2.6** — `coNP` (Definitions 2.19/2.20 and their equivalence, Exercise 2.24),
  `EXP`/`NEXP`, Theorem 2.22 (`EXP ≠ NEXP → P ≠ NP`, padding); `TAUTOLOGY`
  `coNP`-complete (Example 2.21, once formulas exist).
* Selected exercises with structural value: 2.1 (bounded-length certificates),
  2.8 (`HALT` is `NP`-hard but not `NP`-complete — the bridge to Chapter 1),
  2.23 (`P ⊆ NP ∩ coNP`), 2.25 (`P = NP → NP = coNP`), 2.27 (`NEXP` without
  NDTMs).

**Deferred (phase-5-style, not scheduled):** §2.4's web of reductions (`INDSET`,
`0/1 IPROG`, `dHAMPATH`, and the exercise problems — each needs a graph/arithmetic
encoding surface; one exemplar may be pulled forward later to validate the
pattern, and the legacy `NPReductions/*` files may eventually be retargeted as the
structure-level halves); §2.5 decision-versus-search (Theorem 2.18); parsimonious
and Levin reductions (§2.3.6); the universal NDTM (Exercise 2.6 — Chapter 3's
tool); Berman's theorem (Exercise 2.30).

## 2. Foundation decisions

* **`NP` is verifier-first, language-level.** `L ∈ NP` iff there are a
  polynomially bounded certificate length `p` and a *language* `V ∈ P` with
  `x ∈ L ↔ ∃ u, |u| = p |x| ∧ x ++ u ∈ V`. Rendering the verifier as a
  `P`-language (rather than a bare machine) reuses the audited Chapter-1 class
  and — decisively — **sidesteps the pairing/splitting subtlety** of [AB09]'s
  footnote 4: the definition never needs to recover `x` from `x ++ u`. Every
  planned consumer constructs its own concatenations (`P ⊆ NP` takes `p = 0`,
  the `NP ⊆ EXP` enumerator builds `x ++ u` itself, and Cook-Levin's tableau
  works on the literal string `y = x ∘ u` with condition 1 pinning the
  `x`-prefix). Concrete `V`s that *do* split (e.g. `EXP ⊆ NEXP`) prove their
  split computable case by case, against a monotone length majorant.
* **Certificates have exact length `p |x|`** (Definition 2.1 verbatim); the
  bounded-length variant is Exercise 2.1, stated as an equivalence whose proof
  enlarges `p` to the monotone majorant `C(n+1)^c` and pads certificates
  right-self-delimitingly (`u ++ [true] ++ false-run`).
* **NDTMs are binary-choice and functional** (phase 2): two total transition
  functions per [AB09] §2.1.2, semantics by a choice-word-indexed run function
  in the house `runFrom` style — *not* cslib's relational `MultiTapeNTM`
  (Papadimitriou-style arbitrary branching, `List`-chain semantics, stuck
  configurations), for the reasons recorded in the decision log. Acceptance is
  **output-based** (`[true]` on some choice word), consistent with
  `DecidesInTime`; `NTIME`'s totality bound quantifies over *all* choice words.
  Both are flagged as design questions for the phase-2 audit.
* **Poly-time computability of reduction functions is the recurring cost.**
  `Complexity.PolyTimeComputable` (FP) is defined in phase 1 together with its
  closure calculus (identity, composition — via the audited
  `computesFunInTime_comp` plus output-length bounds); further combinators
  (concatenation, constant prefixing, unary padding) are added in the phase that
  first needs them, never speculatively.
* **CNF formulas** (phase 3): the type, its evaluation, and its binary
  serialization with a parser and fallback totalization ([AB09] footnote 3 =
  the `codeFallback` convention). In-house type vs. `Std.Sat.CNF` is a recorded
  design question for the phase-3 audit.
* **Cook-Levin runs on our oblivious machines.** [AB09] proves Lemma 2.11 for
  oblivious *two-tape* machines and notes (footnote 5) the proof generalizes to
  any oblivious machine; `Complexity.oblivious_of_mem_DTIME` (quadratic,
  unrestricted tape count, oblivious on *all* inputs at every physical time) is
  the supply side. Snapshots have constant size `(state, k+1 symbols)`.

## 3. Architecture and module layout

New directory `TCSlib/Complexity/ClassNP/` (namespace `Complexity`), facade
`TCSlib/Complexity/ClassNP.lean`; later phases add `TCSlib/Complexity/Formulas/`
(or similar) for CNF and `NDTM` modules under `TuringMachine/`. Phase-1 layout:

| Module | Contents |
|---|---|
| `ClassNP/PolyTime.lean` | `PolyBound`, `PolyTimeComputable` (FP), identity/composition closure, output-length bound |
| `ClassNP/NP.lean` | `NP` (Definition 2.1, verifier-language form), `P ⊆ NP`, Exercise 2.1 |
| `ClassNP/CoNP.lean` | `coNP` (complement form), Definition 2.20 equivalence, `compl_mem_P`, Exercises 2.23/2.25 |
| `ClassNP/EXP.lean` | `EXP`, `ExpBound`, `NEXP` (Exercise-2.27 form), `P ⊆ EXP`, `NP ⊆ EXP`, `EXP ⊆ NEXP` |
| `ClassNP/Reductions.lean` | `PolyTimeReducible` (`≤ₚ`), `NPHard`, `NPComplete`, Theorem 2.8, downward closure of `P`, Exercise 2.8 (both halves) |

Chapter-1 files remain frozen at their audited surface; any addition to them is
flagged for audit per standing practice.

## 4. Phasing

Audit protocol as in Chapter 1 (`AroraBarakChapter1Plan.md` §5 "Audit protocol"):
each phase lands definitions plus sorried statements with policy-grade proof
sketches, an audit pack goes out, gates close on zero blockers/majors.

1. **Phase 1 — Classes and reductions** (this commit): the table above;
   ~14 sorried statements.
2. **Phase 2 — Nondeterminism**: raw binary-choice NDTM + choice-word semantics
   (`TuringMachine/Nondeterministic.lean`), `NTIME`, Theorem 2.6 (both
   directions as machine compilations), `NEXP` NTIME-form equivalence,
   Theorem 2.22 (padding).
3. **Phase 3 — Formulas, SAT, TMSAT**: CNF type + evaluation + serialization +
   parser/fallback; `SAT`, `3SAT`, membership in `NP`; Claim 2.13; Lemma 2.14
   statement; `TAUTOLOGY` + Example 2.21; `TMSAT` + Theorem 2.9 (supporting
   obligation: polynomial time-constructibility `n ↦ n^c`).
4. **Phase 4 — Cook-Levin**: snapshot/tableau layer over oblivious machines,
   the schedule-computability interface (head positions from a clocked
   simulation on a trivial input), Lemma 2.11, Theorem 2.10.
5. **Fill campaign**: scheduled after all gates close, epochs ordered by risk
   exactly as in Chapter 1 — (E1) assemblies + poly-calculus core, (E2) NDTM
   compilations + `NP ⊆ EXP` enumerator + padding + `TMSAT`, (E3)
   `SAT ≤ₚ 3SAT` machine + tableau correctness mathematics, (E4) the
   Cook-Levin reduction machine (the summit; B2-style continuation budget
   anticipated), (E5) closure: zero-sorry sweep, drift attestation, final audit
   pack, blueprint increment.

## 5. Risks and honest effort assessment

* **The Cook-Levin reduction machine is the summit** — a machine *emitting* the
  tableau formula clause-by-clause within a polynomial ledger, driven by the
  oblivious schedule. Larger than `universal` in my estimate; everything else is
  sequenced to de-risk it first.
* **Poly-time computability obligations recur** at every reduction; the
  mitigation is the phase-1 calculus plus need-driven combinators. A potential
  lever, recorded as an open option: upgrading `MathlibBridge` to preserve
  polynomial bounds (our `bridgeTM` costs O(1) native steps per TM2 statement
  operation, so a Mathlib `TM2ComputableInPolyTime` certificate would transfer)
  — an option, not a load-bearing assumption, since Mathlib supplies few such
  certificates.
* **Definition conventions are where audits bite** (the Argument-A lesson);
  the seeded design questions below go to the auditors *before* any fill.
* Estimated mandatory-core scale: ~35-45 audited sorries over four phases —
  larger than Chapter 1's 21, with one summit instead of two.

## 6. Decision log

| Decision | Status |
|---|---|
| Chapter 2 proceeds on branch `complexity/arora-barak-ch1` (name notwithstanding), same methodology, gates, tooling, and delivery mechanics as Chapter 1; artifacts under `ch2-*` names | Decided |
| **Prior-art survey for NDTMs** (2026-09-18): Mathlib has none (nondeterminism stops at `NFA`/`EpsilonNFA`; TM0/1/2 deterministic). cslib — at our vendoring pin `a3747758` and unchanged on `main` — has `MultiTape/Nondeterministic.lean` (relational `MultiTapeNTM`, Papadimitriou §2.7 style, `List`-chain `ComputationPath` semantics, per-path exact-time notions, no acceptance, no all-branch time bound) and `MultiTape/DeterministicToNondeterministic.lean` (singleton-relation embedding). **Decision: do not port.** [AB09]'s binary-choice model is load-bearing for Theorem 2.6 (the certificate *is* the choice word; general relations have no canonical certificate encoding and admit stuck configurations), the campaign's proof style is functional (`runFrom` algebra — the original vendoring deliberately dropped cslib's relational semantics), and the port would drag in cslib's `IsChainFromTo` foundation plus new-module-system syntax. cslib's model is recorded as related work; a trivial embedding of our binary machine into their relational one is optional future upstream-reconciliation work | Decided |
| Vendored-file upstream drift check (2026-09-18): `Configuration.lean` and `Deterministic.lean` byte-identical upstream since pin `a3747758`; cslib's MultiTape directory has since grown (`TapeLemmas`, `ConfigBound`, combinators, `SingleTape/*`) — nothing needed now | Decided |
| `NP` defined verifier-first with the verifier as a language `V ∈ P` and exact-length concatenated certificates (`x ++ u`, no pairing) — splitting subtleties pushed to the concrete constructions that need them | Decided — flagged for phase-1 audit |
| `EXP := ⋃ c, DTIME (2 ^ n ^ c)` ([AB09] Claim 2.4 verbatim); `NEXP` in Exercise-2.27 verifier form with `ExpBound` certificate lengths, NTIME-form equivalence deferred to phase 2 | Decided — flagged for phase-1 audit |
| Design questions seeded for the **phase-1 audit**: (a) the `V ∈ P` verifier rendering vs. explicit machines; (b) exact-length certificates as primary with Exercise 2.1 as the bridge; (c) `PolyBound`'s `C·(n+1)^c` normal form; (d) `Complexity.compl_mem_P` as a new statement on Chapter-1 classes (addition beyond the audited ch-1 surface, flagged); (e) the `≤ₚ` notation scope | Open — to auditors |
| Design questions seeded for the **phase-2 audit**: (a) output-based acceptance (`[true]` on some choice word) vs. a literal `qaccept` state — [AB09] deviation to be justified or reversed; (b) `NTIME`'s all-branch halting bound quantifier placement; (c) choice words as `List Bool` vs. `ℕ → Bool` | Open — to auditors |
| Design question seeded for the **phase-3 audit**: in-house CNF type vs. `Std.Sat.CNF`; serialization scheme and fallback convention | Open — to auditors |
| §2.4 web of reductions, §2.5 search-to-decision, parsimonious/Levin reductions, Exercise 2.6 (universal NDTM), Berman's theorem: **deferred**, not scheduled in the mandatory core | Decided |
| `MathlibBridge` poly-time upgrade as an optional lever for reduction machines | Open — revisit at phase 3 |

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Ch. 2, pp. 38-67.)
