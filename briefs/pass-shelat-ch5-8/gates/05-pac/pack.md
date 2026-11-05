# Gate 05 (Pass–shelat ch. 5–8, S3d layer 1): external audit pack

**Status: ready to dispatch** (staged 2026-11-05; the user ruled on Q-4 that the PAC layer is
gated before it lands on `main`). The evidence is under `evidence/` and
`../../evidence/pac-2026-11-05/`.

**What is audited:** PR [Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194)
into `main`, at its head `44d27f39c233849a3a30a117bf15434610e485e9` (base: `main` at
`7d36bbc27dfabd4988ee1702bc342049a1f3e006`). This is one combined gate (statements, definitions,
sketches, proofs and docstring citations), as for P0: the PR has no `sorry`, and its proofs are
short. The deliverable is **`gate05-pac-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The sources are attached separately:**
- [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010 (PDF). The item is on
  PDF p. 191 (book p. 179, §8.1, the learning question before Thm 179.1).
- [KV94] Kearns–Vazirani §1.2 and §4, and [SSBD14] Shalev-Shwartz–Ben-David ch. 3 (the second
  sources for PAC learning), if available to the auditor. Otherwise, standard knowledge of them.

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 change: definitions, theorem statements, their
docstrings and proof sketches, against the cited sources. The proofs are machine-checked; do not
review tactic scripts. The failure modes you are hunting are:
1. **Infidelity:** a definition that does not mean what the cited source means.
2. **Trivialization:** a definition or statement satisfiable for degenerate reasons (empty domain,
   empty class, `m = 0`, `ε ≥ 1`, `δ ≥ 1`).
3. **Wrong strength:** a statement weaker or stronger than its docstring claims.
4. **Missing hypotheses:** nonemptiness, finiteness.
5. **Debt:** duplication of existing proved material in the library (`FinDist` and its expectation;
   `BooleanAnalysis`'s expectations are on other carriers).
6. **Attribution:** every source-derived declaration carries a `[Tag, location]`; every deviation
   is declared, with its reason ([`policy.md`](policy.md)).

For **every definition**, restate it in your own words before reading its docstring and compare.
For **every theorem**, say in 1–3 sentences whether the statement is what its docstring claims.
Attempt at least **three adversarial instantiations**. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| New Lean (all declarations audited) | `TCSlib/InformationTheory/Samples.lean` (152 lines), `TCSlib/LearningTheory/PAC/Defs.lean` (228), `TCSlib/LearningTheory/PAC/Prediction.lean` (227) |
| Facades (imports and contents lists only) | `TCSlib/LearningTheory/PAC.lean`, `TCSlib/InformationTheory.lean`, `TCSlib.lean` |
| Context, already on `main` (not under audit) | `TCSlib/InformationTheory/FinDist.lean`, `StatisticalDistance.lean` |
| Design | `design/S3d-pac-learning.md` §"Layer 1" (the intended notions; ruling R-3) |
| Out of scope | tactic proofs; layer 2 (efficient learners and Thm 179.1, prong D) |

## Specific questions

1. **PAC learning.** Is `PACLearnsUnder`/`PACLearns` the definition of [KV94] §1.2 and [SSBD14]
   Def 3.1, apart from the declared deviation? The deviation: `PACLearnable` fixes `m, ε, δ` and
   asks for some learner at those values, where the sources ask for one algorithm for all `ε, δ`
   with a sample bound (and [KV94], efficiency). Is that deviation stated where it matters, and is
   "weaker, so impossibility results are stronger" correct?
2. **Weak learning.** Is `WeakLearnsUnder` [KV94] §4's notion (error `≤ ½ − γ`) at a fixed
   distribution?
3. **The prediction game.** Is `predictSuccess` [PS10]'s learning question on p. 179, read
   uniformly: a random concept, labelled uniform samples, and a fresh uniform point? Is the fresh
   point allowed to coincide with a sample, as in the source?
4. **The bridge and its consequences.** Is `predictSuccess_eq_one_sub_expectedErr` exactly true as
   stated? Does `not_weakLearnsUnder_of_predictAdv_le` say what Thm 179.1(c) needs: no weak learning
   with `γ' > γ + δ` when the prediction advantage is at most `γ`?
5. **`Samples.lean`.** Is `FinDist.iid` the product of `m` copies? Is
   `expect_le_add_of_le_one` stated with the right hypotheses?

## Attestations (maintainer execution claims; evidence under `evidence/`)

At `44d27f39c233849a3a30a117bf15434610e485e9` (`evidence/pac-2026-11-05/` on the records branch):
- **Elaboration:** the upstream `InformationTheory` modules and the five new or changed modules,
  each checked alone into a fresh olean tree: all pass, with 0 errors and 0 warnings.
- **`sorry`:** none.
- **Axioms:** all 38 theorems of the new files print within `propext`, `Classical.choice` and
  `Quot.sound`.
- **Lint:** `scripts/style_lint.py`, rerun by the maintainer at staging on each of
  `Samples.lean`, `PAC/Defs.lean`, `PAC/Prediction.lean` and the `PAC.lean` facade: 0 findings
  (`evidence/lint.log`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide:
- **blocker:** a downstream phase would build on a wrong statement;
- **major:** a statement is fixable but materially misleading as it stands, or accumulated debt
  (failure mode 5) that the gate may not close over without explicit human acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The gate closes at **0 blockers and 0 majors**.
