# Pass–shelat, *A Course in Cryptography*, Chapters 5–8

Status: **draft for planning, 2026-11-04.** Nothing is started; no Lean was written. It was drafted
by the maintainer agent of the Arora–Barak ch. 3–4 campaign, at the user's (Seyoon Ragavan's)
request, to be picked up by a later session. The ch. 2–4 campaign on this branch
(`PassShelatChapter2-4Plan.md`) is Frederick Dehmel's and stays his; this plan builds on its
definitions and does not modify its files.

Companion documents, all in `briefs/pass-shelat-ch5-8/`:
- `README.md`: start here;
- `inventory-ch5-8.md`: every item of ch. 5–8, with its dependencies, prong, scope and difficulty;
- `SPINE-DESIGN.md`: the shared design (base, oracle games, two-party execution, model bridges,
  the statement phase) and the open decisions;
- `WORKFLOW.md`: how the ch. 3–4 campaign is run (roles, lifecycle, gates, replays, the local
  `exchange/` folder, overnight routines), and what carries over.

## Objective and source

Formalize Chapters 5–8 of [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
3rd edition, January 2010 (book pp. 133–184; Cornell CS 4830 course page):
- **ch. 5, Authentication:** MACs from PRFs; digital signatures; Lamport one-time signatures from
  OWFs; collision-resistant hash families and the discrete-log construction; hash-and-sign. The
  many-message constructions are optional.
- **ch. 6, Computing on secret inputs:** Shamir secret sharing; honest-but-curious two-party
  security; oblivious transfer from trapdoor permutations; Yao's garbled circuits. GMW is
  statement-only.
- **ch. 7, Composability:** CPA/CCA security; the CPA/CCA1 analysis of the §3.9 scheme and its
  CCA2 failure; the encrypt-then-tag CCA2 scheme; non-malleability and its relation-based form;
  sequential composition of zero knowledge.
- **ch. 8, More on randomness:** PRFs make some concepts unlearnable; PRGs derandomize BPP into
  `DTIME(2^{n^ε})`; extractors, entropy and min-entropy, the impossibility of extraction from
  efficient sources, and the leftover hash lemma (already on `main`).

Out of scope: [PS10] ch. 1 (classical ciphers, Shannon secrecy) and the appendices, which are not
requested; and the sections the notes leave as outlines (§5.9; §7.2.3–7.3).

## What ch. 5–8 need from ch. 2–4

They need ch. 2–4's **definitions**, almost never its **proofs**. The ch. 2–4 layer's 63 open
sorries (as of its last commit, 2026-10-28) block no statement here. They reach our axiom prints
only through the few results cited:
- the DL candidate, in Thm 142.3;
- the §3.9 scheme's analysis, in Thm 168.2.

The cited declarations are listed in `SPINE-DESIGN.md` §S1 and are to be frozen by agreement with
the ch. 2–4 owner.

Two facts about the base matter:
- **The ch. 2–4 head does not build.** Two duplicate public names (`zipWith_xor_ofFn`,
  `zipWith_xor_ofFn_eq_add`) are each declared twice.
- **It forked from `main` on 2026-10-08.** `main` has since gained ch7's `ClassP/BinaryArith`
  (poly-time `+ − × div mod`, modular exponentiation, gcd, Jacobi) and randomized classes. The
  first is relevant to ch. 2–4's conditional candidates; the second to Thm 180.1 here.

## Architecture: a spine, then prongs

The prongs are independent at statement level: no prong cites another prong's theorem. In
particular Thm 170.4 (CCA2) is proved from PRFs directly, not from ch. 5's MAC. They share
infrastructure, which the **spine** builds once (`SPINE-DESIGN.md`).

| Step | What | Start condition |
|---|---|---|
| **P0** (prong zero) | Shamir secret sharing (§6.1) and extractor basics (§8.3: closeness, extractors, entropy, min-entropy, `k`-sources, the leftover hash bridge) | **now**: needs nothing from ch. 2–4; lands on `main` |
| **S1** base | a building ch. 2–4 commit (ideally merged up to `main`), the frozen interface list, new directories only | the ch. 2–4 owner's fix or agreement |
| **S2** game layer | one oracle-game design: search games (forgery, collisions) and two-phase distinguishing games (CPA/CCA, non-malleability), generalizing `OracleEnsemble` | S1 |
| **S3** shared layers | two-party execution with private inputs and outputs on his `View`; `DAGCircuit.runWith` for garbling; the NUPPT ↔ BPP bridge; the learning game | S1 |
| **S4** statement phase | every core item stated with a sketch; pre-ship probes; **one external statement gate** for ch. 5–8 | S2, S3 |
| **A** authentication (ch. 5) | MAC, signatures, Lamport, CRH from DL, hash-and-sign | S4 |
| **B** secure computation (§6.2–6.3) | special encryption, garbling, OT, Yao; GMW statement-only | S4 |
| **C** composability (ch. 7) | CPA/CCA, Thm 168.2, `π′`, non-malleability, ZK sequential composition | S4 |
| **D** randomness (§8.1–8.2, Thm 183.6) | the learning lower bound, derandomization, extraction impossibility | S4 |

**Pacing.** Run two fill prongs at a time: **B** (Yao, Thm 163.7, is the longest pole) with **A**;
then **C** and **D**. A or B stalling is the cue to start C or D early. The limits are the user's
dispatch and merge attention, review capacity, and the local Lean throttle, not dependencies.

**Sizes (ESTIMATE).** There are 50 core items. ch. 2–4 averaged about 240 landed lines per
inventory item (53k lines, 219 items), heavier in machines; that density suggests 10–20k lines for
ch. 5–8.

| Part | Lines |
|---|---|
| P0 | 0.5–1.5k |
| S2–S3 | 1–2k |
| A | 2–4k |
| B | 4–8k |
| C | 2–4k |
| D | 2–4k (Thm 180.1 is machine-level) |

## Errors and gaps in the source

The inventory's notes column records each; the main ones:
- **typos:**
  - Shamir's degree should be `k − 1`, not `n`;
  - the special encryption scheme has `x` for `m`;
  - OT sends `(z₁, z₂)`, not four values;
  - `π′`'s tag is `f_{k₂}(c₁)`;
  - "`c + 1`" in the CCA2 attack means a fixed XOR;
- **left as exercises:**
  - Shamir's security (Prop 154.5);
  - the OT receiver's simulator (in Prop 161.5);
  - the many-message signatures (§5.7);
- **proof sketches only:**
  - Thm 135.4, Thm 168.2, Thm 170.4, Thm 175.9 and Thm 179.1;
  - Thm 163.7 needs a composition step for the OT simulators that the notes do not state;
- **cited without proof:** Thm 165.2 (GMW) and the two-party fairness impossibility;
- **implicit assumptions:**
  - Thm 183.6 needs the extractor to be efficient;
  - Thm 175.1 assumes expected-polynomial-time simulators, while ch. 2–4's simulators are strict
    or truncated (its D8);
  - Thm 142.3's domain needs exponents below `p − 1`;
- **outline only:** §7.2.3–7.3, §5.9.

Second sources for the gaps, cited per `policy.md`: [Gol04] O. Goldreich, *Foundations of
Cryptography*, vol. 2; [KL] J. Katz, Y. Lindell, *Introduction to Modern Cryptography*.

## Coordination with the ch. 2–4 owner

These need agreement before S1 completes. Suggested points:
1. **A building commit to stack on:** the duplicate-name fix, ideally merged up to `main`.
2. **The interface list:** frozen; changes announced, especially after ch. 2–4's own external
   gate.
3. **New directories only:** requests go to him for anything missing in his layer.
4. **S2's relation to his `OracleEnsemble`** (decision D-2).
5. **The landing order:** ch. 2–4 reaches `main` first, or ch. 5–8 lands stacked behind it.

## Phasing

1. **Run 0:** P0, in parallel with arranging S1.
2. **Run 1, the spine:** S1, then S2 and S3 designed and probed. Decisions D-1…D-7
   (`SPINE-DESIGN.md`) taken.
3. **Run 2, the statement phase (S4):** every core item stated, compiling. Pre-ship probes, then
   one external statement gate; blockers and majors repaired.
4. **Run 3, the fills:** prongs A–D in two waves, each delivery reviewed and landed through a fill
   gate and a replay.
5. **Run 4, closure:**
   - a census and axiom prints;
   - lint and screens;
   - a completion record;
   - the optional and deferred items revisited.

## Risks

- **The base moves:** the ch. 2–4 statements are only internally audited, and its external gate may
  change them. Mitigation: cite few declarations, freeze them by agreement, and re-sync once.
- **The randomized-model split** (his `NUPPT` vs ch7's model on `main`) touches Thm 180.1 and,
  later, the library as a whole. Mitigation: a bridge lemma now (D-6); unification is a separate
  decision.
- **Thm 163.7 (Yao)** is the largest proof, and the notes skip its composition step.
  Mitigation: route probe before the gate, and [Gol04] §7.3 as the second source.
- **Bandwidth:** this is a third active line beside the ch. 3–4 campaign and ch. 2–4.

## Decision log

| Date | Decision | Status |
|---|---|---|
| 2026-11-04 | ch. 2–4 stays with Frederick Dehmel; the user pursues ch. 5–8 in parallel (user) | active |
| 2026-11-04 | Shape: P0 now; a short sequential spine (S1–S4) with one statement gate; then four prongs, two at a time (proposal; user asked for the inventory and spine design) | proposed |
| 2026-11-04 | Decisions D-1…D-7 open (`SPINE-DESIGN.md`) | **Superseded** by the rulings below |
| 2026-11-04 | Maintainer session picks up the line. Preflight passed: 4 CPUs, 15 GiB, about 25 GiB free; `leanprover/lean4:v4.25.0` installs; the narrowed Mathlib cache (12 roots, 2,230 files) fetches with no failure; `scripts/lean_check_tree.sh` elaborates the `InformationTheory` and `SecretSharing` chains (`briefs/pass-shelat-ch5-8/evidence/preflight-2026-11-04.log`) | record |
| 2026-11-04 | Finding: Shamir secret sharing is already proved on `main` (`TCSlib/Cryptography/SecretSharing/`, 2026-09-30): correctness, perfect privacy and the counting form, over any field with every nonzero element a party. [PS10] §6.1 is a special case. The spine design had listed it as new | record |
| 2026-11-04 | Finding: of the two "duplicate names" of the base, only `TCSlib.Cryptography.zipWith_xor_ofFn` clashes (`Asymptotic/Encryption` and `Asymptotic/HardCoreLoops`, joined by the `Asymptotic` facade). The two `zipWith_xor_ofFn_eq_add` are in different namespaces (`TCSlib.Cryptography` and `TCSlib.Cryptography.MultiMsg`): a duplicated statement, not a clash. To be confirmed by Lean in S1 | record (static) |
| 2026-11-04 | Source of record: the user uploaded the notes to this branch (`Pass–Shelat.pdf`, 3rd ed., January 2010, 204 pages, SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`) in commit `52457d2d1b45f690d00b23f04797e7b76dcc6285`. The course host is denied by the cloud session's network policy. No text extract is committed | record |
| 2026-11-04 | **D-0** (user): ch. 5–8 records and Lean PR bases stay on `cryptography/pass-shelat-ch2-4`; records are pushed directly | active |
| 2026-11-04 | **D-0b** (user): an orphan branch `exchange/pass-shelat-ch5-8` holds the hand-off folders `outbox/`, `inbox/`, `archive/` | active |
| 2026-11-04 | **D-1** (user): P0 lands on `main` by its own PR | active |
| 2026-11-04 | **P0, §6.1** (user): main's Shamir is cited in place: docstring-only [PS10] tags and deviation notes on `SecretSharing/Defs.lean` and `Shamir.lean`, no new declarations, in the P0 PR; Frederick is told as a courtesy. P0's new Lean is the extractor basics of §8.3 | active |
| 2026-11-04 | **D-2** (user): the S2 game layer becomes a common base, and Frederick's `OracleEnsemble` is restated over it. This edits his PRF files, so it needs his agreement (S1 note) | active, needs Frederick |
| 2026-11-04 | **D-3** (user): Thm 144.1 is core for messages of length `≤ p(n)`; the unbounded form is optional | active |
| 2026-11-04 | **D-4** (user): optional, deferred and statement-only items as in the inventory | active |
| 2026-11-04 | **D-5** (user): the learning game of Def 179.a and Thm 179.1 is built as PAC learning in `TCSlib/LearningTheory`, not a crypto-style game | active |
| 2026-11-04 | **D-6** (user): a one-way bridge lemma (a `polyTimeModel` BPP verifier gives a NUPPT running it, input hard-wired as advice); Thm 180.1 is stated against main's `InBPP` and `DTIME`. Prong D needs a base that includes `main` | active |
| 2026-11-04 | **D-7** (user): Claude for all fills | active |
| 2026-11-04 | P0 opened as [Shilun-Allan-Li/tcslib#183](https://github.com/Shilun-Allan-Li/tcslib/pull/183) (branch `cryptography/pass-shelat-ch5-8-p0`, head `789cf450527ff6b8c779161e555f04093080b88d`): `InformationTheory/Entropy.lean`, `Extractors.lean`, and [PS10] docstring citations on `SecretSharing/Defs.lean` and `Shamir.lean`. Maintainer checks: an 18-module replay into a fresh olean tree (0 errors, 0 warnings, 0 sorries); axioms standard for all 25 printed; style lint clean on the new files. Its gate is pending | active |
| 2026-11-04 | Duplication note: `EpsClose` (on `FinDist`, #183) parallels Frederick's sampler-based `StatClose` (`Asymptotic/Sampling.lean`, ch. 2–4 only). Not a copy (different carriers); a bridge lemma is owed at the integration of ch. 2–4 with `main` | record |
| 2026-11-04 | S1 note to Frederick drafted (`briefs/pass-shelat-ch5-8/S1-note-frederick.md`); for Seyoon to forward | **Superseded** by the next row |
| 2026-11-04 | The S1 note approved as drafted; Seyoon forwards it (user) | active, awaiting Frederick |
| 2026-11-04 | P0's gate: one combined external gate (statements and proofs together), since #183 has no sorry (user) | active |
| 2026-11-04 | Gate 01 staged: pack and evidence at `briefs/pass-shelat-ch5-8/gates/01-p0/` (`f2653ee20ff0b915fbe40f12fbf90b3af481bc5b`); bundle `exchange/pass-shelat-ch5-8:outbox/gates/01-p0-gate/gate01-p0-bundle.md` (19 sections, SHA-256 `97042aee164fa0e11a0ac1c2bd2f28a5398349a76934f7eee0bd30bb138bf74b`); the auditor also gets the PDF. Replay on #183's head: 18/18 | **dispatched** 2026-11-04 (user); findings awaited as `gate01-p0-findings.md` |
| 2026-11-04 | Security games reviewed (user asked). Finding: ch. 2–4 expresses each notion by hand (fixed functionals `invProb`/`predProb`/`acceptProb`/`distAdv`, one deterministic oracle with a Boolean output, a decoder per notion), which does not reach ch. 5–8's randomized and stateful oracles, oracle families, phases and transcript predicates. A general framework is proposed for S2; its form is under discussion | open |
| 2026-11-04 | **Protocols unified** (user): the S2 framework also carries two-party protocols (secure computation, ZK composition), each party an oracle computation whose oracle is the other's next-message function. This touches how Frederick's ZK layer (`Strategy`, `View`) is read, so it joins D-2 in the S1 agreement | active, needs Frederick |
| 2026-11-04 | **Duplicate DL-1 accepted as debt** (user): `abs_probTrue_sub_le_statDist` (#183) and the concrete layer's `abs_sum_sub_le_statDist`; resolved when that layer reaches `main` (`briefs/pass-shelat-ch5-8/duplication-ledger.md`) | active |
| 2026-11-04 | External code examined for comparison only (nothing taken): VCVio (github.com/dtumad/VCV-io) at `9054989327a7185ff19ef9ff0f119cccea479501`, Apache-2.0; Lean 4.35.0 with Mathlib v4.35.0. If S2's design is adapted from it, `policy.md`'s design-adaptation citation applies | record |
| 2026-11-04 | **S2 framework** (user): home-built at TCSlib's pins, **adapting VCVio's design**: indexed oracle specs, a free monad of oracle computations, stateful logging handlers. VCVio **must be cited** (user) per `policy.md` §2, in every S2 module's `## References` and in design documents: the block is fixed in `briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md`. Kept from TCSlib: `NUPPT` efficiency, finite-seed `uprob` probability, Garg's `QueryTree`/`simulate`/lazy sampling. Not a dependency: Lean 4.35 vs 4.25, a cost-model PPT, measure-valued probability | active |
| 2026-11-04 | S2 design note drafted (`briefs/pass-shelat-ch5-8/design/S2-game-framework.md`); S3b's Yao route probed (`design/S3b-yao-runWith.md`); S3a folded into S2 | record |
| 2026-11-04 | **R-1** (user): sampling is an oracle inside the monad (`unifSpec`, after VCVio), with `Pr` a finite sum; a bridge proves `Pr` equals `uprob` for fixed-shape games | active |
| 2026-11-04 | **R-2** (user): S2's generic lemmas reuse Garg's concrete-layer results through bridges B1/B2 where they fit; only what has no counterpart is proved fresh | active |
| 2026-11-04 | S2 probes: P-S2-1 passed (monad, sampling oracle, finite-sum `Pr`, `invProb` = Pr of a one-line game); P-S2-3 passed in part (stateful fresh-coin oracles, `simulate`, logging proved conservative, IND-CPA for Alg 99.1 as a program, the bad event as a log predicate; the hop itself waits for §5's lemmas) | record |
| 2026-11-04 | S3c: a scratch merge of `main` into Frederick's last Lean commit (never pushed) gives two trivial textual conflicts (`Complexity/Randomized.lean` and `ComputationalModels.lean`) and no new full-name clash. **Correction to the S1 note's point 5**, which named one file. The bridge's statement shape is in `design/S3c-bpp-bridge.md` | record |
| 2026-11-04 | S3d PAC design drafted (`design/S3d-pac-learning.md`); S2 probe P-S2-4 passed in part (two-party execution; an exchange answers `Option`, `none` once the other party has returned); S1 addendum drafted (`S1-note-frederick-addendum.md`) | record |
| 2026-11-04 | **R-3** (user): the information-theoretic PAC layer (`TCSlib/LearningTheory/PAC/`) lands on `main` by its own PR with its own gate, written after S2 settles; its efficient part and Thm 179.1 stay with prong D | active |
| 2026-11-04 | **Gate 01 closed** (#183): round 1 reported 0/0/7/3 (`gates/01-p0/gate01-p0-findings.md`); a review sub-agent confirmed 8 findings, partly confirmed 2, moved #5 to note, and added M1–M4; every minor and the optional items swept in the closing commit `16e2bd02fac1a4656a736b3f0de128e148e60e8c` (docstrings, plus six `rfl` interface lemmas); re-verified on that head: replay 18/18, 31 standard axiom prints, docstring-only on the Shamir files, lint clean. Errata E1 and E2; backlog in `gates/01-p0/resolutions.md` | closed |
| 2026-11-04 | **Spine revisited** (user asked whether spine-then-prongs still fits). Maintainer's assessment: the shape holds (prongs independent at statement level; shared infrastructure real; P0 worked), but S2 is now the largest piece and the main risk, one gate for 50 items is too coarse, and Thm 180.1 is a second long pole that barely uses S2 | record |
| 2026-11-04 | **S2 placement** (user, against the recommendation to put the core on `main`): **all of S2 stays on `cryptography/pass-shelat-ch2-4`**. Consequence: the PAC basics on `main` (R-3) do not use S2; the bridge from PAC's prediction game to S2's example-oracle game moves to prong D on the branch | active |
| 2026-11-04 | **Gating** (user): the single statement gate is **superseded**. S2a (the framework core) and S2b (bridges B1–B5, machine layer) each get an API gate (definitions plus proved lemmas); then each prong gets its own statement gate before its fills | active |
| 2026-11-04 | **Prong order** (user): Yao (B) and Thm 180.1 (D) first; Thm 180.1 starts once `main` is merged into the ch. 2–4 base, independently of S2. Then A with C; Thms 179.1 and 183.6 whenever convenient. **Supersedes** the plan's "A with B, then C with D" | active |
| 2026-11-04 | **S2a written and opened** as [Shilun-Allan-Li/tcslib#185](https://github.com/Shilun-Allan-Li/tcslib/pull/185) into this branch (head `597eef43ccd3c8bfafe0c0c16a2444b12adc1644`): `TCSlib/Cryptography/Games/` (six modules and a facade, 1,325 lines). Every lemma is proved, including identical-until-bad and simulation composition; replay 8/8; 68 standard axiom prints; lint clean. `Games.distAdv` renamed `Games.advantage` (ambiguous with the concrete layer's `distAdv`). Gate 02 (API) staged: bundle `eb9c1c44a45363a793325ad5f5aa69c2cb78b5972c4e6e0aa96e0172733adf05` | **dispatched** 2026-11-04 (user); findings awaited as `gate02-s2a-findings.md` |
| 2026-11-04 | **S2b in progress** on `cryptography/pass-shelat-ch5-8-s2b` (stacked on #185, head `063c2fb975e405ac49207c4dd1e00002f1c96fe2`). B1 (`QueryTree` ≃ one-oracle computations) and B2 (the concrete experiments as games) are proved; the B3 decoder (`NUPPT.toComp`; `toOracleAdversary` is its one-oracle instance) is proved. 18 theorems, all with standard axioms. The PRF closure (90 of Frederick's modules) was bootstrapped on the VM; one of his modules (`NonUniform`) carries an open sorry that nothing of ours reaches. The efficiency route is in `design/S2b-efficiency.md` (iteration via `polyTimeComputable_iterate`) | in progress |
| 2026-11-05 | **Efficiency result** (user asked to look for a relative first): Frederick's GGM reduction machine (`Asymptotic/GGMReduction*.lean`) already runs a next-query machine under a stateful polynomial-time handler in a state loop; its `stateLoopFun`, `stateLoopFun_poly` and `stateLoopFun_eval` are generic. `exists_queryChain_nuppt` is a non-adaptive special case; `main`'s `POracle_eq_P_of_mem_P` is a different machine model. **Ruled (user):** a Claude fill brief on GGM's pattern (reuse the loop lemmas verbatim, abstract the answer step, add log replay for reductions that are oracle machines), staged after gate 02 closes. GGM becomes an instance at integration (new coordination point F-4); the near-duplication goes in the ledger until then | active |
| 2026-11-04 | **#183 merged** into `main` (user) at `7d36bbc27dfabd4988ee1702bc342049a1f3e006`: P0's extractor basics and the [PS10] citations on Shamir are on `main` | done |
