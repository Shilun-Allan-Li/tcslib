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
