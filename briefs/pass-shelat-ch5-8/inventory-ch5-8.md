# Inventory — [PS10] Chapters 5–8 (§5.1–§8.3)

Draft of 2026-11-04, by the maintainer agent of the Arora–Barak ch. 3–4 campaign, for planning only.
Nothing under `TCSlib/` was touched. Source: [PS10] R. Pass, a. shelat, *A Course in
Cryptography*, 3rd edition, January 2010 (book pp. 133–184, PDF pp. 145–196 of
`https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf`). Items are described in our own
words. No text of the notes is copied here.

The companion documents are the plan (`PassShelatChapter5-8Plan.md`, repository root), the spine
design (`SPINE-DESIGN.md`) and the workflow handover (`WORKFLOW.md`, both in this folder).

## Conventions

- **IDs** follow the ch. 2–4 inventories: `Kind-page.seq` for numbered items, and
  `Kind-page.a`, `.b`, … for unnumbered items on that page. Kinds:
  - `Def`, `Thm`, `Lem`, `Prop`, `Claim`, `Fact`, `Rem`;
  - `Prot`/`Alg`/`Constr` for protocols, algorithms and constructions.
- **"His"** means a declaration of the ch. 2–4 layer on `cryptography/pass-shelat-ch2-4`
  (Frederick Dehmel's), in namespace `TCSlib.Cryptography` unless written out. **"main"** means
  `origin/main`.
- **Scope:**
  - **core:** mandatory for the campaign;
  - **optional:** feasible and useful, not needed downstream;
  - **deferred:** research-level, informal in the source, or needing a notion ch. 2–4 left out;
  - **out:** no formal content.
- **diff** is 1 (one-liner, or a citation) to 5 (research-level), as in the ch. 2–4 inventories.
- **Prong** is the parallel workstream of the plan:
  - **P0** needs nothing from ch. 2–4;
  - **A** authentication; **B** secure computation; **C** composability; **D** randomness;
  - **S** the shared spine.

## Headline findings (read first)

1. **ch. 5–8 depend on ch. 2–4's definitions, almost never on its proofs.** His 63 open
   sorries block no statement here. They show up only in our axiom prints, through the few
   results we cite (the DL candidate in Thm 142.3, his §3.9 scheme's analysis in Thm 168.2).
2. **No prong depends on another at statement level.** The source proves Thm 170.4 (CCA2)
   directly from PRFs, not through ch. 5's MAC theorem, so prong C does not wait for A. What
   prongs share is infrastructure, which the spine builds once:
   - the oracle-game layer: A's forgery games and C's CPA/CCA games;
   - the two-party execution layer: B's secure computation and C's ZK composition.
3. **The source is thin in places.** These are recorded in the notes column:
   - §5.7–5.9 are exercises or empty;
   - Shamir security (Prop 154.5) and the OT receiver's simulator (in Prop 161.5) are left as
     exercises;
   - Thm 165.2 is cited from [GMW87] without proof;
   - §7.2.3–7.3 are bullet outlines;
   - Prot 176.2 needs proofs of knowledge, which [PS10] §4.8 leaves as a stub and ch. 2–4 did
     not formalize.

   Where a core item needs a proof the notes do not give, the fill cites a second source, per
   `policy.md`'s attribution rules: [Gol04] O. Goldreich, *Foundations of Cryptography*, vol. 2;
   or [KL] J. Katz, Y. Lindell, *Introduction to Modern Cryptography*.
4. **main already has pieces ch. 8 needs:**
   - `TCSlib/InformationTheory/` has `FinDist`, `HasMinEntropy`, `statDist`, universal hashing
     and `leftover_hash`;
   - `TCSlib/Complexity/CircuitComplexity/DAGCircuit` has `runWith`, a circuit evaluation over
     any value type, which is the shape Yao's garbled evaluation needs;
   - ch7's randomized classes and `ClassP/DTIME` are there for Thm 180.1.

## Chapter 5 — Authentication (book pp. 133–149)

| ID | kind | § | item | depends on | prong | scope | diff | notes |
|---|---|---|---|---|---|---|---|---|
| Def-134.1 | definition | 5.2 | MAC `(Gen, Tag, Ver)`: PPT `Gen`, `Tag`; deterministic poly-time `Ver`; perfect correctness | `Complexity.NUPPT`/`PPT`, `PolyTimeComputable` | A | core | 2 | |
| Def-134.2 | definition | 5.2 | MAC security: a non-uniform PPT forger with a `Tag_k` oracle outputs `(m, σ)`, `m` unqueried, accepted, with negligible probability | S (search-game layer), `Negligible` | A | core | 3 | the first search game of the campaign; the spine designs it |
| Prot-134.3 | construction | 5.2 | PRF MAC: `Tag_k(m) = f_k(m)` | his `PRF` | A | core | 1 | |
| Thm-135.4 | theorem | 5.2 | a PRF gives a secure MAC on `{0,1}^n` | his `PRF` (`OracleEnsemble.Indist`), the random-function guess bound | A | core | 3 | source: proof sketch. The reduction runs the forger against the oracle and tests its forgery; the advantage is at least `ε − 2^{-n}` |
| Def-135.1 | definition | 5.3 | digital signature scheme `(Gen, Sign, Ver)`, perfect correctness | as Def-134.1 | A | core | 2 | |
| Def-136.2 | definition | 5.3 | signature security against a chosen-message forger with a `Sign_sk` oracle | S, `Negligible` | A | core | 3 | `Ver` is public, so no verification oracle is needed |
| Def-136.a | definition | 5.3 | one-time security: at most one signing query | Def-136.2 | A | core | 2 | |
| Prot-137.1 | construction | 5.4 | Lamport one-time signature on `{0,1}^n` from `f` | his `FunFamily` | A | core | 2 | — **2026-11-05:** Stated (prong A, `lamport`): `Ver` checks lengths before evaluating `f`. Source notes: `Ver_pk(σ, m)` argument order; `Ver_sk` for `Ver_pk` |
| Thm-137.2 | theorem | 5.4 | Lamport is one-time secure if `f` is one-way | his `StrongOneWay`, `Closure` (the NUPPT calculus) | A | core | 3 | the reduction guesses the position and bit `(i, c)`, aborts on a conflicting query, and succeeds with `ε/(2n)` — **2026-11-05:** Stated over `FunFamily.StrongOneWay`. Source note: p. 138's "greater than" means "at least" |
| Def-140.1 | definition | 5.5.1 | CRH family: PPT `Gen`, compression (range smaller than domain), efficient evaluation, collision resistance against non-uniform PPT | S (search games), `Negligible` | A | core | 2 | a family is needed against non-uniform adversaries (source remark) — **2026-11-05:** **Statement-phase repair (2026-11-05):** `CRH` carries membership tests for `D_i`, `R_i`; compression `CRH.Compresses` is a proved property (from a threshold on); the game requires `x, x' ∈ D_i` |
| Claim-141.a | claim | 5.5.2 | collision probability of `h` on a random pair is at least one over the range size (Cauchy–Schwarz) | — | A | optional | 2 | |
| Claim-142.a | claim | 5.5.2 | birthday bound: on the order of the square root of the range size, in samples find a collision | — | A | optional | 3 | expectation only in the source |
| Prot-142.2 | construction | 5.5.2 | DL hash `h_{p,g,y}(x, b) = y^b g^x mod p` | his `Candidates.ExpGroupGen`, `ArithmeticFP` | A | core | 2 | conditional, like his candidates (the arithmetic hypothesis bundle) |
| Thm-142.3 | theorem | 5.5.2 | under DL, Prot-142.2 is a CRH compressing by one bit | his `Candidates.DLAssumption` | A | core | 3 | source: the domain is "an `n`-bit `x`" but the proof needs exponents below `p − 1`. State it over `ZMod (p − 1) × Bool` — **2026-11-05:** Stated (`dlHash_crh`) for full groups `m = p − 1`; `D_i = {(x, b) : x < m}` |
| Constr-143.a | construction | 5.5.2 | factoring-based CRH `y^b x^2 mod N`, restricted domain | his factoring candidate | A | deferred | 3 | footnote only |
| Constr-143.b | construction | 5.5.3 | from one-bit to polynomial compression | Thm-142.3 | A | optional | 4 | sketch only: the naive iteration is insecure, and no construction is given. Needs [KL] (Merkle–Damgård) |
| Thm-144.1 | theorem | 5.6 | CRH plus OWF give a one-time signature for long messages (hash-and-sign) | Def-140.1, Thm-137.2, Def-136.a | A | core | 3 | source: CRH from `{0,1}^*`. **Decision D-3:** state it for messages of length `≤ p(n)` with a CRH `{0,1}^{p(n)} → {0,1}^n`, or take the unbounded form with Constr-143.b — **2026-11-05:** Stated (`hashAndSign_oneTimeSecure`) with a full-domain hypothesis: without it the theorem is false (the CRH game counts only in-domain collisions). Its one-time forger reduction needs T2. Source note: `Ver′(σ, m)` order |
| Prot-144.2 | construction | 5.6 | hash-then-sign scheme | Thm-144.1 | A | core | 1 | |
| Constr-146.a | construction | 5.7 | chain-based many-message signature, stateful | Def-136.2 | A | optional | 4 | source: security "left as an exercise" |
| Constr-146.b | construction | 5.7.1 | tree-based (depth `n`) many-message signature | Constr-146.a | A | optional | 4 | idem |
| Constr-148.a | construction | 5.7.1 | stateless tree signatures from PRFs | his `PRF`, Constr-146.b | A | optional | 4 | idem |
| Claim-148.b | claim | 5.8 | textbook trapdoor signatures are forgeable (RSA multiplicativity) | his RSA candidate | A | optional | 2 | |
| Rem-149.a | remark | 5.8 | hash-and-sign in the random oracle model | — | A | out | — | ROM not modeled |
| §5.9 | section | 5.9 | zero-knowledge authentication | — | — | out | — | empty in the source |

## Chapter 6 — Computing on secret inputs (book pp. 151–165)

| ID | kind | § | item | depends on | prong | scope | diff | notes |
|---|---|---|---|---|---|---|---|---|
| Prot-151.a | protocol | 6.1 | additive (sum) sharing for the average of salaries | — | P0 | optional | 2 | |
| Claim-152.a | claim | 6.1 | any `n − 2` transcripts are independent of the other two inputs | Prot-151.a | P0 | optional | 2 | |
| Def-152.1 | definition | 6.1.1 | `(k, n)` secret sharing: `Share`, `Recon`, privacy for `< k` shares | `statDist` (main) | P0 | core | 2 | source: "statistically close". Shamir is exact; define both, and prove the exact one |
| Lem-153.2 | lemma | 6.1.2 | Lagrange interpolation, uniqueness | Mathlib `Lagrange` | P0 | core | 1 | cite Mathlib |
| Fact-153.3 | fact | 6.1.2 | a nonzero degree-`n` polynomial has at most `n` roots | Mathlib `Polynomial.card_roots'` | P0 | core | 1 | cite |
| Prot-154.4 | protocol | 6.1.3 | Shamir sharing over `ZMod p`, `p > n` | Lem-153.2 | P0 | core | 2 | **source typo:** it draws `n − 1` coefficients up to `a_n tⁿ`. Threshold `k` needs degree `k − 1` with `k − 1` random coefficients |
| Prop-154.5 | proposition | 6.1.3 | Shamir is a secure `k`-out-of-`n` scheme | Prot-154.4, Def-152.1 | P0 | core | 3 | source: an exercise. Proof: any `k − 1` shares are uniform (a bijection with the coefficients); reconstruction by Lem-153.2 |
| Def-155.1 | definition | 6.2 | two-party honest-but-curious secure computation: simulators `S_A`, `S_B`; each party's view jointly with the other's output ≈c the ideal | his `Protocol`, `Strategy`, `View` (ZK `Interaction`), `Ensemble.Indist`; S (execution layer) | B | core | 4 | the output clause makes the definition imply correctness (source remark) — **2026-11-05:** Stated (`HBCSecure`): private outputs `(f_A, f_B)` (needed by OT), polynomial lengths, uniform `ε`. Open: the honest parties' efficiency is not required |
| Alg-157.2 | construction | 6.2.2 | special encryption: `Enc_k(m) = (r, 0^n‖m ⊕ f_k(r))` with a length-doubling PRF; a wrong key decrypts to `⊥` | his `PRF`, `PrivateKeyScheme` | B | core | 2 | **source typo:** `x` for `m` |
| Claim-157.a | claim | 6.2.2 | Alg-157.2 is multi-message secure, and decryption under an independent key gives `⊥` except with negligible probability | his `MultiMessageSecure`, `PRF` | B | core | 3 | source: "easy to modify 99.1" |
| Constr-158.a | construction | 6.2.1–3 | garbled circuit: two keys per wire, each gate a randomly permuted table of doubly-encrypted output keys | `DAGCircuit` (main; fan-in two via `FaninTwo`), Alg-157.2 | B | core | 4 | evaluate through `DAGCircuit.runWith` with keys as values |
| Claim-159.a | claim | 6.2.3 | garbled evaluation: exactly one row decrypts per gate, w.h.p.; the output keys encode `C(x, y)` | Constr-158.a, Claim-157.a | B | core | 3 | |
| Def-160.a | definition | 6.2.4 | 1-out-of-2 OT functionality `OT(a₁, a₂, b) = (⊥, a_b)` | Def-155.1 | B | core | 1 | |
| Prot-160.4 | protocol | 6.2.4 | OT from a trapdoor permutation family and a hard-core predicate | his `TrapdoorCollection`, `Collection.HardCore` | B | core | 3 | **source typo:** the sender sends `(z₁, z₂)`, not `(z₁, …, z₄)` — **2026-11-05:** Stated with **five** messages (D8's output convention); `y_{1−b}` a raw domain sample |
| Prop-161.5 | proposition | 6.2.4 | Prot-160.4 is honest-but-curious secure | Def-155.1, his hard-core theorem for TDP collections | B | core | 4 | source gives `S_A` only; `S_B` is "an exercise" and needs the hard-core predicate's unpredictability — **2026-11-05:** Stated with the hypothesis `SamplerCanonical`: without it a non-canonical raw sample reveals `b` to Alice. **Also (gate 03b review; ruling G3-8):** an *enhanced* hard-core hypothesis (`EnhancedHardCore`, [Gol04, App. C.1]); with the plain one the proposition is unprovable, since Bob's sampler coins may reveal the preimage of `y_{1−b}` (prong B `587843c7`) |
| Prot-162.6 | protocol | 6.2.5 | Yao: A garbles, the parties run one OT per input bit of B, B evaluates and sends the output | Constr-158.a, Prot-160.4 | B | core | 3 | |
| Thm-163.7 | theorem | 6.2.5 | Yao is honest-but-curious secure | Prop-161.5, Claim-159.a, Claim-157.a | B | core | 5 | source: a hybrid over the garbled circuit and the OT simulators. It needs a composition step (OT simulators inside a larger protocol) that the notes do not state. Use [Gol04] §7.3 |
| Def-165.1 | definition | 6.3 | multi-party secure computation, real vs ideal, with corrupted subsets | Def-155.1 | B | optional | 4 | informal in the source |
| Thm-165.2 | theorem | 6.3 | [GMW87]: TDPs give honest-majority MPC for any poly-time `f` | Def-165.1 | B | deferred | 5 | cited without proof; statement-only at most |
| Claim-165.a | claim | 6.3 | fairness is impossible for two parties | — | B | deferred | 5 | a remark ([Cleve86]) |

## Chapter 7 — Composability (book pp. 167–178)

| ID | kind | § | item | depends on | prong | scope | diff | notes |
|---|---|---|---|---|---|---|---|---|
| Def-168.1 | definition | 7.1.1 | IND-CPA/CCA1/CCA2 for private-key schemes: oracle pairs `(O₁; O₂)`, and under CCA2 the decryption oracle refuses the challenge | S (game layer), his `PrivateKeyScheme` | C | core | 3 | |
| Thm-168.2 | theorem | 7.1.2 | his §3.9 construction (Alg-99.1, `r‖m ⊕ f_k(r)`) is CPA- and CCA1-secure | his multi-message scheme (`MultiMessage`), `PRF` | C | core | 4 | source: sketch. The bad events are `r` colliding with an oracle query, and a pre-challenge decryption query on the challenge `r`. **Needs `Dec` to refuse malformed ciphertexts** (erratum 2026-11-05, Shilun-Allan-Li/tcslib#193): without it, CCA1 fails for evaluators `E` that leak the key off `|s| = |x|` |
| Claim-169.a | claim | 7.1.3 | Alg-99.1 is not CCA2-secure (mauling the challenge ciphertext) | Thm-168.2's scheme | C | core | 2 | source: "`c + 1`". Formalize as XOR with a fixed nonzero `δ`, giving an explicit adversary with advantage ≈ 1 — **2026-11-05:** Stated with an explicit adversary of advantage 1; "not CCA2" proved from it |
| Alg-169.3 | construction | 7.1.3 | `π′`: encrypt with `f_{k₁}`, then tag the whole ciphertext `(r, c₁)` with `f_{k₂}` | his `PRF` | C | core | 2 | **erratum 2026-11-05 (was: the tag is `f_{k₂}(c₁)`):** the box's `f_{k₂}(c)` has `c` undefined; the proof tags `Enc_{s₁}(m)`, the whole §3.9 ciphertext. Tagging `c₁` alone is **not** CCA2-secure: `Dec′(r*, f(r₁), t₁)`, from the challenge and an encryption of `0^n`, reveals `f(r*)`. With length-preserving PRFs the `2n`-bit input `r‖c₁` takes a `2n`-bit key `k₂` (the source's `\|s\|` convention); the proof writes `g` for this family |
| Thm-170.4 | theorem | 7.1.3 | `π′` is CCA2-secure | Thm-168.2 (CPA), his `PRF` | C | core | 4 | **proved from PRFs directly, not via Thm 135.4**, so C does not depend on prong A |
| Def-171.5 | definition | 7.1.4 | IND-CPA/CCA1/CCA2 for public-key schemes (no encryption oracle) | S, his `PublicKeyScheme` | C | core | 2 | — **2026-11-05:** Stated by canonical padding (ruling 2026-11-05); non-canonical strings decrypt to `⊥` |
| Claim-172.a | claim | 7.1.4 | his Alg-104.3 (TDP bit encryption) is CPA-secure | his `BitPublicKeyScheme` security (Thm-104.4) | C | core | 2 | close to his own theorem; CPA adds nothing when the adversary holds `pk` — **2026-11-05:** Proved from a stated single-bit ⇒ CPA lemma and Thm-104.4, for every admissible padding length |
| Def-172.6 | definition | 7.1.5 | non-malleability: the decryptions of the adversary's ciphertexts (`⊥` for copies of the challenge) are indistinguishable for `m₀`, `m₁` | Def-171.5 | C | core | 3 | source mixes private- and public-key notation; take the public-key reading. **2026-11-05:** at CPA, checked equal to [PSV06, Def 3] |
| Def-173.7 | definition | 7.1.6 | relation-based non-malleability with a simulator and auxiliary input | Def-172.6 | C | core | 3 | — **2026-11-05:** **Not true as written** with Thm-174.8 (the simulator lacks `pk`; quantifiers mismatch). Ruling: follow [PSV06] (waits for the paper, Q-2). **Stated (`aa71d0e7`):** [PSV07, Def 1] (SIM-NME′) at one message, `Composability/SimNonMalleable.lean`; the simulator gets `pk`, the adversary picks a sampler's parameter, with a history function and `COPY` entries |
| Thm-174.8 | theorem | 7.1.6 | the two notions of non-malleability are equivalent | Def-172.6, Def-173.7 | C | core | 4 | source: the (⇐) direction uses the hybrid lemma (his `Ensemble.Indist`) — **2026-11-05:** See Def-173.7: false as written; follows [PSV06] — **[PSV07]: true under CPA only** (Thm 3; strictly separated under CCA1/CCA2 by Thm 4). **Stated (`aa71d0e7`):** the CPA equivalence, and SIM ⇒ IND for every attack (Cor 1); sketches are the maintainer's, since [PSV07] defers its proofs |
| Thm-175.9 | theorem | 7.1.7 | CCA2 secrecy ⇔ CCA2 non-malleability | Def-168.1, Def-172.6 | C | optional | 4 | source: sketch. CCA2 non-malleability is not defined explicitly: add the decryption oracle to Def-172.6 |
| Thm-175.1 | theorem | 7.2.1 | sequential composition: `Q(n)` independent runs of a ZK proof are ZK | his `ZK`/`PerfectZK`, auxiliary input (present in his `Defs`) | C | core | 4 | source assumes **expected** poly-time simulators. His are strict PPT (his D8) or truncated with abort (`PerfectZKAbort`), so the composition must carry the truncation error — **2026-11-05:** Stated (`seqRep`, phases of `2·rounds` moves) with `ProverBounded`: without it false under D8's efficiency (Q-1) |
| Prot-176.2 | protocol | 7.2.2 | a ZK protocol that is not concurrently secure | ZK proofs of knowledge | C | deferred | 5 | needs proofs of knowledge ([PS10] §4.8 is a stub; not in ch. 2–4) |
| §7.2.3–7.3 | sections | 7.2.3–7.3 | witness indistinguishability, a concurrent identification protocol, non-malleable commitments | — | — | out | — | bullet outlines only |

## Chapter 8 — More on randomness and pseudorandomness (book pp. 179–184)

| ID | kind | § | item | depends on | prong | scope | diff | notes |
|---|---|---|---|---|---|---|---|---|
| Def-179.a | definition | 8.1 | the learning game: random concept `C_i`, labelled samples, predict a fresh point | his `NUPPT` | D | core | 2 | **Decision D-5:** a crypto-style prediction game here (recommended), or PAC learning in `TCSlib/LearningTheory` (which has online and mistake-bound learning, not PAC) |
| Thm-179.1 | theorem | 8.1 | PRFs give a PPT-decidable concept class no non-uniform PPT learner predicts with probability `1/2 + ε` | his `PRF`, Def-179.a | D | core | 3 | source: proof sketch. The learner's samples are answered by oracle queries at random points. A fresh point must avoid the sampled ones — **2026-11-05:** Stated on the PAC layer (#194): (a) and (c) proved, (b) a `sorry` |
| Thm-180.1 | theorem | 8.2 | PRGs give BPP ⊆ `DTIME(2^{n^ε})` for every `ε > 0` | his `PRG` with polynomial stretch (his expansion theorem); main's BPP (ch7 `Randomized/Classes`) and `ClassP/DTIME`; S (model bridge) | D | core | 5 | machine-level: seed enumeration in deterministic time. The NUPPT model and ch7's BPP model must meet (Decision D-6). Non-uniform distinguishers, with `x` fixed in the advice, fit his definitions |
| Rem-181.a | remark | 8.2 | subexponentially secure PRGs give BPP ⊆ quasi-polynomial time | Thm-180.1 | D | deferred | 4 | |
| Def-181.1 | definition | 8.3.1 | `ε`-closeness | main's `statDist` | P0 | core | 1 | cite |
| Def-181.2 | definition | 8.3.1 | `m`-bit `ε`-extractor for a class `C` of sources (deterministic) | Def-181.1 | P0 | core | 1 | |
| Claim-182.a | claim | 8.3.2 | von Neumann's procedure extracts unbiased bits from i.i.d. biased coins | — | P0 | optional | 3 | source: "repeat" (Las Vegas). Formalize per accepted pair, or with a bounded number of trials and its failure probability |
| Claim-182.b | claim | 8.3.2 | the XOR of many independent biased coins is `ε`-close to uniform | — | P0 | optional | 2 | piling-up lemma |
| Def-182.3 | definition | 8.3.2 | Shannon entropy | Mathlib (`Real.negMulLog`), main's `FinDist` | P0 | core | 1 | |
| Claim-183.a | claim | 8.3.2 | high Shannon entropy does not allow extraction (the `0ⁿ` w.p. 0.99 source) | Def-182.3 | P0 | optional | 1 | |
| Def-183.4 | definition | 8.3.2 | min-entropy | main's `HasMinEntropy` | P0 | core | 1 | cite; add the min-entropy value if needed |
| Def-183.5 | definition | 8.3.2 | `k`-source, `k`-flat source | Def-183.4 | P0 | core | 1 | |
| Thm-183.6 | theorem | 8.3.2 | no 1-bit `1/4`-extractor for efficiently computable `(n − 2)`-sources | Def-181.2, Def-183.5, his `Ensemble.Samplable` (PPT samplers) | D | core | 3 | **source gap:** the proof needs `Ext` poly-time ("`X` is computable since `Ext` is"), so restrict to efficient `Ext`. The statistical core is P0; the efficiency part needs his sampler model — **2026-11-05:** Stated at every `n` for polynomial-time `Ext` (`not_isExtractor_effSources`) |
| §8.3.3 | section | 8.3.3 | leftover hash lemma | main's `leftover_hash` | P0 | core | 2 | heading only in the source. Cite main, and add the bridge "a universal family is a strong extractor for `k`-sources" in Def-181.2's terms |

## Counts

Counted from the rows above by script (the scope column of each chapter's table).

| Chapter | core | optional | deferred | out |
|---|---|---|---|---|
| 5 | 14 | 7 | 1 | 2 |
| 6 | 15 | 3 | 2 | 0 |
| 7 | 11 | 1 | 1 | 1 |
| 8 | 10 | 3 | 1 | 0 |
| **total** | **50** | **14** | **5** | **3** |

Core items by prong:
- **P0:** 11 (Shamir 5, extractor basics 6);
- **A:** 14;
- **B:** 10;
- **C:** 11;
- **D:** 4 (Def-179.a, Thm-179.1, Thm-180.1, Thm-183.6).

Prong D is small in items, but Thm-180.1 is machine-level and the hardest single item after
Thm-163.7.
