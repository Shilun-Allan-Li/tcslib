# S3d design note: PAC learning in `TCSlib/LearningTheory` (decision D-5)

Status: **draft, 2026-11-04.** D-5 (user): Def 179.a and Thm 179.1 are built on a PAC framework in
`TCSlib/LearningTheory`, not on a crypto-style one-off game. No PAC development exists in the
pinned Mathlib or on any branch (`main`, ch. 2–4, ch. 3–4, Garg), so this is new. `main`'s
`LearningTheory` has online learning (`MistakeBounds`, `Hedge`), Johnson–Lindenstrauss and
minimax, by other authors; their files are not touched.

## What [PS10] §8.1 says (PDF p. 191, book p. 179)

- **The learning question** (Def 179.a, informal):
  - a space `S ⊆ {0,1}^n` and concepts `C_i ⊆ S` for `i ∈ I`;
  - for a random `i`, given samples `(x_j, b_j)` with `b_j = [x_j ∈ C_i]`, decide whether a new
    `x` is in `C_i`.
- **Thm 179.1:** there is a p.p.t.-decidable concept class that cannot be learned. The proof
  sketch is: `S = {0,1}^n`, `I = {0,1}^n`, `C_i = {x : f_i(x)|₁ = 1}` for a PRF `{f_i}`; no
  non-uniform PPT predicts membership of a new sample better than `½ + ε`.
- **Left implicit** (recorded as deviations when stated):
  - the sample distribution: uniform on `S` is the reading under which the sketch works;
  - "a new sample": uniform and independent;
  - "better than `½ + ε`": `ε` non-negligible.

## Two layers

### Layer 1: information-theoretic PAC (`TCSlib/LearningTheory/PAC/`, no machines)

Second source: [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning
Theory*, MIT Press 1994, §1.2 (PAC), §4 (weak learning), and [SSBD14] S. Shalev-Shwartz,
S. Ben-David, *Understanding Machine Learning*, ch. 3. The definitions:

- **Basic objects:** a finite domain `X`; a concept `c : X → Bool`; a concept class, indexed as
  `C : I → X → Bool` (which matches [PS10]'s `{C_i}`).
- **Distributions:** `D : FinDist X`, `main`'s `InformationTheory.FinDist`, reused, so samples,
  products and `statDist` are shared with #183.
- **Error:** `err D h c := ∑_{x : h x ≠ c x} D x`.
- **Samples:** a labelled sample of size `m` is `Fin m → X × Bool`, drawn as `D^m`, labelled by
  `c`.
- **Learners:** a (randomized) learner is `L : (Fin m → X × Bool) → ρ → (X → Bool)`, with finite
  coins `ρ`.
- **PAC learning:** `PACLearns C m L ε δ :=` for every `i` and every `D`, with probability
  `≥ 1 − δ` over the sample and the coins, `err D (L S r) (C i) ≤ ε`. Variants:
  - weak learning: `ε = ½ − γ` [KV94, §4];
  - learning under a fixed distribution: `D` fixed to uniform, the case [PS10] needs.
- **The prediction game (Def 179.a):** sample `i`, `m` examples and a fresh `x`, all uniform;
  the learner predicts `C i x`.
- **The bridge (proved here):** the prediction success equals `1 − E_{i,S,r}[err_U(L S r, C i)]`.
  The fresh point is independent of the sample, so no fresh-point collision issue arises. Hence
  a learner with prediction advantage `≤ γ` does not satisfy `WeakLearnsUnder U C m L γ' δ`
  whenever `γ + δ < γ' ≤ ½`: split the expected error over the accuracy event (error at most
  `½ − γ'`) and its complement (probability at most `δ`, error at most 1). Starting from
  [KV94, §4.1, p. 74]'s weak learner, which succeeds only with probability `1/q`, a small `δ`
  needs confidence amplification [KV94, §4.2, pp. 76–77]; layer 2 applies the bridge to the
  amplified learner, with its own sample count, running time and edge (gate 05, round 2, R2-1
  and R2-2).

### Layer 2: efficient learning and Thm 179.1 (prong D, `TCSlib/Cryptography/Randomness/`)

- **Efficient learner.** A learner is a NUPPT, run through the S2 framework:
  - the **example oracle** `EX(C i, U)` is a handler that samples `x ← U` and answers
    `(x, C i x)`;
  - the learner queries it polynomially often, then receives the challenge `x` and outputs a bit;
  - asymptotically, the learner is decoded by `NUPPT.toComp`.

  This is the PAC model's own example oracle, so the efficient prediction game is an S2 game,
  and its concrete probability is layer 1's prediction game (a bridge).
- **Thm 179.1, stated:** for a PRF `F` (Frederick's `PRF`), the class `C_n(k) = {x : F n k x 0 =
  true}`:
  - (a) is p.p.t.-decidable given `k` (from `PRF.easy`);
  - (b) for every NUPPT learner and polynomial sample count, the prediction advantage
    `|Pr[correct] − ½|` is negligible;
  - (c) as a corollary through layer 1's bridge, no efficient learner weakly PAC-learns `C` under
    the uniform distribution with a noticeable `γ`.
- **Proof route (for the S4 sketch):**
  1. replace the PRF by a random function (S2 §5's oracle substitution: the reduction answers the
     example oracle with PRF queries at uniform points, and the challenge with one more query);
  2. against a random function, the fresh `x`'s label is a uniform bit independent of the view
     unless `x` was sampled, with probability `≤ m · 2^{-n}`;
  3. so the advantage is at most `negl + m · 2^{-n}`.

## Placement and landing

- **Layer 1** needs nothing from ch. 2–4. **Ruled (R-3):** it lands on `main` by its own PR, like
  P0 (D-1), with its own gate. That depends on `main`'s `FinDist` only. Since all of S2 stays on the
  ch. 2–4 branch (ruled 2026-11-04), layer 1 does not refer to S2; the bridge from its prediction
  game to S2's example-oracle game is part of layer 2.
- **Layer 2** needs `NUPPT`, `PRF` and S2, so it lives on the ch. 2–4 branch in prong D.
- **Size estimate:** layer 1 about 400–700 lines; layer 2 about 300–600, beyond S2.

## Decision for the user (ruled 2026-11-04: R-3, its own PR to `main`, written after S2 settles)

- **R-3:** where the information-theoretic PAC layer lands: on `main` by its own PR, now or after
  S2 (recommended, as for P0), or with prong D on the ch. 2–4 branch.
