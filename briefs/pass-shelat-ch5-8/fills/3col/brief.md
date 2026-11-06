# Fill brief: the 3-colouring zero-knowledge admissions (`ThreeColoring/{Protocol, Simulator}`)

**Status: @ISSUED@.** Issue commit: `@ANCESTOR@`.
- **Targets:** the three admissions of gate pack 03g. Gate 03g is closed (round 2: 0 blockers,
  0 majors, 1 minor, R2-1, carried into this brief).
- **Ruled 2026-11-06:** two units on disjoint files; they may run in parallel on separate hosts.
- **Before issue** (each item lands on the campaign branch, so that `@ANCESTOR@` contains it):
  - the rule-10 prerequisites P1–P11 below (published equations missing at the pre-ship commit);
  - a review of this brief by a review sub-agent;
  - the issue commit.

The targets were written in run 2 of the campaign. Each is a `sorry` under a proof sketch, and
the statements were screened by gate 03g (`gates/03-ch2-4/review/gate03g-review.md`, and round 2,
`findings/gate03g-r2-findings.md`). The source is `Pass–Shelat.pdf` at the root of the campaign
branch: [PS10] §4.7, Protocol 127.5, Proposition 127.6, Algorithm 128.7, Proposition 128.8 (book
pp. 127–129, PDF pp. 139–141).

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out `cryptography/pass-shelat-ch2-4`
  at the issue commit `@ANCESTOR@`.
- Work on a **local** branch `fill/<unit>` (`fill/col-a` or `fill/col-b`) created from
  `@ANCESTOR@`. **Never push that branch anywhere.** Record the base hash in `REPORT.md`, and never
  rebase.
- **Delivery is through the exchange branch** `exchange/pass-shelat-ch5-8` (a separate checkout or
  worktree). The protocol is the exchange branch's `README.md` ("For fill workers", "Rules for
  everyone pushing"). You push the folder `inbox/fills/<unit>/`, holding:
  - `REPORT.md`;
  - `patches/`: `git format-patch @ANCESTOR@..fill/<unit>`, the whole series;
  - `src/`: the owned file(s) and any new helper modules at your head, under their repository paths;
  - `evidence/`: the logs that this brief and the environment addendum require.
- **Push at each checkpoint**, with the commit message `fill <unit>: checkpoint <n>`; the final push
  is `fill <unit>: final`. A session that ends early leaves its last checkpoint as the delivery.
- **Rules for pushing:**
  - write only `inbox/fills/<unit>/`;
  - run `git pull --rebase origin exchange/pass-shelat-ch5-8` before each push;
  - never force-push;
  - open no PRs.

## Units (disjoint file ownership; they may run in parallel)

Cross-file dependencies are on **statements** only. The integration replay closes the chain.

| Unit | Owned file(s) | Targets (`sorry`s) |
|---|---|---|
| **col-a** | `ThreeColoring/Protocol.lean`; new helper modules `ThreeColoring/ColRep*.lean` (below) | `R3COL_witnessRelation`, its `decidable` clause (`:846`); `colRep_efficientProverProof` (`:919`) (2) |
| **col-b** | `ThreeColoring/Simulator.lean`; new helper modules `ThreeColoring/ColZK*.lean` (below) | `col_zk` (`:780`) (1) |

`ThreeColoring/` abbreviates `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/`. Line numbers are
at the pre-ship commit `5f2771631fe853dae9c2aa44791ae5b0e09c95eb`.

Each target's docstring carries its proof sketch. **Follow it, or report why it fails.** For
`col_zk`, the binding plan is the sketch as corrected by R2-1 and the ladder below.

### Helper modules: what may go where

- **Why.** `Protocol.lean` has 926 lines and `Simulator.lean` has 804. The fills would take both
  past policy's 1000-line threshold.
- **What a helper module is.** It is imported by its unit's owned file, so it cannot see that
  file's definitions (Lean imports are acyclic). It may import any module of the order list
  upstream of its owned file.
- **What it may hold.**
  - Generic lemmas.
  - Lemmas about definitions of upstream files, read through their published equations.
  - New string functions with their equation and polynomial-time lemmas.
- **What it may not hold.**
  - No new shadow definitions (verbatim copies of the owned file's definitions, as in
    `ProtocolProofs.lean`).
  - No lemma about an existing shadow (`ColProofs.*`, the `ColSimMachine` copies of
    `sampleColorPair`, `colSim`, …) that is then transferred to the original by `rfl`. Under the
    rule-10 seal this transfer fails (pre-ship probe A4).
- **Namespaces and size.** col-a's helpers use `TCSlib.Cryptography.ColRep`, and col-b's use
  `TCSlib.Cryptography.ColZK`. Each helper module has 150–600 lines and the full file header of
  policy §1. Aim to keep each owned file at or under 1000 lines. If an owned file goes over, say why
  in `REPORT.md`: the frozen definitions cannot move.
- **The facade.** `ThreeColoring.lean` belongs to neither unit, so a new helper module is not
  imported by it. This adds a facade FAIL in `campaign_style_lint.py`. Record it in `REPORT.md`
  as a landing edit for the maintainer.

**col-a: what stays in `Protocol.lean`.** Anything that names `colProverRep`, `colVerifierRep`,
`colProtocolRep`, `colProver`, `colVerifier`, `colCoinSlice` or `colIterations`. The
`R3COL` decider is a function of `Language`/`Encoding` definitions only, so it can live entirely
in a helper module (the GI precedent is `GI.Riso_decidable` in `GraphIsomorphism/Efficiency.lean`).

**col-b: what stays in `Simulator.lean`.** `colSim`, `colSimTrunc`, `colSimRed` and the other
simulator definitions live in `Simulator.lean`, not in a lemma file. So does every statement that
names `ColorPair`, `sampleColorPair`, `pair6Equiv`, `colRealView`, `colSimAttempt*`,
`colSimTrunc*`, `colSimHyb`, `colSimAttemptPlanted`, `colSimRed`, `colSimBlock`, `colSimCoins`,
`colSimAttemptStr`, `colSim` or `simColors*`. That covers ladder steps 1–4, the identification
part of step 5, and steps 6–7. The helpers take the generic parts: step 5's machine, the coin
transport, the verifier call, the negligibility and counting facts, and generic forms of the
block-sampling argument of step 3 (in the style of `ColSimLemmas.statClose_truncAttempts`, which
is generic in the attempt function).

## col-a: routes

### `R3COL_witnessRelation`, `decidable` clause

- **The decider (the sketch).** `T ⟨x, y⟩ := decide (x = encGraph (decGraph x).2 ∧
  y = encColoring (decColoring n y) ∧ ProperColoring (decGraph x).2 (decColoring n y))`,
  with `n := (decGraph x).1`.
- **Correctness.** By `decGraph_encGraph`, `decColoring_encColoring` and `R3COL_iff` (P1).
- **Polynomial time.**
  - The well-formedness test is `x = x.take (n·n)` (`ColMachines.encGraph_decGraph_eq_take`; the
    verifier's `verdictStr` already computes it).
  - The colouring re-encoding is `polyTimeComputable_blockMap` / `polyTimeComputable_iterateEmit`.
    It needs the bitwise equation of `encColoring` (P3).
  - The properness scan over the `n²` matrix entries is `polyTimeComputable_iterate` with an
    accumulated conjunction (`ProperColoring_iff`, P2; colour values by `ColMachines.decColoring_val`).
  - Pairing: `polyTimeComputable_pairEq`, `polyTimeComputable_and`, `polyTimeComputable_ite`.
- **Placement.** Recommended in a helper `ThreeColoring/ColRepWitness.lean`, closed in
  `Protocol.lean` by one `exact`.

### `colRep_efficientProverProof`

Follow its docstring sketch (`Protocol.lean:893–916`).
- **The verdict against any `P'`.** Use `Protocol.outV_withV`, after
  `rw [Protocol.withV_self] at h` (probes A1 and A5; not by `rfl`, which reads `outV` and
  `transcriptWith`). The transcript after `4i` moves is `GI.exec_repViews` / `GI.repViews`. These
  are generic in `P'`, `V` (prover first, four moves per iteration); importing them is authorized.
- **Completeness,** iteration by iteration: honest messages, then `colVerify_honest`.
- **Soundness.** Use `ε N := Real.exp (-(Nat.sqrt N)) + N² (1/2)^N + 2⁻¹^N` (the strict clause).
  For `x` not well formed, or with `n < 2`, the verdict is always `[false]`. Otherwise:
  - fix the prover's coins (`Protocol.exists_proverCoins_le`);
  - make the `K = n|E|` challenge samplers uniform by `OneWay.statClose_pi (statClose_sampleEdgeIdx hm |x|) K`
    on the block layout (`StatClose.comp_pushesUniform`, `StatClose.abs_uprob_sub_le_prod`), at cost
    `K (1/2)^{|x|} ≤ |x|² (1/2)^{|x|}`;
  - apply `uprob_col_cheat_le` with `k = K`, `comF`/`opnF` read off the execution;
  - bound `(1 − 1/|E|)^{n|E|} ≤ e^{−n}` by `one_sub_inv_pow_mul_le_exp`, with
    `n = Nat.sqrt |x|` (`length_encGraph`, `Nat.sqrt_eq`).
- **Negligibility:** `negligible_exp_neg_sqrt_div` (`C = 1`, through `Nat.div_one`),
  `Negligible.mul_pow negligible_two_pow_neg 2`, `negligible_two_pow_neg`, `Negligible.add`.
- **The other fields.**
  - Efficiency: `colProverRep_efficient`, `colVerifierRep_efficient`.
  - Message bound: the second component of `colProtocol_proverBounded`.
  - The coin blocks need `Strategy.coinLen_eq` (P4).
- **Templates:** `GI.gi_rep_efficientProverProof` and `GI.giRep_accept_le`
  (`GraphIsomorphism/SoundnessRepGI.lean`), and this file's `col_efficientProverProofErr` with the
  private `colProtocol_sound`.

## col-b: the `col_zk` ladder

Fix `V'` efficient, take `S` from `exists_colSimulator hC.easy` (probe R7), and fix `Lz` and `D`.
- For `x = encGraph G`, `y = encColoring c` (`c` proper) and `|z| ≤ Lz |x|`, write:
  - `n` for the vertex count, `m = edgeCount G` (ordered pairs), `N = |x| = n·n`, `K = n·m`;
  - `V com ρ := V'.next x z (List.ofFn ρ) [com]`, with `ρ : V'.Coins N`;
  - `enc : Option (ColView (V'.Coins N)) → List Bool`, `none ↦ []`,
    `some (ρ, com, opn) ↦ View.encode ⟨x, z, List.ofFn ρ, [com, opn]⟩`;
  - `D' := fun o d => D.distinguisherL N (enc o) d`.
- **New lemmas are public**, with the names below, a docstring with its `[PS10, …]` tag, and a
  proof sketch where nontrivial.
- **New definitions** (an `enc` definition, the hiding machine's string function) are public, land
  with their equation lemmas (policy §1), and have no `@[simp]`.
- **Variables.** In the statements, `{Com : List Bool → List Bool} {ℓ : PolyExpr}` are section
  variables, as in `Simulator.lean`.
- **The statements below are the intended ones.** All but step 5's elaborate at the pre-ship
  commit (`preship/dup-probe-col-b.log`, `preship/route-probe-colb.log`). You may restate one
  through a new `enc` definition, if its content is unchanged.

1. **`statClose_sampleColorPair`** (`Simulator.lean`), the colour-pair analogue of
   `statClose_samplePerm3`:
   ```lean
   theorem statClose_sampleColorPair (T : ℕ) :
       StatClose (fun r : Fin (T * 3) → Bool => sampleColorPair T (List.ofFn r))
         (id : ColorPair → ColorPair) ((1 / 4 : ℝ) ^ T)
   ```
   Prove it as `statClose_samplePerm3` is proved, with `pair6Equiv` in place of `perm3Equiv`
   (`statClose_rejectionSample 6 3 T`, `StatClose.map`, `StatClose.comp_equiv_right`). The
   tape-to-trials step needs P11.
2. **The real view** (step (1) of the sketch):
   ```lean
   theorem statClose_colRealView (V' : Strategy) {n : ℕ} (G : Graph n) (c : Fin n → Fin 3)
       (hc : ProperColoring G c) (z : List Bool) :
       StatClose (fun r => (((colProtocol Com ℓ).withV V').viewV (encGraph G) (encColoring c) z r).encode)
         (fun w : (Equiv.Perm (Fin 3) × (Fin n → Fin (ℓ.eval n) → Bool)) × V'.Coins (encGraph G).length =>
           (some (colRealView Com (ℓ.eval n) G c
               (fun com ρ => V'.next (encGraph G) z (List.ofFn ρ) [com]) w)).elim []
             fun v => View.encode ⟨encGraph G, z, List.ofFn v.1, [v.2.1, v.2.2]⟩)
         ((1 / 4 : ℝ) ^ (encGraph G).length)
   ```
   Use `statClose_samplePerm3`; the prover's randomness is a projection of its tape
   (`StatClose.comp_pushesUniform`); then `StatClose.prod`/`StatClose.refl` with `V'`'s tape, and
   `StatClose.map`. Unfold through `Protocol.viewV_withV`, `View.encode` (P6), `exec_succ`,
   `decGraph_encGraph`, `decColoring_encColoring` and the public `colProver` equations (P10).
3. **`colSim` to `colSimTrunc`** (step (2), `m > 0`):
   ```lean
   theorem statClose_colSim_colSimTrunc (V' : Strategy) {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G)
       (z : List Bool) :
       StatClose (fun r : Fin ((colSimCoins ℓ V').eval (encGraph G).length) → Bool =>
           colSim Com ℓ V' (encGraph G) z (List.ofFn r))
         (fun w : Fin (n * edgeCount G) → ((Fin (edgeCount G) × ColorPair) ×
             (Fin n → Fin (ℓ.eval n) → Bool)) × V'.Coins (encGraph G).length =>
           (colSimTrunc Com (ℓ.eval n) G (fun com ρ => V'.next (encGraph G) z (List.ofFn ρ) [com])
               (n * edgeCount G) w).elim []
             fun v => View.encode ⟨encGraph G, z, List.ofFn v.1, [v.2.1, v.2.2]⟩)
         ((n * edgeCount G : ℕ) * ((1 / 2 : ℝ) ^ (encGraph G).length + (1 / 4 : ℝ) ^ (encGraph G).length))
   ```
   - The `t`-th block (`colCoinSlice`, P10) has disjoint fields:
     - the edge sampler (`statClose_sampleEdgeIdx`);
     - the colour pair (step 1);
     - the commitment randomness and `V'`'s tape (exact projections).
   - Combine the fields with `StatClose.prod`, and the blocks with `OneWay.statClose_pi`.
   - The simulator uses blocks `t < K` of its `N²` (`colIterations`, P10).
4. **`exists_colSimRed_fixCoins`** (step (4); statement and proof checked sealed, probe R1):
   ```lean
   theorem exists_colSimRed_fixCoins {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G) (c : Fin n → Fin 3)
       {ρ : Type*} [Fintype ρ] [Nonempty ρ] (V : List Bool → ρ → List Bool) (N : ℕ) (hN : 0 < N)
       {ρ' : Type*} [Fintype ρ'] (D' : Option (ColView ρ) → ρ' → Bool) :
       ∃ (k : Fin N) (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3))
         (w₀ : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin (ℓ.eval n) → Bool)) × ρ),
         distAdv (colSimTruncW Com (ℓ.eval n) G c V N) (colSimTruncH Com (ℓ.eval n) G c V N) D' / N ≤
           distAdv (fun r : Fin n → Fin (ℓ.eval n) → Bool =>
               multiCom Com (fun i => padColor n (simColorsW (edgeOf G e₀) π₀ c i)) r)
             (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com (fun i => padColor n (π₀ (c i))) r)
             (fun cv c' => colSimRed Com (ℓ.eval n) G c V N k e₀ π₀ D' cv (w₀, c'))
   ```
   The proof is `exists_colSimRed_ge` composed with `CommitmentLemmas.exists_fixCoins`, giving the
   two samplers explicitly. Add beside it **`colSimRed_fixed_eq`**: with `w₀` fixed, only attempt
   `k` reads `cv` (statement elaborates, probe R2):
   ```lean
   colSimRed Com (ℓ.eval n) G c V N k e₀ π₀ D' cv (w₀, c') =
     D' ((firstSome fun t : Fin N => if (t : ℕ) < k then colSimAttemptH Com (ℓ.eval n) G c V (w₀ t) else none) <|>
         colSimAttemptPlanted Com (ℓ.eval n) G c V e₀ π₀ cv (w₀ k) <|>
         (firstSome fun t : Fin N => if k < t then colSimAttemptW Com (ℓ.eval n) G c V (w₀ t) else none)) c'
   ```
5. **`exists_colHidingRed`**, the reduction machine (helper module plus an identification lemma in
   `Simulator.lean`). It cannot be stated exactly before its string function is designed. Its
   interface:
   ```lean
   -- helper: a new string function `ColZK.hidingView Com ℓ V' (adv cv : List Bool) : List Bool`, with
   -- equation lemmas and `polyTimeComputable_hidingView`; then
   theorem exists_colHidingRed {V' : Strategy} (hV' : V'.Efficient) (D : NUPPT) (α : ℕ → List Bool)
       (b : PolyExpr) (hα : ∀ n, (α n).length ≤ b.eval n) :
       ∃ B : NUPPT, B.coins = D.coins.subst (.mul .var .var) ∧
         ∀ n cv r, B.runAtL n cv r = D.runAtL (n * n) (ColZK.hidingView Com ℓ V' (α n) cv) r
   ```
   - **What `hidingView` computes.** It parses the advice `x, z`, the case flag, `ρ_k`, `e₀`, the
     two endpoint commitments and the opening, and `pre`, `post`.
     - If `m > 0`: it outputs `pre` if `pre ≠ ⊥`. Otherwise it splices `cv` at the endpoints
       (`msgAt`), makes **one** call of `V'` on `[com]` with tape `ρ_k`, and compares
       `edgeIdxOfMsg m` with `e₀`; it outputs the encoded view on success, `post` otherwise.
     - If `m = 0`: it outputs `View.encode ⟨x, z, ρ, [cv, []]⟩` and makes no verifier call.
   - **Building `B`.**
     - The machine shape is probe R4: `NUPPT.exists_comp` with `pre := hidingView`, then
       `NUPPT.exists_withAdvice`, and `NUPPT.exists_reparam (.mul .var .var)`.
     - The sketch's `exists_reparam_advice` with `φ n = n²` also works.
     - Reuse `ColSimMachine.comStr_poly`, `opnStr_poly`, `view_poly` and `reply_poly`.
     - `reply_poly` reads the tape as `rVStr ℓ x blk`. Either feed it a block, or write a generic
       one-call lemma `ColZK.polyTimeComputable_next` (`V'.next (X w) (Z w) (R w) [C w]`), which
       needs P12.
   - **In `Simulator.lean`:** the identification `D.distinguisherL (n*n) (hidingView … (α n) cv) =
     D' (pre <|> planted cv <|> post)` for the chosen data.
   - **Coin transport** is the generic two-parameter lemma
     **`ColZK.acceptProb_distinguisherL_reparam`** (helper; probe R5 shape). It is
     `EnsembleLemmas.acceptProb_coins_equiv` along `Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)`,
     and it needs P8 and P9. Report it as a requested shared lemma, to be placed next to
     `CommitmentLemmas.acceptProb_distinguisherL_of_runAtL` (review #2 ripple); keep no private copy.
6. **The edgeless case** (`m = 0`, `n ≥ 1`):
   ```lean
   theorem exists_colZK_edgeless (V' : Strategy) {n : ℕ} (hn : 1 ≤ n) (G : Graph n) (hm : edgeCount G = 0)
       (c : Fin n → Fin 3) (z : List Bool) (D : NUPPT) :
       ∃ (π₀ : Equiv.Perm (Fin 3)) (rV : V'.Coins (encGraph G).length),
         distAdv (fun r => (((colProtocol Com ℓ).withV V').viewV (encGraph G) (encColoring c) z r).encode)
             (fun r : Fin ((colSimCoins ℓ V').eval (encGraph G).length) → Bool =>
               colSim Com ℓ V' (encGraph G) z (List.ofFn r))
             (D.distinguisherL (encGraph G).length) ≤
           (1 / 4 : ℝ) ^ (encGraph G).length +
             distAdv (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com (fun i => padColor n (π₀ (c i))) r)
               (fun r : Fin n → Fin (ℓ.eval n) → Bool => multiCom Com (fun _ => padColor n 0) r)
               (fun cv d => D.distinguisherL (encGraph G).length (View.encode ⟨encGraph G, z, List.ofFn rV, [cv, []]⟩) d)
   ```
   - One attempt is made (`colIterations x = 0`, `colSim`'s edgeless branch). `N ≥ 1`, so block 0
     is complete. Its commitment randomness and `V'`'s tape have the real laws. Only the committed
     vector differs: `π ∘ c` against `0` (`colCommit_eq`, P10).
   - Make `π` uniform (step 2's argument), fix `π` and then `r_V` by `exists_fixCoins`, and take
     the worst `π₀`.
7. **The assembly, `col_zk`** (`intro` through `ZK_iff`, P5).
   - **The data and the machine.** For each `n`, choose the data with the largest fixed-reduction
     gap on its own vectors. The data are: the graph, `c`, `z` with `|z| ≤ Lz(n²)` (finite only
     because of `Lz`; the `Defs.lean` module docstring), the case, `k`, `e₀`, `π₀`, `w₀` (or
     `π₀`, `r_V` when `m = 0`). Use `Finset.exists_max_image` or `Set.Finite.exists_maximal_wrt`;
     any default advice serves at `n = 0`.
   - **The advice bound** is round 2's R2-2:
     `|enc view| ≤ 4n² + 2Lz(n²) + 2·V'.coinLen(n²) + 2|cv| + 2|opn| + 12`, with
     `|cv| ≤ n(2C(2n + ℓ(n) + 3)^d + 2)` (`length_multiCom_le`, `hC.easy.output_length_le`) and
     `|opn| ≤ 3ℓ(n) + 20` (`colProver_length_le`).
   - **The hiding bound.** `hC.multiHiding .var B` gives `ε_B`. Specialise it at `n` and rewrite
     `PolyExpr.eval_var` in the hypothesis (`rw … at`, probe R3b): direct application needs
     `var.eval n ≡ n` (R3a fails under the seal).
   - **Sign and triangle inequality.** `0 ≤ ε_B n` follows from the bound at `v = v'` and needs
     `distAdv_eq` (P7). The triangle inequality is `abs_sub_le` through P7.
   - **Lengths.** `(encGraph G).length = n * n` is `length_encGraph`. Transport `D`'s coin type
     along it with `finCongr`; do not `rw` it inside `D.Coins _`.

### The error accounting (binding; review §2.3 with the R2-1 correction)

`Δ` is `D`'s advantage between the real view and `S(x, z)`, and `ε_B ≥ 0`.
- **`m > 0`** (then `n ≥ 1`): `Δ ≤ 4^{−N} + K(2^{−N} + 4^{−N}) + K ε_B(n) + (1 − 1/m)^K`.
  - The terms are step 2's, step 3's, steps 4–5's, and `statClose_colSimTruncH`'s.
  - `uprob_colSimTruncW_eq` is exact.
  - `(1 − 1/m)^{nm} ≤ e^{−n}` (`one_sub_inv_pow_mul_le_exp`).
- **`m = 0`, `n ≥ 1`** (R2-1): `Δ ≤ 4^{−N} + ε_B(n)`. This is **one** multi-value hiding gap,
  not `K ε_B(n) = 0`; round 2's counterexample has advantage `85/128` at `n = 2`. Bound it by
  `ε_B(n) ≤ N² ε_B(n)`.
- **`n = 0`** (`N = 0`): `Δ ≤ 1`. The simulator's tape is empty while `V'`'s need not be.
- **In every case** `Δ ≤ ε(N)`, with
  `ε N := N² ε_B (Nat.sqrt N) + Real.exp (−(Nat.sqrt N : ℝ)) + N² ((1/2)^N + (1/4)^N) + (1/4)^N`:
  - use `K = n m ≤ n³ ≤ n⁴ = N²` (`n ≥ 1`), `max(1, K) ε_B(n) ≤ N² ε_B(n)`, and
    `Nat.sqrt N = n` (`Nat.sqrt_eq`);
  - at `N = 0`, `ε(0) = 2 ≥ 1`.
- **Negligibility:** `Negligible.mul_pow (Negligible.comp_sqrt hε_B) 2`,
  `negligible_exp_neg_sqrt_div` (`C = 1`), `Negligible.mul_pow negligible_two_pow_neg 2`,
  `(1/4)^N ≤ (1/2)^N` with `Negligible.mono`, and `Negligible.add`. This and `K ≤ N²` may go in a
  helper (no existing lemma: dup probe L7a, L7b).

### The `col_zk` docstring (authorized edit; no statement change)

- **Required (R2-1)**, at `Simulator.lean:769–771`. Replace "so the hiding terms are at most
  `K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` for `n ≥ 1`." by:

  > The hiding term is `K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` if `m > 0`, and one gap
  > `ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` if `m = 0` and `n ≥ 1` (gate 03g round 2, R2-1); in both
  > cases `max(1, K) ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)`.
- **Optional, for synchronization (policy §3).**
  - At `:744–745`, replace "still to be added: the fill ladder's first step, gate 03g review M3"
    by the lemma's name.
  - Name the ladder lemmas at the steps of the sketch that they prove.
- **Nothing else in the docstring changes.**
- **`Negligible.comp_sqrt` stays where it is.** The review's optional move M4 is not part of this
  fill.

## Templates (cite; do not copy)

- **Samplers:**
  - `statClose_samplePerm3` and `statClose_sampleEdgeIdx` (`ThreeColoring/Language.lean`);
  - `statClose_rejectionSample`, `StatClose.prod/map/comp_equiv_left/comp_equiv_right/comp_pushesUniform`
    (`Asymptotic/Sampling.lean`);
  - `OneWay.statClose_pi` (`Asymptotic/OneWayLemmas.lean`).
- **Truncated attempts and hybrids:** `ColSimLemmas.statClose_truncAttempts`,
  `ColSimLemmas.exists_hybRed_ge` (`ThreeColoring/SimulatorLemmas.lean`).
- **Fixed coins, then one call of `D`:** `Commitment.multiHiding` (its proof is this bridge for the
  pair hybrid), `CommitmentLemmas.exists_fixCoins`, `CommitmentLemmas.exists_pairSpliceRed`,
  `CommitmentLemmas.acceptProb_distinguisherL_of_runAtL`.
- **Machines:**
  - `ColSimMachine.exists_simulator` and its components (`ThreeColoring/SimulatorMachine.lean`);
  - the closure calculus `NUPPT.exists_comp/exists_compParam/exists_withAdvice/exists_reparam`
    (`Complexity/Randomized/Closure.lean`);
  - `LevinTransfer.distinguisherL_lift` (`ZeroKnowledge/NPLemmas.lean`), as a model for the
    two-parameter coin transport.
- **The real view:** `GIZK.viewV_encode` and the GI statistical-ZK chain
  (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean`).
- **Repeated protocols (col-a):** `GraphIsomorphism/SoundnessRepGI.lean`, `GraphIsomorphism/SoundnessRep.lean`.
- **Deciders (col-a):** `GI.Riso_decidable`, `GI.risoTest_iff`, `GI.wellFormed_poly`
  (`GraphIsomorphism/Efficiency.lean`).

## Authorized imports

- **col-a.**
  - `Protocol.lean` may import its new `ThreeColoring/ColRep*.lean` helpers.
  - `Protocol.lean` or a helper may import `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI`
    (for `GI.exec_repViews`, `GI.repViews`) and `…GraphIsomorphism.Efficiency` (for the GI decider's
    components).
  - These create no cycle: the GI modules import nothing from `ThreeColoring`.
- **col-b.**
  - `Simulator.lean` may import its new `ThreeColoring/ColZK*.lean` helpers.
  - A helper may import any order-list module upstream of `Simulator.lean`, never `Simulator.lean`.
  - `ZeroKnowledge/NPLemmas.lean` is also cycle-free, but is not needed.
- **No new Mathlib roots** are expected. A new one is fetched as the addendum says, and reported.

## Lint sweep (decision 2026-11-05)

- **Run** `python3 -I scripts/style_lint.py <files>` on the owned files and your helpers, before and
  after.
- **Also run** `python3 -I scripts/campaign_style_lint.py --check8b TCSlib/Cryptography/ZeroKnowledge/ThreeColoring`.
  It takes a **directory**; given a file it prints "no .lean files". Read the lines of your files.
- **The 20 pre-existing `style_lint.py` findings** of the 3-colouring files
  (`preship/lint-base.log`) split as follows:
  - **col-a, 1:** `Protocol.lean:723`, `colProtocol_sound` (99 lines, no **Proof sketch.**). Add a
    sketch paragraph to its docstring (authorized docstring edit).
  - **col-b, 0:** none in `Simulator.lean`.
  - **Neither unit, 19 (out of scope; do not edit):**
    - `Machines.lean`, 12: no `## Main definitions`; no sketch for `polyTimeComputable_loopState'`
      (:95), `polyTimeComputable_flatMap_range` (:152), `iterSnd_poly` (:182), `countTrue_poly`
      (:361), `natOfBits_poly` (:628), `findSome?_finRange_eq` (:662), `sampleVal_poly` (:724);
      no docstring for `countTrue_zero` (:333), `countTrue_succ` (:335), `natOfBits_zero` (:597),
      `natOfBits_succ` (:599).
    - `Parties.lean`, 3: no `## Main definitions`; no sketch for `checkStr_poly` (:218),
      `proverRepStr_poly` (:312).
    - `ProtocolProofs.lean`, 4: no `## Main definitions`; no sketch for `colVerifier_next_eq`
      (:204), `colProverRep_next_eq` (:252), `colVerifierRep_next_eq` (:279).
- **Also pre-existing, not in the 20:**
  - `campaign_style_lint.py` reports 6 facade FAILs on `ThreeColoring.lean` (owned by neither);
  - check-8 WARNs: `Protocol.lean` 7, `Simulator.lean` 17.
- **Your delivery** adds no new check-8 name and no FAIL in your files, apart from the facade line
  of each new helper module (see above).

## Rule-10 prerequisites (before issue)

At the pre-ship commit these definitions are read by the routes but have no published equation.
The probes under seal confirm it where marked (`preship/route-probe-colb.log`,
`preship/seal-probe-col-a.log`). Each prerequisite lands beside its definition, with no `@[simp]`
(policy §1).

| # | Definition (file) | Lemma needed | Unit(s) | Probe |
|---|---|---|---|---|
| P1 | `R3COL` (`ThreeColoring/Language.lean`) | `R3COL_iff` | col-a, col-b | A3 fails sealed |
| P2 | `ProperColoring` (`Language.lean`) | `ProperColoring_iff` | col-a | — |
| P3 | `encColoring` (`ZeroKnowledge/Encoding.lean`) | a bitwise equation (`getD_encColoring` or a `flatMap` form) | col-a | — |
| P4 | `Strategy.coinLen` (`ZeroKnowledge/Interaction.lean`) | `Strategy.coinLen_eq` | col-a, col-b | A6 fails sealed |
| P5 | `ZK` (`ZeroKnowledge/Defs.lean`) | `ZK_iff` | col-b | R6 fails sealed |
| P6 | `Protocol.viewV`, `View.encode` (`Interaction.lean`) | `Protocol.viewV_withV` (as `outV_withV`), `View.encode_mk` | col-b | — |
| P7 | `distAdv` (`Foundations/Experiments.lean`) | `distAdv_eq` | col-b | C2, R8 fail sealed |
| P8 | `NUPPT.distinguisherL` (`Asymptotic/Adversary.lean`) | `NUPPT.distinguisherL_eq` | col-b | R5 |
| P9 | `NUPPT.coinLen` (`Complexity/Randomized/PPT.lean`) | `NUPPT.coinLen_eq` | col-b | R5 |
| P10 | `colCommit`, `colOpen`, `colCoinSlice`, `colIterations`, `colProver`, `colProtocol` (`ThreeColoring/Protocol.lean`, col-a's file) | `_eq` lemmas; public `colProver` next-message equations (today private, `:644–667`); `colProtocol` field lemmas | col-b | — |
| P11 | `sampleIdx` (`Language.lean`) | public tape lemma (today private `tapeEquiv`, `sampleIdx_ofFn`), or a generic `statClose_sampleIdx` | col-b | — |
| P12 (optional) | `Strategy.Efficient` (`Interaction.lean`) | `Strategy.efficient_iff` | col-b, only for a generic verifier-call lemma | B1 fails sealed |

- **P10 changes col-a's file,** so it cannot be left to col-a while col-b runs in parallel.
- **If a prerequisite is missing at `@ANCESTOR@`,** report the step that needs it as blocked
  (escalation E-API). Do not read the body.
- **Published equations that already exist and suffice:**
  - `Protocol.outV_withV`, `Protocol.withV_self/withV_P/withV_V`, `exec_succ`, `exec_zero`;
  - `NUPPT.runAt_eq`, `NUPPT.simulate_eq`;
  - `PolyExpr.eval_var/mul/add/const/pow/normal/subst`;
  - `ColSimLemmas.msgAt_multiCom`, `mergeAt_fst/snd`.

## Ground rules (binding)

1. **Statement freeze.** Every definition and every existing statement is byte-identical in your
   delivery. Only these change:
   - the bodies of the listed `sorry`s;
   - the docstring edits authorized above (`col_zk`'s sketch; `colProtocol_sound`'s sketch);
   - new lemmas: the ladder lemmas named above, plus `private` helpers prefixed `colRep_`
     (col-a) or `colZK_` (col-b) in the owned file;
   - new helper modules under the rules above.
2. **Rule 10.** Read other files' TCSlib definitions only through their published equations (the
   table above). Core and Mathlib definitions may reduce in `rfl`, `decide` or `show`, never in
   `simp`, `rw` or `unfold`.
   - **Self-check:** seal the foreign definitions your proofs touch (`attribute [local irreducible]`;
     `attribute [-simp]` for `@[simp]` ones) on a copy of each new proof. Add a control that reads
     one of them through its body: it must fail sealed and pass unsealed.
   - Shadows count as foreign (probe A4).
3. **Rule 11.** Cite no private declaration of another file. For col-b this includes
   `Protocol.lean`'s private `colProver_next_*` and `Language.lean`'s private `tapeEquiv` and
   `sampleIdx_ofFn`.
4. **Reuse, not copy.**
   - If a lemma you need is private elsewhere, request it in `REPORT.md` and prove a generic
     version under your prefix.
   - Disclose every copy (policy §1, duplication).
   - Do not duplicate `ColSimMachine.reply_poly`.
   - The two-parameter coin transport is one public generic lemma, requested for promotion.
5. **Escalation.** A target that looks false or unprovable as stated is reported with the missing
   hypothesis or a counterexample, never patched. Gate 03g found all three provable as stated, so a
   report is a finding against pack 03g.
6. **Budget.** Complete targets beat partial ones.
   - col-a: the decider first, then `colRep_efficientProverProof`.
   - col-b: ladder steps in the order 1, 4, 5, 2, 3, 6, then the assembly. Each step is a
     standalone public lemma, so a partial delivery leaves usable steps and a precise frontier.

## Environment and verification

- **Environment.** Use the environment addendum attached at dispatch (v1). **Never `lake build`**,
  and never an unfiltered `lake exe cache get`. Run one Lean process at a time
  (`scripts/lean_check_tree.sh <module>`).
- **Build inputs** (identical for both units at the pre-ship commit; regenerate them at
  `@ANCESTOR@` and record their counts):
  - `inputs/<unit>/order.txt`: 142 modules;
  - `roots.txt`: 66 Mathlib roots;
  - `base-sorries.txt`: 21 sorried declarations in 10 modules.
    - The owned files hold exactly the targets: `Protocol.lean` 2, `Simulator.lean` 1.
    - The other 18 are in `Complexity/TuringMachine/*`, `ClassP/TimeConstructible` and
      `Randomized/NonUniform`. Do not cite them: your axiom prints would show `sorryAx`.
- **Bootstrap** per the addendum (item 5). Check new helper modules in order, before their owned
  file.
- **Final checks** (logs in `evidence/`):
  - each owned file and helper with zero errors, and no `sorry` warning for a filled target;
  - the sweep of the order list's modules downstream of your owned file;
  - axiom prints of the filled targets and their consumers (`col_hvzk`, `col_zeroKnowledgeProof`
    for col-b; `colRep_interactiveProof` for col-a; the `NP.lean` wrappers): at most `propext`,
    `Classical.choice`, `Quot.sound`, except `sorryAx` from the other unit's still-open targets;
  - lint as above;
  - the rule-10 seal log, with its controls.

## REPORT.md checklist

- [ ] Base hash (`@ANCESTOR@`) and the exchange commits of each checkpoint.
- [ ] Each target: filled, partial (with its frontier), or escalated (with the reason). For col-b,
      the status of each ladder step.
- [ ] Every new public lemma and definition (with its equation lemmas), every new `private`, and
      every new helper module, each with its role and line count. Owned files over 1000 lines:
      the reason.
- [ ] The error accounting actually used by `col_zk`, if it differs from the binding one.
- [ ] Requested shared lemmas (the two-parameter coin transport; any private found elsewhere).
- [ ] The reuse-not-copy screen and the rule-10 seal (sealed names, controls).
- [ ] The final sweep tail, the axiom prints, and the lint lines (before and after).
- [ ] The diff touches only the owned file(s) and new helper modules; the facade landing edit.
- [ ] Prerequisites P1–P12 found missing at `@ANCESTOR@`, if any, and the steps they blocked.

## Pre-ship record

All checks were run at `5f2771631fe853dae9c2aa44791ae5b0e09c95eb` (`git rev-parse`), in a detached
worktree, with one Lean process at a time and no build. Logs are in `preship/`; the inputs are in
`inputs/`.

| Check | Result | Log |
|---|---|---|
| Build inputs (`fillinputs.py`), per unit | col-a and col-b identical: order 142, roots 66, 21 sorried declarations in 10 modules; owned files: `Protocol.lean` 2 (`R3COL_witnessRelation`, `colRep_efficientProverProof`), `Simulator.lean` 1 (`col_zk`), equal to the targets | `inputs/col-a/`, `inputs/col-b/` |
| Import probe, col-a | All names cited for col-a present and imported. `colProtocol_outV_honest`, `uprob_check_uniform_le`, `colProtocol_sound` are private to `Protocol.lean`. GI templates (`GI.Riso_decidable`, `GI.exec_repViews`, …) are present but not imported, cycle-free, and authorized above | `preship/import-probe-col-a.log` |
| Import probe, col-b | All names cited by the sketch, review §2.3 and the ladder present and imported, except the three ladder lemmas to be added and `GIZK.statClose_pi` (use `OneWay.statClose_pi`) | `preship/import-probe-col-b.log` |
| Duplication probe, col-a | `exact?` (maxHeartbeats 400000): no existing proof of the decider, the targets or the planned facts. One timeout (inconclusive, covered by `OneWay.statClose_pi`) | `preship/dup-probe-col-a.log` |
| Duplication probe, col-b | All ladder statements elaborate. `exact?`: L4, L7a, L7b none; L7 only the target; L1–L3, L5a–c, L6 time out (inconclusive). Greps find no equivalent public lemma | `preship/dup-probe-col-b.log` |
| Route probe, col-b (sealed, controls C1/C2) | The bridge lines up: R1 (`exists_colSimRed_ge` + `exists_fixCoins`), R4 (the machine shape), R7 pass sealed. Mismatches: R3a (`Fin (var.eval n)` vs `Fin n`; fixed by `rw [PolyExpr.eval_var] at`, R3b), R5 (P8, P9), R6 (P5), R8 (P7) | `preship/route-probe-colb.log` |
| Rule-10 probe, col-a (sealed, controls) | A1/A5 pass (`outV_withV`, `withV_self`); A3 (P1), A6 (P4), A4 (shadows), B1 (P12) fail sealed and pass unsealed | `preship/seal-probe-col-a.log` |
| Lint at the base | `style_lint.py`: 20 findings (col-a 1, col-b 0, neither 19); `campaign_style_lint.py`: 4 FAIL (Machines docstrings) plus 6 facade FAILs, check-8 WARNs | `preship/lint-base.log` |

**Not verified:**
- the ladder statements' truth: they elaborate, but are unproved;
- step 5's string function, which is designed by the fill;
- the duplication probes that timed out;
- a full all-branch search for the new public names.
