# S3c route note: the BPP → NUPPT bridge for Thm 180.1 (decision D-6)

Status: **statement shape fixed and merge feasibility checked, 2026-11-04.** The Lean probe of the
statement waits for a tree that has both models, which is S1 point 5 (merging `main` into the
ch. 2–4 branch).

## The ruling

D-6 (user, 2026-11-04): a **one-way bridge lemma**. A `polyTimeModel` BPP verifier gives a NUPPT
that runs it, with a chosen input hard-wired as advice. Thm 180.1 is stated against `main`'s
`Randomized.InBPP Randomized.polyTimeModel` and `Complexity.DTIME`. Unifying the two models is a
separate, later decision.

## Merge feasibility (checked on a scratch merge, never committed or pushed)

Merging `origin/main` (`06e61e912eedc2bce49b3ccff77bb9c4a7e18579`) into Frederick's last Lean
commit (`a7a3e0af0ecd261bd8643fcf96a2cfcbaa5757b7`) produced:

- **Two textual conflicts, both trivial:**
  - `TCSlib/Complexity/Randomized.lean`: both sides added the facade (add/add); keep the union
    of the imports;
  - `TCSlib/ComputationalModels.lean`: each side added one line to the docstring's references
    ([PS10] and [AFM26]); keep both.

  **Correction to the S1 note's point 5**, which named only the first file.
- **No new clash of full declaration names.** A namespace-aware scan of the merged tree finds 13
  names declared in more than one file:
  - 12 are graph-theory names that `main` already has on its own, in files never imported
    together;
  - the 13th is the known `TCSlib.Cryptography.zipWith_xor_ofFn` (S1 point 1).

  The models' namespaces (`Complexity` for Frederick's, `Randomized` for ch7's) do not collide.
- **Size of what prong D needs from `main`:** `Randomized/PolyTimeModel`'s import closure is 82
  modules, `Randomized/Classes` 1, `ClassP/DTIME` 4. A probe on a local merged tree is cheap.

## The statement shape (for the S4 statement phase)

Two lemmas, in a new file of prong D (`TCSlib/Cryptography/Randomness/BPPBridge.lean`), citing both
models and editing neither.

1. **Running a verifier as a NUPPT.** Let:
   - `M : List Bool → List Bool → Bool` with `Randomized.polyTimeModel.Eff (boolVerifier M)`:
     its true-set and false-set on `pairEncode x r` are in `P`;
   - `xs : ℕ → List Bool` be a sequence of inputs of polynomially bounded length (the advice).

   Then there is a NUPPT `D` with advice `xs n` at parameter `n` such that, at parameter `n`, on a
   candidate random string `y`, `D` outputs `[M (xs n) y]` for every coin string:

   ```lean
   theorem verifier_toNUPPT {M : List Bool → List Bool → Bool}
       (hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M))
       (xs : ℕ → List Bool) (p : PolyExpr) (hxs : ∀ n, (xs n).length ≤ p.eval n) :
       ∃ D : Complexity.NUPPT, D.advice = xs ∧
         ∀ n (y : List Bool) (r : D.Coins n), D.runAt n y r = [M (xs n) y]
   ```

   **Route:**
   - `Eff` gives `P`-languages `V₁` and `V₀`; their indicators are `PolyTimeComputable` (`main`'s
     `ClassP`);
   - the layout projection `⟨⟨⟨1^n, y⟩, adv⟩, r⟩ ↦ pairEncode adv y` is `PolyTimeComputable`
     (`pairFstD`, `pairSndD`, `pairEncode`);
   - compose the two, and apply Frederick's `NUPPT.ofPolyTime` with advice `xs` (its advice field
     needs the length bound `hxs`).

   This is the NUPPT distinguisher in Thm 180.1's proof: the bad input `x`, hard-wired. Advice is
   indexed by the PRG's parameter, so `xs` is "the bad input of length `n^{ε'}`".
2. **The two probabilities agree.** `main`'s `randProb m A` (a ℚ counting ratio over
   `Fin m → Bool`) cast to ℝ equals Frederick's `uprob` over the same type:
   `(randProb m A : ℝ) = uprob (fun r : Fin m → Bool => A (List.ofFn r))`. Both are a filter count
   over `2^m`. Thm 180.1's error bounds, stated with `randProb`, then turn into a distinguisher's
   advantage.

`polyLen a k`, `main`'s coin schedule `n ↦ a·(n+1)^k`, is the `PolyExpr`
`mul (const a) (pow (add var (const 1)) k)`; a `rfl`-level equation lemma goes in the same file.

## Thm 180.1 itself (the hard part, for the record)

1. Pick `ε' < ε` and a PRG `G : {0,1}^{ℓ} → {0,1}^{m(ℓ)}` with `m` large enough, using Frederick's
   `prg_expand`.
2. Replace the coins `r ∈ {0,1}^{a(n+1)^k}` of the BPP verifier by `G(s)` with
   `|s| = ℓ(n) ≈ n^{ε'}`.
3. If for infinitely many `n` some input `x` of length `n` has its acceptance probability move by
   more than `1/6`, lemma 1 with `xs` = those inputs gives a NUPPT distinguisher for `G`, a
   contradiction.
4. So for large `n`, the majority vote over all `2^{ℓ(n)}` seeds decides `L` (finitely many small
   inputs are hard-wired).

The **machine-level obligation** is a deterministic machine that enumerates the seeds, runs `G`
and the verifier, and takes the majority, in `DTIME(2^{n^ε})`. It sits on `main`'s `DTIME` and the
TM library. It costs the same whichever way D-6 went, and it is the largest single construction of
prong D.
