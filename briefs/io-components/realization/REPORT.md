# Shared realisation file: report

- **Branch:** `foundations/realization`, pushed to origin. No PR was opened.
- **Head:** `cdc0934f36365533d410607d0664a0570ae92679`. It is one SSH-signed commit on
  `cbce64d1c135c710b7c036968ed9d4f21414aa72` (#374, `foundations/subexp`). It is independent of
  the sampler branch.
- **Files:**
  - `TCSlib/Cryptography/Asymptotic/Realization.lean` is new, 250 lines.
  - `TCSlib/Cryptography/Asymptotic.lean` gains one import and a Contents entry, +4 lines.
- **Rulings served:** sPRG Q-S9 (A) = PHFE Q5 (A). sPRG Q-S11 (A) gets its generic link lemma here.

## 1. Statements

The file uses `namespace TCSlib.Cryptography` with `_root_.Complexity.NUPPT.*` names, as
`UniversalLemmas.lean` and `Adversary.lean` do. It has `open Complexity Turing`.

```lean
def Complexity.NUPPT.RealizesOn (B : NUPPT) {X : ℕ → Type*} (enc : ∀ m, X m → List Bool)
    (c : PolyExpr) (R : ∀ m, X m → List Bool → List Bool) : Prop :=
  B.coins = c ∧ ∀ m (x : X m) (r : List Bool), r.length = c.eval m →
    B.runAtL m (enc m x) r = R m x r
```

**Readers.**

- `realizesOn_iff`: `B.RealizesOn enc c R ↔ B.coins = c ∧ ∀ m x r, r.length = c.eval m → B.runAtL m (enc m x) r = R m x r` (proved by `Iff.rfl`).
- `RealizesOn.coins_eq`: `B.coins = c`.
- `RealizesOn.runAtL_eq (m) (x) (hr : r.length = c.eval m)`: `B.runAtL m (enc m x) r = R m x r`.
- `RealizesOn.runAt_eq (m) (x) (ρ : B.Coins m)`: `B.runAt m (enc m x) ρ = R m x (List.ofFn ρ)`.
- `RealizesOn.distinguisherL_eq (m) (x) (ρ)`: `B.distinguisherL m (enc m x) ρ = decide (R m x (List.ofFn ρ) = [true])`.
  This is the verdict lemma both designs ask for.
- `RealizesOn.runAt_coinsEquivPoly_symm (m) (x) (w : Fin (c.eval m) → Bool)`:
  `B.runAt m (enc m x) ((NUPPT.coinsEquivPoly h.coins_eq m).symm w) = R m x (List.ofFn w)`.
  It moves sums over `B.Coins m` to `{0,1}^{c(m)}`.

**Introduction and congruence.**

- `realizesOn_of_forall (hc : B.coins = c) (h : ∀ m x r, B.runAtL m (enc m x) r = R m x r)`:
  `B.RealizesOn enc c R`.
- `RealizesOn.congr (h) (hR : ∀ m x r, r.length = c.eval m → R m x r = R' m x r)`:
  `B.RealizesOn enc c R'`.

**Non-vacuity.**

- `realizesOn_self A enc`: `A.RealizesOn enc A.coins (fun m x r => A.runAtL m (enc m x) r)`.
- `realizesOn_self_take A enc`:
  `A.RealizesOn enc A.coins (fun m x r => A.runAtL m (enc m x) (r.take (A.coinLen m)))`.
  This is the identity reduction (`XPre := enc`, `φ := id`) in the reduction shape, realised by
  `A` itself.

**Link "targets ⇒ realisers" (Q-S11 (A)).**

```lean
theorem exists_realizesOn_reparam_pre_post (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ m, φ m ≤ p.eval m) (enc : ∀ m, X m → List Bool) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ m, (β m).length ≤ b.eval m) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post)
    (g : ∀ m, X m → List Bool) (hg : ∀ m (x : X m), pre (pairEncode (β m) (enc m x)) = g m x) :
    ∃ B : NUPPT, B.RealizesOn enc (A.coins.subst p)
      (fun m x r => post (A.runAtL (φ m) (g m x) (r.take (A.coinLen (φ m)))))

theorem exists_realizesOn_of_preTarget (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ m, φ m ≤ p.eval m) {Ω : ℕ → Type*} (enc : ∀ m, X m → List Bool)
    (encΩ : ∀ m, Ω m → List Bool) (pre : ∀ m, Ω m → X m → List Bool)
    {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hfpre : ∀ m (w : Ω m) (x : X m), f (pairEncode (encΩ m w) (enc m x)) = pre m w x)
    (ω : ∀ m, Ω m) (b : PolyExpr) (hb : ∀ m, (encΩ m (ω m)).length ≤ b.eval m) :
    ∃ B : NUPPT, B.RealizesOn enc (A.coins.subst p)
      (fun m x r => A.runAtL (φ m) (pre m (ω m) x) (r.take (A.coinLen (φ m))))

theorem exists_realizesOn_of_preTarget_id (A : NUPPT) {Ω : ℕ → Type*}
    (enc : ∀ m, X m → List Bool) (encΩ : ∀ m, Ω m → List Bool)
    (pre : ∀ m, Ω m → X m → List Bool) {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hfpre : ∀ m (w : Ω m) (x : X m), f (pairEncode (encΩ m w) (enc m x)) = pre m w x)
    (ω : ∀ m, Ω m) (b : PolyExpr) (hb : ∀ m, (encΩ m (ω m)).length ≤ b.eval m) :
    ∃ B : NUPPT, B.RealizesOn enc A.coins
      (fun m x r => A.runAtL m (pre m (ω m) x) (r.take (A.coinLen m)))
```

The module docstring has the uniformity paragraph, and the definition's docstring repeats it.
This predicate is for reductions, which may use advice. Honest algorithms use
`PolyTimeComputable` or `∃ A, A.Uniform ∧ A.Computes f`, never this.

## 2. Reconciliation

Both drafts write the same signature, `RealizesOn B enc c R` with `R : ∀ m, X m → List Bool → List Bool`.
In both, the advice family is applied inside `R`:

- sPRG: `fun L x r => P.lpnRed π A L (ωL L) x r`;
- PHFE: `dlinToMddh … D ω` and `wee20Red … A q i (ω i)`.

So there is no genuine split, and no specialisation lemma is needed for the predicate itself. ω
appears explicitly only in the link lemmas, as the family whose `pre m (ω m)` is realised.

**One change from both drafts' bodies.** The drafts quantify over **every** coin string `r`. The
file quantifies over coin strings with `r.length = c.eval m`, which are the coins of the layout.

- **It is weaker.** It admits more realisers, so the theorems "∀ B realising ⇒ inequality" get
  stronger, and the `Realizable` propositions get easier.
- **Consumers lose nothing.** Every use reads the realiser through typed coins `ρ : B.Coins m`,
  and `List.ofFn ρ` has length `c.eval m` (`runAt_eq`, `distinguisherL_eq`).
- **The drafts' form still works.** It is a sufficient condition (`realizesOn_of_forall`), and
  `exists_reparam_pre_post` delivers it.
- **The identity reduction gets a realiser.** It is realised by the adversary itself
  (`realizesOn_self_take`). Under the every-`r` form it is not, because `A.runAtL m y r` reads
  coins past `A.coinLen m`.
- **It matches the brief.** It also matches "Phase B's programs are correct on well-formed inputs
  only" (sPRG risk 3 (iii)).

The statements of both drafts are unchanged syntactically. Only the body differs. **The
dispatch prompts should mention this.**

**sPRG mapping** (design-r2 §4.8–§4.10):

- `BL.RealizesOn (P.lpnEnc π) (A.coins.subst .var) (fun L x r => P.lpnRed π A L (ωL L) x r)`
  has `X := P.LPNChal π` and `enc := P.lpnEnc π`. `R` is as written, with the advice applied.
- `realizable_of_targets` is `exists_realizesOn_of_preTarget A (κOf) .var hκOf (P.lpnEnc π)
  (P.encLPNAdvice π) (P.lpnPre π) hf (hT π) ω b (fun L => hlen L (ω L))`.
  `lpnPreTarget` quantifies `π` inside, so the job instantiates it at `π`. The conclusion is
  `lpnRed` up to delta, and `exact` closes it. The same holds for `prg`.
- The probe below elaborates `XRealizable` and `realizable_of_targets` in exactly this shape.

**PHFE mapping** (design-r2 §4.4, §4.10):

- `B.RealizesOn G.dlinEnc A.A₂.coins (wee20Red … A q i (ω i))` has `φ = id` and coins `A.A₂.coins`.
- For Phase B, `exists_realizesOn_of_preTarget_id A.A₂ G.dlinEnc encΩ XPre hf hT ω b hb` gives
  `∃ B, B.RealizesOn G.dlinEnc A.A₂.coins (fun κ x r => A.A₂.runAtL κ (XPre κ (ω κ) x) (r.take …))`.
  `A.coins.subst .var` is rewritten to `A.coins` by `PolyExpr.subst_var`.
- The design does not propose this lemma for PHFE in Phase A. Phase A needs only the predicate
  and the verdict lemma.

## 3. Checks

All Lean checks ran through `scripts/lean_check_tree.sh`, one process at a time, against a
`cp -al` copy of olean snapshot #10 (`$SP/real-oleans`). The snapshot itself was never written.

| Module | rc | errors | warnings |
|---|---|---|---|
| `Foundations/Subexponential` (#374, checked first) | 0 | 0 | 0 |
| `Foundations` facade (#374) | 0 | 0 | 0 |
| `Asymptotic/Realization` | 0 | 0 | 0 |
| `Asymptotic` facade | 0 | 0 | 0 |

**Scratch probe.** It was uncommitted and has been deleted. It contained:

- the sPRG shape (`XRed`, `XRealizable`, `realizable_of_targets` via `exists_realizesOn_of_preTarget`,
  and the verdict lemma in a hop);
- the PHFE shape (`PRed` with `φ = id`, coins `A₂.coins`, via `exists_realizesOn_of_preTarget_id`);
- a non-vacuity instance of the link with `f := pairSndD`;
- `#print axioms` for all 14 declarations.

The probe gave rc 0. **Every declaration depends only on `[propext, Classical.choice, Quot.sound]`.**

**Other checks.**

- `python3 -I scripts/style_lint.py` on both files gave **0 findings in 2 files**.
- No line is longer than 100 characters (counted in characters).
- There is no `sorry`, `admit`, `native_decide` or `axiom`.

**Facade and Stage 2.** No row of `briefs/pass-shelat-ch5-8/cleanup-stage2/scope.tsv`, and
nothing in `s2a-items.tsv`, names `Asymptotic.lean`. So the import went into the `Asymptotic`
facade, after `Universal`, with a Contents entry. It is not in `TCSlib.lean` or
`Cryptography.lean`.

## 4. Helpers reused, and the duplication searches

**Searches** (`git grep` at `cbce64d1c`):

- `realis|realiz` over `Asymptotic/`, `Games/`, `Complexity/Randomized/` and `Foundations/`
  found only prose.
- `RealizesOn|ComputesOn|def Computes|toCompOn|exists_toCompOn_of_toComp`, and the definitions
  in `Games/Machines.lean`, `ReductionSupport.lean`, `Adversary.lean` and
  `Games/Efficiency.lean`, did not turn up a duplicate either. Each candidate does a different
  job:
  - `NUPPT.Computes f` constrains every argument `y`, on `advInput n y`, and reads no typed
    challenge.
  - `toComp`/`toCompOn` are oracle-computation builders, not predicates.
  - `exists_toCompOn_of_toComp` is a construction.
  - `Lamport/Realization.lean` is a specific T1 realisation. The sPRG duplication sweep r2 also
    rates it NR.
- **No existing predicate does this job.** The sPRG sweep (§D) and the PHFE sweep (§4a) reached
  the same result.

**Helpers used (none duplicated):**

- `NUPPT.runAtL`, `runAt_eq`, `coinLen_eq`, `length_ofFn_coins`, `coinsEquivPoly`,
  `coinsEquivPoly_symm_ofFn` (`Complexity/Randomized/PPT.lean`);
- `NUPPT.distinguisherL_eq` (`Asymptotic/Adversary.lean`);
- `NUPPT.exists_reparam_pre_post` (`Asymptotic/UniversalLemmas.lean`);
- `PolyExpr.eval_var`, `PolyExpr.subst_var` (`PolyExpr.lean`);
- `polyTimeComputable_id`;
- `List.take_of_length_le`.

The probe also used `polyTimeComputable_pairSndD` and `pairSndD_pairEncode`.

## 5. Cleanup

- The worktree `$SP/wt-realization` and the olean copy `$SP/real-oleans` have been removed.
- `git worktree prune` has been run.
- Snapshot #10 was not touched: the rebuilt oleans were unlinked in the copy before writing.
