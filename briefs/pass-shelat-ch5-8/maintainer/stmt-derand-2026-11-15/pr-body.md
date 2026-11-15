# Statement: the seed-majority enumeration host (derand, PS10 Thm 180.1)

Draft maintainer statement PR, by Seyoon's ruling of 2026-11-14: the contract of the deterministic
counting/majority enumeration host that `bpp_subset_dtime_subexp` ([PS10, §8.2, Theorem 180.1]) needs is
stated first, as `sorry`, with its own gate. `derand` is dispatched only after that gate.

Branch `stmt/pass-shelat-derand-host` (local, not pushed), head `8972fb4ef15fa3d4e3df37d6aa8674408835593d`,
tree `ba544f9ca0d80ff12644128a2cc32a94d6b5f709`, on base `013119f006af40d03b88b0fc2d9b453cf0a9b348`
(`origin/cryptography/pass-shelat-ch2-4` after fetching, 2026-11-14).

## Changes

- **New:** `TCSlib/Complexity/Randomized/SeedMajority.lean` (163 lines).
  - `Complexity.seedMajority_mem_DTIME`: the host's contract. Stated; the only `sorry`.
  - `Randomized.half_lt_randProb_iff`: majority as a probability. Proved.
  - Module docstring: the formal reading, the consumers, the design, and the route for the fill.
- **Facade:** `TCSlib/Complexity/Randomized.lean` imports the module and lists it under `## Contents`.

## The statement

```lean
open Classical in
theorem seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  sorry

theorem half_lt_randProb_iff (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    1 / 2 < randProb m A ↔
      2 ^ m < 2 * (univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card
```

## Design

- **The machine is existential.** The contract is a class membership in `DTIME`. That one
  membership carries both halves:
  - *correctness:* some machine decides exactly the strict-majority language;
  - *time:* it runs within `c · 2^{w(n)} · (n+1)^e`.

  Consumers read it only through published readers: `DTIME.mono`, `Randomized.DTIME_const_mul_subset`
  and `half_lt_randProb_iff`. No new `def` is introduced, so no sorried definition and no reader
  obligation arise (Rule 10).
- **Generality is what derand consumes, kept generic in what consumers vary.**
  - *The test* is any `V ∈ P` on `pairEncode x u`, so it depends on the input as well as the seed.
    `pairEncode` is the convention of `Randomized.polyTimeModel`, so derand's test is a `P`-preimage
    of its verifier's language.
  - *The width* is any `w` with a polynomial-time unary word. Derand uses the integer root `ℓ(n)`,
    piecewise with the true coin length `m(n)` below a threshold, which removes the need for a
    finite-table lemma.
  - *The count* is the `Finset` numerator of `randProb`, and *majority* is strict.
- **Placement.** The module goes in the shared Randomized layer of Complexity, not in derand's
  helper directory. Policy §1 puts hosts in the shared layer, there is a second consumer (`BPP ⊆ EXP`
  by coin enumeration, [AB09, p. 126]), and Complexity does not import Cryptography.
- **Nearest relatives, not reused.** `Complexity.exists_proj_decider` has an any-verdict, a fixed
  width `C(n+1)^c`, a test on `x ++ u`, and a private engine. The polynomial block-majority tests
  count over polynomially many blocks, not exponentially many seeds.

## Feasibility (the host fill)

1. **Pure layer, about 400–700 lines.**
   - The state is `⟨x, ⟨i, a⟩⟩`: the binary seed rank and the binary accept count.
   - Start at `⟨x, ⟨0, 0⟩⟩`. Each step adds `[⟨x, word_w(i)⟩ ∈ V]` to `a` and increments `i`.
     The run stops at `i = 2^{w}` with payload `[2^w < 2a]`.
   - Each piece is polynomial-time by `BinArith.polyTimeComputable_add`/`_lt`/`_beq`,
     `polyTimeComputable_ite`, `PolyTimeComputable.pairEncode`, `mem_P_iff_polyTimeComputable` and
     `hw`.
   - The state length is `O(n + w n)` by `PolyTimeComputable.output_length_le`.
2. **Machine, about 250–400 lines.** This is `Turing.FinTM.exists_loopFindTM` over
   `Complexity.IterateFind.hostTM`/`hostCtrl`/`hostRet`. The pieces are:
   - the modules `copyTM`/`copy_clean` and `Turing.ModuleHost.clean_install`/`clean_emit`;
   - `host_call`, `host_clean`, `host_dispatch`, `host_branch`, `host_halt`, `guard_add` and
     `request_budget`.

   It follows `Complexity.IterateFind.polyTimeComputable_find`'s proof, with the exponential fuel
   `Nat.bits (2^{w|x|})` (w zeros, then a one) taken from `hw`. The bound is
   `c (T n + 1)(2^{w n} + 2)` with `T` polynomial.

   `IterateFind`'s helpers `Inv`, `verdictWord`, `stepWord`, `outWord` and `final_bound` are private.
   The fill either re-derives them (about 100 lines, disclosed) or uses a harvested generic-fuel form;
   see the decisions below.
3. **Count, about 150–300 lines.**
   - The first stop index is `2^w` (`IterateFind.find?_range_and_lt` / `StateLoop.find?_range_eq_some`).
   - `a` equals the `Finset` count through the bijection `i ↦ word_w(i)` between `[0, 2^w)` and
     `Fin w → Bool` (Mathlib `finFunctionFinEquiv`, `Nat.testBit`).
4. **Normal form, about 80–150 lines.** Show `c (T n + 1)(2^{w n} + 2) ≤ b · 2^{w n} (n+1)^e`, then
   introduce the `DTIME` membership.
5. **Total: about 900–1,600 lines.** The brief estimated 1,500–3,000 for this item.
   - Every route lemma above prints only `propext`, `Classical.choice` and `Quot.sound`
     (`probes/RouteAxioms.log`).
   - The route uses none of the admitted `loopHostTM_*` and `timedCondTM_*` specs: `exists_loopFindTM`
     comes from the private, proved `loopHost_contracts`.

## Theorem 180.1 from the contract and the PRG hypothesis (paper proof)

**Setup.** Let `L ∈ BPP` have verifier `M` with `M x r = true ↔ ⟨x, r⟩ ∈ V₁ ∈ P` and `m(n) = a(n+1)^k`.
Fix `d ≥ 2` with `1/d < min(ε, 1)`, and let `ℓ(n)` be the least `t` with `n ≤ t^d`.

1. **Expand the generator.** From `∃ G, G.Secure`, obtain a secure `G'` with stretch at least
   `P(s) = a(s^d+1)^k + s + 1` (`prg_expand`, `PRG.Secure.truncateTo_easy`/`_negligible`) and an
   evaluator `F'` (`PRG.easy_iff`). Since `n ≤ ℓ(n)^d`, we have `m(n) ≤ P(ℓ(n))`.
2. **Bound the gap.** There is `n₀` such that `|Pr_u[M(x; F'(u)↾m)] − Pr_r[M(x; r)]| ≤ 1/12` for every
   `|x| ≥ n₀`.
   - Otherwise infinitely many input lengths are bad.
   - Each seed length `s` is `ℓ(n)` for at most `s^d + 1` values of `n`, so infinitely many seed
     lengths are bad.
   - Take one bad `x` per bad seed length as advice (`|x| ≤ s^d`), and let `D(1^s, y) = M(x; y↾m(|x|))`.
     It is a NUPPT by `verifier_toNUPPT` and `NUPPT.exists_withAdvice(On)`.
   - Then `prgAdv > 1/12` infinitely often (`randProb_eq_uprob`), which contradicts `PRG.secure_iff`.
3. **Define the test and the width.**
   - `w(n) = if n < n₀ then m(n) else ℓ(n)`. Its unary word is polynomial-time.
   - `V'' = {⟨x, u⟩ | if |x| < n₀ then ⟨x, u⟩ ∈ V₁ else ⟨x, F'(u)↾m(|x|)⟩ ∈ V₁}`. It is in `P` by
     `preimage_mem_P`, `inter`/`union`/`compl_mem_P`, `PolyTimeComputable.pairEncode` and
     `takePrefixByLen`.
4. **`L` is exactly the majority language of `(V'', w)`.**
   - Below `n₀` the coins are true, so the acceptance probability is at least `2/3` or at most `1/3`.
   - From `n₀` on, it is at least `2/3 − 1/12 = 7/12 > 1/2` or at most `1/3 + 1/12 = 5/12 < 1/2`.
   - `half_lt_randProb_iff` turns this into the count.
5. **Apply the contract.** There is `e` with `L ∈ DTIME (2^{w n} (n+1)^e)`.
6. **Absorb the bound.** For large `n`, `ℓ(n) ≤ n^{1/d} + 1`, so `2^{w n}(n+1)^e ≤ 2^{n^{1/d} + 1 + e log₂(n+1)}`.
   Since `1/d < ε`, this is at most `subexpBound ε n` from some `N` on.
   - The finitely many lengths below `max(N, n₀)` are absorbed into `c` (`subexpBound_pos`).
   - Hence `∀ n, 2^{w n}(n+1)^e ≤ c · subexpBound ε n`, and `DTIME.mono` followed by
     `Randomized.DTIME_const_mul_subset` closes the goal.
   - `probes/ConsumerProbe.lean` checks this step through readers only, with `DTIME`, `randProb`,
     `P`, `PolyTimeComputable` and `pairEncode` sealed.

## Checks (evidence `stmt-derand-evidence.zip`)

- **Build.** 63 modules are checked one at a time into `dl-oleans-2`, all rc 0 with 0 errors (both
  forms counted). They are:
  - the new module and its facade;
  - the 51 tip-vs-olean-base Cryptography modules and their downstream;
  - root `TCSlib` and `audits/pass-shelat/Checks`.

  The only `sorry` warning is `seedMajority_mem_DTIME` (`SeedMajority.lean:154`).
- **Axioms.** `seedMajority_mem_DTIME` has `sorryAx` (intended). `half_lt_randProb_iff` has the
  standard three.
- **Seals.**
  - Whole-file seal of the new module (`randProb`, `DTIME`, `P`, `PolyTimeComputable`, `pairEncode`):
    rc 0.
  - Paired control: passes unsealed, fails sealed exactly once.
  - Consumer probe: passes sealed apart from its control, which fails exactly once; passes unsealed.
- **Lint.**
  - `campaign_style_lint.py TCSlib/Cryptography --check8b`: 92 FAIL / 101 WARN at base and at head,
    identical line sets.
  - `TCSlib/Complexity --check8b`: 25 / 391 at both, identical line sets. Six pre-existing facade
    FAILs for `Randomized/Build/*` are unchanged.
  - The new file has no FAIL or WARN.
- **Width and size.** The changed files have at most 100 characters per line and 163 and 210 lines.
- **Tree.** `dl-oleans-2` is restored. Its snapshot SHA-256 is
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` before and after, byte-identical.

## Decisions for Seyoon

1. **Placement and name.** `Complexity/Randomized/SeedMajority.lean`, with
   `Complexity.seedMajority_mem_DTIME`.
2. **Generality.**
   - The test is `V ∈ P`, not a decider with arbitrary time `Tv`. A generic-time form needs a clean
     module for a decider of arbitrary time.
   - Majority is strict, with no general threshold.
   - The test uses `pairEncode`, not `x ++ u`.
   - There is only the `DTIME` form, with no machine-level `DecidesInTime` contract.
3. **No head-envelope clause.** Policy §1 asks hosts for time and space clauses. This contract is
   decision-layer, as `exists_proj_decider` is.
4. **Registry row H17** (`machine-library-design.md` §14). It is not edited here; the draft is below.
5. **Fill route.** Either harvest a generic-fuel `computesFunInTime_find` into
   `Randomized/Build/IterateFind.lean` (preferred; `polyTimeComputable_find` would become its
   corollary), or have the fill re-derive the private `IterateFind` helpers, disclosed.
6. **Introducing `DTIME` membership.** There is no `mem_DTIME_iff` reader beside `DTIME`. Either
   approve the anonymous-constructor idiom used by `DTIME_const_mul_subset` and
   `mem_DTIME_of_decidesInTimeVia`, or add the reader, which rebuilds `DTIME`'s downstream.
7. **The derand brief.** Route step 4 and checkpoint 1 become a consumption of this contract. The
   finite table can fold into the width. Derand's closure gains `Randomized/SeedMajority` and
   `Randomized/QuasiPolyHierarchy`, so `order.txt` and `roots.txt` need regenerating.
8. **Sequencing.** Assign the gate number, and decide whether derand may run proved-modulo while the
   host fill runs.

## Draft registry row (for `machine-library-design.md` §14)

| H17 | **Seed-majority enumeration host:** `Complexity.seedMajority_mem_DTIME` in `TCSlib/Complexity/Randomized/SeedMajority.lean`. For a test `V ∈ P` on `pairEncode x u` and a width `w` with a polynomial-time unary word, the strict-majority language `{x | 2^{w|x|} < 2·#{u ∈ {0,1}^{w|x|} : ⟨x,u⟩ ∈ V}}` is in `DTIME(2^{w(n)}·(n+1)^e)` for some `e`; reader `Randomized.half_lt_randProb_iff`. Decision layer; no head-envelope clause. | **Statement only**, in this PR; gate to be assigned. Fill route: `exists_loopFindTM` over the clean-module host (H14) with exponential fuel. | `bpp_subset_dtime_subexp` (derand, [PS10, Thm 180.1]); prospectively `BPP ⊆ EXP` by coin enumeration [AB09, p. 126]. |

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
