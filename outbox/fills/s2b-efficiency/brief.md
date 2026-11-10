# Claude fill · shared reduction efficiency

**Issue base** `b50f0a416cbf0a9f05acf14a254ba53cd97a7701` on `cryptography/pass-shelat-ch2-4`.
**Unit** `s2b-efficiency`. **Worker** Claude. **Lean** 4.25.0 and the Mathlib revision
in that commit's `lake-manifest.json`.

Prove the four admitted theorems in `TCSlib/Cryptography/Games/Efficiency.lean`.
They turn the simulated reductions into machines quantified over by the
cryptographic assumptions. T1 is the dependency for the public-key CPA bridge.
T2, the input-free companion and T4 also support the pending private-key and
authentication proofs. The statements passed Gate 04 and landed in PR #195.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/s2b-efficiency` at the exact issue base above. Record the base in
  `REPORT.md`. Keep the local branch at that ancestry.
- Read `policy.md`, the attached environment addendum and `README.md`.
  In `briefs/pass-shelat-ch5-8/design/S2b-efficiency.md` use the route section
  for proof design. The current paths, scope, checkpoints and commands in this
  brief supersede the historical setup notes in that design.
- Deliver every checkpoint and the final payload under
  `inbox/fills/s2b-efficiency/` on `exchange/pass-shelat-ch5-8`. Include
  `REPORT.md`, `patches/` containing the whole `git format-patch` series from the
  issue base, `src/` with owned paths, and `evidence/`. Use commit messages
  `fill s2b-efficiency: checkpoint N` and `fill s2b-efficiency: final`.
  Pull the exchange with rebase before pushing. Push only your delivery path.
  Keep the proof branch local. Campaign changes land by a maintainer PR for
  Seyoon's approval.

## Targets

| Target | Declaration in `TCSlib.Cryptography.Games` | Issue-base line |
|---|---|---:|
| T1 | `exists_handlerMachine` | 300 |
| T2 | `exists_interactiveHandlerMachine` | 510 |
| Companion | `exists_toCompOn_of_toComp` | 538 |
| T4 | `exists_toOracleAdversary_of_bitCodec` | 569 |

The source declarations are frozen. These quotes come directly from the issue base.

```lean
theorem exists_handlerMachine (A : NUPPT) (q : PolyExpr) (din dout : Fin k → PolyExpr)
    (dα : PolyExpr) (H : PolyHandler k din dout) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        ∃ (a : Fin (dα.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
          simulate (H.impl n z ω)
              (A.toCompOn
                (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
                n (q.eval n) (H.advInput n z ω) r) (H.init n) = .pure (a, s) ∧
            B.runAt n z (φ (ω, r)) = H.result n z ω s a := by
  sorry
```

```lean
theorem exists_interactiveHandlerMachine (A : NUPPT) (q : PolyExpr)
    (din dout : Fin k → PolyExpr) (din' dout' : Fin k' → PolyExpr) (dα : PolyExpr)
    (H : InteractiveHandler k din dout k' din' dout') :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        (simulate (H.impl n z ω)
            (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
              n (q.eval n) (H.advInput n z ω) r) (H.init n)).bind
            (fun res => H.finish n z ω res.2 res.1) =
          B.toCompOn
            (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (H.outLen.eval n))
            n (q.eval n * H.perCall.eval n + H.finCall.eval n) z (φ (ω, r)) := by
  sorry
```

```lean
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  sorry
```

```lean
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  sorry
```

## Published interfaces

| Interface | Current provider |
|---|---|
| `NUPPT.coinLen_eq`, `runAt_eq` and machine constructors | `TCSlib/Complexity/Randomized/PPT.lean` and `NonUniform.lean` |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_split`, `exists_withAdvice` and `runAtL_eq_output_layout` | `TCSlib/Complexity/Randomized/Closure.lean` |
| `decodeOracleMove_pairEncode_false`, `decodeOracleMove_pairEncode_ofFn`, `decodeOracleMove_true_two`, `decodeOracleMove_pairEncode_false_of_length_ne`, `decodeOracleMove_of_ne` | `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean` |
| `decodeFin_eq_some_iff`, `decodeFin_ofFn` and `length_eq_of_decodeFin_eq_some` | `TCSlib/Cryptography/Asymptotic/Adversary.lean` |
| `GGMRed.stateLoopFun`, `stateLoopFun_poly`, `stateLoopFun_eval` and `pairEncode_append_right` | `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean` |
| `StateLoop.orbit_zero`, `orbit_succ`, `gstep_iterate_eq` and `find?_range_eq_some` | `TCSlib/Complexity/Randomized/Build/StateLoop.lean` |
| `polyTimeComputable_iterateEmit` and `polyTimeComputable_iterateFind` | `TCSlib/Complexity/Randomized/Repetition.lean` |
| `decodeBitMove_query`, `decodeBitMove_ret`, `decodeBitMove_of_not_canonical` and `encodeLog_bitCodec` | `TCSlib/Cryptography/Games/BitCodec.lean` |
| `NUPPT.toComp_eq`, `toCompOn_eq`, `toCompOn_costBoundedBy` and `buildComp` case equations | `TCSlib/Cryptography/Games/Machines.lean` |
| `simulate_costBoundedBy`, `OracleComp.CostBoundedBy.bind` and the pure/query equations | `TCSlib/Cryptography/Games/Simulate.lean` and `OracleComp.lean` |
| `toComp_singleCodec`, `encodeLog_singleCodec` and `toHist` readers | `TCSlib/Cryptography/Games/Bridges/Machines.lean` |

Seyoon approved citation of the existing public helper proofs at this issue base
on 2026-11-10. The dependency screen records historical cleanup findings in
their transitive proof dependencies, including the use of `StateLoop.gstep`
inside `GGMRed.stateLoopFun_poly`. Cite the public theorems under seal in the
new proofs. Keep the cited provider files and proof bodies frozen. Record any
new missing reader in `REPORT.md` for the maintainer to triage. The existing
findings stay in the cleanup ledger.

## Proof route and checkpoints

1. **Companion.** Use `NUPPT.exists_comp` with `pre = pairSndD` and `post = id`.
   Pair projection removes the added input. Transport the coin vector along the
   equality from `coinLen_eq`, using `List.ofFn_congr` for the actual tape.
   Rewrite through `toCompOn_eq` and `toComp_eq`. Send checkpoint 1.
2. **T1.** Set up the shared canonical move/answer decoding and log appending.
   Put `List.ofFn (H.init n)` beside `A.advice n` in the advice of the new
   machine. Split coins into the handler seed and adversary tape. The bounded
   state loop retains the original input, state and log, recomputes the context,
   and advances the simulation one move at a time. Show the actual orbit fits
   the length bound, and use `GGMRed.stateLoopFun_eval` with the exact number
   of rounds. Check the zero-query case and finalization. Send checkpoint 2.
3. **T4.** Translate the ch. 2–4 history into the `Fin 1` bit-codec log, preserving
   order, then translate the move returned by `B`. Reuse the iteration and
   pairing combinators. `NUPPT.exists_compParam` exposes `1^n` to both
   translators if they need evaluated lengths. Use the published decoder cases
   and induct on the remaining budget. Check `ℓ₁(n) = 0` and the default verdict.
   Send checkpoint 3.
4. **T2.** Implement the replay of the adversary, each handler call and the
   finalization. Thread the outer-log cursor, the current inner history and the
   separate budgets. The target is equality of computation trees, including
   arbitrary outer answers. Prove the per-call and final query bounds before
   using the replay lemma. With one activation per round, the proposed replay
   bound is `(q + 1) + q * (perCall + 1) + finCall + 1` at parameter `n`.
   Include any extra initialization activation in the bound. The supplied
   cost-scaling probe exercises the pure/query induction under seal. Send
   checkpoint 4 and then the final payload.

The round-level cases in the design note include two distinct defaults.
`PolyHandler.answer` defaults componentwise. `InteractiveHandler.call`
decodes one combined word and defaults both components together. Projections
can give empty words on malformed inputs, so check canonicity by re-encoding.
At budget zero the machine still decodes a verdict, and a pending query gives
the timeout without calling its oracle. These cases apply to every replay.

## Scope and proof discipline

- Own `TCSlib/Cryptography/Games/Efficiency.lean`. Replace the four proof bodies
  and add local helpers in `TCSlib.Cryptography.Games.EffFill`. EF-1 permits helper
  modules under `TCSlib/Cryptography/Games/Efficiency/` with precise acyclic imports.
  Import the existing GGM reduction module directly from the first consumer.
  Keep helper files below 1000 lines and publish the needed reader equations and
  proof sketches. Cite public GGM loop results where they apply. New shared
  helper declarations live in the fill's namespace and the report lists them.
- EF-2 permits editing the four proof sketches to describe the proofs actually
  delivered. Preserve the statements, all existing non-target declarations
  and the statement prose in docstrings. Keep global simp attributes unchanged.
- Use published readers for other files' definitions in both tactics and term
  elaboration. `NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryTree` and
  `OracleAdversary` are abbreviations. For core and Mathlib use their equation
  lemmas in `simp`, `rw` and `unfold`. Preserve the policy's existing rules on
  opacity, private names, and proof axioms.
- If a frozen target appears false or a required reader has no clean route,
  give the exact failing obligation and the smallest proposed correction in
  `REPORT.md`. Continue independent targets where feasible. At a partial
  delivery identify each remaining admission and include the checked frontier.

## Checks and report

- Bootstrap from `order.txt` and the narrow `roots.txt` using the environment
  addendum. The order includes the authorized GGM reduction import. Insert any
  new helper module before its consumers and recalculate roots if imports change.
  Check one module per `scripts/lean_check_tree.sh` invocation. Keep one Lean
  process per olean tree.
- Recheck `Games/Efficiency` and `Games/Bridges` and sweep the supplied order.
  Compare the warnings with `base-sorries.txt`. A complete owner check has no
  sorry warnings. Use the checker for scratch axiom prints and probes too.
- Print the axioms of the four targets. Each completed proof should use only
  `propext`, `Classical.choice` and `Quot.sound` as needed.
- Collect foreign references from the elaborated new proofs, including
  generated matcher and projection helpers. Run an instance-aware seal of the
  touched proofs with the full candidate list, plus a control that passes
  before sealing and fails after sealing. Report the candidates, controls and
  any findings. Include the explicit-unfold scan and
  `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Games --check8b`.
- Report the issue base, each target's status, exact changed files and sketch
  edits, published helper citations, any reader or machine requests, and
  the resource, cache, bootstrap, sweep, axioms, seals and lint evidence.

**Ready to dispatch**
