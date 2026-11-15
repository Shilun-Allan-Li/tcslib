# derand · final

## Status and review disposition

All three frozen targets are **proved with only `propext`, `Classical.choice`, and
`Quot.sound`**. No target is proved modulo an admission in this payload. The exact
final source passes the complete 387-module replay with zero errors; its sorry list
is the issued baseline minus precisely the three requested targets: **23 declarations
in 10 modules**. No statement is weakened.

**Rule 10 disposition: HOLD, disclosed exception EX-02.** The canonical seals of the
harvest E1 retain nine new diagnostics, alongside eleven inherited diagnostics in
the unchanged old theorem, in each of four variants. All 56 variants for the other
14 changed/new files pass. This delivery does not claim seal clearance. A proposed
reader fix in two further frozen providers was rejected by automatic approval review
and was not applied. The maintainer must assess this exception before landing.

Worker: external Codex, the worker called “Claude” in issued-r2. The host addendum
overrides the environment addendum where stated. The r2 issue replaces r1.

* Issued exchange pin: `7d85785c2e98f0bfdec081a875a9343f06043a8a`.
* Source base: `01de2d8baed9113e4a099e13c5d50c81e6dbc66f` on `cryptography/pass-shelat-ch2-4`.
* Final source tip: `5e12a169e671dc16b6766e21067b79c16835af67` on local-only branch `fill/derand`.
* Lean: 4.25.0, arm64 macOS; Mathlib pin
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
* The source branch is never pushed; delivery is only `inbox/fills/derand/`.

| Frozen target | Final status |
|---|---|
| `Complexity.exists_seedMajorityTM` | proved; standard axioms |
| `Complexity.seedMajority_mem_DTIME` | proved from the contract through `mem_DTIME_iff`; standard axioms |
| `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` | proved; standard axioms |

## Checkpoints and proof route

Checkpoint 1 delivered E1, E2, E3, approved SR-01, and the corollary from the still
admitted host; its full 377-module replay passed. This payload completes checkpoint
2's host as well as Theorem 180.1. The consumer was developed first modulo the host,
as the issued proved-modulo rule expressly permits. Filling the host removed that
dependency, verified by both the all-constant axiom census and a kernel dependency
path audit. No mathematical work was delegated; all proofs and checks were run by
this worker. Other-worker messages concerned shared resource scheduling only.

The host retains `x` in the paired state `⟨x, ⟨i, a⟩⟩`. Binary ranks enumerate all
`2^w` seeds using the existing `bitsEquiv`; the finite prefix count supplies the
induction invariant. The generic-fuel harvest uses the existing total length guard
and its closed `Inv`. The terminal rank is included in `range (R+1)`; no bound is
assumed for an unguarded increment past termination. Fuel is binary `Nat.bits (2^w)`,
never an exponential unary word. Published arithmetic and pairing machines compute
each round, and the explicit polynomial per-round budget yields
`c * (2^w * (n+1)^e)`. The native initial-configuration envelope follows from the
public head-position interval bound before halting and the public halt/run readers
after halting. A zero time coefficient is impossible by `not_computesInTime_zero`.

The consumer uses `ceilRoot d n = 0` for `n=0`, and
`Nat.nthRoot d (n-1)+1` otherwise. The unary word is computed using the published
bounded state search and fixed unary powers, not a copied root machine. A secure
generator is truncated and expanded to the syntactic envelope
`a*(s^d+1)^k+s+1`. Non-uniform advice chooses a bad input at each seed length and
security gives a uniform `1/12` gap threshold directly; this is the quantified
threshold form of the paper's infinite-bad-length contradiction. Published
`verifier_toNUPPT`, probability and uniform-prefix identities identify the advantage.
Below the threshold, both width and test use true coins; above it they use generated
coins. Thus the acceptance margins are `7/12` and `5/12`, and the strict-majority
reader identifies the language. There is no finite table. Logarithm/rpow limits and
one finite-exception constant give the time comparison, followed by the published
DTIME monotonicity and constant-factor transports.

## Source files, scope, and sketch edits

| File | Base lines | Final lines | Maximum width |
|---|---:|---:|---:|
| `TCSlib/Complexity/ClassP/DTIME.lean` | 117 | 135 | 90 |
| `TCSlib/Complexity/Randomized/Build/IterateFind.lean` | 556 | 801 | 99 |
| `TCSlib/Complexity/Randomized/Classes.lean` | 1403 | 1415 | 97 |
| `TCSlib/Complexity/Randomized/SeedMajority.lean` | 234 | 261 | 98 |
| `TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean` | 0 | 127 | 87 |
| `TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean` | 0 | 63 | 86 |
| `TCSlib/Complexity/Randomized/SeedMajority/State.lean` | 0 | 233 | 95 |
| `TCSlib/Complexity/Randomized/SeedMajority/Words.lean` | 0 | 172 | 92 |
| `TCSlib/Cryptography/Randomness/Derandomization.lean` | 97 | 127 | 99 |
| `TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean` | 0 | 139 | 85 |
| `TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean` | 0 | 95 | 87 |
| `TCSlib/Cryptography/Randomness/Derandomization/Expanded.lean` | 0 | 70 | 84 |
| `TCSlib/Cryptography/Randomness/Derandomization/Majority.lean` | 0 | 159 | 93 |
| `TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean` | 0 | 173 | 90 |
| `TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean` | 0 | 142 | 87 |

Every changed/new Lean line has Python `len` at most 100. Every file has at most
1000 lines except `Classes.lean`, whose inherited 1403→1415 length was specifically
approved with SR-01. E1 stays at 801 lines. No new `@[simp]` attribute is added and
imports are precise. The source audit verifies each file's SHA256 against the final
commit. Four host helpers and six consumer helpers are inserted before consumers
in the final order; the original 377-module relative order is preserved, without
cycles. No parent facade or other frozen provider is edited.

The two owned module titles/Main results/Contents and target Status/sketch paragraphs
describe the delivered proofs. The helper docstrings give their formulas and source
tags; every proof of at least 15 nonblank proof lines has a proof sketch. The explicit
`advance` formula was clarified in the final comment-only commit. All 93 original
declaration headers, whole definitions, declaration order, and frozen proofs in the
five affected existing files are preserved byte for byte; the one-character header
control reports exactly one difference. This includes leaving the original
`polyTimeComputable_find` and `final_bound` unchanged.

## New declarations and final signatures

There are 54 source declarations (53 public, one private). The complete kernel-type
signatures are listed below; section variables are included by the elaborated
universal quantifiers. `source-audit/signatures.json` also records the actual kernel
name of the private lemma. Generated auxiliary constants are included in the separate
321-constant census, rather than mistaken for additional source declarations.

E1's source signature, in full, is:

```lean
theorem computesFunInTime_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    {init : List Bool → List Bool} (hinit : PolyTimeComputable init)
    (R : ℕ → ℕ) (P : PolyExpr)
    (hbound : ∀ x : List Bool, (init x).length ≤ P.eval x.length)
    (F : FinTM Bool) (aF dF : ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length))
      (fun n => aF * (n + 1) ^ dF)) :
    ∃ (M : FinTM Bool) (c A D : ℕ),
      M.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x (init x))))) with
          | some i => out (pairSndD ((step g P x)^[i] (pairEncode x (init x))))
          | none => [])
        (fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2))
```

This is one public generic-fuel addition. It accepts arbitrary numerical `R` via a
fuel machine for `Nat.bits (R |x|)` and gives
`c*(A*(2*n+2+P.eval n+5)^D+1)*(R n+2)`. It reuses the private helpers in place,
retains the total guard/invariant, and uses an arbitrary FP initializer so that the
host can carry `x`. It never applies `final_bound` to exponential fuel. E2 and E3
use the issued signatures without binder-style changes; SR-01 is the only additional
approved shared-file declaration.

```lean
-- TCSlib/Complexity/Randomized/Build/IterateFind.lean:575
Complexity.IterateFind.computesFunInTime_find :
∀ {g : List Bool → List Bool},
  Complexity.PolyTimeComputable g →
    ∀ {acc : List Bool → Bool},
      (Complexity.PolyTimeComputable fun s => [acc s]) →
        ∀ {out : List Bool → List Bool},
          Complexity.PolyTimeComputable out →
            ∀ {init : List Bool → List Bool},
              Complexity.PolyTimeComputable init →
                ∀ (R : ℕ → ℕ) (P : Complexity.PolyExpr),
                  (∀ (x : List Bool), (init x).length ≤ P.eval x.length) →
                    ∀ (F : Turing.FinTM Bool) (aF dF : ℕ),
                      (F.ComputesFunInTime (fun x => (R x.length).bits) fun n => aF * (n + 1) ^ dF) →
                        ∃ M c A D,
                          M.ComputesFunInTime
                            (fun x =>
                              match
                                List.find?
                                  (fun i =>
                                    acc
                                      (Complexity.pairSndD
                                        ((Complexity.IterateFind.step g P x)^[i] (Turing.pairEncode x (init x)))))
                                  (List.range (R x.length + 1)) with
                              | some i =>
                                out
                                  (Complexity.pairSndD
                                    ((Complexity.IterateFind.step g P x)^[i] (Turing.pairEncode x (init x))))
                              | none => [])
                            fun n => c * (A * (2 * n + 2 + P.eval n + 5) ^ D + 1) * (R n + 2)
```
```lean
-- TCSlib/Complexity/ClassP/DTIME.lean:83
Turing.FinTM.decidesInTime_iff :
∀ (M : Turing.FinTM Bool) (L : Language Bool) (T : ℕ → ℕ),
  M.DecidesInTime L T ↔ ∀ (x : List Bool), M.ComputesInTime x [Turing.MultiTapeTM.indicator L x] (T x.length)
```
```lean
-- TCSlib/Complexity/ClassP/DTIME.lean:105
Complexity.mem_DTIME_iff :
∀ {T : ℕ → ℕ} {L : Language Bool}, L ∈ Complexity.DTIME T ↔ ∃ c M, M.DecidesInTime L fun n => c * T n
```
```lean
-- TCSlib/Complexity/Randomized/Classes.lean:299
Randomized.inBPP_iff :
∀ (E : Randomized.VerifierModel) (L : Language Bool),
  Randomized.InBPP E L ↔
    ∃ M a k,
      E.Eff (Randomized.boolVerifier M) ∧
        ∀ (x : List Bool),
          (x ∈ L → 2 / 3 ≤ Randomized.randProb (Randomized.polyLen a k x.length) fun r => M x r = true) ∧
            (x ∉ L → 2 / 3 ≤ Randomized.randProb (Randomized.polyLen a k x.length) fun r => M x r = false)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean:54
Complexity.SeedMajority.exists_countingTM :
∀ {V : Language Bool},
  V ∈ Complexity.P →
    ∀ (w : ℕ → ℕ),
      (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
        ∃ M c e,
          M.ComputesFunInTime
            (fun x => [decide (2 ^ w x.length < 2 * {u | Turing.pairEncode x (List.ofFn u) ∈ V}.card)]) fun n =>
            c * (2 ^ w n * (n + 1) ^ e)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean:43
Complexity.SeedMajority.envelope_of_computesInTime :
∀ {M : Turing.FinTM Bool} {x y : List Bool} {t : ℕ},
  M.ComputesInTime x y t →
    ∀ (v : ℕ) (j : Fin M.k), |(Turing.MultiTapeTM.runFrom (Turing.MultiTapeTM.initCfg x) v).workTapePos j| ≤ ↑t
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:51
Complexity.SeedMajority.seedFor :
(ℕ → ℕ) → List Bool → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:57
Complexity.SeedMajority.seedFor_eq :
∀ (w : ℕ → ℕ) (z : List Bool),
  Complexity.SeedMajority.seedFor w z =
    List.take (w (Complexity.pairFstD z).length)
      (Complexity.pairFstD (Complexity.pairSndD z) ++ (2 ^ w (Complexity.pairFstD z).length).bits)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:64
Complexity.SeedMajority.seedFor_state :
∀ (w : ℕ → ℕ) (x : List Bool) (i a : ℕ),
  Complexity.SeedMajority.seedFor w (Complexity.SeedMajority.state x i a) = Complexity.SeedMajority.word (w x.length) i
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:71
Complexity.SeedMajority.polyTimeComputable_seedFuel :
∀ {w : ℕ → ℕ},
  (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
    Complexity.PolyTimeComputable fun x => (2 ^ w x.length).bits
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:84
Complexity.SeedMajority.polyTimeComputable_seedFor :
∀ {w : ℕ → ℕ},
  (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
    Complexity.PolyTimeComputable (Complexity.SeedMajority.seedFor w)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:100
Complexity.SeedMajority.advance :
Language Bool → (ℕ → ℕ) → List Bool → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:110
Complexity.SeedMajority.advance_eq :
∀ (V : Language Bool) (w : ℕ → ℕ) (z : List Bool),
  Complexity.SeedMajority.advance V w z =
    Turing.pairEncode (Complexity.pairFstD z)
      (Turing.pairEncode
        (Complexity.BinArith.add (Turing.pairEncode (Complexity.pairFstD (Complexity.pairSndD z)) (Nat.bits 1)))
        (Complexity.BinArith.add
          (Turing.pairEncode (Complexity.pairSndD (Complexity.pairSndD z))
            (if
                Turing.MultiTapeTM.indicator V
                    (Turing.pairEncode (Complexity.pairFstD z) (Complexity.SeedMajority.seedFor w z)) =
                  true then
              Nat.bits 1
            else Nat.bits 0))))
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:125
Complexity.SeedMajority.polyTimeComputable_advance :
∀ {V : Language Bool},
  V ∈ Complexity.P →
    ∀ {w : ℕ → ℕ},
      (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
        Complexity.PolyTimeComputable (Complexity.SeedMajority.advance V w)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:143
Complexity.SeedMajority.advance_state :
∀ (V : Language Bool) (w : ℕ → ℕ) (x : List Bool) (i a : ℕ),
  Complexity.SeedMajority.advance V w (Complexity.SeedMajority.state x i a) =
    Complexity.SeedMajority.state x (i + 1)
      (a + if Turing.pairEncode x (Complexity.SeedMajority.word (w x.length) i) ∈ V then 1 else 0)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:156
Complexity.SeedMajority.finished :
(ℕ → ℕ) → List Bool → Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:161
Complexity.SeedMajority.finished_eq :
∀ (w : ℕ → ℕ) (z : List Bool),
  Complexity.SeedMajority.finished w z =
    Complexity.BinArith.beq
      (Turing.pairEncode (Complexity.pairFstD (Complexity.pairSndD z)) (2 ^ w (Complexity.pairFstD z).length).bits)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:167
Complexity.SeedMajority.polyTimeComputable_finished :
∀ {w : ℕ → ℕ},
  (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
    Complexity.PolyTimeComputable fun z => [Complexity.SeedMajority.finished w z]
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:176
Complexity.SeedMajority.finished_state :
∀ (w : ℕ → ℕ) (x : List Bool) (i a : ℕ),
  Complexity.SeedMajority.finished w (Complexity.SeedMajority.state x i a) = decide (i = 2 ^ w x.length)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:184
Complexity.SeedMajority.payload :
(ℕ → ℕ) → List Bool → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:190
Complexity.SeedMajority.payload_eq :
∀ (w : ℕ → ℕ) (z : List Bool),
  Complexity.SeedMajority.payload w z =
    [Complexity.BinArith.lt
        (Turing.pairEncode (2 ^ w (Complexity.pairFstD z).length).bits
          (Complexity.BinArith.add
            (Turing.pairEncode (Complexity.pairSndD (Complexity.pairSndD z))
              (Complexity.pairSndD (Complexity.pairSndD z)))))]
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:196
Complexity.SeedMajority.polyTimeComputable_payload :
∀ {w : ℕ → ℕ},
  (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) →
    Complexity.PolyTimeComputable (Complexity.SeedMajority.payload w)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:207
Complexity.SeedMajority.payload_state :
∀ (w : ℕ → ℕ) (x : List Bool) (i a : ℕ),
  Complexity.SeedMajority.payload w (Complexity.SeedMajority.state x i a) = [decide (2 ^ w x.length < 2 * a)]
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:213
Complexity.SeedMajority.polyTimeComputable_initial :
Complexity.PolyTimeComputable fun x => Complexity.SeedMajority.state x 0 0
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/State.lean:221
Complexity.SeedMajority.length_state_le :
∀ (x : List Bool) (m i a : ℕ),
  i ≤ 2 ^ m → a ≤ i → (Complexity.SeedMajority.state x i a).length ≤ 2 * x.length + 3 * m + 7
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:46
Complexity.SeedMajority.word :
ℕ → ℕ → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:50
Complexity.SeedMajority.word_eq :
∀ (m i : ℕ), Complexity.SeedMajority.word m i = List.take m (i.bits ++ (2 ^ m).bits)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:54
Complexity.SeedMajority.length_word :
∀ (m i : ℕ), (Complexity.SeedMajority.word m i).length = m
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:67
Complexity.SeedMajority.word_eq_ofFn :
∀ (m i : ℕ) (hi : i < 2 ^ m), Complexity.SeedMajority.word m i = List.ofFn ((Randomized.bitsEquiv m).symm ⟨i, hi⟩)
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:89
Complexity.SeedMajority.count :
Language Bool → List Bool → ℕ → ℕ → ℕ
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:95
Complexity.SeedMajority.count_eq :
∀ (V : Language Bool) (x : List Bool) (m i : ℕ),
  Complexity.SeedMajority.count V x m i =
    {j ∈ Finset.range i | Turing.pairEncode x (Complexity.SeedMajority.word m j) ∈ V}.card
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:100
Complexity.SeedMajority.count_zero :
∀ (V : Language Bool) (x : List Bool) (m : ℕ), Complexity.SeedMajority.count V x m 0 = 0
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:106
Complexity.SeedMajority.count_le :
∀ (V : Language Bool) (x : List Bool) (m i : ℕ), Complexity.SeedMajority.count V x m i ≤ i
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:117
Complexity.SeedMajority.count_succ :
∀ (V : Language Bool) (x : List Bool) (m i : ℕ),
  Complexity.SeedMajority.count V x m (i + 1) =
    Complexity.SeedMajority.count V x m i + if Turing.pairEncode x (Complexity.SeedMajority.word m i) ∈ V then 1 else 0
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:136
Complexity.SeedMajority.count_all :
∀ (V : Language Bool) (x : List Bool) (m : ℕ),
  Complexity.SeedMajority.count V x m (2 ^ m) = {u | Turing.pairEncode x (List.ofFn u) ∈ V}.card
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:164
Complexity.SeedMajority.state :
List Bool → ℕ → ℕ → List Bool
```
```lean
-- TCSlib/Complexity/Randomized/SeedMajority/Words.lean:169
Complexity.SeedMajority.state_eq :
∀ (x : List Bool) (i a : ℕ), Complexity.SeedMajority.state x i a = Turing.pairEncode x (Turing.pairEncode i.bits a.bits)
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean:46
TCSlib.Cryptography.Randomness.Derand.eff_mapCoins :
∀ {M : List Bool → List Bool → Bool},
  Randomized.polyTimeModel.Eff (Randomized.boolVerifier M) →
    ∀ {C : List Bool → List Bool},
      Complexity.PolyTimeComputable C →
        Randomized.polyTimeModel.Eff (Randomized.boolVerifier fun x r => M x (C (Turing.pairEncode x r)))
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean:80
TCSlib.Cryptography.Randomness.Derand.exists_verifier_gap_bound :
∀ {M : List Bool → List Bool → Bool},
  Randomized.polyTimeModel.Eff (Randomized.boolVerifier M) →
    ∀ (w : ℕ → ℕ) (p : Complexity.PolyExpr),
      (∀ (n : ℕ), n ≤ p.eval (w n)) →
        ∀ (G : TCSlib.Cryptography.PRG),
          G.Secure →
            ∃ S,
              ∀ (x : List Bool),
                S ≤ w x.length →
                  |(TCSlib.Cryptography.uprob fun r => M x (List.ofFn (G.G (w x.length) r)) = true) -
                        TCSlib.Cryptography.uprob fun r => M x (List.ofFn r) = true| ≤
                    1 / 12
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean:50
TCSlib.Cryptography.Randomness.Derand.exists_coin_gap_threshold :
(∃ G, G.Secure) →
  ∀ {M : List Bool → List Bool → Bool},
    Randomized.polyTimeModel.Eff (Randomized.boolVerifier M) →
      ∀ (a k d : ℕ),
        0 < d →
          ∃ F n₀,
            Complexity.PolyTimeComputable F ∧
              ∀ (x : List Bool),
                n₀ ≤ x.length →
                  |↑(Randomized.randProb (TCSlib.Cryptography.Randomness.Derand.ceilRoot d x.length) fun u =>
                            M x (List.take (Randomized.polyLen a k x.length) (F u)) = true) -
                        ↑(Randomized.randProb (Randomized.polyLen a k x.length) fun r => M x r = true)| ≤
                    1 / 12
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/Expanded.lean:47
TCSlib.Cryptography.Randomness.Derand.exists_secure_cover :
(∃ G, G.Secure) →
  ∀ (a k d : ℕ),
    0 < d →
      ∃ G F,
        G.Secure ∧
          Complexity.PolyTimeComputable F ∧
            (∀ (n : ℕ) (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G.G n s)) ∧
              ∀ (n : ℕ), Randomized.polyLen a k n ≤ G.stretch.eval (TCSlib.Cryptography.Randomness.Derand.ceilRoot d n)
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/Majority.lean:39 (private)
TCSlib.Cryptography.Randomness.Derand.short_poly :
∀ {f : List Bool → List Bool},
  Complexity.PolyTimeComputable f → ∀ (N : ℕ), Complexity.PolyTimeComputable fun z => [decide ((f z).length < N)]
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/Majority.lean:63
TCSlib.Cryptography.Randomness.Derand.exists_seed_majority :
(∃ G, G.Secure) →
  ∀ {L : Language Bool},
    Randomized.InBPP Randomized.polyTimeModel L →
      ∀ (d : ℕ),
        0 < d →
          ∃ V w n₀,
            V ∈ Complexity.P ∧
              (Complexity.PolyTimeComputable fun x => List.replicate (w x.length) true) ∧
                (∀ (n : ℕ), n₀ ≤ n → w n = TCSlib.Cryptography.Randomness.Derand.ceilRoot d n) ∧
                  L = {x | 2 ^ w x.length < 2 * {u | Turing.pairEncode x (List.ofFn u) ∈ V}.card}
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:44
TCSlib.Cryptography.Randomness.Derand.ceilRoot :
ℕ → ℕ → ℕ
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:48
TCSlib.Cryptography.Randomness.Derand.ceilRoot_eq :
∀ (d n : ℕ), TCSlib.Cryptography.Randomness.Derand.ceilRoot d n = if n = 0 then 0 else d.nthRoot (n - 1) + 1
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:53
TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_iff :
∀ {d : ℕ}, 0 < d → ∀ (n t : ℕ), TCSlib.Cryptography.Randomness.Derand.ceilRoot d n ≤ t ↔ n ≤ t ^ d
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:65
TCSlib.Cryptography.Randomness.Derand.le_ceilRoot_pow :
∀ {d : ℕ}, 0 < d → ∀ (n : ℕ), n ≤ TCSlib.Cryptography.Randomness.Derand.ceilRoot d n ^ d
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:69
TCSlib.Cryptography.Randomness.Derand.ceilRoot_zero :
∀ (d : ℕ), TCSlib.Cryptography.Randomness.Derand.ceilRoot d 0 = 0
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:75
TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_nat :
∀ {d : ℕ}, 0 < d → ∀ (n : ℕ), TCSlib.Cryptography.Randomness.Derand.ceilRoot d n ≤ n
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:86
TCSlib.Cryptography.Randomness.Derand.lt_ceilRoot_iff :
∀ {d : ℕ}, 0 < d → ∀ (n t : ℕ), t < TCSlib.Cryptography.Randomness.Derand.ceilRoot d n ↔ t ^ d < n
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:98
TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_real :
∀ {d : ℕ}, 0 < d → ∀ (n : ℕ), ↑(TCSlib.Cryptography.Randomness.Derand.ceilRoot d n) ≤ ↑n ^ (1 / ↑d) + 1
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:128
TCSlib.Cryptography.Randomness.Derand.polyTimeComputable_ceilRoot :
∀ {d : ℕ},
  0 < d →
    Complexity.PolyTimeComputable fun x =>
      List.replicate (TCSlib.Cryptography.Randomness.Derand.ceilRoot d x.length) true
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean:40
TCSlib.Cryptography.Randomness.Derand.exists_root_degree :
∀ {ε : ℝ}, 0 < ε → ∃ d, 2 ≤ d ∧ 1 / ↑d < ε ∧ 1 / ↑d < 1
```
```lean
-- TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean:64
TCSlib.Cryptography.Randomness.Derand.seed_time_le_subexp :
∀ {d : ℕ},
  0 < d →
    ∀ {ε : ℝ},
      0 < ε →
        1 / ↑d < ε →
          ∀ (w : ℕ → ℕ) (n₀ : ℕ),
            (∀ (n : ℕ), n₀ ≤ n → w n = TCSlib.Cryptography.Randomness.Derand.ceilRoot d n) →
              ∀ (e : ℕ), ∃ C, ∀ (n : ℕ), 2 ^ w n * (n + 1) ^ e ≤ C * ⌈2 ^ ↑n ^ ε⌉₊
```

## Overlap and reuse

All 54 additions are disclosed below, including technical specializations and the
private lemma. Unless marked “new”, TCSlib path/line references are at the issue base;
Mathlib references are at the pinned revision. New own-definition references are at
the final tip. No private foreign lemma is silently copied.

| New declaration | Nearest relative | Relation and reuse decision |
|---|---|---|
| `Complexity.IterateFind.computesFunInTime_find` | `TCSlib/Complexity/Randomized/Build/IterateFind.lean:331` | Generalizes polyTimeComputable_find to binary numerical fuel and an arbitrary initializer. The brief requires this assembly repetition in place; all private helpers and the old theorem/final_bound are retained unchanged. |
| `Turing.FinTM.decidesInTime_iff` | `TCSlib/Complexity/ClassP/DTIME.lean:75` | Required home-file reader of DecidesInTime by Iff.rfl (E3); no existing reader has this contract. |
| `Complexity.mem_DTIME_iff` | `TCSlib/Complexity/ClassP/DTIME.lean:88` | Required home-file reader of DTIME by Iff.rfl (E2); no existing reader has this contract. |
| `Randomized.inBPP_iff` | `TCSlib/Complexity/Randomized/Classes.lean:288` | SR-01 approved home-file reader of InBPP by Iff.rfl; no existing reader exposed these witnesses. |
| `Complexity.SeedMajority.exists_countingTM` | `TCSlib/Complexity/ClassNP/EXP.lean:2419; TCSlib/Complexity/Randomized/Build/IterateFind.lean:575 (new E1)` | The existential projection decider accepts some witness and does not count acceptances or give this linear-in-2^w bound. The new host instead reuses E1. H16 is unary-counter driven and would require exponential unary fuel; it is not copied. |
| `Complexity.SeedMajority.envelope_of_computesInTime` | `TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:244; TCSlib/Complexity/TuringMachine/Finite.lean:471` | Generalizes the envelope argument to a native initial configuration with only a completed computation. Clean.envelope requires a clean seam contract, absent for the composite machine. Reuses the public interval/run readers; promotion to Finite.lean is requested. |
| `Complexity.SeedMajority.seedFor` | `TCSlib/Complexity/ClassNP/PolyTimePrefix.lean:46` | Specializes the total prefix operation to a raw counting state and its unary width; reuses the existing prefix machine. |
| `Complexity.SeedMajority.seedFor_eq` | `TCSlib/Complexity/Randomized/SeedMajority/State.lean:51 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.seedFor_state` | `TCSlib/Complexity/TuringMachine/Encoding.lean:325` | Representation-specific bridge from the raw-state seed to word; all projections use published pair readers. |
| `Complexity.SeedMajority.polyTimeComputable_seedFuel` | `TCSlib/Complexity/ClassP/BinaryArith/Unary.lean:43` | Composition of polyTimeComputable_powerOfTwo with the FP unary width; no exponential unary fuel or competing evaluator is introduced. |
| `Complexity.SeedMajority.polyTimeComputable_seedFor` | `TCSlib/Complexity/ClassNP/PolyTimePrefix.lean:355` | Reuses polyTimeComputable_takePrefixByLength, pairing, and the published binary-fuel composition for the new state. |
| `Complexity.SeedMajority.advance` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:147` | Counting-state-specific round using the published binary adder and P indicator. No arithmetic implementation or private loop lemma is copied. |
| `Complexity.SeedMajority.advance_eq` | `TCSlib/Complexity/Randomized/SeedMajority/State.lean:100 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.polyTimeComputable_advance` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:162` | Composes published FP addition, indicator, branching, pairing, and seedFor; the input is an arbitrary raw word. |
| `Complexity.SeedMajority.advance_state` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:147` | Specializes add_pairEncode and the indicator reader to the new state representation. |
| `Complexity.SeedMajority.finished` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:206` | Terminal-rank comparison expressed using the existing binary equality test. |
| `Complexity.SeedMajority.finished_eq` | `TCSlib/Complexity/Randomized/SeedMajority/State.lean:156 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.polyTimeComputable_finished` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:227` | Reuses the existing FP equality comparator and binary fuel on projected state words. |
| `Complexity.SeedMajority.finished_state` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:206` | Specializes the equality comparator reader to the terminal rank; no new equality algorithm. |
| `Complexity.SeedMajority.payload` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:198` | Strict-majority bit using existing addition and strict comparison; ties reject. |
| `Complexity.SeedMajority.payload_eq` | `TCSlib/Complexity/Randomized/SeedMajority/State.lean:184 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.polyTimeComputable_payload` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:211` | Reuses FP strict comparison and addition; only the counting-state wiring is new. |
| `Complexity.SeedMajority.payload_state` | `TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean:198` | Representation-specific interpretation of the existing strict comparator and doubled binary count. |
| `Complexity.SeedMajority.polyTimeComputable_initial` | `TCSlib/Complexity/ClassNP/PolyTimePairing.lean:71; TCSlib/Complexity/ClassNP/PolyTimePairing.lean:129` | Pairs the input with two constant zero words using existing FP closure. |
| `Complexity.SeedMajority.length_state_le` | `TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean:123` | Applies the public binary-width bound to both counters, including rank 2^m, then the pairing-length reader. The result is specific to the new state layout. |
| `Complexity.SeedMajority.word` | `TCSlib/Complexity/TuringMachine/Encoding.lean:325` | Uses the published binary power-of-two padding. This names the fixed-width rank word; it does not define another binary encoding engine. |
| `Complexity.SeedMajority.word_eq` | `TCSlib/Complexity/Randomized/SeedMajority/Words.lean:46 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.length_word` | `TCSlib/Complexity/TuringMachine/Encoding.lean:325` | Specializes binary padding and Mathlib List.length_take to the new rank word; both published operations are reused. |
| `Complexity.SeedMajority.word_eq_ofFn` | `TCSlib/Complexity/Randomized/RandomBits.lean:228; TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:300` | Reuses bitsEquiv_apply and eq_bits_append_replicate. The new glue identifies the padded word with the inverse of the existing bijection; no bijection is re-proved. |
| `Complexity.SeedMajority.count` | `TCSlib/Complexity/Randomized/SeedMajority.lean:147` | Defines the finite prefix of accepted ranks needed by the machine. The existing majority reader counts all tuples, not rank prefixes. |
| `Complexity.SeedMajority.count_eq` | `TCSlib/Complexity/Randomized/SeedMajority/Words.lean:89 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `Complexity.SeedMajority.count_zero` | `Mathlib/Data/Finset/Card.lean:163` | Specializes the empty range/filter cardinality to the new prefix count through its reader. |
| `Complexity.SeedMajority.count_le` | `Mathlib/Data/Finset/Card.lean:62; Mathlib/Data/Finset/Card.lean:163` | Direct application of card_le_card and card_range to the new count. |
| `Complexity.SeedMajority.count_succ` | `Mathlib/Data/Finset/Card.lean:100` | Specializes card_insert_of_notMem after range_add_one/filter_insert; this is the machine-count recurrence, not a new cardinality identity. |
| `Complexity.SeedMajority.count_all` | `Mathlib/Data/Finset/Card.lean:337; TCSlib/Complexity/Randomized/RandomBits.lean:224` | Applies card_bij using the existing bitsEquiv. The language predicate is preserved by word_eq_ofFn; no separate rank bijection is constructed. |
| `Complexity.SeedMajority.state` | `TCSlib/Complexity/ClassNP/PolyTimePairing.lean:129` | Retained-input binary rank/count representation built from the published pairing; existing clean-host stateWord is a tape layout, not this payload. |
| `Complexity.SeedMajority.state_eq` | `TCSlib/Complexity/Randomized/SeedMajority/Words.lean:164 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `TCSlib.Cryptography.Randomness.Derand.eff_mapCoins` | `TCSlib/Complexity/Randomized/PolyTimeModel.lean:86; TCSlib/Complexity/ClassNP/PClosure.lean:69` | Generic verifier-level wrapper around the existing efficiency reader and P-preimage closure. No identical published coin-map wrapper was found; promotion to PolyTimeModel.lean is requested. |
| `TCSlib.Cryptography.Randomness.Derand.exists_verifier_gap_bound` | `TCSlib/Cryptography/Randomness/BPPBridge.lean:80; TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Defs.lean:186` | New non-uniform bad-advice threshold argument. Reuses verifier_toNUPPT, secure_iff, negligible_iff, prgAdv/acceptance readers and uprob_fst. No advantage/expectation or uniform-projection identity is re-proved. |
| `TCSlib.Cryptography.Randomness.Derand.exists_coin_gap_threshold` | `TCSlib/Cryptography/Randomness/BPPBridge.lean:113; TCSlib/Complexity/Randomized/Classes.lean:238` | Reuses randProb_eq_uprob and randProb_take to identify the generic gap. The new content is the root/input threshold and generator envelope. |
| `TCSlib.Cryptography.Randomness.Derand.exists_secure_cover` | `TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean:209; TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean:397` | Specializes the existing secure one-bit truncation/expansion to the syntactic envelope and extracts its existing evaluator. |
| `TCSlib.Cryptography.Randomness.Derand.short_poly` | `TCSlib/Complexity/Randomized/Build/StateLoop.lean:79` | Private specialization of lenLe_comp to |f z|+1≤N. No length-comparison machine is copied. A generic threshold-wrapper promotion beside StateLoop.lenLe_comp is requested. |
| `TCSlib.Cryptography.Randomness.Derand.exists_seed_majority` | `TCSlib/Complexity/Randomized/SeedMajority.lean:147; TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean:179` | Reuses the majority-probability reader. Existing blockMajorityTest handles polynomially many blocks, not this full seed-space majority with piecewise PRG/true coins. No block-majority engine is copied. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | A ceiling root from the existing floor root of n-1; no root algorithm is copied. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_eq` | `TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:44 (new definition)` | Required home-file equation reader for this new definition, proved by rfl; no pre-existing reader can refer to the new symbol. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_iff` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Transports nthRoot_lt_iff to the new ceiling convention, with zero handled separately. |
| `TCSlib.Cryptography.Randomness.Derand.le_ceilRoot_pow` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Immediate least-root specialization through ceilRoot_le_iff, not a separate root construction. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_zero` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Zero-case equation of the new ceiling schedule, through its own reader. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_nat` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Least-root specialization using n≤n^d. The schedule is ceiling, unlike the floor-root provider. |
| `TCSlib.Cryptography.Randomness.Derand.lt_ceilRoot_iff` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:129` | Strict-order dual of the new least-root reader; no new arithmetic algorithm. |
| `TCSlib.Cryptography.Randomness.Derand.ceilRoot_le_real` | `Mathlib/Analysis/SpecialFunctions/Pow/NthRootLemmas.lean:57; Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:562` | Reuses pow_nthRoot_le and the real inverse-power comparison, then adds the ceiling increment. |
| `TCSlib.Cryptography.Randomness.Derand.polyTimeComputable_ceilRoot` | `TCSlib/Cryptography/Asymptotic/UniversalPadding/BinaryRoot.lean:171; TCSlib/Complexity/Randomized/Repetition.lean:241` | The existing evaluator returns a shifted binary floor root; this needs an exact unary ceiling root of input length. Reuses the published stateFind search and unary fixed-power/length comparisons, with no binary-root implementation copied. |
| `TCSlib.Cryptography.Randomness.Derand.exists_root_degree` | `Mathlib/Algebra/Order/Archimedean/Basic.lean:175` | Specializes exists_nat_gt to reciprocal exponent bounds, including ε≥1. |
| `TCSlib.Cryptography.Randomness.Derand.seed_time_le_subexp` | `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:323; TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean:279` | Uses existing logarithm/rpow limits and the existing DTIME constant-factor transport later in the consumer. The new inequality combines the ceiling-root time and finite exceptions; no new general asymptotic or DTIME transport theorem is re-proved. |

E1's generalized assembly is deliberate repetition explicitly required by the brief.
Its own-file private `Inv`, `inv_*`, `verdictWord`, `stepWord`, and `outWord` are reused
in place. The existing theorem is not re-derived or modified. The machine assembly
uses proved `exists_loopFindTM`/`loopHost_contracts` and the published clean-module
host interfaces; it does not consume admitted loop-host or timed-conditional specs.
The existential projection engine does not count witnesses with the required time
bound, the unary H16 counter is unsuitable as exponential unary fuel, and polynomial
block-majority tests do not supply this full seed-space host. No competing loop or
binary-arithmetic engine is introduced.

Searches used `rg`/`rg --files` across TCSlib and pinned Mathlib before each cluster.
The complete raw search records and probe sources are retained. The searched shapes
include `exists_proj_decider`, `enumMachine_contracts`, H16/counter loops,
`polyTimeComputable_find`, `Clean.envelope`, `Nat.bits`, `Nat.testBit`, `bitsEquiv`,
`finFunctionFinEquiv`, `eq_bits_append_replicate`, binary arithmetic, `Nat.sqrt`,
`Nat.nthRoot`, unary/stateFind searches, and EXP/BPP inclusions. Before the probability
argument, searches included `prfAdv_eq_expect`, `prgAdv_*`, `uexp_*`, `uprob_*`,
`uprob_comp_equiv`, `uprob_comp_eq_sum_map`, `uprob_eq_one_div_card`,
`HardcoreBit.pushesUniform_restrict`, `randProb_eq`, `randProb_eq_uprob`, and
`abs_uexp_sub_le_uprob`. The implementation reuses published probability/expectation
and uniform-prefix identities; it introduces no replacement identity of those kinds.

## Scope requests

### SR-01: specifically approved

Exact session request and answer:

```text
User reply received in this Codex chat, 2026-11-15 PST:

Question:
Approve SR-01: add only `Randomized.inBPP_iff` beside `InBPP` in `TCSlib/Complexity/Randomized/Classes.lean`, proved by `Iff.rfl`? It exposes the existing verifier, coin-schedule, efficiency, and 2/3 correctness witnesses without changing any definition or existing statement. The concrete patch is `/private/tmp/derand-worker/scope-inbpp-reader.patch`. The brief’s Scope rule requires your approval for this fourth shared-file addition; it also needs an exception for Classes.lean’s inherited length above 1000 lines. The three pre-approved additions and checkpoint-1 work continue while this is pending.

Answer:
Approve SR-01 and the inherited file-size exception
```

The reader is beside `InBPP`, proved by `Iff.rfl`, with a formula docstring and no
attribute. It changes no definition or existing statement. The exact diff/search
record is under `evidence/worker/scope-request/SR-01/`.

### Standing exception instruction

```text
User instruction received in this Codex chat, 2026-11-15 PST, verbatim:

I am going to be asleep and away from the keyboard. Use your best judgment when it comes to exceptions, and disclose them completely and transparently in your checkpoints and delivery. You are free to message other workers to coordinate access to shared Mac resources (and the cap of 3 Lean processes) as you see fit.

Worker interpretation:
Narrowly necessary exceptions may be decided without a further keyboard approval,
with exact changes, reasons, and validation disclosed in checkpoints and delivery.
The frozen target statements, shared three-Lean-process cap, own-tree isolation,
delivery-path restriction, and no-force-push rule remain in force.
SR-01 already has separate explicit approval; no additional exception is made here.
```

### SR-02: proposal not applied; specific human answer pending

```text
# Scope request SR-02: typed views of the two bundled constructors

Status: proposed, NOT applied. Automatic approval review rejected application.

The new generic-fuel harvest elaborates and has only the standard axioms, but
the full closure seals add nine diagnostics in its new proof. Eight arise from
the hidden tape/state fields of `ModuleHost.hostTM` and `IterateFind.copyTM`;
one needs an explicit local-budget simplification. The untouched original
`polyTimeComputable_find` independently has eleven baseline diagnostics. No
existing proof or definition is changed to hide any of those findings.

Prototype 3 validates the solution with both constructors still sealed. Prototypes
1 and 2 demonstrate why whole-machine equalities and raw run equalities alone
do not repair the dependent carrier types. Every source and raw log is retained.

## Exact proposed addition

`typed-views.patch` adds 84 lines to
`TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean` (672 → 756):

* `Turing.ModuleHost.hostTMView`, a reducible abbreviation whose explicit fields
  are `k := K`, `State := State C M`, and the original host's underlying machine;
* `hostTMView_eq` and `hostTMView_q₀`;
* `hostTMView_step_inl`, `host_call_view`, and `host_clean_view`, proved directly
  from the existing public contracts in the same file.

It adds 22 lines to
`TCSlib/Complexity/Randomized/Build/IterateFindHost.lean` (362 → 384):

* `Complexity.IterateFind.copyTMView`, with explicit one-tape, `Fin 2` fields;
* `copyTMView_eq` and `copy_clean_view`, reusing the existing copier contract.

Every existing declaration, definition, proof, and attribute remains byte-for-byte
unchanged. There is no transition-table copy, time-bound change, new admission,
or `simp` attribute. Both proposed files remain below 1000 lines and width 100.
The risk is expansion of the frozen shared-provider/rebuild scope; the purpose
is to remove implicit type-field reads in E1 while preserving all operational
seals. Header, clash, full-source seal, axiom, lint, and replay evidence would
cover both providers if approved.

## Authorization and automatic review

Seyoon delegated judgment over exceptions while away (see
`standing-discretion.txt`). The worker interpreted this as allowing these narrowly
necessary reader additions and attempted to apply/check them. Automatic approval
review rejected the action because it requires a specific scope approval for
these two provider files. No provider mutation occurred. The exact rejection is
in `automatic-review-rejection.txt`. Specific SR-02 approval is now requested;
independent final-consumer work continues in the meantime.

Answer: PENDING.
```

Automatic review rejected applying/checking the provider patch. Exact recorded reason:

```text
Automatic approval review rejected applying/checking the typed provider views.
No command or provider mutation ran.

Verbatim reason:
This would modify two additional frozen provider files beyond the three pre-approved additions, but the brief requires a specific scope request to Seyoon for any such change and none authorizes these typed-view readers.
Do not bypass this rejection through a workaround or indirect execution. Continue with a safer alternative, or carry out checks to prove that the action is authorized or low risk before trying again. Complete unaffected work without asking for confirmation. Report anything that remains blocked, clarify why it was blocked by auto-review, inform the user of the risk and ask for approval.
```

No mutation of either provider was made. The proposed patch and prototype source
remain historical evidence, not part of `src/` or the patch series. There is no
claim that standing discretion overruled this automatic rejection.

### EX-01: execution arrangement

The standing instruction was used to run independent baseline/verification and
proof worktrees with separate single-writer TCSlib olean trees. The proof worktree
links the verification worktree's job-owned packages read-only by convention and
runs no Lake. No dependency tree or TCSlib olean was copied. An initial evidence
symlink was replaced by physical evidence after a root-containment probe failure;
that failure is retained. This is an exception to the single-checkout environment
arrangement, not a mathematical-scope change. The complete decision and exact paths
are in `evidence/worker/scope-request/EX-01.md`; resource details are below.

### EX-02: remaining Rule 10 finding

The worker used standing discretion to deliver the completed mathematics with
the uncleared E1 Rule 10 finding, while leaving both further frozen providers
untouched. Eight initial new diagnostics involve opaque tape/state carriers;
the ninth is a computation-transport mismatch with matching printed types. The
explicit per-input reader transport does not clear them. A supplementary probe
excluding two constructors still has five E1 diagnostics, so it is not clearance.
The exact exception, limits and review implication are in
`evidence/worker/scope-request/EX-02.md` and the full seal accounting below.

These are the complete exceptions used. E1/E2/E3 were pre-approved by the issue;
SR-01 and its inherited-size exception were expressly approved. No other frozen-file
change was taken. EX-02 is a transparent exception disposition under the standing
instruction and remains a maintainer review HOLD, not specific approval of SR-02.

## Promotion and reader requests

* Promote `SeedMajority.envelope_of_computesInTime` to the native finite-machine
  layer (`TuringMachine/Finite.lean`): `Clean.envelope` requires a clean seam
  contract, while this generic result only needs a completed native computation.
* Promote `Derand.eff_mapCoins` beside the `polyTimeModel` efficiency readers: it is
  a generic coin-map/P-preimage wrapper, not specific to PRG derandomization.
* Promote a generic length-threshold wrapper beside `StateLoop.lenLe_comp`; the
  local private `short_poly` merely specializes that public machine.
* SR-02 is the proposed typed-view/interface route for the remaining E1 issue.
  It requires specific scope approval and subsequent proof/seal work before use.
* The ceiling-root order lemmas could be proposed to the pinned Mathlib root layer
  at integration. No package source was edited.

These are requests for maintainer integration, not extra changes in this payload.

## Native replay, axioms, headers, and edge cases

| Check | Result |
|---|---|
| Both issued SHA256SUMS (`shasum -a 256 -c`) | PASS |
| Exact-base full issued order | 377/377; zero errors; 26 sorry declarations/12 modules |
| Checkpoint-1 full issued order | 377/377; zero errors; 25/12, exactly the corollary removed |
| Final order with ten helpers | 387/387; zero errors; 23/10, exactly all three targets removed |
| Final source provenance | every one of 387 recorded source hashes equals `5e12a169e671dc16b6766e21067b79c16835af67` |
| All stored constants of changed/new files, plus old-find consumer | 321; standard axioms only |
| Old `polyTimeComputable_find` and `polyTimeComputable_iterateFind` axiom sets | identical at base and final |
| Kernel sorry-dependency paths from all three targets | absent |
| Frozen header/body/order/proof audit | 93 original declarations; zero differences |
| One-character header negative control | exactly one difference |
| Name-clash scan over 1274 base Lean files | 54 additions; zero collisions |
| Explicit foreign-definition selector scan | base 0, final 0, added 0 |
| Public docs and long-proof sketches | 54 additions; zero issues |
| Source scope/width/size | PASS with specifically approved Classes inherited-size exception |

The final replay began at `904123d3780cc1f5daf4f37ad49d90395595c1a9` and advanced to
`5e12a169e671dc16b6766e21067b79c16835af67` before `State.lean` was visited. The only transition was that file's explicit
formula in a docstring; non-comment source tokens are identical. The advance record
and source diff are retained. The final validator independently compares **every**
recorded source hash, including modules checked before the advance, to the final tip.
It is therefore an exact-final-source replay, without pretending the checkout stayed
at one hash from its first step.

The edge probe checks zero width/coins and zero root, rejects zero time coefficient,
and verifies the zero-prefix probability behavior. The main proofs handle ties by
strict comparison, all small lengths and `n=0` through the piecewise true-coin branch,
seed lengths shared by many input lengths through the advice length bound `|x_s|≤s^d`,
and `ε≥1` through the same positive degree choice with reciprocal below `min(ε,1)`.
The generator envelope holds at every length, including zero. The finite-exception
constant is positive since it starts with 1. The enumeration includes terminal rank
`R`; its prefix count bounds include the terminal value and zero-width seed space.

## Whole-file Rule 10 evidence

All seals use the actual full TCSlib import closure, resolved Lean Names (including
private declarations), with installation/EOF checks and raw request catalogs. A
excludes `PolyExpr.eval` as notation and B seals it. Strict seals projection coercions;
canonical coe treats projection coercions as notation. Reducible abbreviations remain
notation in both. The canonical summary verifies its generated sources against the
exact final source before selecting results from development phases.

| File | Base (each variant) | Final A strict | A coe | B strict | B coe | Status |
|---|---:|---:|---:|---:|---:|---|
| `TCSlib/Complexity/ClassP/DTIME.lean` | 0 | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/Classes.lean` | 0 | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/Build/IterateFind.lean` | 11 | 20 | 20 | 20 | 20 | HOLD EX-02 |
| `TCSlib/Complexity/Randomized/SeedMajority.lean` | 0 | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization.lean` | 0 | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/SeedMajority/Words.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/SeedMajority/State.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Complexity/Randomized/SeedMajority/Envelope.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/Expanded.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/CoinGap.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/Majority.lean` | new file | 0 | 0 | 0 | 0 | PASS |
| `TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean` | new file | 0 | 0 | 0 | 0 | PASS |

The only failing declarations in every harvest variant are the unchanged
`polyTimeComputable_find` (11 diagnostics at final lines 362×2, 380, 382, 389, 390,
433, 434, 539, 555, 556) and E1 `computesFunInTime_find` (9 at 602×2, 622, 624,
631, 632, 676, 677, 799). These are source line numbers, with raw probe line maps
delivered separately. There is no strict/coe or A/B diagnostic-count difference to
attribute. Base seals cover the five pre-existing edited files; helpers have no base.

All four paired controls pass unsealed; each sealed negative fails exactly once,
while its reader-based positive remains valid. Diagnostic counting recognizes both
`error:` and `error(...)`. Failed early harness prototypes remain in the evidence and
are not treated as valid seals. The non-canonical carrier probes reduce 20 diagnostics
to 12, with five E1 diagnostics remaining; they neither isolate every dependency nor
clear Rule 10. The explicit-unfold scan passing does not erase implicit reductions.

## Lint line-set comparison

The prescribed `python3 -I scripts/campaign_style_lint.py ... --check8b` commands ran
at the exact base and final. Their nonzero exit codes reflect inherited FAILs.

| Corpus | Base FAIL/WARN | Final FAIL/WARN | Added FAIL lines |
|---|---:|---:|---:|
| Cryptography | 92/101 | 92/101 | 0 |
| Complexity | 25/391 | 25/390 | 0 |

The diff compares diagnostic line sets, not just totals. E3 removes the DTIME
`DecidesInTime` missing-reader warning. In Classes, the size warning changes
1403→1415 under the approved inherited-size exception, and the missing-reader list
changes from `InBPP, InBPPStrong, InCoRP` to `InBPPStrong, InCoRP` because SR-01
supplies the reader. These two changed WARN lines are the only added WARN lines;
three old WARN lines disappear. All full lint logs and line-set records are included.

## Host resources and coordination

The cap was **at most three Lean processes total on this Mac**, shared with other
jobs. Every Lean, Lake, and `scripts/lean_check_tree.sh` command used the unchanged
issued `lean-slot.sh`, `LEAN_SLOT_TAG=derand`, and default `~/.lean-slots`. Every cache
command acquired `-k 3`. No `lake build` or unfiltered cache get ran. Each check-tree
call checked one module; each olean tree had one writer. Python used `python3 -I`.

The Mac has 12 CPUs and 19,327,352,832 physical memory bytes (18 GiB). Initial
headroom was `(4182+276651+28714+9187)*16384 = 5,222,137,856` bytes, 4.863495 GiB;
initial disk free was 231,367,417,856 bytes, 215.477699 GiB. The final replay preflight
recorded 7.389206 GiB headroom and 186.241554 GiB disk free. The delivery artifact
preflight recorded 6.491745 GiB and 182.661835 GiB. All passed the 4/12 GiB floors.
`sysctl`, `vm_stat`, `memory_pressure -Q`, `df -k`, `mount`, and explicit computations
are delivered. All working/scratch paths are APFS, with no RAM disk. No Lean
137/139 or jetsam shortage occurred. Long modules and wrapper waits were normal;
there were no self-imposed module timeouts.

The physical package tree is job-owned in the verification worktree. The proof
worktree links that same job's tree read-only by convention and runs no Lake;
it has its own independent TCSlib olean tree. No package/dependency tree or TCSlib
olean was copied from another worker. The shared host toolchain is
`~/.elan/toolchains/leanprover--lean4---v4.25.0`; the permitted archive store is
`~/.cache/mathlib`. It already contained **32,667 files, 1,595,387,830 bytes** before
this session's cache work. Their individual origin is unknown; they are not described
as session downloads. The narrowed 129-root cache command downloaded zero archives
and decompressed 3,082. The one extra `NthRootLemmas` root downloaded zero and
decompressed 1,933. Additional exact imports were already cached. Pin checks report
`PACKAGE PINS PASS: 11 present; 4 absent; 0 mismatches`. The four absent packages are
documentation-only `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, and `MD4Lean`, not imported
by this order. There are no zero-byte package oleans; Mathlib-import probes pass.

Only derand slot-log lines are copied to `logs/slots.log`. Resource coordination
messages were authorized by Seyoon. At peer requests, only validated derand Python
dispatchers paused to let current native children finish and provide acquisition
gaps. No native Lean or other worker process was signaled. The precise 12-second
gap and 40-second dispatcher pause, release/acquire times and finally-block resumes
are recorded in `resource-coordination.md`, `courtesy-gap.jsonl`, and
`cache-window.jsonl`. No mathematical work was shared or delegated.

## Evidence index and completeness

`evidence/verification/` contains the complete verification-worktree evidence;
`evidence/worker/` contains the complete proof-worktree evidence. Their README maps
the original absolute paths. Both include raw logs, successful and failed probes,
source archives, tool versions, catalogs, manifests, request records and controls.
The scratch snapshot preserves all top-level scratch files and the complete rejected
SR-02 prototype; its provenance inventory distinguishes historical proposals from
the accepted source. No running log was moved; packaging happened after check writers
finished. No package tree, toolchain, or compiled TCSlib olean is delivered.

| Evidence | Location under `evidence/` |
|---|---|
| Issued packs, sums, wrapper | `verification/inputs/issued/` |
| Baseline/CP1/final replay, timestamps and max RSS | `verification/logs/base-bootstrap/`, `checkpoint1-full/`, `final-full/` |
| Final replay order and source advance | `verification/logs/final-order.txt`, `final-source-advance.json` |
| Final validation and post-check controller | `verification/logs/final-validation.json`, `post-replay.log`, `post-replay-*.log` |
| Final all-constant axiom and path probes/logs | `verification/axioms/final/`, `verification/logs/final-replay-axioms/`, `final-replay-paths/` |
| Canonical final seal selection and all failures | `worker/seals/summary/`, `worker/seals/<phase>/` |
| Baseline seal logs | `verification/seals/base/` |
| Paired controls | `worker/controls/`, `worker/seals/controls/`, `worker/logs/controls-unsealed/` |
| Frozen headers, output, one-character control | `verification/headers/final-replay/` |
| Clash/lint results | `verification/clash/`, `verification/lint/` |
| Full-closure explicit-unfold scan (3,928 catalog entries) | `worker/unfold/`, `worker/logs/explicit-unfold-exact-final.log` |
| Source widths, lines, SHA256 and signatures | `worker/source-audit/`, `worker/logs/source-audit-final.log` |
| Overlap and doc audit | `worker/overlap/`, `worker/docs/` |
| Scope decisions and automatic-review rejection | `worker/scope-request/` |
| Historical scratch inputs and prototypes | `worker/scratch/` |
| Development tools and delivery generators | `worker/tools/`, `worker/generators/`, `verification/tools/` |
| Exact commit reproduction | `reproduction/replay.log`, `reproduction/metadata.json` |

`evidence/SHA256SUMS` names every evidence file except itself. The top-level
`SHA256SUMS` names every payload file except itself, including the evidence manifest.
Hash verification and exact path-set checks run before each push; the delivery Git
index is checked against that same physical set. Nothing named in a manifest is
omitted. Invalid/failed research attempts are retained transparently, not substituted
for the final accepted checks. The final ZIP has `derand/` at its root. Every ZIP entry is compared by SHA256
to this payload and checked by ZIP CRC before the final push.

## Commit reproduction and delivery

The complete format-patch series starts at the exact issue base. `COMMITS.tsv` gives
author, email, author date, committer, email, committer date, and signing for every
commit. All source commits use the configured identity
`Seyoon Ragavan <complexzetaprime@gmail.com>` with `commit.gpgsign=false`.

| Source commit | Signing |
|---|---|
| `776dabdabb276c75b98780e5018275fbcdc25e3a` | `none` |
| `0c7862af4943c075a9db31ad5e6ac79665c39c49` | `none` |
| `904123d3780cc1f5daf4f37ad49d90395595c1a9` | `none` |
| `5e12a169e671dc16b6766e21067b79c16835af67` | `none` |

Applying every patch to a separate scratch clone at `01de2d8baed9113e4a099e13c5d50c81e6dbc66f`, with the recorded
committer identity/dates and signing disabled, reproduced **every commit hash** and
ended at `5e12a169e671dc16b6766e21067b79c16835af67`. This is checked afresh for this payload before pushing; the raw
commands, expected/actual hashes and metadata are delivered under `reproduction/`.

Earlier delivery records:

* checkpoint 1: `d90a03638e06f560f02ddce1f5aeba1bfba0e25c`; ordinary push to exchange/pass-shelat-ch5-8 succeeded
* checkpoint 2: `aa23fc19cdba95238e822d963660f315030452aa`; ordinary push to exchange/pass-shelat-ch5-8 succeeded

The worker uses its own `codex/delivery-derand` exchange worktree and stages only
`inbox/fills/derand/`. Each delivery commit uses `commit.gpgsign=false`, pulls with
rebase from `exchange/pass-shelat-ch5-8`, rechecks hashes/exact tracked file sets,
and pushes normally to that branch. No force push or other inbox edit is used.
The delivery commit cannot include its own hash in its payload; the chat records it
after the push. Maintainer review and Seyoon's PR approval remain the landing process.
The maintainer also rebuilds full-library downstream modules outside this issued
order and `audits/pass-shelat/Checks`, as the brief specifies.
