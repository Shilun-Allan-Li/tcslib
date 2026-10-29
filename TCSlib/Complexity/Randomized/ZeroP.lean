/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.ZeroPRun
import TCSlib.Complexity.Randomized.Fingerprint
import TCSlib.Complexity.Randomized.Primality

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `ZEROP ∈ coRP`

The class half of [AB09, §7.2.3, p.130]: the fingerprinting test for `ZEROP`
(`Randomized.zeropVerifier`, analysed in `TCSlib.Complexity.Randomized.Fingerprint`) runs in
polynomial time, so `ZEROP ∈ coRP`, hence `ZEROP ∈ BPP`, in the certificate form over
`Randomized.polyTimeModel` and in the PTM form of [AB09, Def 7.2/7.6]. The test on words cuts
the coins into the point and the moduli and evaluates the circuit modulo each modulus with
`Randomized.PIT.evalModW` (`TCSlib.Complexity.Randomized.ZeroPRun`).

## Main definitions

* `Randomized.PIT.pipe` — cut the coins into the point and the moduli, and compare the values
  of two codes modulo every modulus.
* `Randomized.PIT.zeropW` — `Randomized.zeropVerifier` on `⟨x, r⟩`, on words.

## Main results

* `Randomized.PIT.pipe_eq`, `Randomized.PIT.zeroTest_eq`, `Randomized.PIT.zeropW_pairEncode`.
* `Randomized.eff_zeropVerifier` — the ZEROP test is polynomial-time.
* `Randomized.inCoRP_ZEROP_polyTime`, `Randomized.inBPP_ZEROP_polyTime`,
  `Randomized.ZEROP_mem_coRP_PTM`, `Randomized.ZEROP_mem_BPP_PTM` — [AB09, §7.2.3].

## Divergences

* None beyond those of `TCSlib.Complexity.Randomized.Fingerprint` (the test's parameters);
  this file only shows that test is polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

namespace PIT

open Complexity Turing BinArith AlgCircuit
open Complexity.LogProg (bitsVal bitsVal_bits)

/-! ### Cutting the coins into blocks -/

/-- One round of the point loop on `⟨1^b, ⟨u, P⟩⟩`: move the first `b` bits of `u` to the end
of the list `P`. -/
def ptStep (d : List Bool) : List Bool :=
  pairEncode (pairFstD d)
    (pairEncode (dropPrefixByLen (pairEncode (pairFstD d) (pairFstD (pairSndD d))))
      (pairSndD (pairSndD d) ++
        pairEncode (takePrefixByLen (pairEncode (pairFstD d) (pairFstD (pairSndD d)))) []))

/-- The rounds of the point loop. -/
theorem iterate_ptStep (b : ℕ) (u : List Bool) (P : List (List Bool)) (i : ℕ) :
    ptStep^[i] (pairEncode (List.replicate b true) (pairEncode u (encWords P))) =
      pairEncode (List.replicate b true) (pairEncode (u.drop (i * b))
        (encWords (P ++ (List.range i).map (fun j => (u.drop (j * b)).take b)))) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [ptStep, pairFstD_pairEncode, pairSndD_pairEncode, dropPrefixByLen,
      takePrefixByLen, List.length_replicate, List.drop_drop, List.range_succ, List.map_append,
      List.map_singleton, ← List.append_assoc, encWords_append_singleton]
    rw [Nat.succ_mul]

/-- The point loop is polynomial-time. -/
theorem polyTimeComputable_ptLoop : PolyTimeComputable (forLoop ptStep) := by
  have hb : PolyTimeComputable (fun d => pairEncode (pairFstD d) (pairFstD (pairSndD d))) :=
    polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot2
  have hstep : PolyTimeComputable ptStep :=
    polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_dropPrefixByLen.comp hb).pairEncode
      (polyTimeComputable_slot3.append
        ((polyTimeComputable_takePrefixByLen.comp hb).pairEncode (polyTimeComputable_const []))))
  refine polyTimeComputable_forLoop hstep (6 + 1) 2 (forLoop_bound_of_ctx 6 (fun d => by
    simp [ptStep]) (fun d => ?_))
  have h1 := length_pair_components_le d
  have h2 := length_pair_components_le (pairSndD d)
  have ht := List.length_take_le (pairFstD d).length (pairFstD (pairSndD d))
  simp only [ptStep, length_pairEncode, List.length_append, dropPrefixByLen, takePrefixByLen,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_drop, List.length_nil]
  omega

/-! ### The trials -/

/-- The trial context `Q = ⟨1^L, ⟨1^n, ⟨G₁, ⟨G₂, P⟩⟩⟩⟩`: block length, inputs, two codes, point. -/
def qL (Q : List Bool) : List Bool := pairFstD Q

/-- The number of inputs. -/
def qN (Q : List Bool) : List Bool := pairFstD (pairSndD Q)

/-- The first code. -/
def qG₁ (Q : List Bool) : List Bool := pairFstD (pairSndD (pairSndD Q))

/-- The second code. -/
def qG₂ (Q : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD Q)))

/-- The point. -/
def qP (Q : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (pairSndD Q)))

/-- One trial with modulus `R + 1`: do the two codes have the same value mod `R + 1`? -/
def trialTest (Q R : List Bool) : Bool :=
  BinArith.beq (pairEncode (evalModW (pairEncode (pairEncode (qN Q) (pairEncode R (qP Q))) (qG₁ Q)))
    (evalModW (pairEncode (pairEncode (qN Q) (pairEncode R (qP Q))) (qG₂ Q))))

/-- One round of the trial loop on `⟨Q, ⟨s, [acc]⟩⟩`: test the next block of `s`, `AND` into
`acc`. -/
def trStep (d : List Bool) : List Bool :=
  pairEncode (pairFstD d)
    (pairEncode (dropPrefixByLen (pairEncode (qL (pairFstD d)) (pairFstD (pairSndD d))))
      [(pairSndD (pairSndD d)).headD false &&
        trialTest (pairFstD d)
          (takePrefixByLen (pairEncode (qL (pairFstD d)) (pairFstD (pairSndD d))))])

/-- The rounds of the trial loop. -/
theorem iterate_trStep (Q s : List Bool) (b : Bool) (i : ℕ) :
    trStep^[i] (pairEncode Q (pairEncode s [b])) =
      pairEncode Q (pairEncode (s.drop (i * (qL Q).length))
        [b && (List.range i).all (fun j => trialTest Q
          ((s.drop (j * (qL Q).length)).take (qL Q).length))]) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [trStep, pairFstD_pairEncode, pairSndD_pairEncode, dropPrefixByLen,
      takePrefixByLen, List.drop_drop, List.range_succ, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, List.headD_cons, Bool.and_assoc]
    rw [Nat.succ_mul]

/-- The test of a trial is polynomial-time.

**Proof sketch.** The fields of the trial context are projections; evaluating both circuits
at the point modulo the trial's modulus (`polyTimeComputable_evalModW`) and comparing the two
residues (`polyTimeComputable_beq`) compose by `polyTimeComputable_app`. -/
theorem polyTimeComputable_trialTest :
    PolyTimeComputable (fun z => [trialTest (pairFstD z) (pairSndD z)]) := by
  have hN : PolyTimeComputable (fun z => qN (pairFstD z)) :=
    polyTimeComputable_app polyTimeComputable_slot2 polyTimeComputable_pairFstD
  have hP : PolyTimeComputable (fun z => qP (pairFstD z)) :=
    polyTimeComputable_app (show PolyTimeComputable qP from
      polyTimeComputable_pairSndD.comp polyTimeComputable_slot4) polyTimeComputable_pairFstD
  have hG₁ : PolyTimeComputable (fun z => qG₁ (pairFstD z)) :=
    polyTimeComputable_app (show PolyTimeComputable qG₁ from
      polyTimeComputable_pairFstD.comp polyTimeComputable_slot3) polyTimeComputable_pairFstD
  have hG₂ : PolyTimeComputable (fun z => qG₂ (pairFstD z)) :=
    polyTimeComputable_app (show PolyTimeComputable qG₂ from
      polyTimeComputable_pairFstD.comp polyTimeComputable_slot4) polyTimeComputable_pairFstD
  have hctx : PolyTimeComputable (fun z => pairEncode (qN (pairFstD z))
      (pairEncode (pairSndD z) (qP (pairFstD z)))) :=
    hN.pairEncode (polyTimeComputable_pairSndD.pairEncode hP)
  have h1 : PolyTimeComputable (fun z => evalModW (pairEncode (pairEncode (qN (pairFstD z))
      (pairEncode (pairSndD z) (qP (pairFstD z)))) (qG₁ (pairFstD z)))) :=
    polyTimeComputable_app polyTimeComputable_evalModW (hctx.pairEncode hG₁)
  have h2 : PolyTimeComputable (fun z => evalModW (pairEncode (pairEncode (qN (pairFstD z))
      (pairEncode (pairSndD z) (qP (pairFstD z)))) (qG₂ (pairFstD z)))) :=
    polyTimeComputable_app polyTimeComputable_evalModW (hctx.pairEncode hG₂)
  have h : (fun z => [trialTest (pairFstD z) (pairSndD z)]) = (fun z => [BinArith.beq
      (pairEncode (evalModW (pairEncode (pairEncode (qN (pairFstD z))
        (pairEncode (pairSndD z) (qP (pairFstD z)))) (qG₁ (pairFstD z))))
        (evalModW (pairEncode (pairEncode (qN (pairFstD z))
          (pairEncode (pairSndD z) (qP (pairFstD z)))) (qG₂ (pairFstD z)))))]) := by
    funext z; simp only [trialTest]
  rw [h]
  exact polyTimeComputable_test_app polyTimeComputable_beq (h1.pairEncode h2)

/-- The trial loop is polynomial-time.

**Proof sketch.** The round keeps its context and moves the next block of coins from the
coin field into the trial test (`takePrefixByLen`, `dropPrefixByLen`), conjoining the result
into a one-bit accumulator; it grows the state by at most `5(|context| + 1)` bits, so
`polyTimeComputable_forLoop` with `forLoop_bound_of_ctx` applies. -/
theorem polyTimeComputable_trLoop : PolyTimeComputable (forLoop trStep) := by
  have hb : PolyTimeComputable (fun d => pairEncode (qL (pairFstD d)) (pairFstD (pairSndD d))) :=
    (polyTimeComputable_app polyTimeComputable_pairFstD polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_slot2
  have ht : PolyTimeComputable (fun d => [trialTest (pairFstD d)
      (takePrefixByLen (pairEncode (qL (pairFstD d)) (pairFstD (pairSndD d))))]) := by
    have := polyTimeComputable_test_app polyTimeComputable_trialTest
      (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_app
        polyTimeComputable_takePrefixByLen hb))
    simpa only [pairFstD_pairEncode, pairSndD_pairEncode] using this
  have hacc : PolyTimeComputable (fun d => [(pairSndD (pairSndD d)).headD false]) :=
    polyTimeComputable_test_app polyTimeComputable_headD polyTimeComputable_slot3
  have hstep : PolyTimeComputable trStep := by
    have := polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_app
      polyTimeComputable_dropPrefixByLen hb).pairEncode (polyTimeComputable_and hacc ht))
    have h : trStep = fun d => pairEncode (pairFstD d)
        (pairEncode (dropPrefixByLen (pairEncode (qL (pairFstD d)) (pairFstD (pairSndD d))))
          [(pairSndD (pairSndD d)).headD false && trialTest (pairFstD d)
            (takePrefixByLen (pairEncode (qL (pairFstD d)) (pairFstD (pairSndD d))))]) := by
      funext d; simp only [trStep]
    rw [h]
    exact this
  refine polyTimeComputable_forLoop hstep (5 + 1) 2 (forLoop_bound_of_ctx 5 (fun d => by
    simp [trStep]) (fun d => ?_))
  have h1 := length_pair_components_le d
  have h2 := length_pair_components_le (pairSndD d)
  simp only [trStep, length_pairEncode, dropPrefixByLen, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_drop, List.length_cons, List.length_nil]
  omega

/-! ### The pipeline -/

/-- The packed input `⟨1^n, ⟨1^m, ⟨G₁, ⟨G₂, r⟩⟩⟩⟩`: inputs. -/
def pN (z : List Bool) : List Bool := pairFstD z

/-- The circuit size `m`, in unary. -/
def pI (z : List Bool) : List Bool := pairFstD (pairSndD z)

/-- The first code. -/
def pG₁ (z : List Bool) : List Bool := pairFstD (pairSndD (pairSndD z))

/-- The second code. -/
def pG₂ (z : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD z)))

/-- The coins. -/
def pR (z : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (pairSndD z)))

/-- `M = m + 12`, in unary. -/
def pM (z : List Bool) : List Bool := pI z ++ List.replicate 12 true

/-- The point loop on the coins: blocks of `m + 4` bits, one per input. -/
def pPts (z : List Bool) : List Bool :=
  forLoop ptStep (pairEncode (pN z) (pairEncode (pI z ++ List.replicate 4 true)
    (pairEncode (pR z) [])))

/-- **The test on words**: with `M = m + 12`, cut `n` blocks of `m + 4` coins into the point
`a` (`aᵢ = 1 + block`), then for `8M` blocks of `2M` coins compare the values of `G₁` and `G₂`
modulo `k = 1 + block`; accept iff they always agree.  [AB09, §7.2.3, p.130] -/
def pipe (z : List Bool) : Bool :=
  (pairSndD (pairSndD (pairSndD (forLoop trStep (pairEncode
    (pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z)
    (pairEncode (pairEncode (pM z ++ pM z) (pairEncode (pN z) (pairEncode (pG₁ z)
        (pairEncode (pG₂ z) (pairSndD (pairSndD (pairSndD (pPts z))))))))
      (pairEncode (pairFstD (pairSndD (pairSndD (pPts z)))) [true]))))))).headD false

/-- The pipeline is polynomial-time.

**Proof sketch.** The pipeline is the point loop (`polyTimeComputable_ptLoop`) followed by
the trial loop (`polyTimeComputable_trLoop`) on a state assembled by pairing, projections and
concatenation of polynomial-time pieces, then the accumulator bit; each step composes by
`polyTimeComputable_app`. -/
theorem polyTimeComputable_pipe : PolyTimeComputable (fun z => [pipe z]) := by
  have hN : PolyTimeComputable pN := polyTimeComputable_pairFstD
  have hI : PolyTimeComputable pI := polyTimeComputable_slot2
  have hG₁ : PolyTimeComputable pG₁ := polyTimeComputable_pairFstD.comp polyTimeComputable_slot3
  have hG₂ : PolyTimeComputable pG₂ := polyTimeComputable_pairFstD.comp polyTimeComputable_slot4
  have hR : PolyTimeComputable pR := polyTimeComputable_pairSndD.comp polyTimeComputable_slot4
  have hM : PolyTimeComputable pM := hI.append (polyTimeComputable_const (List.replicate 12 true))
  have hP : PolyTimeComputable pPts := by
    have := polyTimeComputable_app polyTimeComputable_ptLoop (hN.pairEncode
      ((hI.append (polyTimeComputable_const (List.replicate 4 true))).pairEncode
        (hR.pairEncode (polyTimeComputable_const []))))
    have h : pPts = fun z => forLoop ptStep (pairEncode (pN z) (pairEncode
        (pI z ++ List.replicate 4 true) (pairEncode (pR z) []))) := by
      funext z; simp only [pPts]
    rw [h]
    exact this
  have h8 : PolyTimeComputable
      (fun z => pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z) :=
    ((((((hM.append hM).append hM).append hM).append hM).append hM).append hM).append hM
  have hPs : PolyTimeComputable (fun z => pairSndD (pairSndD (pairSndD (pPts z)))) :=
    @polyTimeComputable_app (fun S => pairSndD (pairSndD (pairSndD S))) pPts
      polyTimeComputable_slot4 hP
  have hS : PolyTimeComputable (fun z => pairFstD (pairSndD (pairSndD (pPts z)))) :=
    @polyTimeComputable_app (fun S => pairFstD (pairSndD (pairSndD S))) pPts
      (polyTimeComputable_pairFstD.comp polyTimeComputable_slot3) hP
  have hQ : PolyTimeComputable (fun z => pairEncode (pM z ++ pM z) (pairEncode (pN z)
      (pairEncode (pG₁ z) (pairEncode (pG₂ z) (pairSndD (pairSndD (pairSndD (pPts z)))))))) :=
    (hM.append hM).pairEncode (hN.pairEncode (hG₁.pairEncode (hG₂.pairEncode hPs)))
  have hs : PolyTimeComputable (fun z => pairEncode (pairFstD (pairSndD (pairSndD (pPts z))))
      [true]) := hS.pairEncode (polyTimeComputable_const [true])
  have hL := @polyTimeComputable_app (forLoop trStep) _ polyTimeComputable_trLoop
    (h8.pairEncode (hQ.pairEncode hs))
  have h := @polyTimeComputable_test_app (fun w => w.headD false) _ polyTimeComputable_headD
    (@polyTimeComputable_app (fun S => pairSndD (pairSndD (pairSndD S))) _
      polyTimeComputable_slot4 hL)
  have he : (fun z => [pipe z]) = (fun z => [(pairSndD (pairSndD (pairSndD (forLoop trStep
      (pairEncode (pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z)
        (pairEncode (pairEncode (pM z ++ pM z) (pairEncode (pN z) (pairEncode (pG₁ z)
          (pairEncode (pG₂ z) (pairSndD (pairSndD (pairSndD (pPts z))))))))
          (pairEncode (pairFstD (pairSndD (pairSndD (pPts z)))) [true]))))))).headD false]) := by
    funext z; simp only [pipe]
  rw [he]
  exact h

/-- The point: `n` blocks of `m + 4` coins. -/
def pts (n m : ℕ) (r : List Bool) : List (List Bool) :=
  (List.range n).map (fun i => (r.drop (i * (m + 4))).take (m + 4))

/-- The `j`-th modulus block: `2(m + 12)` coins after the point. -/
def rawj (n m : ℕ) (r : List Bool) (j : ℕ) : List Bool :=
  ((r.drop (n * (m + 4))).drop (j * (2 * (m + 12)))).take (2 * (m + 12))

/-- **The pipeline computes the test**: on `⟨1^n, ⟨1^m, ⟨G₁, ⟨G₂, r⟩⟩⟩⟩` it accepts iff for each
of the `8(m+12)` moduli the two codes have the same value.

**Proof sketch.** The point loop runs `n` rounds and leaves the point `pts n m r` and the coins
`r.drop (n(m+4))` (`iterate_ptStep`); the trial loop runs `8(m+12)` rounds of `2(m+12)` coins
and leaves the conjunction of the trials (`iterate_trStep`); a trial compares the two values
with `beq`. -/
theorem pipe_eq (n m : ℕ) (G₁ G₂ r : List Bool) :
    pipe (pairEncode (List.replicate n true) (pairEncode (List.replicate m true)
      (pairEncode G₁ (pairEncode G₂ r)))) =
      decide (∀ j < 8 * (m + 12),
        bitsVal (evalModW (pairEncode (ctxOf n (rawj n m r j) (pts n m r)) G₁)) =
          bitsVal (evalModW (pairEncode (ctxOf n (rawj n m r j) (pts n m r)) G₂))) := by
  set z := pairEncode (List.replicate n true) (pairEncode (List.replicate m true)
      (pairEncode G₁ (pairEncode G₂ r))) with hz
  have e1 : pN z = List.replicate n true := by simp [pN, z]
  have e2 : pI z = List.replicate m true := by simp [pI, z]
  have e3 : pG₁ z = G₁ := by simp [pG₁, z]
  have e4 : pG₂ z = G₂ := by simp [pG₂, z]
  have e5 : pR z = r := by simp [pR, z]
  have eM : pM z = List.replicate (m + 12) true := by simp [pM, e2, List.replicate_add]
  have e8 : pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z ++ pM z =
      List.replicate (8 * (m + 12)) true := by
    rw [eM]; simp only [← List.replicate_add]; congr 1; ring
  have e2M : pM z ++ pM z = List.replicate (2 * (m + 12)) true := by
    rw [eM, ← List.replicate_add]; congr 1; ring
  have hpts : pPts z = pairEncode [] (pairEncode (List.replicate (m + 4) true)
      (pairEncode (r.drop (n * (m + 4))) (encWords (pts n m r)))) := by
    rw [pPts, e1, e2, e5, ← List.replicate_add,
      show (pairEncode r [] : List Bool) = pairEncode r (encWords []) from rfl,
      forLoop_pairEncode, iterate_ptStep, List.length_replicate, List.nil_append]
    rfl
  unfold pipe
  rw [e8, e2M, e1, e3, e4, hpts]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [forLoop_pairEncode, pairSndD_pairEncode, iterate_trStep]
  simp only [pairSndD_pairEncode, List.headD_cons, Bool.true_and, qL, pairFstD_pairEncode,
    List.length_replicate]
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine forall_congr' fun j => imp_congr_right fun _ => ?_
  simp only [trialTest, qN, qP, qG₁, qG₂, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.beq, decide_eq_true_eq, ctxOf, rawj]

/-! ### The fingerprint test through the pipeline -/

/-- A block read inside a prefix of the coins is the block of the whole string. -/
theorem take_drop_take {l : List Bool} {N a b : ℕ} (h : a + b ≤ N) :
    ((l.take N).drop a).take b = (l.drop a).take b := by
  rw [List.drop_take, List.take_take]
  congr 1
  omega

/-- **The ZEROP test through `pts` and `rawj`**: `D.zeroTest r` accepts iff `D(a) ≡ 0` modulo
each of the `8(m+12)` moduli read by the pipeline.

**Proof sketch.** The test reads its point and moduli from the first `testLen` coins; every
block it reads lies inside that prefix (`(i+1)(m+4) ≤ n(m+4)` and
`(j+1)·2(m+12) ≤ 8(m+12)·2(m+12)`), so it is the block of the whole string
(`take_drop_take`): the test's point is `ptVal (pts …)` and its `j`-th modulus is
`rawj … j + 1`. -/
theorem zeroTest_eq {n : ℕ} (D : AlgCircuit n) (r : List Bool) :
    D.zeroTest r = decide (∀ j < 8 * (D.size + 12), D.eval (fun i =>
      (ptVal (pts n D.size r) i : ZMod (bitsVal (rawj n D.size r j) + 1))) = 0) := by
  have hL : n * (D.size + 4) ≤ testLen n D.size := by simp [testLen, inputBits]
  have hpt : ∀ i : Fin n, D.testPoint ((r.take (testLen n D.size)).take (n * inputBits D.size)) i =
      ptVal (pts n D.size r) i := by
    intro i
    have h1 : (i : ℕ) * (D.size + 4) + (D.size + 4) ≤ n * (D.size + 4) := by
      have := Nat.mul_le_mul_right (D.size + 4) (show (i : ℕ) + 1 ≤ n from i.isLt)
      rw [Nat.succ_mul] at this
      exact this
    have hg : (pts n D.size r).getD i [] = (r.drop (i * (D.size + 4))).take (D.size + 4) := by
      simp [pts, List.getD_eq_getElem?_getD, i.isLt]
    simp only [AlgCircuit.testPoint, ptVal, blockVal, inputBits, hg]
    rw [List.take_take, take_drop_take (le_min h1 (h1.trans hL))]
  have hmod : ∀ j < 8 * (D.size + 12),
      D.testModulus ((r.take (testLen n D.size)).drop (n * inputBits D.size)) j =
        bitsVal (rawj n D.size r j) + 1 := by
    intro j hj
    have h1 : j * (2 * (D.size + 12)) + 2 * (D.size + 12) ≤
        testLen n D.size - n * (D.size + 4) := by
      have := Nat.mul_le_mul_right (2 * (D.size + 12)) (show j + 1 ≤ 8 * (D.size + 12) from hj)
      simp only [testLen, inputBits, numTrials, modParam]
      rw [Nat.succ_mul] at this
      omega
    simp only [AlgCircuit.testModulus, blockVal, rawj, inputBits, modParam]
    rw [List.drop_take, take_drop_take h1]
  unfold AlgCircuit.zeroTest AlgCircuit.ZeroTestCore
  rw [decide_eq_decide]
  constructor
  · intro h j hj
    have hj' : j < numTrials D.size := by simp only [numTrials, modParam]; exact hj
    have := h ⟨j, hj'⟩
    rw [hmod j hj] at this
    simpa only [hpt] using this
  · intro h j
    have hj : (j : ℕ) < 8 * (D.size + 12) := by
      have := j.isLt; simp only [numTrials, modParam] at this; exact this
    rw [hmod j hj]
    simpa only [hpt] using h j hj

/-- The empty code has value `0`. -/
theorem bitsVal_evalModW_nil (n : ℕ) (R : List Bool) (P : List (List Bool)) :
    bitsVal (evalModW (pairEncode (ctxOf n R P) [])) = 0 := by
  rw [evalModW, gateRun_eq (n := n)]
  simp [runVal_encState, Nat.zero_bits, bitsVal]

/-- A residue below `k` is `0` in `ZMod k` only if it is `0`. -/
theorem natCast_eq_zero_iff_of_lt {v k : ℕ} (h : v < k) : (v : ZMod k) = 0 ↔ v = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · intro hd
    exact Nat.eq_zero_of_dvd_of_lt hd h
  · rintro rfl
    exact dvd_zero k

/-- **The ZEROP verifier on words**: reject (`true`) malformed inputs, otherwise run the
pipeline on the circuit against the empty code (value `0`) and negate. -/
def zeropW (z : List Bool) : Bool :=
  !validW (pairFstD z) || !pipe (pairEncode (uHead (pairFstD z))
    (pairEncode (sI (scanRun (pairFstD z))) (pairEncode (uRest (pairFstD z))
      (pairEncode [] (pairSndD z)))))

/-- The ZEROP verifier on words is polynomial-time. -/
theorem polyTimeComputable_zeropW : PolyTimeComputable (fun z => [zeropW z]) := by
  have hv : PolyTimeComputable (fun z => [validW (pairFstD z)]) :=
    polyTimeComputable_test_app polyTimeComputable_validW polyTimeComputable_pairFstD
  have hI : PolyTimeComputable (fun z => sI (scanRun (pairFstD z))) :=
    @polyTimeComputable_app (fun x => sI (scanRun x)) pairFstD
      (@polyTimeComputable_app sI scanRun
        (polyTimeComputable_pairFstD.comp polyTimeComputable_slot3) polyTimeComputable_scanRun)
      polyTimeComputable_pairFstD
  have hpack : PolyTimeComputable (fun z => pairEncode (uHead (pairFstD z))
      (pairEncode (sI (scanRun (pairFstD z))) (pairEncode (uRest (pairFstD z))
        (pairEncode [] (pairSndD z))))) :=
    (polyTimeComputable_app polyTimeComputable_uHead polyTimeComputable_pairFstD).pairEncode
      (hI.pairEncode ((polyTimeComputable_app polyTimeComputable_uRest
        polyTimeComputable_pairFstD).pairEncode
        ((polyTimeComputable_const []).pairEncode polyTimeComputable_pairSndD)))
  have hp := polyTimeComputable_not (polyTimeComputable_test_app polyTimeComputable_pipe hpack)
  exact polyTimeComputable_or (polyTimeComputable_not hv) hp

/-- **The word-level verifier computes `zeropVerifier`.**

**Proof sketch.** If `x` is not the code of a well-formed circuit both sides are `true`
(`validW_iff`). Otherwise `x = 1ⁿ0·code(C)`, the scan counts `|C|` (`sI_scanRun`), and by
`pipe_eq` the pipeline asks, for each modulus `k`, that `C(a) mod k` equal the value `0` of the
empty code; by `evalModW_spec` this is `C(a) = 0` in `ZMod k`, which is the ZEROP test
(`zeroTest_eq`). -/
theorem zeropW_pairEncode (x r : List Bool) :
    zeropW (pairEncode x r) = zeropVerifier x r := by
  simp only [zeropW, pairFstD_pairEncode, pairSndD_pairEncode]
  by_cases hv : validW x = true
  · rw [hv, Bool.not_true, Bool.false_or]
    obtain ⟨⟨n, C⟩, hd, hw⟩ := (validW_iff x).mp hv
    have hx := encode_of_decode hd
    simp only [encode] at hx
    have hu : uHead x = List.replicate n true := by rw [← hx, uHead_encodeNat]
    have hr : uRest x = encodeGates C.gates := by rw [← hx, uRest_encodeNat]
    rw [sI_scanRun hd hw, hu, hr, pipe_eq]
    have hz : zeropVerifier x r = !(C.zeroTest r) := by
      simp only [zeropVerifier, hd]
      exact if_pos hw
    rw [hz, zeroTest_eq]
    refine congrArg (fun b => !b) ?_
    rw [decide_eq_decide]
    refine forall_congr' fun j => imp_congr_right fun _ => ?_
    rw [bitsVal_evalModW_nil]
    obtain ⟨hlt, hcast⟩ := evalModW_spec (rawj n C.size r j) (pts n C.size r) C hw
    rw [← hcast, natCast_eq_zero_iff_of_lt hlt]
  · rw [Bool.eq_false_iff.mpr hv, Bool.not_false, Bool.true_or]
    have hno : ¬ ∃ c : (n : ℕ) × AlgCircuit n, decode x = some c ∧ c.2.WellFormed :=
      fun h => hv ((validW_iff x).mpr h)
    unfold zeropVerifier
    cases hd : decode x with
    | none => rfl
    | some c =>
      have hw : ¬ c.2.WellFormed := fun hw => hno ⟨c, hd, hw⟩
      simp [hw]

end PIT

/-! ### `ZEROP ∈ coRP` -/

/-- **The ZEROP test is polynomial-time** [AB09, §7.2.3, p.130]: `zeropVerifier` is efficient
for `polyTimeModel`. -/
theorem eff_zeropVerifier : polyTimeModel.Eff (boolVerifier zeropVerifier) :=
  eff_boolVerifier_of_test PIT.polyTimeComputable_zeropW PIT.zeropW_pairEncode

/-- **`ZEROP ∈ coRP`** [AB09, §7.2.3, p.130], certificate form over polynomial-time verifiers. -/
theorem inCoRP_ZEROP_polyTime : InCoRP polyTimeModel ZEROP :=
  inCoRP_ZEROP polyTimeModel eff_zeropVerifier

/-- **`ZEROP ∈ BPP`** [AB09, §7.2.3], certificate form. -/
theorem inBPP_ZEROP_polyTime : InBPP polyTimeModel ZEROP :=
  InCoRP.inBPP_polyTime inCoRP_ZEROP_polyTime

/-- **`ZEROP ∈ coRP`**, PTM form [AB09, Def 7.6]. -/
theorem ZEROP_mem_coRP_PTM : ZEROP ∈ coRP_PTM :=
  (mem_coRP_PTM_iff _).2 inCoRP_ZEROP_polyTime

/-- **`ZEROP ∈ BPP`**, PTM form [AB09, Def 7.2]. -/
theorem ZEROP_mem_BPP_PTM : ZEROP ∈ BPP_PTM :=
  (mem_BPP_PTM_iff _).2 inBPP_ZEROP_polyTime

end Randomized
