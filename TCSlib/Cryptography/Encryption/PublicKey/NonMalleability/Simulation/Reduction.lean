/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Simulator
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The NM adversary of IND ⇒ SIM

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message), under CPA.
The NM adversary `B` runs the SIM adversary `A` on `pk`, answering `Dec` with `⊥`. On `A`'s first
challenge `a` it draws `m = M(a; ρ)` and `m̃ = M(a; ρ̃)` with its own coins (and `M`'s advice, from
its input `⟨pk, α_M⟩`), asks its own challenge on `⟨m, m̃⟩`, receives `y = Enc_pk(m_b)` and answers
`A` with `⟨y, h(m)⟩`, recording `⟨y, h(m), a⟩`. It outputs, for each of `A`'s ciphertexts `c_i`,
`c_i` followed by the pair `Enc_pk(f^{msgLen})`, `Enc_pk((¬f)^{msgLen})` for the copy flag
`f = [c_i = y]`, and then the same pair for each bit of `a`, `m = M(a; ρ)` and `σ` (one encryption
tape `re` for all of them).

It is the challenge handler (`chalHandler`) with the parameters `nmParams`. Against `NM_b`'s
oracles, its run is `A`'s run against the hybrid oracle `rImpl … b …` (`nmComp_abs`).

## Main definitions

* `NMSim.altMsg`: `m̃` read from a round input.
* `NMSim.encBit`, `NMSim.encPair`, `NMSim.encF`, `NMSim.bitF`, `NMSim.nmOutL`, `NMSim.nmFin`:
  the finalization.
* `NMSim.nmParams`, `NMSim.nmLen`: the parameters and the number of output ciphertexts.

## Main results

* `NMSim.nmFinish`, `NMSim.nmComp_abs`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rZ rW rS rI rX rL rAns finA)
open TCSlib.Cryptography.EnsembleLemmas (seedEquiv seedEquivPoly seedEquiv_ofFn seedEquivPoly_ofFn
  ofFn_padFin_eq_padL)
open TCSlib.Cryptography.Games.InteractiveHandler (rU_input rZ_input rW_input rX_input rAns_input
  rU_finInput rZ_finInput rW_finInput rS_finInput finA_finInput polyTimeComputable_rU
  polyTimeComputable_rZ polyTimeComputable_rW polyTimeComputable_rS polyTimeComputable_rX
  polyTimeComputable_rAns polyTimeComputable_finA)

variable (S : FixedLengthPKScheme) (samp : NUPPT)

/-! ### The challenge pair -/

/-- The second message `m̃ = M(a; ρ̃)` read in a round `w`: as `simMsg`, with the coins `ρ̃` after
the first `coins(n)` bits of the seed. -/
def altMsg (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
    (samp.output (NUPPT.layout (rU w) (rX w) (pairSndD (rZ w))
      (((rW w).drop (samp.coins.eval (rU w).length)).take (samp.coins.eval (rU w).length))))

/-- `altMsg S samp w = padL msgLen(n) (M.output (layout 1^n a α ρ̃))`. -/
theorem altMsg_eq (w : List Bool) :
    altMsg S samp w = EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
      (samp.output (NUPPT.layout (rU w) (rX w) (pairSndD (rZ w))
        (((rW w).drop (samp.coins.eval (rU w).length)).take
          (samp.coins.eval (rU w).length)))) := rfl

/-- The second message is polynomial-time. -/
theorem polyTimeComputable_altMsg : PolyTimeComputable (altMsg S samp) := by
  have hU := polyTimeComputable_rU
  have hZ := polyTimeComputable_rZ
  have hW := polyTimeComputable_rW
  have hQ := polyTimeComputable_rX
  have hd : PolyTimeComputable fun w => (rW w).drop (samp.coins.eval (rU w).length) :=
    ((polyTimeComputable_pairDropPoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hρ : PolyTimeComputable fun w =>
      ((rW w).drop (samp.coins.eval (rU w).length)).take (samp.coins.eval (rU w).length) :=
    ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hd)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout hU hQ (polyTimeComputable_pairSndD.comp hZ) hρ))

/-! ### The finalization -/

/-- The bit encryption `Enc_pk(x^{msgLen}; re)` on the context `⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`: `pk = fst z`
and `re` the seed after its first `2·coins(n)` bits, padded to `ctLen(n)` bits. -/
def encBit (ctx : List Bool) (x : Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (pairFstD ctx).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (pairFstD ctx)
      (pairEncode (pairFstD (pairFstD (pairSndD ctx)))
        (List.replicate (S.msgLen.eval (pairFstD ctx).length) x))) [])
      ((pairFstD (pairSndD (pairSndD ctx))).drop
        ((samp.coins.add samp.coins).eval (pairFstD ctx).length))))

/-- `encBit S samp ctx x = padL ctLen(n) (Enc.output ⟨⟨⟨1^n, ⟨pk, x^{msgLen}⟩⟩, []⟩, re⟩)`. -/
theorem encBit_eq (ctx : List Bool) (x : Bool) :
    encBit S samp ctx x = EnsembleLemmas.padL (S.ctLen.eval (pairFstD ctx).length)
      (S.enc.output (pairEncode (pairEncode (pairEncode (pairFstD ctx)
        (pairEncode (pairFstD (pairFstD (pairSndD ctx)))
          (List.replicate (S.msgLen.eval (pairFstD ctx).length) x))) [])
        ((pairFstD (pairSndD (pairSndD ctx))).drop
          ((samp.coins.add samp.coins).eval (pairFstD ctx).length)))) := rfl

/-- **The encoding of a bit** `x`: `Enc_pk(x^{msgLen}) ‖ Enc_pk((¬x)^{msgLen})`. -/
def encPair (ctx : List Bool) (x : Bool) : List Bool :=
  encBit S samp ctx x ++ encBit S samp ctx (!x)

/-- `encPair S samp ctx x = encBit ctx x ++ encBit ctx (¬x)`. -/
theorem encPair_eq (ctx : List Bool) (x : Bool) :
    encPair S samp ctx x = encBit S samp ctx x ++ encBit S samp ctx (!x) := rfl

/-- The state `s` of the context `⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`. -/
def ctxSt (ctx : List Bool) : List Bool := pairSndD (pairSndD (pairSndD ctx))

/-- `ctxSt ctx = pairSndD (pairSndD (pairSndD ctx))`. -/
theorem ctxSt_eq (ctx : List Bool) : ctxSt ctx = pairSndD (pairSndD (pairSndD ctx)) := rfl

/-- **A ciphertext with its copy flag**: `c` followed by the encoding of
`[flag ∧ c = y]`, with `s = [flag] ‖ y ‖ …` the state of the context. -/
def encF (ctx c : List Bool) : List Bool :=
  c ++ encPair S samp ctx ((ctxSt ctx).headD false &&
    decide (c = ((ctxSt ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length)))

/-- `encF S samp ctx c = c ++ encPair ctx [flag ∧ c = y]`. -/
theorem encF_eq (ctx c : List Bool) :
    encF S samp ctx c = c ++ encPair S samp ctx ((ctxSt ctx).headD false &&
      decide (c = ((ctxSt ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length))) := rfl

/-- **A bit of the view**, encoded: `bitF ctx b = encPair ctx (b.headD false)`. -/
def bitF (ctx b : List Bool) : List Bool := encPair S samp ctx (b.headD false)

/-- `bitF S samp ctx b = encPair ctx (b.headD false)`. -/
theorem bitF_eq (ctx b : List Bool) : bitF S samp ctx b = encPair S samp ctx (b.headD false) := rfl

/-- The bit encryption is polynomial-time, for a computed context and bit. -/
theorem polyTimeComputable_encBit {u : List Bool → List Bool} {x : List Bool → Bool}
    (hu : PolyTimeComputable u) (hx : PolyTimeComputable fun z => [x z]) :
    PolyTimeComputable fun z => encBit S samp (u z) (x z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable fun z => pairFstD (u z) := hF.comp hu
  have hrep : PolyTimeComputable fun z =>
      List.replicate (S.msgLen.eval (pairFstD (u z)).length) (x z) :=
    (polyTimeComputable_ite hx ((polyTimeComputable_unaryPoly S.msgLen).comp hU)
      (EnsembleLemmas.polyTimeComputable_zeros S.msgLen hU)).congr fun z => by
        cases x z <;> rfl
  have hre : PolyTimeComputable fun z => (pairFstD (pairSndD (pairSndD (u z)))).drop
      ((samp.coins.add samp.coins).eval (pairFstD (u z)).length) :=
    ((polyTimeComputable_pairDropPoly (samp.coins.add samp.coins)).comp
      (hU.pairEncode (hF.comp (hD.comp (hD.comp hu))))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
    (((hU.pairEncode ((hF.comp (hF.comp (hD.comp hu))).pairEncode hrep)).pairEncode
      (polyTimeComputable_const [])).pairEncode hre))

/-- The encoding of a bit is polynomial-time, for a computed context and bit. -/
theorem polyTimeComputable_encPair {u : List Bool → List Bool} {x : List Bool → Bool}
    (hu : PolyTimeComputable u) (hx : PolyTimeComputable fun z => [x z]) :
    PolyTimeComputable fun z => encPair S samp (u z) (x z) :=
  (polyTimeComputable_encBit S samp hu hx).append
    (polyTimeComputable_encBit S samp hu (polyTimeComputable_not hx))

/-- `encF` is polynomial-time, as a function of `⟨ctx, c⟩`. -/
theorem polyTimeComputable_encF :
    PolyTimeComputable fun z => encF S samp (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hst : PolyTimeComputable fun z => ctxSt (pairFstD z) := hD.comp (hD.comp (hD.comp hF))
  have hy : PolyTimeComputable fun z =>
      ((ctxSt (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairTakePoly S.ctLen).comp ((hF.comp hF).pairEncode
      (polyTimeComputable_tail.comp hst))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have heq : PolyTimeComputable fun z => [decide (pairSndD z =
      ((ctxSt (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length))] :=
    (polyTimeComputable_pairEq.comp (hD.pairEncode hy)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact hD.append (polyTimeComputable_encPair S samp hF
    (polyTimeComputable_and (polyTimeComputable_headD.comp hst) heq))

/-- `bitF` is polynomial-time, as a function of `⟨ctx, b⟩`. -/
theorem polyTimeComputable_bitF :
    PolyTimeComputable fun z => bitF S samp (pairFstD z) (pairSndD z) :=
  polyTimeComputable_encPair S samp polyTimeComputable_pairFstD
    (polyTimeComputable_headD.comp polyTimeComputable_pairSndD)

variable (pl hl : PolyExpr)

/-- **The NM adversary's output** at parameter `n` on the context `ctx = ⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`, for
`A`'s output `a` (`r(n)` ciphertexts, then `σ`), the recorded parameter `aP` and the message `mP`:
`encF ctx c_i` for each ciphertext, then `encPair ctx x` for each bit `x` of `aP ‖ mP ‖ σ`. -/
def nmOutL (r : PolyExpr) (n : ℕ) (ctx a aP mP : List Bool) : List Bool :=
  ((List.range (r.eval n)).map fun i => encF S samp ctx (coinBlock (S.ctLen.eval n) i a)).flatten ++
    ((aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n)).map fun x => encPair S samp ctx x).flatten

/-- `nmOutL S samp r n ctx a aP mP = (encF ctx c_i)_i ++ (encPair ctx x)_{x ∈ aP ‖ mP ‖ σ}`. -/
theorem nmOutL_eq (r : PolyExpr) (n : ℕ) (ctx a aP mP : List Bool) :
    nmOutL S samp r n ctx a aP mP =
      ((List.range (r.eval n)).map fun i =>
        encF S samp ctx (coinBlock (S.ctLen.eval n) i a)).flatten ++
        ((aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n)).map fun x =>
          encPair S samp ctx x).flatten := rfl

/-- The parameter recorded in a state `[flag] ‖ y ‖ h ‖ a` (`1 + (ctLen + hl)` bits before `a`). -/
def stParam (n : ℕ) (st : List Bool) : List Bool :=
  st.drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval n)

/-- `stParam S hl n st = st.drop (1 + (ctLen(n) + hl(n)))`. -/
theorem stParam_eq (n : ℕ) (st : List Bool) :
    stParam S hl n st = st.drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval n) := rfl

/-- The message `M(aP; ρ)` of the finalization, with the advice `α` and the seed `ω` (`ρ` its first
`coins(n)` bits). -/
def finMsg (n : ℕ) (α ω aP : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.msgLen.eval n)
    (samp.output (NUPPT.layout (List.replicate n true) aP α (ω.take (samp.coins.eval n))))

/-- `finMsg S samp n α ω aP = padL msgLen(n) (M.output (layout 1^n aP α ρ))`. -/
theorem finMsg_eq (n : ℕ) (α ω aP : List Bool) :
    finMsg S samp n α ω aP = EnsembleLemmas.padL (S.msgLen.eval n)
      (samp.output (NUPPT.layout (List.replicate n true) aP α (ω.take (samp.coins.eval n)))) := rfl

/-- **The NM adversary's finalization round**: `⟨[true], chunkMap ctLen encF ⟨ctx, a.take (r·ctLen)⟩
‖ chunkMap 1 bitF ⟨ctx, aP ‖ M(aP; ρ) ‖ a.drop (r·ctLen)⟩⟩`, with `ctx = ⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩` and
no outer query. -/
def nmFin (r : PolyExpr) (w : List Bool) : List Bool :=
  pairEncode [true]
    (chunkMap S.ctLen (encF S samp)
        (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))))
          ((finA w).take ((r.mul S.ctLen).eval (rU w).length))) ++
      chunkMap (.const 1) (bitF S samp)
        (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))))
          ((rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length) ++
            EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
              (samp.output (NUPPT.layout (rU w)
                ((rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length))
                (pairSndD (rZ w)) ((rW w).take (samp.coins.eval (rU w).length)))) ++
            (finA w).drop ((r.mul S.ctLen).eval (rU w).length))))

/-- `nmFin S samp hl r w = ⟨[true], E ‖ B⟩`, with `E = chunkMap ctLen encF ⟨ctx, a.take (r·ctLen)⟩`
and `B = chunkMap 1 bitF ⟨ctx, aP ‖ M(aP; ρ) ‖ a.drop (r·ctLen)⟩`, where
`ctx = ⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`, `aP = s.drop (1 + ctLen + hl)`, `ρ = ω.take coins` and
`M(aP; ρ) = padL msgLen (M.output (layout 1^n aP (snd z) ρ))`. -/
theorem nmFin_eq (r : PolyExpr) (w : List Bool) :
    nmFin S samp hl r w = pairEncode [true]
      (chunkMap S.ctLen (encF S samp)
          (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))))
            ((finA w).take ((r.mul S.ctLen).eval (rU w).length))) ++
        chunkMap (.const 1) (bitF S samp)
          (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))))
            ((rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length) ++
              EnsembleLemmas.padL (S.msgLen.eval (rU w).length)
                (samp.output (NUPPT.layout (rU w)
                  ((rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length))
                  (pairSndD (rZ w)) ((rW w).take (samp.coins.eval (rU w).length)))) ++
              (finA w).drop ((r.mul S.ctLen).eval (rU w).length)))) := rfl

/-- The finalization round is polynomial-time.

**Proof sketch.** From the polynomial-time field readers (`polyTimeComputable_rU`,
…, `polyTimeComputable_finA`): the context by `pairEncode`; the cuts of `a` at `r·ctLen`, the
parameter `aP` and the coins `ρ` by `pairTakePoly`/`pairDropPoly`; the message by
`polyTimeComputable_padL` of `M`'s output on `layout`. The two chunk maps are
`polyTimeComputable_chunkMap` of `encF` and `bitF`, joined by `append` and `pairEncode`. -/
theorem polyTimeComputable_nmFin (r : PolyExpr) : PolyTimeComputable (nmFin S samp hl r) := by
  have hU := polyTimeComputable_rU
  have hZ := polyTimeComputable_rZ
  have hW := polyTimeComputable_rW
  have hA := polyTimeComputable_finA
  have hS := polyTimeComputable_rS
  have hctx : PolyTimeComputable fun w =>
      pairEncode (rU w) (pairEncode (rZ w) (pairEncode (rW w) (rS w))) :=
    hU.pairEncode (hZ.pairEncode (hW.pairEncode hS))
  have htake : PolyTimeComputable fun w => (finA w).take ((r.mul S.ctLen).eval (rU w).length) :=
    ((polyTimeComputable_pairTakePoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hdrop : PolyTimeComputable fun w => (finA w).drop ((r.mul S.ctLen).eval (rU w).length) :=
    ((polyTimeComputable_pairDropPoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have haP : PolyTimeComputable fun w =>
      (rS w).drop (((PolyExpr.const 1).add (S.ctLen.add hl)).eval (rU w).length) :=
    ((polyTimeComputable_pairDropPoly ((PolyExpr.const 1).add (S.ctLen.add hl))).comp
      (hU.pairEncode hS)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hρ : PolyTimeComputable fun w => (rW w).take (samp.coins.eval (rU w).length) :=
    ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hm := EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout hU haP (polyTimeComputable_pairSndD.comp hZ) hρ))
  exact (polyTimeComputable_const [true]).pairEncode
    (((polyTimeComputable_chunkMap S.ctLen (polyTimeComputable_encF S samp)).comp
      (hctx.pairEncode htake)).append
      ((polyTimeComputable_chunkMap (.const 1) (polyTimeComputable_bitF S samp)).comp
        (hctx.pairEncode ((haP.append hm).append hdrop))))

/-- **The finalization round on a finalization input** (for `A`'s output of `r·ctLen + sl` bits, and
`ctLen(n) > 0`) returns `⟨[true], nmOutL …⟩`.

**Proof sketch.** Read the fields of the input in `nmFin_eq` (`rU_finInput`,
…, `finA_finInput`). Cut `a.take (r·ctLen)` into its `r` chunks of `ctLen(n) > 0` bits
(`take_eq_flatten_chunkAt`, `length_coinBlock`), so the first chunk map is `encF` over them
(`chunkMap_flatten`). Write `aP ‖ M(aP; ρ) ‖ σ` as the flatten of its singletons, so the second,
with chunk length `1`, is `bitF` over its bits; both match `nmOutL_eq`. -/
theorem nmFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) (hct : 0 < S.ctLen.eval n) :
    nmFin S samp hl r (InteractiveHandler.finInput n z ω s a L) =
      pairEncode [true] (nmOutL S samp r n
        (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω s))) a (stParam S hl n s)
        (finMsg S samp n (pairSndD z) ω (stParam S hl n s))) := by
  have hU := rU_finInput n z ω s a L
  have hZ := rZ_finInput n z ω s a L
  have hW := rW_finInput n z ω s a L
  have hA := finA_finInput n z ω s a L
  have hbits : ∀ l : List Bool, l = (l.map fun x => [x]).flatten := by
    intro l
    induction l with
    | nil => rfl
    | cons x t ih => rw [List.map_cons, List.flatten_cons, ← ih]; rfl
  rw [nmFin_eq, hU, hZ, hW, hA, rS_finInput, List.length_replicate, PolyExpr.eval_mul,
    take_eq_flatten_chunkAt,
    chunkMap_flatten _ _ n _ _ (fun ch hch => ?_) hct, List.map_map, nmOutL_eq, stParam_eq,
    finMsg_eq]
  · congr 1
    rw [hbits (List.drop _ s ++ _ ++ _), chunkMap_flatten _ _ n _ _ (fun ch hch => ?_)
      (by rw [PolyExpr.eval_const]; omega), List.map_map, ← hbits]
    · rfl
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hch
      rw [PolyExpr.eval_const, List.length_singleton]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
    rw [List.mem_range] at hi
    refine length_coinBlock ?_
    rw [ha]
    have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
    omega

/-! ### The handler -/

/-- **The number of the NM adversary's ciphertexts**: `3r` (each of `A`'s ciphertexts with the
encoding of its copy flag) and `2(pl + msgLen + sl)` (the encodings of `a`, `m`, `σ`). -/
def nmLen (r sl : PolyExpr) : PolyExpr :=
  ((PolyExpr.const 3).mul r).add ((PolyExpr.const 2).mul ((pl.add S.msgLen).add sl))

/-- `nmLen S pl r sl = 3·r + 2·(pl + msgLen + sl)`. -/
theorem nmLen_eval (r sl : PolyExpr) (n : ℕ) :
    (nmLen S pl r sl).eval n = 3 * r.eval n + 2 * (pl.eval n + S.msgLen.eval n + sl.eval n) := by
  rw [nmLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_mul, PolyExpr.eval_add,
    PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_const]

variable (hist : List Bool → List Bool) (hist_poly : PolyTimeComputable hist)

/-- **The parameters of the NM adversary's handler** (on the real experiment's oracles with
parameter length `pl` and history `hist` of length `hl`; the outer oracles are those of
Definition 171.5 on T2's lengths): the first challenge `a` asks the challenge `⟨m, m̃⟩`
(oracle `1`),
with `m = M(a; ρ)` (`simMsg`) and `m̃ = M(a; ρ̃)` (`altMsg`); it answers `⟨y, h(m)⟩` with `y` the
outer answer. The seed is `ρ ‖ ρ̃ ‖ re`, the adversary runs on `pk = fst z`, the output is `nmLen`
ciphertexts (`nmFin`), and the finalization asks nothing. -/
def nmParams (r sl : PolyExpr) :
    ChalParams S pl hl 2 (snmDin S (S.msgLen.add S.msgLen)) (snmDout S (.const 0)) where
  j := 1
  seedLen := samp.coins.add (samp.coins.add S.enc.coins)
  advIn ctx := pairFstD (pairFstD (pairSndD ctx))
  advIn_poly := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  qry w := EnsembleLemmas.padL ((S.msgLen.add S.msgLen).eval (rU w).length)
    (simMsg S samp w ++ altMsg S samp w)
  qry_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rU
    ((polyTimeComputable_simMsg S samp).append (polyTimeComputable_altMsg S samp))
  qry_len w := by rw [EnsembleLemmas.length_padL, snmDin_one]
  ansY w := EnsembleLemmas.padL (S.ctLen.eval (rU w).length) (rAns w)
  ansY_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rU
    polyTimeComputable_rAns
  ansY_len _ := EnsembleLemmas.length_padL _ _
  ansH w := EnsembleLemmas.padL (hl.eval (rU w).length) (hist (simMsg S samp w))
  ansH_poly := EnsembleLemmas.polyTimeComputable_padL _ polyTimeComputable_rU
    (hist_poly.comp (polyTimeComputable_simMsg S samp))
  ansH_len _ := EnsembleLemmas.length_padL _ _
  outLen := (nmLen S pl r sl).mul S.ctLen
  finCall := .const 0
  finRun := nmFin S samp hl r
  finRun_poly := polyTimeComputable_nmFin S samp hl r

attribute [simps (config := { isSimp := false }) j seedLen advIn qry ansY ansH outLen finCall
  finRun] nmParams

section Run

variable (r sl : PolyExpr) (n : ℕ)

/-- The NM adversary's seed is `ρ ‖ (ρ̃ ‖ re)`. -/
theorem nmParams_seedLen_handler :
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen =
      samp.coins.add (samp.coins.add S.enc.coins) := by
  rw [chalHandler_seedLen, nmParams_seedLen]

/-- The NM adversary outputs `nmLen · ctLen` bits. -/
theorem nmParams_outLen_eval :
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).outLen.eval n =
      (nmLen S pl r sl).eval n * S.ctLen.eval n := by
  rw [chalHandler_outLen, nmParams_outLen, PolyExpr.eval_mul]

/-- The NM adversary runs `A` on `pk`: `advInput n ⟨pk, α⟩ ω = pk`. -/
theorem nmParams_advInput (pk α : List Bool)
    (ω : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool) :
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).advInput n (pairEncode pk α) ω =
      pk := by
  rw [InteractiveHandler.advInput_eq, chalHandler_advIn, nmParams_advIn, seedIn_eq,
    pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode]

/-- The bit encryptions have `ctLen(n)` bits. -/
theorem length_encBit (n : ℕ) (e : List Bool) (x : Bool) :
    (encBit S samp (pairEncode (List.replicate n true) e) x).length = S.ctLen.eval n := by
  rw [encBit_eq, EnsembleLemmas.length_padL, pairFstD_pairEncode, List.length_replicate]

/-- **The NM adversary outputs `nmLen` ciphertexts:** for `A`'s output of `r·ctLen + sl` bits, a
parameter of `pl` bits and a message of `msgLen` bits, `|nmOutL …| = nmLen · ctLen`. -/
theorem length_nmOutL (e a aP mP : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n)
    (haP : aP.length = pl.eval n) (hmP : mP.length = S.msgLen.eval n) :
    (nmOutL S samp r n (pairEncode (List.replicate n true) e) a aP mP).length =
      (nmLen S pl r sl).eval n * S.ctLen.eval n := by
  rw [nmLen_eval, nmOutL_eq, List.length_append,
    length_flatten_map_range (S.ctLen.eval n + 2 * S.ctLen.eval n) _ _ fun i hi => ?_,
    length_flatten_map_const _ _ (2 * S.ctLen.eval n) fun x => ?_, List.length_append,
    List.length_append, List.length_drop, ha, haP, hmP]
  · rw [Nat.add_sub_cancel_left]
    ring
  · rw [encPair_eq, List.length_append, length_encBit, length_encBit]
    ring
  · rw [encF_eq, encPair_eq, List.length_append, List.length_append, length_encBit,
      length_encBit, length_coinBlock (by
        rw [ha]
        have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
        omega)]
    ring

/-- **The NM adversary's finalization** on `A`'s output `a` (`r·ctLen + sl` bits, `ctLen(n) > 0`)
returns `nmOutL` on the context `⟨1^n, ⟨z, ⟨ω, s⟩⟩⟩`, asking nothing. -/
theorem nmFinish (z : List Bool)
    (ω : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool)
    (s : Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).stateLen.eval n) → Bool)
    {d : ℕ} (a : Fin d → Bool) (hd : d = r.eval n * S.ctLen.eval n + sl.eval n)
    (hct : 0 < S.ctLen.eval n) :
    (chalHandler (nmParams S samp pl hl hist hist_poly r sl)).finish n z ω s a =
      .pure (padFin _ (nmOutL S samp r n
        (pairEncode (List.replicate n true) (pairEncode z (pairEncode (List.ofFn ω) (List.ofFn s))))
        (List.ofFn a) (stParam S hl n (List.ofFn s))
        (finMsg S samp n (pairSndD z) (List.ofFn ω) (stParam S hl n (List.ofFn s))))) := by
  have ha : (List.ofFn a).length = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [List.length_ofFn, hd]
  refine InteractiveHandler.finish_of_ret_padFin _ n z ω s a _ ?_ ?_
  · have hs : (List.ofFn s).length = 1 + (S.ctLen.eval n + hl.eval n) + pl.eval n := by
      rw [List.length_ofFn, chalHandler_stateLen_eval]
    rw [nmParams_outLen_eval, length_nmOutL S samp pl r sl n _ _ _ _ ha ?_ ?_]
    · rw [stParam_eq, List.length_drop, hs, PolyExpr.eval_add, PolyExpr.eval_add,
        PolyExpr.eval_const]
      omega
    · rw [finMsg_eq, EnsembleLemmas.length_padL]
  · rw [chalHandler_finRun, nmParams_finRun]
    exact nmFin_finInput S samp hl r sl n z _ _ _ _ ha hct

end Run

/-! ### The NM adversary against `NM_b`'s oracles -/

section Composite

variable (r sl : PolyExpr) (n : ℕ)

/-- The NM adversary's seed for the coins `ρ`, `ρ̃` and `re`: `ρ ‖ (ρ̃ ‖ re)`. -/
def nmSeed (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) :
    Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).seedLen.eval n) → Bool :=
  seedEquivPoly (nmParams_seedLen_handler S samp pl hl hist hist_poly r sl) n
    (ρ, seedEquiv (A := samp) (B := S.enc) rfl n (ρ', re))

/-- `nmSeed … ρ ρ̃ re = seedEquivPoly _ n (ρ, seedEquiv rfl n (ρ̃, re))`. -/
theorem nmSeed_eq (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) :
    nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re =
      seedEquivPoly (nmParams_seedLen_handler S samp pl hl hist hist_poly r sl) n
        (ρ, seedEquiv (A := samp) (B := S.enc) rfl n (ρ', re)) := rfl

/-- `⟦nmSeed … ρ ρ̃ re⟧ = ⟦ρ⟧ ++ (⟦ρ̃⟧ ++ ⟦re⟧)`. -/
theorem nmSeed_ofFn (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) :
    List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re) =
      List.ofFn ρ ++ (List.ofFn ρ' ++ List.ofFn re) := by
  rw [nmSeed, seedEquivPoly_ofFn, seedEquiv_ofFn]

/-- **The messages of a round of the NM adversary** (input `⟨pk, M.advice n⟩`, seed `ρ ‖ ρ̃ ‖ re`,
parameter `xs` of `pl(n)` bits): `m = M(xs; ρ)` and `m̃ = M(xs; ρ̃)`. -/
theorem nmMsgs_input (pk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (s : List Bool)
    (i : Fin 2) (xs L : List Bool) (hxs : xs.length = pl.eval n) :
    simMsg S samp (InteractiveHandler.input n (pairEncode pk (samp.advice n))
        (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L) =
      List.ofFn (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) xs) ρ) ∧
    altMsg S samp (InteractiveHandler.input n (pairEncode pk (samp.advice n))
        (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L) =
      List.ofFn (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) xs) ρ') := by
  have hU := rU_input n (pairEncode pk (samp.advice n))
    (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L
  have hZ := rZ_input n (pairEncode pk (samp.advice n))
    (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L
  have hW := rW_input n (pairEncode pk (samp.advice n))
    (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L
  have hQ := rX_input n (pairEncode pk (samp.advice n))
    (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s i xs L
  have hρ := length_ofFn_coins samp n ρ
  have hρ' := length_ofFn_coins samp n ρ'
  rw [simMsg_eq, altMsg_eq, hU, hZ, hW, hQ, List.length_replicate, pairSndD_pairEncode,
    nmSeed_ofFn, List.take_left' hρ, List.drop_left' hρ, List.take_left' hρ', drawWith_eq,
    drawWith_eq, ofFn_padFin_of_length hxs, ofFn_padFin_eq_padL, ofFn_padFin_eq_padL,
    NUPPT.runAt_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, NUPPT.runAtL_eq_output_layout]
  exact ⟨rfl, rfl⟩

/-- The challenge pair `⟨M(a; ρ), M(a; ρ̃)⟩` asked on the parameter `a`. -/
def nmPair (ρ ρ' : samp.Coins n) (a : Fin (pl.eval n) → Bool) :
    Fin ((S.msgLen.add S.msgLen).eval n) → Bool :=
  padFin _ (List.ofFn (drawWith samp (S.msgLen.eval n) n a ρ) ++
    List.ofFn (drawWith samp (S.msgLen.eval n) n a ρ'))

/-- `nmPair … ρ ρ̃ a = padFin _ (⟦M(a; ρ)⟧ ++ ⟦M(a; ρ̃)⟧)`. -/
theorem nmPair_eq (ρ ρ' : samp.Coins n) (a : Fin (pl.eval n) → Bool) :
    nmPair S samp pl n ρ ρ' a = padFin _ (List.ofFn (drawWith samp (S.msgLen.eval n) n a ρ) ++
      List.ofFn (drawWith samp (S.msgLen.eval n) n a ρ')) := rfl

/-- **The abstraction of the hybrid's state** to the NM adversary's and `NM_b`'s: no challenge is
`(empty, none)`; the challenge `y` on `a` is
`(⟨y, h(M(a; ρ)), a⟩, some (y, ⟨M(a; ρ), M(a; ρ̃)⟩))`. -/
def nmAbs (ρ ρ' : samp.Coins n) :
    Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)) →
      (Fin ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).stateLen.eval n) → Bool) ×
        Option ((Fin (S.ctLen.eval n) → Bool) × (Fin ((S.msgLen.add S.msgLen).eval n) → Bool))
  | none => (chalState (nmParams S samp pl hl hist hist_poly r sl) n none, none)
  | some (y, a) => (chalState (nmParams S samp pl hl hist hist_poly r sl) n
      (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)),
      some (y, nmPair S samp pl n ρ ρ' a))

/-- `nmAbs … none = (chalState none, none)`. -/
theorem nmAbs_none (ρ ρ' : samp.Coins n) :
    nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' none =
      (chalState (nmParams S samp pl hl hist hist_poly r sl) n none, none) := rfl

/-- `nmAbs … (some (y, a)) = (chalState (some (y, h(M(a; ρ)), a)), some (y, nmPair a))`. -/
theorem nmAbs_some (ρ ρ' : samp.Coins n) (y : Fin (S.ctLen.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' (some (y, a)) =
      (chalState (nmParams S samp pl hl hist hist_poly r sl) n
        (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)),
        some (y, nmPair S samp pl n ρ ρ' a)) := rfl

/-- `NM_b`'s part of the abstraction records the hybrid's challenge ciphertext. -/
theorem nmAbs_snd_fst (ρ ρ' : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s).2.map Prod.fst = s.map Prod.fst := by
  cases s with
  | none => rfl
  | some ya => rfl

/-- **The NM adversary against `NM_b`'s oracles is the hybrid `H_b`:** for the input
`⟨pk, M.advice n⟩` and the seed `ρ ‖ ρ̃ ‖ re`, the composition of `NM_b`'s oracles (the hybrid
oracle
with the sampler `halfSamp` and its coin `b`, under CPA) with the NM adversary's handler, from the
abstracted state, is `rImpl … b … ρ ρ̃ none` with its state abstracted (`nmAbs`).

**Proof sketch.** Query by query: `Dec` is `⊥` on both sides; a repeated challenge repeats
`⟨y, h(M(a; ρ))⟩`; a first challenge asks `⟨M(a; ρ), M(a; ρ̃)⟩` (`nmMsgs_input`), whose half `b` is
`M(a; ρ_b)` (`ofFn_drawWith_half`), so the challenge ciphertext is `Enc_pk(M(a; ρ_b))` with the same
lazily drawn coins, and answers it with `h(M(a; ρ))`. -/
theorem nmComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (b : Bool)
    (ρ'' : (halfSamp S).Coins n) (i : Fin 2) (x : (bitSpecAt (snmDin S pl) (snmDout S hl) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    ((rImpl S .cpa false (halfSamp S) (S.msgLen.add S.msgLen) (.const 0) (fun _ => []) n pk sk
        ((halfCoins S n).symm b) ρ'' none).comp
        ((chalHandler (nmParams S samp pl hl hist hist_poly r sl)).impl n
          (pairEncode pk (samp.advice n)) (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)))
        i x (nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' s) =
      (rImpl S .cpa b samp pl hl hist n pk sk ρ ρ' none i x s).bind
        fun p => .pure (p.1, nmAbs S samp pl hl hist hist_poly r sl n ρ ρ' p.2) := by
  rw [QueryImpl.comp_apply]
  match i, x, s with
  | 0, x, none =>
    rw [nmAbs_none, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, nmAbs_none]
  | 0, x, some (y, a) =>
    rw [nmAbs_some, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, nmAbs_some]
  | 1, x, some (y, a) =>
    rw [nmAbs_some, chalHandler_impl_some, simulate_pure, OracleComp.pure_bind, rImpl_some,
      OracleComp.pure_bind, nmAbs_some]
  | 1, x, none =>
    have hxl : (List.ofFn x).length = pl.eval n := by
      rw [List.length_ofFn]
      show (snmDin S pl 1).eval n = _
      rw [snmDin_one]
    have hpl : (S.msgLen.add S.msgLen).eval n = S.msgLen.eval n + S.msgLen.eval n :=
      PolyExpr.eval_add _ _ _
    have hq : ∀ (s' L : List Bool), (nmParams S samp pl hl hist hist_poly r sl).qry
        (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s' (1 : Fin 2)
          (List.ofFn x) L) =
        List.ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))) := by
      intro s' L
      obtain ⟨hm, hm'⟩ := nmMsgs_input S samp pl hl hist hist_poly r sl n pk ρ ρ' re s' 1
        (List.ofFn x) L hxl
      rw [nmParams_qry, rU_input (k := 2) n _ _ s' 1 _ L, List.length_replicate, hm, hm',
        nmPair_eq, ofFn_padFin_eq_padL]
    have hH : ∀ (s' q t : List Bool), (nmParams S samp pl hl hist hist_poly r sl).ansH
        (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s' (1 : Fin 2)
          (List.ofFn x)
          (pairEncode (pairEncode (List.replicate ((1 : Fin 2) : ℕ) true) (pairEncode q t))
            [])) =
        List.ofFn (histWith hist (hl.eval n)
          (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x)) ρ)) := by
      intro s' q t
      rw [nmParams_ansH, rU_input (k := 2) n _ _ s' 1 _ _, List.length_replicate,
        (nmMsgs_input S samp pl hl hist hist_poly r sl n pk ρ ρ' re s' 1 (List.ofFn x) _ hxl).1,
        histWith_eq, ofFn_padFin_eq_padL]
    have hY : ∀ (s' q t : List Bool), (nmParams S samp pl hl hist hist_poly r sl).ansY
        (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (nmSeed S samp pl hl hist hist_poly r sl n ρ ρ' re)) s' (1 : Fin 2)
          (List.ofFn x)
          (pairEncode (pairEncode (List.replicate ((1 : Fin 2) : ℕ) true) (pairEncode q t))
            [])) =
        EnsembleLemmas.padL (S.ctLen.eval n) t := by
      intro s' q t
      rw [nmParams_ansY, rU_input (k := 2) n _ _ s' 1 _ _, List.length_replicate,
        rAns_input]
    have hdraw : ∀ re' : S.enc.Coins n, encWith S n pk (drawWith (halfSamp S) (S.msgLen.eval n) n
        (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))) ((halfCoins S n).symm b)) re' =
        encWith S n pk (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
          (if b then ρ' else ρ)) re' := by
      intro re'
      have hlen : (List.ofFn (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
            ρ)
          ++ List.ofFn (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
            ρ')).length = (S.msgLen.add S.msgLen).eval n := by
        rw [List.length_append, List.length_ofFn, List.length_ofFn, hpl]
      rw [encWith_eq, encWith_eq, ofFn_drawWith_half S n _ hpl, nmPair_eq,
        ofFn_padFin_of_length hlen]
      cases b
      · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
          List.take_left' List.length_ofFn]
      · rw [if_pos rfl, if_pos rfl, List.drop_left' List.length_ofFn]
    have h0 : ∀ m : Fin (S.msgLen.eval n) → Bool,
        List.ofFn (histWith (fun _ => []) ((PolyExpr.const 0).eval n) m) = [] := fun m =>
      List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, PolyExpr.eval_const])
    rw [nmAbs_none, chalHandler_impl_none, nmParams_j, simulate_query, rImpl_none_lazy,
      rImpl_none_lazy, OracleComp.bind_assoc, OracleComp.bind_assoc, OracleComp.bind_assoc]
    refine congrArg _ (funext fun re' => ?_)
    have hx' : List.ofFn (padFin ((snmDin S (S.msgLen.add S.msgLen) 1).eval n)
        (List.ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))))) =
        List.ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))) :=
      ofFn_padFin_of_length (by rw [List.length_ofFn, snmDin_one])
    have hlen : (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re') ++ []).length =
        (snmDout S (.const 0) 1).eval n := by
      rw [List.append_nil, List.length_ofFn, snmDout_one, PolyExpr.eval_add, PolyExpr.eval_const,
        Nat.add_zero]
    have hans := ofFn_padFin_of_length hlen
    rw [rImpl_none_eager, rImpl_none_eager]
    simp only [OracleComp.pure_bind, simulate_pure, nmAbs_some, Bool.false_eq_true, ↓reduceIte, hq]
    rw [hx', padFin_ofFn (nmPair S samp pl n ρ ρ' (padFin (pl.eval n) (List.ofFn x))), hdraw, h0]
    simp only [hH, hY]
    rw [hans, List.append_nil, ← ofFn_padFin_eq_padL,
      padFin_ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re'),
      padFin_ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re'),
      padFin_ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ))]

end Composite

end TCSlib.Cryptography.Composability.NMSim
