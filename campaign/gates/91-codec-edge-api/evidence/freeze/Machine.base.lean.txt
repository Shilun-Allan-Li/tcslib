/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Checks
import TCSlib.Complexity.SpaceComplexity.Codec.Engine
import TCSlib.Complexity.SpaceComplexity.Codec.Regs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The abstract register machine deciding the code languages

One abstract register machine (`Complexity.LogProg.ARM`) over 21 registers, calling the
logspace length and bit oracles of its input (`Complexity.inputLenLang`,
`Complexity.inputBitLang`), decides each of the four code languages; the `mode` selects the
language. On an input `⟨x, ⟨w, s⟩⟩` (or `⟨x, ⟨w, ⟨w', s⟩⟩⟩` for steps) it

1. measures the input and parses its fields with aligned pair scans, rejecting malformed
   inputs, and decodes the radius `s` from the last field after a width check;
2. computes, with copy, scale and increment loops, the layout of the code word `w` — its
   chunk region, its position field, its length — and checks the length and the final
   letter, decodes the input position and compares it with `|x| + 1`;
3. (steps) does the same for `w'`, reads the input symbol under the input head into a
   register, and prepares the pointers of the second scan;
4. runs the validity scan over the chunk region of `w` — the finite-state device of
   `TCSlib.Complexity.SpaceComplexity.Codec.Valid`, letter by letter through the scan engine;
5. finishes per mode: valid and accepting codes answer from the scan state; the initial code
   also tests the position field and the middle cell; a step moves the input position by the
   action of each choice bit and compares it with that of `w'`, then runs the double sliding
   scan of the two chunk regions.

All registers hold pointers into the input, lengths, or values bounded by a constant times
the input length, so `Complexity.LogProg.arm_decides_poly` makes the languages logspace
(`TCSlib.Complexity.SpaceComplexity.Codec.Deciders`).

Logspace machine infrastructure for the codec; not a result of [AB09].

## Main definitions

* `Complexity.Codec.Lab` — the labels.
* `Complexity.Codec.CA` — the machine, by `Complexity.Codec.CMode`.

## Main results

* `Complexity.Codec.dcStride_le`, `Complexity.Codec.scFactor_le`,
  `Complexity.Codec.icCount_le` — the label families are finite.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.Codec

open Turing LogProg

/-! ## Oracles and modes -/

/-- The length oracle: `Complexity.inputLenLang`. -/
abbrev jLen : Fin 2 := 0

/-- The bit oracle: `Complexity.inputBitLang`. -/
abbrev jBit : Fin 2 := 1

/-- Which code language the machine decides. -/
inductive CMode where
  /-- valid codes -/
  | valid
  /-- the initial code -/
  | init
  /-- accepting codes -/
  | accept
  /-- step pairs -/
  | step
  deriving DecidableEq

/-! ## Labels -/

/-- The copy loops of the machine (destination `cpDst`, source `cpSrc`). -/
inductive CpId where
  | A | B | Q1s | Cap | Q2 | N1 | Tn | E | Ts | F | Tw | U | Q1f
  | E2 | Ts2 | F2 | Tw2 | U2 | Q1f2 | Tpos | Q3 | Q4 | Q1a | Q2a | Uc | Tsc
  deriving DecidableEq, Fintype

/-- The scale loops of the machine (`scDst += scFactor · scSrc`). -/
inductive ScId where
  | E | F | E2 | F2 | In | C
  deriving DecidableEq, Fintype

/-- The increment chains of the machine (`icReg += icCount`). -/
inductive IcId where
  | E | U | E2 | U2 | C
  deriving DecidableEq, Fintype

/-- The decoding loops of the machine: the radius, and the two input positions. -/
inductive DcId where
  | S | Pos | Pos2
  deriving DecidableEq, Fintype

/-- The phases of moving the input position by one choice bit's action and comparing. -/
inductive PmPh where
  | start | eq | inc | eq2 | decR (r : Bool) | decN | eq3 | incR (r : Bool)
  deriving DecidableEq, Fintype

variable (N : FinNDTM Bool)

/-- The validity-scan state through the chunk adaptor. -/
abbrev VAd := AdSt (VSt N) (Bool × Bool) (hH N + 3 * N.k)

/-- The double-sliding-scan state through the chunk adaptor. -/
abbrev SAd := AdSt (SSt N) (Bool × Bool) (hH N + 3 * N.k)

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 2000 in
/-- The labels of the codec machine. -/
inductive Lab where
  | rej | acc
  | lenScan | lenInc
  | prScan (p : Fin 3) | prFirst (p : Fin 3) | prTest (p : Fin 3) (b : Bool)
  | prRead (p : Fin 3) (b : Bool) | prAdv (p : Fin 3) (k : Fin 4)
  | cp (c : CpId) | cpI (c : CpId)
  | ctTest (b : Bool) | ctCheck | ctRead | ctHalve (b : Bool) | ctAdv (b : Bool)
  | dcTest (c : DcId) | dcDown (c : DcId) (i : Fin 2) | dcRead (c : DcId)
  | dcCopy (c : DcId) (b : Bool) | dcBump (c : DcId) (b : Bool) | dcClear (c : DcId) (b : Bool)
  | dcScale (c : DcId) (b : Bool) | dcTake (c : DcId) (b : Bool)
  | dcInc (c : DcId) (b : Bool) (i : Fin 2) | dcAdd (c : DcId) (b : Bool)
  | halveN
  | hcTest | hcHalve | hcBump
  | sc (c : ScId) | scDown (c : ScId) | scInc (c : ScId) (i : Fin (4 * W N))
  | ic (c : IcId) (i : Fin (4 * W N))
  | clrU | lenChk | term | clrQ1
  | leT1 | leT2 | leBump | leClr
  | clrU2 | lenChk2 | term2 | clrQ1b
  | inZ | inN | inDec | clrU3 | inRead | inT1 | inF
  | clrQ1v | clrQ2v
  | vTest (st : VAd N) | vRd1 (st : VAd N) | vRd2 (st : VAd N) (b : Bool)
  | vAdv1 (st : VAd N) (i : Fin 2) | vAdv2 (st : VAd N) (i : Fin 2) | vDone (st : VAd N)
  | iz1 | iz2 | iz3 | icen | clrUc | cenRead
  | zA (σ : VSt N) | zB (σ : VSt N) | zC (σ : VSt N)
  | pm (I : SInfo N) (b f : Bool) (ph : PmPh)
  | sTest (I : SInfo N) (f₀ f₁ : Bool) (st : SAd N) | sRd1 (I : SInfo N) (f₀ f₁ : Bool) (st : SAd N)
  | sRd2 (I : SInfo N) (f₀ f₁ : Bool) (st : SAd N) (b : Bool)
  | sAdv1 (I : SInfo N) (f₀ f₁ : Bool) (st : SAd N) (i : Fin 2)
  | sAdv2 (I : SInfo N) (f₀ f₁ : Bool) (st : SAd N) (i : Fin 2)
  | sFin (I : SInfo N) (f₀ f₁ : Bool) (st : SAd N)
  deriving DecidableEq, Fintype

end Complexity.Codec

/-! ## The machine -/

namespace Complexity.Codec

open Turing LogProg

variable (N : FinNDTM Bool)

/-- An unconditional jump (a zero test with equal branches). -/
def goto (l : Lab N) : Ins 21 2 (Lab N) := .jz rZ l l

/-- Destination register of a copy loop. -/
def cpDst : CpId → Fin 21
  | .A => rA | .B => rB | .Q1s => rQ1 | .Cap => rCap | .Q2 => rQ2 | .N1 => rN1 | .Tn => rT
  | .E => rE | .Ts => rT | .F => rF | .Tw => rT | .U => rU | .Q1f => rQ1 | .E2 => rE2
  | .Ts2 => rT | .F2 => rF2 | .Tw2 => rT | .U2 => rU | .Q1f2 => rQ1 | .Tpos => rT
  | .Q3 => rQ3 | .Q4 => rQ4 | .Q1a => rQ1 | .Q2a => rQ2 | .Uc => rU | .Tsc => rT

/-- Source register of a copy loop. -/
def cpSrc : CpId → Fin 21
  | .A => rP | .B => rP | .Q1s => rP | .Cap => rL | .Q2 => rL | .N1 => rA | .Tn => rN1
  | .E => rA | .Ts => rS | .F => rE | .Tw => rWp | .U => rF | .Q1f => rF | .E2 => rB
  | .Ts2 => rS | .F2 => rE2 | .Tw2 => rWp | .U2 => rF2 | .Q1f2 => rF2 | .Tpos => rPos
  | .Q3 => rA | .Q4 => rB | .Q1a => rA | .Q2a => rA | .Uc => rA | .Tsc => rS

/-- The initial validity-scan state. -/
def vAd0 : VAd N := (vInit N, 0, fun _ => (false, false))

/-- The initial double-sliding-scan state. -/
def sAd0 : SAd N := ((sInit N, sInit N), 0, fun _ => (false, false))

/-- Successor of a copy loop. -/
def cpNext : CpId → Lab N
  | .A => .prScan 1 | .B => .prScan 2 | .Q1s => .cp .Cap | .Cap => .ctTest true
  | .Q2 => .dcTest .S | .N1 => .halveN | .Tn => .hcTest | .E => .cp .Ts | .Ts => .sc .E
  | .F => .cp .Tw | .Tw => .sc .F | .U => .ic .U ⟨0, by simp [W]⟩ | .Q1f => .dcTest .Pos
  | .E2 => .cp .Ts2 | .Ts2 => .sc .E2 | .F2 => .cp .Tw2 | .Tw2 => .sc .F2
  | .U2 => .ic .U2 ⟨0, by simp [W]⟩ | .Q1f2 => .dcTest .Pos2 | .Tpos => .inDec
  | .Q3 => .cp .Q4 | .Q4 => .clrQ1v | .Q1a => .cp .Q2a | .Q2a => .vTest (vAd0 N)
  | .Uc => .cp .Tsc | .Tsc => .sc .C

/-- Pointer, base, accumulator, temporary of a decoding loop. -/
def dcPtr : DcId → Fin 21 | .S => rQ2 | .Pos => rQ1 | .Pos2 => rQ1
/-- Base register of a decoding loop. -/
def dcBase : DcId → Fin 21 | .S => rP | .Pos => rE | .Pos2 => rE2
/-- Accumulator of a decoding loop. -/
def dcAcc : DcId → Fin 21 | .S => rS | .Pos => rPos | .Pos2 => rPos2
/-- The stride of a decoding loop: the radius field is plain, code fields are doubled. -/
def dcStride : DcId → ℕ | .S => 1 | .Pos => 2 | .Pos2 => 2

/-- The stride of a decoding loop is at most two. -/
lemma dcStride_le (c : DcId) : dcStride c ≤ 2 := by cases c <;> simp [dcStride]

/-- The decrement labels of a decoding loop. -/
def dcDowns (c : DcId) (i : ℕ) : Lab N :=
  if h : i < dcStride c then .dcDown c ⟨i, by have := dcStride_le c; omega⟩ else .dcRead c

/-- The increment labels of a decoding loop. -/
def dcIncs (c : DcId) (b : Bool) (i : ℕ) : Lab N :=
  if h : i < 2 then .dcInc c b ⟨i, h⟩ else .dcScale c b

/-- Successor of a decoding loop. -/
def dcNext : DcId → Lab N | .S => .cp .N1 | .Pos => .leT1 | .Pos2 => .inZ

/-- Source of a scale loop. -/
def scSrc : ScId → Fin 21 | _ => rT
/-- Destination of a scale loop. -/
def scDst : ScId → Fin 21
  | .E => rE | .F => rF | .E2 => rE2 | .F2 => rF2 | .In => rU | .C => rU
/-- Factor of a scale loop. -/
def scFactor : ScId → ℕ
  | .E => 4 * W N | .F => 2 | .E2 => 4 * W N | .F2 => 2 | .In => 2 | .C => 2 * W N

/-- Factors are at most `4 W`. -/
lemma scFactor_le (c : ScId) : scFactor N c ≤ 4 * W N := by
  have : 1 ≤ W N := by simp [W]
  cases c <;> simp [scFactor] <;> omega

/-- The increment labels of a scale loop. -/
def scIncs (c : ScId) (i : ℕ) : Lab N :=
  if h : i < scFactor N c then .scInc c ⟨i, by have := scFactor_le N c; omega⟩ else .sc c

/-- Successor of a scale loop. -/
def scNext : ScId → Lab N
  | .E => .ic .E ⟨0, by simp [W]⟩ | .F => .clrU
  | .E2 => .ic .E2 ⟨0, by simp [W]⟩ | .F2 => .clrU2 | .In => .inRead
  | .C => .ic .C ⟨0, by simp [W]⟩

/-- Register of an increment chain. -/
def icReg : IcId → Fin 21 | .E => rE | .U => rU | .E2 => rE2 | .U2 => rU | .C => rU
/-- Length of an increment chain. -/
def icCount : IcId → ℕ
  | .E => 2 * W N | .U => 4 | .E2 => 2 * W N | .U2 => 4 | .C => 2 * (hH N + 2)

/-- Chain lengths are at most `4 W`. -/
lemma icCount_le (c : IcId) : icCount N c ≤ 4 * W N := by
  simp only [W]
  cases c <;> simp only [icCount, W] <;> omega

/-- Successor of an increment chain. -/
def icNext : IcId → Lab N
  | .E => .cp .F | .U => .lenChk | .E2 => .cp .F2 | .U2 => .lenChk2 | .C => .cenRead

/-- The labels of an increment chain. -/
def icL (c : IcId) (i : ℕ) : Lab N :=
  if h : i < icCount N c then .ic c ⟨i, by have := icCount_le N c; omega⟩ else icNext N c

/-- The continuation of a parse loop after an advance (`k`: the case). -/
def prCont (mode : CMode) (p : Fin 3) (k : Fin 4) : Lab N :=
  match k with
  | 0 => .prTest p false
  | 1 => .prTest p true
  | 2 => .prScan p
  | 3 => match p with
    | 0 => .cp .A
    | 1 => if mode = .step then .cp .B else .cp .Q1s
    | 2 => .cp .Q1s

/-- The advance labels of a parse loop. -/
def prAdvL (mode : CMode) (p : Fin 3) (k : Fin 4) (i : ℕ) : Lab N :=
  if i = 0 then .prAdv p k else prCont N mode p k

/-- The pointer-advance labels of the validity scan. -/
def vA2 (st : VAd N) (i : ℕ) : Lab N := if h : i < 2 then .vAdv2 st ⟨i, h⟩ else .vTest st

/-- The pointer-advance labels of the validity scan (first pointer). -/
def vA1 (st : VAd N) (i : ℕ) : Lab N := if h : i < 2 then .vAdv1 st ⟨i, h⟩ else vA2 N st 0

/-- The letter step of the validity scan. -/
noncomputable def δV : VAd N → Bool × Bool → VAd N := adStep (vChunk N)

/-- The letter step of the double sliding scan under step data `I`. -/
noncomputable def δS (I : SInfo N) : SAd N → Bool × Bool → SAd N :=
  adStep (sChunk N (Gs N I false) (Gs N I true))

/-- The pointer-advance labels of the double sliding scan. -/
def sA2 (I : SInfo N) (f₀ f₁ : Bool) (st : SAd N) (i : ℕ) : Lab N :=
  if h : i < 2 then .sAdv2 I f₀ f₁ st ⟨i, h⟩ else .sTest I f₀ f₁ st

/-- The pointer-advance labels of the double sliding scan (first pointer). -/
def sA1 (I : SInfo N) (f₀ f₁ : Bool) (st : SAd N) (i : ℕ) : Lab N :=
  if h : i < 2 then .sAdv1 I f₀ f₁ st ⟨i, h⟩ else sA2 N I f₀ f₁ st 0

/-- After the position comparison for choice bit `b` with verdict `r`: the next bit, or the
double sliding scan with both verdicts. -/
def pmNext (I : SInfo N) (b f r : Bool) : Lab N :=
  if b then .sTest I f r (sAd0 N) else .pm I true r .start

/-- **The codec machine** in mode `mode` (see the module docstring). -/
noncomputable def CA (mode : CMode) : ARM 21 2 (Lab N)
  | .rej => .ret false
  | .acc => .ret true
  | .lenScan => .call jLen .whole [rL] .lenInc (.prScan 0)
  | .lenInc => .inc rL .lenScan
  | .prScan p => .jeq rP rL .rej (.prFirst p)
  | .prFirst p => .call jBit .whole [rP] (prAdvL N mode p 1 0) (prAdvL N mode p 0 0)
  | .prTest p b => .jeq rP rL .rej (.prRead p b)
  | .prRead p b => .call jBit .whole [rP]
      (if b then prAdvL N mode p 2 0 else prAdvL N mode p 3 0)
      (if b then .rej else prAdvL N mode p 2 0)
  | .prAdv p k => .inc rP (prAdvL N mode p k 1)
  | .cp c => .jeq (cpDst c) (cpSrc c) (cpNext N c) (.cpI c)
  | .cpI c => .inc (cpDst c) (.cp c)
  | .ctTest b => .jeq rQ1 rL (if b then .cp .Q2 else .rej) .ctCheck
  | .ctCheck => .jz rCap .rej .ctRead
  | .ctRead => .call jBit .whole [rQ1] (.ctHalve true) (.ctHalve false)
  | .ctHalve b => .half rCap (.ctAdv b)
  | .ctAdv b => .inc rQ1 (.ctTest b)
  | .dcTest c => .jeq (dcPtr c) (dcBase c) (dcNext N c) (dcDowns N c 0)
  | .dcDown c i => .dec (dcPtr c) (dcDowns N c (i + 1))
  | .dcRead c => .call jBit .whole [dcPtr c] (.dcCopy c true) (.dcCopy c false)
  | .dcCopy c b => .jeq rT (dcAcc c) (.dcClear c b) (.dcBump c b)
  | .dcBump c b => .inc rT (.dcCopy c b)
  | .dcClear c b => .clr (dcAcc c) (.dcScale c b)
  | .dcScale c b => .jz rT (.dcAdd c b) (.dcTake c b)
  | .dcTake c b => .dec rT (dcIncs N c b 0)
  | .dcInc c b i => .inc (dcAcc c) (dcIncs N c b (i + 1))
  | .dcAdd c b => if b then .inc (dcAcc c) (.dcTest c) else .jz rT (.dcTest c) (.dcTest c)
  | .halveN => .half rN1 (.cp .Tn)
  | .hcTest => .jz rT (.cp .E) .hcHalve
  | .hcHalve => .half rT .hcBump
  | .hcBump => .inc rWp .hcTest
  | .sc c => .jz (scSrc c) (scNext N c) (.scDown c)
  | .scDown c => .dec (scSrc c) (scIncs N c 0)
  | .scInc c i => .inc (scDst c) (scIncs N c (i + 1))
  | .ic c i => .inc (icReg c) (icL N c (i + 1))
  | .clrU => .clr rU (.cp .U)
  | .lenChk => .jeq rU (if mode = .step then rB else rP) .term .rej
  | .term => .call jBit .whole [rF] .clrQ1 .rej
  | .clrQ1 => .clr rQ1 (.cp .Q1f)
  | .leT1 => .jeq rT rPos .leClr .leT2
  | .leT2 => .jeq rT rN1 .rej .leBump
  | .leBump => .inc rT .leT1
  | .leClr => .clr rT (if mode = .step then .cp .E2 else .clrQ1v)
  | .clrU2 => .clr rU (.cp .U2)
  | .lenChk2 => .jeq rU rP .term2 .rej
  | .term2 => .call jBit .whole [rF2] .clrQ1b .rej
  | .clrQ1b => .clr rQ1 (.cp .Q1f2)
  | .inZ => .jz rPos (.cp .Q3) .inN
  | .inN => .jeq rPos rN1 (.cp .Q3) (.cp .Tpos)
  | .inDec => .dec rT .clrU3
  | .clrU3 => .clr rU (.sc .In)
  | .inRead => .call jBit .whole [rU] .inT1 .inF
  | .inT1 => .inc rZ .inF
  | .inF => .inc rZ (.cp .Q3)
  | .clrQ1v => .clr rQ1 .clrQ2v
  | .clrQ2v => .clr rQ2 (.cp .Q1a)
  | .vTest st => .jeq rQ1 rE (.vDone st) (.vRd1 st)
  | .vRd1 st => .call jBit .whole [rQ1] (.vRd2 st true) (.vRd2 st false)
  | .vRd2 st b => .call jBit .whole [rQ2] (vA1 N (δV N st (b, true)) 0)
      (vA1 N (δV N st (b, false)) 0)
  | .vAdv1 st i => .inc rQ1 (vA1 N st (i + 1))
  | .vAdv2 st i => .inc rQ2 (vA2 N st (i + 1))
  | .vDone st =>
    match mode with
    | .valid => .ret (decide (VAcc N st.1))
    | .accept => .ret (decide (VAcc N st.1 ∧ st.1.2.1 = some (none, 1)))
    | .init => goto N (if VAcc N st.1 ∧ st.1.2.1 = some (some N.tm.q₀, 0) ∧
        st.1.2.2.2.2.2 = true then .iz1 else .rej)
    | .step => goto N (if VAcc N st.1 then .zA st.1 else .rej)
  | .iz1 => .jz rPos .rej .iz2
  | .iz2 => .dec rPos .iz3
  | .iz3 => .jz rPos .icen .rej
  | .icen => if N.k = 0 then .ret true else goto N .clrUc
  | .clrUc => .clr rU (.cp .Uc)
  | .cenRead => .call jBit .whole [rU] .acc .rej
  | .zA σ => .jz rZ (.pm (σ, none) false false .start) (.zB σ)
  | .zB σ => .dec rZ (.zC σ)
  | .zC σ => .jz rZ (.pm (σ, some false) false false .start) (.pm (σ, some true) false false .start)
  | .pm I b f ph =>
    match ph with
    | .start =>
      match (aI N I b).inputTape with
      | .zero => .jeq rPos rPos2 (pmNext N I b f true) (pmNext N I b f false)
      | .pos => .jeq rPos rN1 (.pm I b f .eq) (.pm I b f .inc)
      | .neg => .jz rPos (.pm I b f .eq) (.pm I b f .decN)
    | .eq => .jeq rPos rPos2 (pmNext N I b f true) (pmNext N I b f false)
    | .inc => .inc rPos (.pm I b f .eq2)
    | .eq2 => .jeq rPos rPos2 (.pm I b f (.decR true)) (.pm I b f (.decR false))
    | .decR r => .dec rPos (pmNext N I b f r)
    | .decN => .dec rPos (.pm I b f .eq3)
    | .eq3 => .jeq rPos rPos2 (.pm I b f (.incR true)) (.pm I b f (.incR false))
    | .incR r => .inc rPos (pmNext N I b f r)
  | .sTest I f₀ f₁ st => .jeq rQ3 rE (.sFin I f₀ f₁ st) (.sRd1 I f₀ f₁ st)
  | .sRd1 I f₀ f₁ st => .call jBit .whole [rQ3] (.sRd2 I f₀ f₁ st true) (.sRd2 I f₀ f₁ st false)
  | .sRd2 I f₀ f₁ st b => .call jBit .whole [rQ4] (sA1 N I f₀ f₁ (δS N I st (b, true)) 0)
      (sA1 N I f₀ f₁ (δS N I st (b, false)) 0)
  | .sAdv1 I f₀ f₁ st i => .inc rQ3 (sA1 N I f₀ f₁ st (i + 1))
  | .sAdv2 I f₀ f₁ st i => .inc rQ4 (sA2 N I f₀ f₁ st (i + 1))
  | .sFin I f₀ f₁ st =>
    .ret ((f₀ && sDone N (Gs N I false) st.1.1) || (f₁ && sDone N (Gs N I true) st.1.2))

end Complexity.Codec
