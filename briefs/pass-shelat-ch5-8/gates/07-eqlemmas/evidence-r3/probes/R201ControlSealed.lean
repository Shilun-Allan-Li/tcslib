import TCSlib.Cryptography.Asymptotic.HardCoreCollection

set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography

-- SEAL-LINE
attribute [local irreducible] TCSlib.Cryptography.Collection.glPad.match_1 TCSlib.Cryptography.Collection.glPad.match_3 Turing.Action.apply.match_1 Turing.MultiTapeTM.step.match_1 Turing.pairDecode.match_1 Complexity.NUPPT.Uniform Complexity.NUPPT.advInput Complexity.NUPPT.coinLen Complexity.NUPPT.inArg Complexity.NUPPT.inCoins Complexity.NUPPT.inParam Complexity.NUPPT.layout Complexity.NUPPT.ofPolyTime Complexity.NUPPT.ofPolyTimeUniform Complexity.NUPPT.output Complexity.NUPPT.runAt Complexity.NUPPT.timeBound Complexity.PolyTimeComputable Complexity.pairFstD Complexity.pairSndD TCSlib.Cryptography.Collection.glPad TCSlib.Cryptography.Collection.glPadSampleFun TCSlib.Cryptography.Collection.index TCSlib.Cryptography.PermCollection.glPad TCSlib.Cryptography.decodeFin Turing.Action.apply Turing.Cfg.init Turing.Cfg.inputSymbol Turing.Cfg.workTapeSymbols Turing.FinTM.ComputesFunInTime Turing.FinTM.ComputesInTime Turing.MultiTapeTM.ComputesInTimeAndSpace Turing.MultiTapeTM.initCfg Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.spaceUsed Turing.MultiTapeTM.spaceUsedByTape Turing.MultiTapeTM.step Turing.MultiTapeTM.visitedByTapeHead Turing.moveInputPos Turing.pairDecode Turing.pairEncode  TCSlib.Cryptography.PermCollection.glPad_domEquiv

variable (P : PermCollection) (m : PolyExpr)
  (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
  (i : List Bool)

/-! ## Controls: the old reading (product domain and permutation read directly) -/

-- C1 (domain read as a product): the first component of an element of the padded domain.
example (z : (P.glPad m henc).D i) : P.D i := z.1

-- C2 (domain read as a product): an element of the padded domain built as a pair.
example (x : P.D i) (r : Fin (P.encD i default).length → Bool) : (P.glPad m henc).D i := (x, r)

-- C3 (permutation read directly): `perm'` is `perm_i × id` applied to the padded element
-- read as a pair, by unfolding.
example (z : (P.glPad m henc).D i) :
    (P.glPad m henc).perm i z = (P.perm i).prodCongr (Equiv.refl _) z :=
  rfl

-- C4 (permutation equation by unfolding): the conjugation equation of P3, proved by `rfl`.
example : (P.glPad m henc).perm i = ((P.glPad_domEquiv m henc i).trans
    ((P.perm i).prodCongr (Equiv.refl _))).trans (P.glPad_domEquiv m henc i).symm :=
  rfl

-- C5 (`glPad_domEquiv_apply`, the identity on the definition): `e z = z` is well typed only by
-- reading `(P.glPad m henc).D i` as the product.
example (z : (P.glPad m henc).D i) : P.glPad_domEquiv m henc i z = z :=
  P.glPad_domEquiv_apply m henc i z
