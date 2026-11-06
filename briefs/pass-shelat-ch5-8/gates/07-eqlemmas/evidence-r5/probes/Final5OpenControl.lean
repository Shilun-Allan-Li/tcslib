import TCSlib.Cryptography.ZeroKnowledge.NP
import TCSlib.Cryptography.ZeroKnowledge.Encryption
import TCSlib.Cryptography.Candidates.Factoring
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Asymptotic.Universal
import TCSlib.Cryptography.Asymptotic.PublicKey
import TCSlib.Cryptography.Asymptotic.HardCoreClaims
import TCSlib.Cryptography.Asymptotic.HardCorePermutation
import TCSlib.Cryptography.Asymptotic.GGMReductionEval
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol

set_option autoImplicit false

open TCSlib.Cryptography TCSlib.Cryptography.Candidates Complexity Turing NumberTheory


/-! final5 probe (control): the old readings; each must fail sealed and pass open. -/

-- C1 old hard-core hypothesis: `HardCore P.toFunFamily h` with `h` on `{0,1}^n`
example (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (hh : HardCore P.toFunFamily h) :
    True := trivial

-- C2 old glHalf_f_even: `glPad` of `P.toFunFamily` applied to `z : {0,1}^{m+m}`
example (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) :
    P.glHalf.f (m + m) z = P.toFunFamily.glPad.f m z := sorry

-- C3 old thm_87_3_1 argument: `A` on `Fin.appendEquiv … y`
example (𝓕 : FunFamily) {ρ : Type} (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool)
    (y : (Fin (𝓕.outLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool)) (r : ρ) : Bool :=
  A (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) r

-- C4 old bitCom_false_eq_owpGenPRG: output index `i : Fin (n + 1)`
example (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (r : Fin n → Bool)
    (i : Fin (n + 1)) : Bool := (owpGenPRG P h).G n r i

-- C5 old oddCoins target: `Fin.appendEquiv` lands in the wrapper's coins
example (A : NUPPT) {pre post : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (hpost : PolyTimeComputable post) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ)
    (w : Fin (p.eval n + A.coinLen n) → Bool) : (A.wrap hpre hpost β b hβ p).Coins n := w

-- C6 old bitwise coins: `coinBlocks` lands in the bitwise encryptor's coins
example (S : BitPublicKeyScheme) (n : ℕ) (v : Fin n → S.enc.Coins n) : S.bitwise.enc.Coins n :=
  coinBlocks n (S.enc.coinLen n) v

-- C7 old predCoins body
example (D : NUPPT) (flip : Bool) (n : ℕ) : Bool × D.Coins n ≃ (tdpPredictor D flip).Coins n :=
  ((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (Equiv.refl _)).trans
    (Fin.appendEquiv 1 (D.coinLen n))

-- C8 old ofFn_fUniversal_f: `x : {0,1}^n` as an input of `fUniversal c`
example (c : EffectiveMachineCode) (n : ℕ) (x : Fin n → Bool) : List Bool :=
  List.ofFn ((fUniversal c).f n x)

-- C9 old vTapeSplit / giBitEquiv / giRepCoins bodies
example (N : ℕ) : Bool × (Fin (1 * (N + 1) ^ 2) → Bool) ≃ GI.gniProtocol.V.Coins N :=
  GI.tapeSplit (1 * (N + 1) ^ 2)
example (N : ℕ) : Bool ≃ GI.giProtocol.V.Coins N := (Equiv.funUnique (Fin 1) Bool).symm
example (P' : Strategy) (x : List Bool) :
    (Fin x.length → Bool) × P'.Coins x.length ≃ GI.giProtocolRep.ExecCoins P' x :=
  Equiv.prodComm _ _

-- C10 old Factoring readings
example (A : NUPPT) (n : ℕ) (ys : Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool))
    (r : A.Coins n) : Option (Fin ((fmult.prod fmultBlocks).inLen.eval n) → Bool) :=
  A.inverter n ((fmult.prod fmultBlocks).inLen.eval n) ((fmult.prod fmultBlocks).outLen.eval n)
    ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm ys) r
example (n : ℕ) : fmultWeakPoly.eval n = 8 * (n + 1) ^ 2 := rfl
example (n : ℕ) : (fmult.prod fmultBlocks).inLen.eval n = 4 * n ^ 3 * (2 * n) := rfl
example (m : ℕ) (z : DistinctPrimes m) :
    encodeDistinctPrimes m z = pairEncode (natToList m z.1.1.1) (natToList m z.1.2.1) := rfl

-- C11 col-b readings by `rfl`
example (w : List Bool) (i : ℕ) : msgAt w i = pairFstD (pairSndD^[i] w) := rfl
example (m : ℕ) (w : List Bool) : edgeIdxOfMsg m w = w.length % m := rfl

-- C12 #195 readings by `rfl`
example (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) : (PRG.expand G ℓ hℓ).stretch = ℓ := rfl
example (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (D : NUPPT) : Prop :=
  Negligible fun n => prgAdv ((PRG.oneBit G).G n) (D.distinguisher n (n + 1))
example (D : NUPPT) (q : PolyExpr) (n : ℕ) :
    (GGMRed.coinPoly D q).eval n = q.eval n * n + (q.eval n * (2 * n) + D.coinLen n) := rfl
example (z : List Bool) (h : pairDecode z = none) : pairSndD z = [] := by
  rw [show pairSndD z = ((pairDecode z).map Prod.snd).getD [] from rfl, h]; rfl

-- C13 fac readings: yaoB by its body, Uniform by application
example (inLen outLen m : PolyExpr) (A' : NUPPT) (n : ℕ)
    (ys : Fin (m.eval n) → Fin (outLen.eval n) → Bool) (r : A'.Coins n) (j : Fin (m.eval n)) :
    OneWay.yaoB inLen outLen m A' n ys r j = OneWay.padTrue (inLen.eval n)
      ((A'.runAt n (List.ofFn ((OneWay.blocksE (m.eval n) (outLen.eval n)).symm ys)) r).drop
        (j * inLen.eval n)) := rfl
example (A : NUPPT) (h : A.Uniform) (n : ℕ) : A.advice n = [] := h n

-- C14 coin readings earlier in the round
example (G : Collection) (n : ℕ) :
    (Fin (G.gen.coins.eval n + G.sample.coins.eval n) → Bool) ≃
      (Fin (G.gen.coinLen n + G.sample.coinLen n) → Bool) := Equiv.refl _
example (D : OneWay.YaoMachine.Data) (n : ℕ) :
    (Fin ((OneWay.YaoMachine.ρP D).eval n) → Bool) ≃
      (Fin (n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n)) → Bool) :=
  Equiv.refl _

-- C15 #195: `PRG.expand_G` at an index typed by the stretch
example (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr) (hℓ : ∀ n, n < ℓ.eval n)
    (n : ℕ) (s : Fin n → Bool) (i : Fin ((PRG.expand G ℓ hℓ).stretch.eval n)) :
    (PRG.expand G ℓ hℓ).G n s i = G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) :=
  PRG.expand_G G ℓ hℓ n s i

-- C16 rsa: the old `show` proof of rsaCollection_index
example (H : ArithmeticFP) (n : ℕ) (r : (rsaCollection H).gen.Coins n) :
    (rsaCollection H).index n r = rsaIndexOf _ (rsaGenParams n (List.ofFn r)) := by
  show pairFstD ((rsaGen H).runAt n [] r) = _
  rw [rsaGen_runAt, rsaGenOut, pairFstD_pairEncode]
