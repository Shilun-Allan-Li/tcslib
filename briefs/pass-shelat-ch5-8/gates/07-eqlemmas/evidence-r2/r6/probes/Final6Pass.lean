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

attribute [local irreducible] Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTime
  Complexity.NUPPT.ofPolyTimeUniform Complexity.NUPPT.wrap Complexity.NUPPT.Uniform
  TCSlib.Cryptography.PermFamily.toFunFamily TCSlib.Cryptography.FunFamily.glPad
  TCSlib.Cryptography.FunFamily.ofString TCSlib.Cryptography.FunFamily.prod
  TCSlib.Cryptography.owpGenPRG TCSlib.Cryptography.PRG.oneBit TCSlib.Cryptography.PRG.expand
  TCSlib.Cryptography.Strategy.coinLen TCSlib.Cryptography.GI.gniProtocol
  TCSlib.Cryptography.GI.gniProtocolRep TCSlib.Cryptography.GI.giProtocol
  TCSlib.Cryptography.GI.giProtocolRep Complexity.PolyExpr.normal TCSlib.Cryptography.OneWay.yaoB
  TCSlib.Cryptography.msgAt TCSlib.Cryptography.edgeIdxOfMsg Complexity.pairFstD Complexity.pairSndD
  TCSlib.Cryptography.GGMRed.coinPoly TCSlib.Cryptography.GGMRed.ggmRedMachine
  TCSlib.Cryptography.tdpPredictor TCSlib.Cryptography.Candidates.encodeDistinctPrimes
  TCSlib.Cryptography.OneWay.YaoMachine.ρP
  TCSlib.Cryptography.Collection.index TCSlib.Cryptography.OneWayPermutation
  TCSlib.Cryptography.FunFamily.Easy TCSlib.Cryptography.HardcoreBit.perfectInverter
  TCSlib.Cryptography.HardcoreBit.majorityInverter TCSlib.Cryptography.HardcoreBit.guessInverter
  TCSlib.Cryptography.owpPredictor

/-! final5 probe (pass): every reading through the published lemmas, sealed. -/

-- P1 PermFamily.HardCore: permutation-form clauses and restated consumers
example (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (hh : P.HardCore h) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x] := hh.easy
example (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (hh : P.HardCore h) (A : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, predProb (P.f n) (h n) (A.predictor n n) ≤ 1 / 2 + ε n :=
  hh.hard A
example (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (hP : OneWayPermutation P)
    (hh : P.HardCore h) : (owpGenPRG P h).Secure := owp_hardcore_prg P h hP hh
example (h : ∃ P : PermFamily, OneWayPermutation P) :
    ∃ (P : PermFamily) (b : ∀ n, (Fin n → Bool) → Bool), OneWayPermutation P ∧ P.HardCore b :=
  exists_owp_hardCore h

-- P2 glPad equivalences (FunFamily and PermFamily forms)
example (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) :
    P.glHalf.f (m + m) z =
      P.glPad_outEquiv m (P.toFunFamily.glPad.f m ((P.glPad_inEquiv m).symm z)) :=
  PermFamily.glHalf_f_even P m z
example (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) :
    glHalfBit (m + m) z = P.toFunFamily.glBit m ((P.glPad_inEquiv m).symm z) := glHalfBit_even P m z
example (𝓕 : FunFamily) {ρ : Type} [Fintype ρ] (n : ℕ)
    (A : (Fin (𝓕.glPad.outLen.eval n) → Bool) → ρ → Bool)
    (h : predProb (𝓕.glPad.f n) (𝓕.glBit n) A = 1) :
    invProb (𝓕.glPad.f n) (𝓕.glInverter n (HardcoreBit.perfectRecover
      fun y r => A ((𝓕.glPad_outEquiv n).symm
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y)) r)) = 1 := thm_87_3_1 𝓕 n A h
example (𝓕 : FunFamily) (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) :
    𝓕.glPad_outEquiv n (𝓕.glPad.f n ((𝓕.glPad_inEquiv n).symm (Fin.append x r))) =
      Fin.append (𝓕.f n x) r := 𝓕.glPad_f_equiv n x r

-- P3 owpGenPRG_outEquiv
example (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (r : Fin n → Bool)
    (i : Fin (n + 1)) :
    bitCom (P.f n) (h n) false r i = owpGenPRG_outEquiv P h n ((owpGenPRG P h).G n r) i :=
  bitCom_false_eq_owpGenPRG P h n r i

-- P4 wrapCoinsEquiv
example (A : NUPPT) {pre post : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (hpost : PolyTimeComputable post) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ)
    (w : Fin (p.eval n + A.coinLen n) → Bool) :
    List.ofFn ((A.wrapCoinsEquiv hpre hpost β b hβ p n).symm w) = List.ofFn w :=
  A.wrapCoinsEquiv_symm_ofFn hpre hpost β b hβ p n w

-- P5 bitwiseEncCoins, predCoins
example (S : BitPublicKeyScheme) (n : ℕ) (v : Fin n → S.enc.Coins n) :
    List.ofFn (S.bitwiseEncCoins n v) = List.ofFn (coinBlocks n (S.enc.coinLen n) v) :=
  S.bitwiseEncCoins_ofFn n v
example (D : NUPPT) (flip : Bool) (n : ℕ) (c : Bool) (ρ : D.Coins n) :
    List.ofFn (predCoins D flip n (c, ρ)) = c :: List.ofFn ρ := ofFn_predCoins D flip n c ρ

-- P6 ofString / fUniversal input space
example (c : EffectiveMachineCode) (n : ℕ) : (fUniversal c).inLen.eval n = n :=
  fUniversal_inLen_eval c n
example (c : EffectiveMachineCode) (n : ℕ) (x : Fin ((fUniversal c).inLen.eval n) → Bool) :
    List.ofFn ((fUniversal c).f n x) =
      (fUniversalStr c (List.ofFn x) ++ List.replicate (univOutLen.eval n) false).take
        (univOutLen.eval n) := ofFn_fUniversal_f c n x

-- P7 GI verifier tapes
example (N : ℕ) : GI.gniProtocol.V.coinLen N = 1 + 1 * (N + 1) ^ 2 := GI.gniProtocol_V_coinLen N
example (N : ℕ) (b : Bool) (t : Fin (1 * (N + 1) ^ 2) → Bool) :
    List.ofFn (GI.vTapeSplit N (b, t)) = b :: List.ofFn t := GI.ofFn_vTapeSplit N b t
example (N : ℕ) (b : Bool) : List.ofFn (GI.giBitEquiv N b) = [b] := GI.ofFn_giBitEquiv N b
example (N : ℕ) (b : Fin N → Bool) (ts : Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) :
    List.ofFn (GI.gniTapes N (b, ts)) =
      List.ofFn (GI.blocksEquiv N (1 + 1 * (N + 1) ^ 2) (fun j => GI.tapeSplit _ (b j, ts j))) :=
  GI.gniTapes_apply N b ts

-- P8 Factoring: prodInverter_eq, re-pointed lengths, re-pointed proofs (sealed)
example (A : NUPPT) (n : ℕ) (ys : Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool))
    (r : A.Coins n) :
    prodInverter A n ys r = FunFamily.blocks (fmultBlocks.eval n) (2 * n)
      ((A.inverter n (fmultBlocks.eval n * (2 * n)) (fmultBlocks.eval n * (2 * n))
        ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm ys) r).getD (fun _ => false)) :=
  prodInverter_eq A n ys r
example (n : ℕ) : fmultWeakPoly.eval n = 8 * (n + 1) ^ 2 := by
  unfold fmultWeakPoly
  exact PolyExpr.eval_normal 8 2 n
example (n : ℕ) : (fmult.prod fmultBlocks).inLen.eval n = 4 * n ^ 3 * (2 * n) := by
  rw [FunFamily.prod_inLen, PolyExpr.eval_mul, eval_fmultBlocks, fmult_inLen]
example (m : ℕ) (hm : 2 ≤ m) (a b : List Bool) :
    ∃ z : DistinctPrimes m, samplePairOut m hm a b = encodeDistinctPrimes m z := by
  unfold samplePairOut
  split_ifs with h
  · exact ⟨⟨(⟨⟨listToNat a, h.2.2.2.1⟩, h.1⟩, ⟨⟨listToNat b, h.2.2.2.2⟩, h.2.1⟩), h.2.2.1⟩,
      by rw [encodeDistinctPrimes_eq, DistinctPrimes.p_eq, DistinctPrimes.q_eq]⟩
  · exact ⟨_, rfl⟩
example (H : ArithmeticFP) (n : ℕ) (r : (factoringCollection H).gen.Coins n) :
    (factoringCollection H).index n r = List.replicate n true := by
  rw [Collection.index_eq]
  exact (congrArg pairFstD (factoringGen_runAt n r)).trans (pairFstD_pairEncode _ _)

-- P9 col-b equations
example (w : List Bool) (i : ℕ) : msgAt w i = pairFstD (pairSndD^[i] w) := msgAt_eq w i
example (m : ℕ) (w : List Bool) : edgeIdxOfMsg m w = w.length % m := edgeIdxOfMsg_eq m w

-- P10 #195's requests
example (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
    (hℓ : ∀ n, n < ℓ.eval n) : (PRG.expand G ℓ hℓ).stretch = ℓ := PRG.expand_stretch G ℓ hℓ
example (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) :
    (PRG.oneBit G).Secure ↔
      (∃ F : List Bool → List Bool, PolyTimeComputable F ∧
        ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s)) ∧
      ∀ D : NUPPT, Negligible fun n => prgAdv (G n) (D.distinguisher n (n + 1)) :=
  PRG.oneBit_secure_iff G
example (D : NUPPT) (q : PolyExpr) (n : ℕ) :
    (GGMRed.coinPoly D q).eval n = q.eval n * n + (q.eval n * (2 * n) + D.coinLen n) :=
  GGMRed.coinPoly_eval D q n
example {E : List Bool → List Bool} (hE : PolyTimeComputable E) (D : NUPPT) (q : PolyExpr)
    (i j : ℕ → ℕ) (n : ℕ) (c : (GGMRed.ggmRedMachine hE D q i j).Coins n) :
    List.ofFn (GGMRed.ggmRedMachine_coinsEquiv hE D q i j n c) = List.ofFn c :=
  GGMRed.ggmRedMachine_coinsEquiv_ofFn hE D q i j n c
example (z : List Bool) (h : pairDecode z = none) : pairSndD z = [] :=
  pairSndD_of_pairDecode_eq_none h
example (z : List Bool) (h : pairDecode z = none) : pairFstD z = [] :=
  pairFstD_of_pairDecode_eq_none h

-- P11 fac fill: yaoB, Uniform, blocks
example (inLen outLen m : PolyExpr) (A' : NUPPT) (n : ℕ)
    (ys : Fin (m.eval n) → Fin (outLen.eval n) → Bool) (r : A'.Coins n) (j : Fin (m.eval n)) :
    OneWay.yaoB inLen outLen m A' n ys r j = OneWay.padTrue (inLen.eval n)
      ((A'.runAt n (List.ofFn ((OneWay.blocksE (m.eval n) (outLen.eval n)).symm ys)) r).drop
        (j * inLen.eval n)) := OneWay.yaoB_apply inLen outLen m A' n ys r j
example (A : NUPPT) (h : A.Uniform) (n : ℕ) : A.advice n = [] := h.advice_eq n
example (A : NUPPT) : A.Uniform ↔ ∀ n, A.advice n = [] := NUPPT.uniform_iff A
example (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) := FunFamily.blocks_apply q ℓ x i j

-- P12 coin equivalences earlier in the round
example (G : Collection) (n : ℕ) (r : Fin (G.gen.coins.eval n + G.sample.coins.eval n) → Bool) :
    List.ofFn (G.owfCoinsEquiv n r) = List.ofFn r := G.owfCoinsEquiv_ofFn n r
example (D : OneWay.YaoMachine.Data) (n : ℕ) (r : Fin ((OneWay.YaoMachine.ρP D).eval n) → Bool) :
    List.ofFn (OneWay.YaoMachine.ρPEquiv D n r) = List.ofFn r := OneWay.YaoMachine.ρPEquiv_ofFn D n r

-- P13 #195: PRG.expand_G_stretch (index typed by the stretch)
example (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr) (hℓ : ∀ n, n < ℓ.eval n)
    (n : ℕ) (s : Fin n → Bool) (i : Fin ((PRG.expand G ℓ hℓ).stretch.eval n)) :
    (PRG.expand G ℓ hℓ).G n s i = G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) :=
  PRG.expand_G_stretch G ℓ hℓ n s i

-- P14 rsa: rsaCollection_index re-pointed (sealed)
example (H : ArithmeticFP) (n : ℕ) (r : (rsaCollection H).gen.Coins n) :
    (rsaCollection H).index n r = rsaIndexOf _ (rsaGenParams n (List.ofFn r)) := by
  have key : ∀ (g : NUPPT), g = rsaGen H → ∀ r : g.Coins n,
      pairFstD (g.runAt n [] r) = rsaIndexOf _ (rsaGenParams n (List.ofFn r)) := by
    rintro g rfl r
    rw [rsaGen_runAt, rsaGenOut, pairFstD_pairEncode]
  rw [Collection.index_eq]
  exact key _ (rsaCollection_gen H) r

/-! final6 additions (pass) -/

-- R1 prodInverter_eq (no length read)
example (A : NUPPT) (n : ℕ) (ys : Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) (r : A.Coins n) :
    (fmult.prod fmultBlocks).outLen.eval n = 4 * n ^ 3 * (2 * n) ∧
      prodInverter A n ys r = FunFamily.blocks (fmultBlocks.eval n) (2 * n)
        ((A.inverter n (fmultBlocks.eval n * (2 * n)) (fmultBlocks.eval n * (2 * n))
          ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm ys) r).getD (fun _ => false)) :=
  ⟨fmult_prod_outLen n, prodInverter_eq A n ys r⟩

-- R2 OneWayPermutation interface
example (P : PermFamily) (hP : OneWayPermutation P) :
    ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
      ∀ n (x : Fin n → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (P.f n x) :=
  hP.evaluator
example (P : PermFamily) (hP : OneWayPermutation P) : P.toFunFamily.glPad.StrongOneWay :=
  ((oneWayPermutation_iff P).1 hP).glPad

-- R3 ofString equations
example (f : List Bool → List Bool) (p : PolyExpr) (n : ℕ)
    (x : Fin ((FunFamily.ofString f p).inLen.eval n) → Bool)
    (i : Fin ((FunFamily.ofString f p).outLen.eval n)) :
    (FunFamily.ofString f p).f n x i = (f (List.ofFn x)).getD i false ∧
      (FunFamily.ofString f p).outLen.eval n = p.eval n :=
  ⟨FunFamily.ofString_f_apply f p n x i, FunFamily.ofString_outLen_eval f p n⟩

-- R4 HardcoreBit inverter equations, owpPredictor
example {n : ℕ} {β ρ : Type} [Fintype ρ] (A : β × (Fin n → Bool) → ρ → Bool) :
    HardcoreBit.perfectInverter A = HardcoreBit.glInverter (HardcoreBit.perfectRecover A) :=
  HardcoreBit.perfectInverter_eq A
example {α β ρ : Type} [Fintype α] [Fintype β] [Fintype ρ] (D : α × β × Bool → ρ → Bool) (flip : Bool) (y : α × β) (c : Bool × ρ) :
    owpPredictor D flip y c = xor (if D (y.1, y.2, c.1) c.2 then c.1 else !c.1) flip :=
  owpPredictor_apply D flip y c

-- R5 PermFamily glPad append lemmas
example (P : PermFamily) (m : ℕ) (x r : Fin m → Bool) :
    P.glPad_outEquiv m (P.toFunFamily.glPad.f m ((P.glPad_inEquiv m).symm (Fin.append x r))) =
      Fin.append (P.f m x) r := P.glPad_f_append m x r
example (P : PermFamily) (m : ℕ) (x r : Fin m → Bool) :
    P.toFunFamily.glBit m ((P.glPad_inEquiv m).symm (Fin.append x r)) = HardcoreBit.ip x r :=
  P.glBit_append m x r
