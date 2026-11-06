| `NUPPT.inAdvice_eq` | Cx/Randomized/Closure.lean:119 | `(z : List Bool) : inAdvice z = pairSndD (pairFstD z)` |
| `NUPPT.inArg_eq` | Cx/Randomized/Closure.lean:116 | `(z : List Bool) : inArg z = pairSndD (pairFstD (pairFstD z))` |
| `NUPPT.inCoins_eq` | Cx/Randomized/Closure.lean:122 | `(z : List Bool) : inCoins z = pairSndD z` |
| `NUPPT.inParam_eq` | Cx/Randomized/Closure.lean:113 | `(z : List Bool) : inParam z = pairFstD (pairFstD (pairFstD z))` |
| `NUPPT.layout_eq` | Cx/Randomized/Closure.lean:109 | `(u y α r : List Bool) : layout u y α r = pairEncode (pairEncode (pairEncode u y) α) r` |
| `NUPPT.advInput_eq` | Cx/Randomized/PPT.lean:206 | `(n : ℕ) (y : List Bool) : advInput n y = pairEncode (List.replicate n true) y` |
| `NUPPT.coinLen_eq` | Cx/Randomized/PPT.lean:163 | `(n : ℕ) : A.coinLen n = A.coins.eval n` |
| `NUPPT.runAtL_eq` | Cx/Randomized/PPT.lean:230 | `(n : ℕ) (y r : List Bool) : A.runAtL n y r = A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)` |
| `NUPPT.distinguisherL_eq` | C/Asymptotic/Adversary.lean:137 | `(A : NUPPT) (n : ℕ) (w : List Bool) (r : A.Coins n) : A.distinguisherL n w r = decide (A.runAt n w r = [true])` |
| `decodeFin_eq` | C/Asymptotic/Adversary.lean:82 | `(ℓ : ℕ) (w : List Bool) : decodeFin ℓ w = if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none` |
| `Collection.hardCore_iff` | C/Asymptotic/Collections.lean:255 | `(F : Collection) (h : ∀ i, F.D i → Bool) : F.HardCore h ↔ (∃ H : List Bool → List Bool, PolyTimeComputable H ∧ ∀ i x, H (pairEncode i (F.encD i x))...` |
| `Collection.index_eq` | C/Asymptotic/Collections.lean:185 | `(F : Collection) (n : ℕ) (r : F.gen.Coins n) : F.index n r = pairFstD (F.gen.runAt n [] r)` |
| `Collection.invProbAt_eq` | C/Asymptotic/Collections.lean:221 | `(F : Collection) (A : NUPPT) (n : ℕ) : F.invProbAt A n = uexp fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n => ∃ x', F.decD ...` |
| `Collection.sampleClose_iff` | C/Asymptotic/Collections.lean:202 | `(F : Collection) (δ : ℕ → ℝ) : F.SampleClose δ ↔ ∀ n (r : F.gen.Coins n), StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.run...` |
| `FunFamily.toCollection_decD` | C/Asymptotic/Collections.lean:507 | `(i w : List Bool) : (𝓕.toCollection F hF hspec).decD i w = (decodeFin (𝓕.inLen.eval i.length) w).map (𝓕.toCollection_domEquiv F hF hspec i).symm` |
| `FunFamily.toCollection_domEquiv` | C/Asymptotic/Collections.lean:493 | `(i : List Bool) : (𝓕.toCollection F hF hspec).D i ≃ (Fin (𝓕.inLen.eval i.length) → Bool)` |
| `FunFamily.toCollection_domEquiv_apply` | C/Asymptotic/Collections.lean:497 | `(i : List Bool) (x : (𝓕.toCollection F hF hspec).D i) : 𝓕.toCollection_domEquiv F hF hspec i x = x` |
| `FunFamily.toCollection_encD` | C/Asymptotic/Collections.lean:502 | `(i : List Bool) (x : (𝓕.toCollection F hF hspec).D i) : (𝓕.toCollection F hF hspec).encD i x = List.ofFn (𝓕.toCollection_domEquiv F hF hspec i x)` |
| `FunFamily.toCollection_eval` | C/Asymptotic/Collections.lean:528 | `(z : List Bool) : (𝓕.toCollection F hF hspec).eval z = F (pairEncode (List.replicate (pairFstD z).length true) (pairSndD z))` |
| `FunFamily.toCollection_f` | C/Asymptotic/Collections.lean:515 | `(i : List Bool) (x : (𝓕.toCollection F hF hspec).D i) : (𝓕.toCollection F hF hspec).f i x = List.ofFn (𝓕.f i.length (𝓕.toCollection_domEquiv F hF h...` |
| `FunFamily.toCollection_gen` | C/Asymptotic/Collections.lean:520 | `: (𝓕.toCollection F hF hspec).gen = NUPPT.ofPolyTimeUniform (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)` |
| `FunFamily.toCollection_sample_eq` | C/Asymptotic/Collections.lean:524 | `: (𝓕.toCollection F hF hspec).sample = NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inCoins 𝓕.inLen` |
| `PermCollection.oneWay_iff` | C/Asymptotic/Collections.lean:344 | `(P : PermCollection) : P.OneWay ↔ P.toCollection.OneWay` |
| `TrapdoorCollection.oneWay_iff` | C/Asymptotic/Collections.lean:384 | `(T : TrapdoorCollection) : T.OneWay ↔ T.toCollection.OneWay` |
| `TrapdoorCollection.toCollection_domEquiv` | C/Asymptotic/Collections.lean:391 | `(T : TrapdoorCollection) (i : List Bool) : T.toCollection.D i ≃ T.D i` |
| `TrapdoorCollection.toCollection_domEquiv_apply` | C/Asymptotic/Collections.lean:395 | `(T : TrapdoorCollection) (i : List Bool) (x : T.toCollection.D i) : T.toCollection_domEquiv i x = x` |
| `PrivateKeyScheme.encodeList_nil` | C/Asymptotic/Encryption.lean:229 | `: encodeList [] = []` |
| `PrivateKeyScheme.multiEncDist_apply` | C/Asymptotic/Encryption.lean:233 | `(S : PrivateKeyScheme) (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool) (r : S.gen.Coins n × (Fin (q + 1) → S.enc.Coins n)) : S.multiEncDist n q m r = en...` |
| `PrivateKeyScheme.multiMessageSecure_iff` | C/Asymptotic/Encryption.lean:241 | `(S : PrivateKeyScheme) : S.MultiMessageSecure ↔ ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m m' : Fin (q.eval n + 1) → Fin n → ...` |
| `Ensemble.pseudorandom_iff` | C/Asymptotic/Ensembles.lean:197 | `(X : Ensemble ℓ) : X.Pseudorandom ↔ Indist X (uniform ℓ)` |
| `Ensemble.uniform_X` | C/Asymptotic/Ensembles.lean:161 | `(ℓ : PolyExpr) (n : ℕ) (x : (uniform ℓ).σ n) : (uniform ℓ).X n x = cast (uniform_σ ℓ n) x` |
| `Ensemble.uniform_σ` | C/Asymptotic/Ensembles.lean:157 | `(ℓ : PolyExpr) (n : ℕ) : (uniform ℓ).σ n = (Fin (ℓ.eval n) → Bool)` |
| `GGMRed.histEnc_eq` | C/Asymptotic/GGMReduction.lean:144 | `{ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : histEnc h = h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p....` |
| `GGMRed.queryOf_eq` | C/Asymptotic/GGMReduction.lean:97 | `(ℓ₁ : ℕ) (w : List Bool) : queryOf ℓ₁ w = match pairDecode w with` |
| `GGMRed.verdictOf_eq` | C/Asymptotic/GGMReduction.lean:107 | `(w : List Bool) : verdictOf w = decide (w = [true, true])` |
| `GGMRed.coinStr_eq` | C/Asymptotic/GGMReductionEval.lean:249 | `: coinStr d = List.ofFn ((FunFamily.blocks (q.eval n) n).symm d.W.1) ++ (List.ofFn ((FunFamily.blocks (q.eval n) (2 * n)).symm fun k => splitHalves...` |
| `Collection.glPad_decD` | C/Asymptotic/HardCoreCollection.lean:220 | `(m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i w : List Bool) : (F.glPad m ...` |
| `Collection.glPad_domEquiv` | C/Asymptotic/HardCoreCollection.lean:195 | `(m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i : List Bool) : (F.glPad m he...` |
| `Collection.glPad_domEquiv_apply` | C/Asymptotic/HardCoreCollection.lean:203 | `(m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i : List Bool) (z : (F.glPad m...` |
| `Collection.glPad_encD` | C/Asymptotic/HardCoreCollection.lean:210 | `(m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i : List Bool) (z : (F.glPad m...` |
| `Collection.glPad_eval` | C/Asymptotic/HardCoreCollection.lean:248 | `(m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (w : List Bool) : (F.glPad m he...` |
| `Collection.glPad_f_domEquiv` | C/Asymptotic/HardCoreCollection.lean:231 | `(m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) (i : List Bool) (z : (F.glPad m...` |
| `Collection.glPad_sample` | C/Asymptotic/HardCoreCollection.lean:241 | `(m : PolyExpr) (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)), (F.encD (F.index n r) x).length = m.eval n) : (F.glPad m henc).sample = NUP...` |
| `PermCollection.glPad_domEquiv` | C/Asymptotic/HardCoreCollection.lean:361 | `(P : PermCollection) (m : PolyExpr) (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) (i : List ...` |
| `PermCollection.glPad_domEquiv_apply` | C/Asymptotic/HardCoreCollection.lean:368 | `(P : PermCollection) (m : PolyExpr) (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) (i : List ...` |
| `PermCollection.glPad_perm` | C/Asymptotic/HardCoreCollection.lean:374 | `(P : PermCollection) (m : PolyExpr) (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n) (i : List ...` |
| `TrapdoorCollection.glPad_domEquiv` | C/Asymptotic/HardCoreCollection.lean:425 | `(T : TrapdoorCollection) (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) (i : L...` |
| `TrapdoorCollection.glPad_domEquiv_apply` | C/Asymptotic/HardCoreCollection.lean:432 | `(T : TrapdoorCollection) (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) (i : L...` |
| `TrapdoorCollection.glPad_inv` | C/Asymptotic/HardCoreCollection.lean:438 | `(T : TrapdoorCollection) (m : PolyExpr) (henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = m.eval n) : (T.g...` |
| `FunFamily.easy_iff` | C/Asymptotic/OneWay.lean:115 | `(𝓕 : FunFamily) : 𝓕.Easy ↔ ∃ F : List Bool → List Bool, PolyTimeComputable F ∧ ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofF...` |
| `firstHit_eq` | C/Asymptotic/Sampling.lean:466 | `(xs : Fin T → α) : firstHit E xs = (List.finRange T).findSome? fun t => if E (xs t) then some (xs t) else none` |
| `statClose_iff` | C/Asymptotic/Sampling.lean:128 | `(X : σ → γ) (Y : τ → γ) (δ : ℝ) : StatClose X Y δ ↔ ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ` |
| `negligible_iff` | C/Foundations/Negligible.lean:62 | `(μ : ℕ → ℝ) : Negligible μ ↔ ∀ c : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, |μ n| < 1 / (n : ℝ) ^ c` |
| `HardcoreBit.pushesUniform_iff` | C/HardcoreBit/Basic.lean:177 | `(π : Ω → γ) : PushesUniform π ↔ ∀ F : γ → ℝ, uexp (fun ω => F (π ω)) = uexp F` |
| `OneWay.prodFun_apply` | C/OneWayFunctions/Amplification.lean:79 | `(f : α → β) (q : ℕ) (xs : Fin q → α) (i : Fin q) : prodFun f q xs i = f (xs i)` |
| `OneWay.yaoTry_eq` | C/OneWayFunctions/Amplification.lean:96 | `(f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (y : β) (c : Fin q × (Fin q → α) × ρ) : yaoTry f B y c = B (Function.update (prodFun f q c.2.1) c.1...` |
| `prgAdv_eq` | C/Pseudorandom/Generators.lean:77 | `[Fintype γ] (G : σ → γ) (D : γ → ρ → Bool) : prgAdv G D = distAdv G (id : γ → γ) D` |
| `ZK_iff` | C/ZeroKnowledge/Defs.lean:166 | `(π : Protocol) (R : List Bool → List Bool → Prop) : ZK π R ↔ ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT)...` |
| `encColoring_eq` | C/ZeroKnowledge/Encoding.lean:237 | `{n : ℕ} (c : Fin n → Fin 3) : encColoring c = List.ofFn fun k : Fin (n * 2) => if (finProdFinEquiv.symm k).2 = 0 then decide ((c (finProdFinEquiv.s...` |
| `getD_encColoring` | C/ZeroKnowledge/Encoding.lean:244 | `{n : ℕ} (c : Fin n → Fin 3) (i : Fin n) (b : Fin 2) : (encColoring c).getD (finProdFinEquiv (i, b)) false = if b = 0 then decide ((c i).val / 2 = 1...` |
| `getD_encColoring_two_mul` | C/ZeroKnowledge/Encoding.lean:257 | `{n : ℕ} (c : Fin n → Fin 3) (i : Fin n) : (encColoring c).getD (2 * i) false = decide ((c i).val / 2 = 1)` |
| `getD_encColoring_two_mul_add_one` | C/ZeroKnowledge/Encoding.lean:264 | `{n : ℕ} (c : Fin n → Fin 3) (i : Fin n) : (encColoring c).getD (2 * i + 1) false = decide ((c i).val % 2 = 1)` |
| `Protocol.viewV_withV` | C/ZeroKnowledge/Interaction.lean:415 | `(π : Protocol) (V' : Strategy) (x y z : List Bool) (r : (π.withV V').ExecCoins (π.withV V').P x) : (π.withV V').viewV x y z r = ⟨x, z, List.ofFn r....` |
| `Strategy.coinLen_eq` | C/ZeroKnowledge/Interaction.lean:126 | `(S : Strategy) (n : ℕ) : S.coinLen n = S.coins.eval n` |
| `Strategy.efficient_iff` | C/ZeroKnowledge/Interaction.lean:181 | `(S : Strategy) : S.Efficient ↔ ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧ ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist` |
| `View.encode_mk` | C/ZeroKnowledge/Interaction.lean:294 | `(x z r : List Bool) (received : List (List Bool)) : View.encode ⟨x, z, r, received⟩ = pairEncode (pairEncode x z) (pairEncode r (Strategy.encodeMsg...` |
| `ProperColoring_iff` | C/ZeroKnowledge/ThreeColoring/Language.lean:90 | `{n : ℕ} (G : Graph n) (c : Fin n → Fin 3) : ProperColoring G c ↔ ∀ u v, G u v = true → c u ≠ c v` |
| `R3COL_iff` | C/ZeroKnowledge/ThreeColoring/Language.lean:126 | `(x y : List Bool) : R3COL x y ↔ ∃ (n : ℕ) (G : Graph n) (c : Fin n → Fin 3), x = encGraph G ∧ y = encColoring c ∧ ProperColoring G c` |
| `sampleIdx_eq_rejectionSample` | C/ZeroKnowledge/ThreeColoring/Language.lean:306 | `(m k T : ℕ) (r : List Bool) : sampleIdx m k T r = rejectionSample m k T fun t j => r.getD (t * k + j) false` |
| `sampleIdx_ofFn_eq_rejectionSample` | C/ZeroKnowledge/ThreeColoring/Language.lean:381 | `(m k T : ℕ) (r : Fin (T * k) → Bool) : sampleIdx m k T (List.ofFn r) = rejectionSample m k T fun t j => r (finProdFinEquiv (t, j))` |
| `colCoinSlice_eq` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:491 | `(c t : ℕ) (r : List Bool) : colCoinSlice c t r = (r.drop (t * c)).take c` |
| `colCommit_eq` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:125 | `(Com : List Bool → List Bool) (n ℓn : ℕ) (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) : colCommit Com n ℓn c' r = multiCom Com (fun i => padCol...` |
| `colIterations_eq` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:500 | `(x : List Bool) : colIterations x = (decGraph x).1 * edgeCount (decGraph x).2` |
| `colOpen_eq` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:137 | `{n ℓn : ℕ} (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) (p : Fin n × Fin n) : colOpen c' r p = pairEncode (pairEncode (encColor (c' p.1)) (List...` |
| `colProtocol_P` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:469 | `(Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProtocol Com ℓ).P = colProver Com ℓ` |
| `colProtocol_V` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:473 | `(Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProtocol Com ℓ).V = colVerifier Com ℓ` |
| `colProtocol_rounds` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:477 | `(Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProtocol Com ℓ).rounds = .const 3` |
| `colProtocol_verifierFirst` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:481 | `(Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProtocol Com ℓ).verifierFirst = false` |
| `colProver_coins` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:436 | `(Com : List Bool → List Bool) (ℓ : PolyExpr) : (colProver Com ℓ).coins = .add (.mul (.const 3) .var) (.mul .var ℓ)` |
| `colProver_next_cons` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:716 | `(Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool} {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (hm : 0 < edgeCount G) (y r w : List ...` |
| `colProver_next_cons_of_edgeCount_eq_zero` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:726 | `(Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool} {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (hm : edgeCount G = 0) (y r w : List ...` |
| `colProver_next_nil` | C/ZeroKnowledge/ThreeColoring/Protocol.lean:707 | `(Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool} {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (y r : List Bool) : (colProver Com ℓ)...` |
| `TCSlib.InformationTheory.statDist_eq` | IT/StatisticalDistance.lean:49 | `(p q : FinDist α) : statDist p q = (1 / 2) * ∑ a, |p a - q a|` |
