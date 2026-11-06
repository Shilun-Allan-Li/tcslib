import TCSlib.Cryptography.Candidates.Rabin

/-! Pre-ship probe (factoring-candidates fill brief): the rule-10 equation lemmas the targets'
sketches need and that are missing at the issue tree, each stated and checked here by `rfl`,
`Iff.rfl` or a one-line proof; and the three shared statements proposed in the brief (sorried,
elaboration only). Nothing here is added to TCSlib. -/

set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates
  TCSlib.Cryptography.NumberTheory

namespace ProbePrereqs

/-! ### Collections.lean -/

theorem Collection_sampleClose_iff (F : Collection) (δ : ℕ → ℝ) :
    F.SampleClose δ ↔ ∀ n (r : F.gen.Coins n),
      StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s))
        (fun x : F.D (F.index n r) => some x) (δ n) := Iff.rfl

theorem Collection_invProbAt_eq (F : Collection) (A : NUPPT) (n : ℕ) :
    F.invProbAt A n = uexp fun r : F.gen.Coins n =>
      uprob fun z : F.D (F.index n r) × A.Coins n =>
        ∃ x', F.decD (F.index n r)
            (A.runAt n (pairEncode (F.index n r) (F.f (F.index n r) z.1)) z.2) = some x' ∧
          F.f (F.index n r) x' = F.f (F.index n r) z.1 := rfl

theorem Collection_index_eq (F : Collection) (n : ℕ) (r : F.gen.Coins n) :
    F.index n r = pairFstD (F.gen.runAt n [] r) := rfl

theorem TrapdoorCollection_oneWay_iff (T : TrapdoorCollection) :
    T.OneWay ↔ T.toCollection.OneWay := Iff.rfl

/-! ### Sampling.lean -/

theorem statClose_iff {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) :
    StatClose X Y δ ↔ ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ :=
  Iff.rfl

/-! ### OneWay.lean, PPT.lean, Closure.lean -/

theorem FunFamily_easy_iff (𝓕 : FunFamily) :
    𝓕.Easy ↔ ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
      ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
        F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x) := Iff.rfl

theorem NUPPT_advInput_eq (n : ℕ) (y : List Bool) :
    NUPPT.advInput n y = pairEncode (List.replicate n true) y := rfl

theorem NUPPT_inParam_eq (z : List Bool) : NUPPT.inParam z = pairFstD (pairFstD (pairFstD z)) := rfl
theorem NUPPT_inArg_eq (z : List Bool) : NUPPT.inArg z = pairSndD (pairFstD (pairFstD z)) := rfl
theorem NUPPT_inAdvice_eq (z : List Bool) : NUPPT.inAdvice z = pairSndD (pairFstD z) := rfl
theorem NUPPT_inCoins_eq (z : List Bool) : NUPPT.inCoins z = pairSndD z := rfl

/-! ### Concrete.lean, Primality.lean, Amplification.lean -/

theorem encodeDistinctPrimes_eq (m : ℕ) (z : DistinctPrimes m) :
    encodeDistinctPrimes m z = pairEncode (natToList m z.p) (natToList m z.q) := rfl

theorem DistinctPrimes_p_eq {n : ℕ} (z : DistinctPrimes n) : z.p = ((z.1.1 : Fin (2 ^ n)) : ℕ) := rfl
theorem DistinctPrimes_q_eq {n : ℕ} (z : DistinctPrimes n) : z.q = ((z.1.2 : Fin (2 ^ n)) : ℕ) := rfl
theorem DistinctPrimes_default_p {n : ℕ} (hn : 2 ≤ n) : (DistinctPrimes.default hn).p = 2 := rfl
theorem DistinctPrimes_default_q {n : ℕ} (hn : 2 ≤ n) : (DistinctPrimes.default hn).q = 3 := rfl

theorem chunk_apply (T n : ℕ) (r : Fin (T * n) → Bool) (t : Fin T) (i : Fin n) :
    chunk T n r t i = r (finProdFinEquiv (t, i)) := by
  unfold chunk
  congr 1
  ext
  simp [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]

theorem yaoTry_eq {α β ρ : Type*} {q : ℕ} (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (y : β)
    (c : Fin q × (Fin q → α) × ρ) :
    OneWay.yaoTry f B y c = B (Function.update (OneWay.prodFun f q c.2.1) c.1 y) c.2.2 c.1 := rfl

theorem prodFun_apply {α β : Type*} (f : α → β) (q : ℕ) (xs : Fin q → α) (i : Fin q) :
    OneWay.prodFun f q xs i = f (xs i) := rfl

/-! ### Arithmetic.lean -/

theorem xgcdStr_pairEncode (a b : List Bool) :
    xgcdStr (pairEncode a b) = pairEncode (natToList b.length (Nat.gcd (listToNat a) (listToNat b)))
      (natToList b.length ((listToNat a : ZMod (listToNat b))⁻¹).val) := by
  unfold xgcdStr
  rw [pairFstD_pairEncode, pairSndD_pairEncode]

theorem divModStr_pairEncode (a b : List Bool) :
    divModStr (pairEncode a b) = pairEncode (natToList a.length (listToNat a / listToNat b))
      (natToList b.length (listToNat a % listToNat b)) := by
  simp [divModStr]

/-! ### Factoring.lean, RSA.lean (read by the other units) -/

theorem factorProb_eq (A : NUPPT) (n : ℕ) :
    factorProb A n = uprob fun w : DistinctPrimes n × A.Coins n =>
      ∃ x : Fin n → Bool, A.inverter n n (2 * n) (modulusBits n w.1) w.2 = some x ∧
        (bitsToNat x = w.1.p ∨ bitsToNat x = w.1.q) := rfl

theorem modulusBits_eq (n : ℕ) (z : DistinctPrimes n) :
    modulusBits n z = natToBits (2 * n) (z.p * z.q) := rfl

theorem samplePrimeL_eq (n : ℕ) (r : List Bool) :
    samplePrimeL n r = List.ofFn ((samplePrime n (2 * n ^ 2)
      (chunk (2 * n ^ 2) n (padFin (2 * n ^ 2 * n) r))).getD (natToBits n 2)) := rfl

theorem unitSampleStr_eq (w : List Bool) (n : ℕ) (r : List Bool) :
    unitSampleStr w n r = natToList w.length
      ((sampleUnitL (listToNat w) (Nat.size (listToNat w)) (rsaBlock.eval n) (rsaTrials.eval n) r).getD
        (1 % listToNat w)) := rfl

theorem sampleUnitL_eq (N k B T : ℕ) (r : List Bool) :
    sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r := rfl

theorem eval_rsaBlock (n : ℕ) : rsaBlock.eval n = 2 * (n + 2) := rfl
theorem eval_rsaTrials (n : ℕ) : rsaTrials.eval n = (4 * n + 8) * n := rfl
theorem eval_rsaSampleCoins (n : ℕ) : rsaSampleCoins.eval n = rsaTrials.eval n * rsaBlock.eval n := rfl

/-! ### Proposed shared statements (option A of the brief; sorried here) -/

/-- Shared statement S1 (in `Factoring.lean`, owned by fac; cited by rsa): the prime sampler
`samplePrimeL` is polynomial-time on `⟨1^n, r⟩`. -/
theorem polyTimeComputable_samplePrimeL (hP : PolyTimeComputable primeStr) :
    PolyTimeComputable fun z => samplePrimeL (pairFstD z).length (pairSndD z) := by
  sorry

/-- Shared statement S2 (in `Factoring.lean`, owned by fac; cited by rsa): the values of two
independent `samplePrimeL` runs are within `2 · 2^{-n} + 2n/2^n` of a uniform pair of distinct
primes of `Π_n`. -/
theorem statClose_samplePrimeL_pair (n : ℕ) (hn : 2 ≤ n) :
    StatClose (fun s : Fin (2 * (2 * n ^ 2 * n)) → Bool =>
        (listToNat (samplePrimeL n ((List.ofFn s).take (2 * n ^ 2 * n))),
          listToNat (samplePrimeL n ((List.ofFn s).drop (2 * n ^ 2 * n)))))
      (fun z : DistinctPrimes n => (z.p, z.q))
      (2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n) := by
  sorry

/-- Shared statement S3 (in `RSA.lean`, owned by rsa; cited by rabin, and by rsa itself for the
domain sampler and the exponent): the unit sampler at a modulus `N ≥ 1` of bit length at most
`B(n)` is within `e^{-n}` of the uniform unit of `Z_N`, read as its residue. -/
theorem statClose_sampleUnitL (n N : ℕ) [NeZero N] (hk : Nat.size N ≤ rsaBlock.eval n) :
    StatClose (fun s : Fin (rsaSampleCoins.eval n) → Bool =>
        (sampleUnitL N (Nat.size N) (rsaBlock.eval n) (rsaTrials.eval n) (List.ofFn s)).getD (1 % N))
      (fun x : (ZMod N)ˣ => (x : ZMod N).val) (Real.exp (-(n : ℝ))) := by
  sorry

end ProbePrereqs
