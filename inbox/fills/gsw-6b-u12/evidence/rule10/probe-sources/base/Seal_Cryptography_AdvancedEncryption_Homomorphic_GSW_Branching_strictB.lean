import Lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import TCSlib.Complexity.BranchingPrograms.Eval
import TCSlib.Complexity.BranchingPrograms.Barrington

set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "BoolCircuit.Lit._sizeOf_1\nBoolCircuit.Lit._sizeOf_inst\nBoolCircuit.Lit.eval\nBoolCircuit.Lit.mk._flat_ctor\nBoolCircuit.NAndCircuit._sizeOf_1\nBoolCircuit.NAndCircuit._sizeOf_2\nBoolCircuit.NAndCircuit._sizeOf_3\nBoolCircuit.NAndCircuit._sizeOf_4\nBoolCircuit.NAndCircuit._sizeOf_inst\nBoolCircuit.NAndCircuit.constTrue\nBoolCircuit.NAndCircuit.depth\nBoolCircuit.NAndCircuit.depth._mutual\nBoolCircuit.NAndCircuit.depth._unsafe_rec\nBoolCircuit.NAndCircuit.eval\nBoolCircuit.NAndCircuit.eval._mutual\nBoolCircuit.NAndCircuit.eval._unsafe_rec\nBoolCircuit.NAndCircuit.eval.match_1\nBoolCircuit.NAndCircuit.litCount\nBoolCircuit.NAndCircuit.litCount._mutual\nBoolCircuit.NAndCircuit.litCount._unsafe_rec\nBoolCircuit.NAndCircuit.litCount.match_1\nBoolCircuit.NAndCircuit.ofVar\nBoolCircuit.NAndCircuit.size\nBoolCircuit.NAndCircuit.size._mutual\nBoolCircuit.NAndCircuit.size._unsafe_rec\nBoolCircuit.NAndCircuit.toTreeCircuit\nBoolCircuit.NAndCircuit.toTreeCircuit._mutual\nBoolCircuit.NAndCircuit.toTreeCircuit._unsafe_rec\nBoolCircuit.NOrCircuit._sizeOf_inst\nBoolCircuit.NOrCircuit.constFalse\nBoolCircuit.NOrCircuit.depth\nBoolCircuit.NOrCircuit.depth._unsafe_rec\nBoolCircuit.NOrCircuit.eval\nBoolCircuit.NOrCircuit.eval._unsafe_rec\nBoolCircuit.NOrCircuit.eval.match_1\nBoolCircuit.NOrCircuit.litCount\nBoolCircuit.NOrCircuit.litCount._unsafe_rec\nBoolCircuit.NOrCircuit.litCount.match_1\nBoolCircuit.NOrCircuit.ofVar\nBoolCircuit.NOrCircuit.size\nBoolCircuit.NOrCircuit.size._unsafe_rec\nBoolCircuit.NOrCircuit.toTreeCircuit\nBoolCircuit.NOrCircuit.toTreeCircuit._unsafe_rec\nBoolCircuit.TreeCircuit._sizeOf_1\nBoolCircuit.TreeCircuit._sizeOf_2\nBoolCircuit.TreeCircuit._sizeOf_inst\nBoolCircuit.TreeCircuit.depth\nBoolCircuit.TreeCircuit.depth._unsafe_rec\nBoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1\nBoolCircuit.TreeCircuit.eval\nBoolCircuit.TreeCircuit.eval._unary\nBoolCircuit.TreeCircuit.eval._unsafe_rec\nBoolCircuit.TreeCircuit.eval.match_1\nBoolCircuit.TreeCircuit.ind.match_1_1\nBoolCircuit.TreeCircuit.length_le_sumSize.match_1_1\nBoolCircuit.TreeCircuit.litCount\nBoolCircuit.TreeCircuit.litCount._unsafe_rec\nBoolCircuit.TreeCircuit.maxDepth\nBoolCircuit.TreeCircuit.maxFanin\nBoolCircuit.TreeCircuit.maxFanin._unsafe_rec\nBoolCircuit.TreeCircuit.maxFaninL\nBoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1\nBoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1\nBoolCircuit.TreeCircuit.size\nBoolCircuit.TreeCircuit.size._unsafe_rec\nBoolCircuit.TreeCircuit.sumSize\nBoolCircuit.TreeCircuit.toNAnd\nBoolCircuit.TreeCircuit.toNAnd._mutual\nBoolCircuit.TreeCircuit.toNAnd._unsafe_rec\nBoolCircuit.TreeCircuit.toNAnd.match_1\nBoolCircuit.TreeCircuit.toNOr\nBoolCircuit.TreeCircuit.toNOr._unsafe_rec\nBoolCircuit.TreeCircuit.toNOr.match_1\nBoolCircuit.instDecidableEqLit\nBoolCircuit.instDecidableEqLit.decEq\nBoolCircuit.instDecidableEqLit.decEq.match_1\nBoolCircuit.instHashableLit\nBoolCircuit.instHashableLit.hash\nBoolCircuit.instHashableLit.hash.match_1\nBoolCircuit.instReprLit\nBoolCircuit.instReprLit.repr\nBoolCircuit.instReprTreeCircuit\nBoolCircuit.instReprTreeCircuit.repr._unsafe_rec\nBoolCircuit.instReprTreeCircuit.repr.match_1\nBranchingProgram.FiveCycleRecognizes\nBranchingProgram.Instr.IsPermutation\nBranchingProgram.Instr._sizeOf_1\nBranchingProgram.Instr._sizeOf_inst\nBranchingProgram.Instr.eval\nBranchingProgram.Instr.mk._flat_ctor\nBranchingProgram.Instr.ofPerm\nBranchingProgram.Instr.stepWith\nBranchingProgram.IsFiveCycle\nBranchingProgram.IsPermutation\nBranchingProgram._sizeOf_1\nBranchingProgram._sizeOf_inst\nBranchingProgram.append\nBranchingProgram.barrington\nBranchingProgram.barrington._unary\nBranchingProgram.barrington._unsafe_rec\nBranchingProgram.barrington.match_1\nBranchingProgram.barrington_recognizes.match_1_1\nBranchingProgram.commutatorProgram\nBranchingProgram.complementLast\nBranchingProgram.complementLast.match_1\nBranchingProgram.conj\nBranchingProgram.conjugator\nBranchingProgram.conjugatorFun\nBranchingProgram.conjugatorIndex\nBranchingProgram.conjugatorTable\nBranchingProgram.evalWith\nBranchingProgram.instAppend\nBranchingProgram.instDecidablePredIsFiveCycle\nBranchingProgram.length\nBranchingProgram.mk._flat_ctor\nBranchingProgram.sigma1\nBranchingProgram.sigma2\nBranchingProgram.yield\nBranchingProgramFamily.IsPermutation\nBranchingProgramFamily.IsPolyLength\nBranchingProgramFamily._sizeOf_1\nBranchingProgramFamily._sizeOf_inst\nBranchingProgramFamily.language\nBranchingProgramFamily.mk._flat_ctor\nComplexity.LogProg.bitsVal\nComplexity.LogProg.bitsVal._sunfold\nComplexity.LogProg.bitsVal._unsafe_rec\nComplexity.LogProg.bitsVal.match_1\nComplexity.LogProg.eq_of_bitsVal_eq.match_1_1\nComplexity.LogProg.incW\nComplexity.LogProg.incW._sunfold\nComplexity.LogProg.incW._unsafe_rec\nComplexity.LogProg.incW.match_1\nLanguage.InBWBP\nLanguage.InPBP\nRandomized.ClosedUnderAnswerIs\nRandomized.ClosedUnderAny\nRandomized.ClosedUnderMajority\nRandomized.ClosedUnderNot\nRandomized.ClosedUnderRace\nRandomized.InBPP\nRandomized.InBPPStrong\nRandomized.InBPPWeak\nRandomized.InCoRP\nRandomized.InRP\nRandomized.InZPP\nRandomized.VerifierModel._sizeOf_1\nRandomized.VerifierModel._sizeOf_inst\nRandomized.VerifierModel.mk._flat_ctor\nRandomized.anyVerifier\nRandomized.bitsEquiv\nRandomized.blockCount\nRandomized.blockVal\nRandomized.blocksEquiv\nRandomized.boolVerifier\nRandomized.majorityVerifier\nRandomized.polyLen\nRandomized.raceVerifier\nRandomized.randProb\nRandomized.randProb_blockCount.match_1_1\nRandomized.randProb_mem_eq_sum.match_1_2\nRandomized.weakAdv\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Encrypts\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters._sizeOf_1\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters._sizeOf_inst\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.mk._flat_ctor\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.chain\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decompose\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decomposeVec\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.digit\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.gadget\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.lift\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.mul\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.nand\nTCSlib.Cryptography.LWE.Noise.Bounded\nTCSlib.Cryptography.LWE.Noise._sizeOf_1\nTCSlib.Cryptography.LWE.Noise._sizeOf_inst\nTCSlib.Cryptography.LWE.Noise.mk._flat_ctor\nTCSlib.Cryptography.LWE.Parameters._sizeOf_1\nTCSlib.Cryptography.LWE.Parameters._sizeOf_inst\nTCSlib.Cryptography.LWE.Parameters.mk._flat_ctor\nTCSlib.Cryptography.LWE.noisyValues\nTCSlib.Cryptography.LWE.sample\nTCSlib.Cryptography.TrapdoorFunctions.Lossy.decode\nTCSlib.Cryptography.TrapdoorFunctions.Lossy.digits\nTCSlib.Cryptography.TrapdoorFunctions.Lossy.encode\nTCSlib.Cryptography.TrapdoorFunctions.Lossy.gadget\n_private.TCSlib.Complexity.BranchingPrograms.Barrington.0.BranchingProgram.barrington.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.eval.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.litCount.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.eval.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.litCount.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.eval.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.sumSize_add_length_le.match_1_1\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNAnd.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNOr.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.instReprTreeCircuit.repr.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.List.map_unattach.match_1.splitter\n_private.TCSlib.Complexity.SpaceComplexity.Machines.Bin.0.Complexity.LogProg.bitsVal.match_1.splitter\n_private.TCSlib.Complexity.SpaceComplexity.Machines.Bin.0.Complexity.LogProg.incW.match_1.splitter"
  let want : List String := if payload.isEmpty then [] else payload.splitOn "\n"
  let env ← Lean.getEnv
  let mut byName : Std.HashMap String Lean.Name := {}
  for (n, _) in env.constants.toList do
    byName := byName.insert n.toString n
  let mut count : Nat := 0
  for s in want do
    let some n := byName[s]? | throwError "SEAL-HARNESS unknown constant {s}"
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if false then
      unless st == .irreducible do throwError "SEAL-VERIFY not irreducible: {s}"
    else
      unless st == .irreducible do
        Lean.Elab.Command.elabCommand
          (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    count := count + 1
  Lean.logInfo m!"SEAL-INSTALL base/Cryptography_AdvancedEncryption_Homomorphic_GSW_Branching/strict-B part 1: {count}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Homomorphic evaluation of permutation branching programs and formulas (GSW)

## Main definitions

* `select`: the homomorphic selector `select P C U V = (G − C) ⊡ U + C ⊡ V`, fresh selector
  on the left.
* `homEvalPBP`: a branching program run homomorphically, the shared host
  `BranchingProgram.evalWith` (registry row H18) instantiated with `select P`.
* `homEvalFormula`: a fan-in-2 formula through Barrington's program (output `sigma1`), read at
  coordinate `sigma1 0`.

## Main results

* `Encrypts.select` (G1): one selector step costs an additive `2·N·β`.
* `encrypts_homEvalPBP` (G2): a permutation program of length `L` gives noise `L·2·N·β`.
* `encrypts_homEvalFormula` (G3): a formula of depth `d` gives noise `4^d·2·N·β`.

All three are statement-phase targets (admitted); the definitions are total and computable.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: §3.3 (Eq. (4), Eval with Eq. (5)–(6)), Thm 3.5, Lemma 3.6 with its
  proof.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: Eq. (4.1), Lemma 4.1.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, §6.1.3 (bootstrapping).
* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1) (1989), 150–164: Thm 1.

**Deviations.** The selector carries the fresh ciphertext on the left of both products
(`(G − C) ⊡ U`, `C ⊡ V`), mirroring [BV14, Eq. (5)–(6)], which multiplies the state on the
left; with the library's `⊡` (`GSW.mul`, right operand decomposed) this order makes the noise
of a step additive in the state's noise. Noise bounds are worst case, not probabilistic
([BV14, Lemma 3.6] holds with overwhelming probability). The formula's output is coordinate
`σ 0` of the state started at `0` (Barrington's C16 reading), not [BV14]'s coordinate `1`:
a five-cycle moves `0`, so coordinate `0` would encode the complement.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit

/-- **The homomorphic selector** `select P C U V = (G − C) ⊡ U + C ⊡ V`: if `C` encrypts the
bit `b`, the result encrypts `(1 − b)·u + b·v`, selecting `U`'s message when `b = 0` and `V`'s
when `b = 1` [BV14, §3.3, Eq. (5)–(6), p014-b002, mirrored; AP14, Eq. (4.1), p011-b001].
The fresh selector ciphertext is on the left of both products (Gate 41's convention). -/
def select (P : Parameters) (C U V : Ciphertext P) : Ciphertext P :=
  mul P (gadget P - C) U + mul P C V

/-- `select P C U V` is `mul P (gadget P - C) U + mul P C V`. -/
theorem select_eq (P : Parameters) (C U V : Ciphertext P) :
    select P C U V = mul P (gadget P - C) U + mul P C V := rfl

/-- **Homomorphic evaluation of a branching program**: the host
`BranchingProgram.evalWith` (H18) with values and selectors in `Ciphertext P` and selector
`select P`, `homEvalPBP P B cts V = B.evalWith (select P) cts V`; instruction `ι` selects with
the input ciphertext `cts ι.var` [BV14, §3.3, Eval, p014-b002; AP14, Eq. (4.1), p011-b001].
For a permutation program each step is the pull form `V'_i = select (cts var) (V (σ₀⁻¹ i))
(V (σ₁⁻¹ i))` (`Instr.stepWith_of_isPermutation`). Computable. -/
def homEvalPBP (P : Parameters) {w k : ℕ} (B : BranchingProgram w k)
    (cts : Fin k → Ciphertext P) (V : Fin w → Ciphertext P) : Fin w → Ciphertext P :=
  B.evalWith (select P) cts V

/-- `homEvalPBP P B cts V` is `B.evalWith (select P) cts V`. -/
theorem homEvalPBP_eq (P : Parameters) {w k : ℕ} (B : BranchingProgram w k)
    (cts : Fin k → Ciphertext P) (V : Fin w → Ciphertext P) :
    homEvalPBP P B cts V = B.evalWith (select P) cts V := rfl

/-- **Homomorphic evaluation of a formula** [BV14, §3.3, Eval, p014-b002, with Thm 3.5,
p014-b001; Pei16, §6.1.3, p070-b001]: convert the formula `c` on `k ≥ 1` inputs to
Barrington's width-5 permutation program with output five-cycle `sigma1`, run it
homomorphically from the state `Pi.single 0 G` (an encryption of the one-hot state `0` with
zero noise), and read coordinate `sigma1 0`:
`homEvalFormula P c cts = homEvalPBP P (barrington c sigma1) cts (Pi.single 0 (gadget P))
(sigma1 0)`. Deviation: [BV14] outputs the state's coordinate `1`; here the accepting
coordinate is `σ 0` (`barrington_yield_zero`, r3 §H3.7). Computable (P6-Q13). -/
def homEvalFormula (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) : Ciphertext P :=
  homEvalPBP P (BranchingProgram.barrington c BranchingProgram.sigma1) cts
    (Pi.single 0 (gadget P)) (BranchingProgram.sigma1 0)

/-- `homEvalFormula P c cts` is `homEvalPBP P (barrington c sigma1) cts (Pi.single 0 (gadget P))`
at coordinate `sigma1 0`. -/
theorem homEvalFormula_eq (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) :
    homEvalFormula P c cts =
      homEvalPBP P (BranchingProgram.barrington c BranchingProgram.sigma1) cts
        (Pi.single 0 (gadget P)) (BranchingProgram.sigma1 0) := rfl

/-! ### Targets G1–G3 -/

/-- **G1. The selector step.** If `C` encrypts a bit `b ∈ {0, 1}` with noise at most `β` and
`U`, `V` encrypt `u`, `v` with noise at most `βV`, all under the key vector `t`, then
`select P C U V` encrypts `(1 − b)·u + b·v` with noise at most `βV + 2·(N·β)`, `N = P.columns`:
`Encrypts P t ((1 - b) * u + b * v) (βV + 2 * (P.columns * β)) (select P C U V)`
[BV14, §3.3, Eq. (5)–(6), p014-b002; Lemma 3.6 proof, p015-b002, mirrored; AP14, Eq. (4.1),
p011-b001; Lemma 4.1, p012-b001]. Deviation: worst case, and the selector sits on the left.

**Proof sketch.** `encrypts_gadget` and `Encrypts.sub` give `G − C` encrypting `1 − b` with
noise `0 + β`. `Encrypts.mul` gives `(G − C) ⊡ U` with noise `N·β + |1 − b|·βV` and `C ⊡ V` with
noise `N·β + |b|·βV`, the two products that `select_eq` exposes. `Encrypts.add` sums the
two; since `b ∈ {0, 1}`, `|1 − b| + |b| = 1`, so the noise is at most `βV + 2·(N·β)` by
`Encrypts.mono`, and the message is `(1 − b)·u + b·v`. -/
theorem Encrypts.select (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}
    {b u v : ℤ} {β βV : ℕ} {C U V : Ciphertext P} (hC : Encrypts P t b β C)
    (hU : Encrypts P t u βV U) (hV : Encrypts P t v βV V) (hb : b = 0 ∨ b = 1) :
    Encrypts P t ((1 - b) * u + b * v) (βV + 2 * (P.columns * β)) (select P C U V) := by
  sorry

/-- **G2. Homomorphic permutation-program evaluation.** For a permutation program `B` of
width `w` on `k` inputs, input ciphertexts `cts j` encrypting the bits `x j` with noise at most
`β` under `t`, and the start state `Pi.single s₀ G`, coordinate `i` of the evaluated state
encrypts the indicator of `B.yield x s₀ = i` with noise at most `B.length·(2·(N·β))`:
`Encrypts P t (decide (B.yield x s₀ = i)).toNat (B.length * (2 * (P.columns * β)))
(homEvalPBP P B cts (Pi.single s₀ (gadget P)) i)`
[BV14, Lemma 3.6, p015-b001, with its proof, p015-b002; AP14, Lemma 4.1, p012-b001].
Deviation: worst case (BV14: with overwhelming probability), for every permutation program.

**Proof sketch.** Apply the host lemma `BranchingProgram.evalWith_rel` (C7) to the
homomorphic run and to the Boolean run `evalWith (fun b u v => if b then v else u) x
(Pi.single s₀ 1)` (whose result is `Pi.single (B.yield x s₀) 1` by `evalWith_single`, C8),
with the relation at step `τ`: every coordinate `i` of the ciphertext state encrypts the
natural number at coordinate `i` of the Boolean state, with noise at most `τ·(2·(N·β))`. At
step `0`: `Pi.single` coordinates are `G` (`encrypts_gadget`) and `0` (`encrypts_zero`). Step:
the instruction is a permutation (`isPermutation_iff`), so both steps are pull forms
(`Instr.stepWith_of_isPermutation`, C6); coordinate `i` is `select (cts var) U V` with `U`, `V`
the predecessors' ciphertexts, and `Encrypts.select` (G1) with `βV = τ·(2·(N·β))` gives
`(τ + 1)·(2·(N·β))`; the messages agree because the Boolean coordinates are `0`/`1` and the
selector picks the branch of `x var`. At `τ = B.length` read `evalWith_single` and
`Pi.single_apply`. Uses the `homEvalPBP_eq` reader. -/
theorem encrypts_homEvalPBP (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}
    {w k : ℕ} (B : BranchingProgram w k) (hB : B.IsPermutation) (x : Fin k → Bool)
    (cts : Fin k → Ciphertext P) (β : ℕ)
    (hin : ∀ j, Encrypts P t ((x j).toNat : ℤ) β (cts j)) (s₀ i : Fin w) :
    Encrypts P t ((decide (B.yield x s₀ = i)).toNat : ℤ) (B.length * (2 * (P.columns * β)))
      (homEvalPBP P B cts (Pi.single s₀ (gadget P)) i) := by
  sorry

/-- **G3. Homomorphic formula evaluation.** For a formula `c` of fan-in at most two on
`k ≥ 1` inputs and input ciphertexts `cts j` encrypting the bits `x j` with noise at most `β`
under `t`, `homEvalFormula P c cts` encrypts `c.eval x` with noise at most
`4^(c.depth)·(2·(N·β))`:
`Encrypts P t (c.eval x).toNat (4 ^ c.depth * (2 * (P.columns * β))) (homEvalFormula P c cts)`
[BV14, Thm 3.5, p014-b001, with Lemma 3.6, p015-b001; Pei16, §6.1.3, p070-b001; Bar89, Thm 1,
p003-b002]. Deviation: the output coordinate is `σ 0` (BV14: coordinate `1`), worst case.

**Proof sketch.** `homEvalFormula_eq`, then G2 (`encrypts_homEvalPBP`) for the program
`barrington c sigma1`, which is a permutation program (`isPermutation_barrington`, C15), at
`s₀ = 0` and `i = sigma1 0`. Its message is `decide (yield x 0 = sigma1 0)`; by
`barrington_yield_zero` (C16, with `isFiveCycle_sigma1`) the yield at `0` is `sigma1 0` if
`c.eval x` and `0` otherwise, and `sigma1 0 ≠ 0` (a five-cycle has no fixed point:
`isFiveCycle_iff`, or by `decide` on `Fin 5`), so the message is `(c.eval x).toNat`. The noise
`length·(2·(N·β))` is at most `4^(c.depth)·(2·(N·β))` by `barrington_length_le` (C14) and
`Encrypts.mono`. -/
theorem encrypts_homEvalFormula (P : Parameters)
    {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus} {k : ℕ} [NeZero k]
    (c : TreeCircuit k) (hc : c.maxFanin ≤ 2) (x : Fin k → Bool) (cts : Fin k → Ciphertext P)
    (β : ℕ) (hin : ∀ j, Encrypts P t ((x j).toNat : ℤ) β (cts j)) :
    Encrypts P t ((c.eval x).toNat : ℤ) (4 ^ c.depth * (2 * (P.columns * β)))
      (homEvalFormula P c cts) := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW


set_option maxHeartbeats 0 in
run_cmd do
  let payload : String := "BoolCircuit.Lit._sizeOf_1\nBoolCircuit.Lit._sizeOf_inst\nBoolCircuit.Lit.eval\nBoolCircuit.Lit.mk._flat_ctor\nBoolCircuit.NAndCircuit._sizeOf_1\nBoolCircuit.NAndCircuit._sizeOf_2\nBoolCircuit.NAndCircuit._sizeOf_3\nBoolCircuit.NAndCircuit._sizeOf_4\nBoolCircuit.NAndCircuit._sizeOf_inst\nBoolCircuit.NAndCircuit.constTrue\nBoolCircuit.NAndCircuit.depth\nBoolCircuit.NAndCircuit.depth._mutual\nBoolCircuit.NAndCircuit.depth._unsafe_rec\nBoolCircuit.NAndCircuit.eval\nBoolCircuit.NAndCircuit.eval._mutual\nBoolCircuit.NAndCircuit.eval._unsafe_rec\nBoolCircuit.NAndCircuit.eval.match_1\nBoolCircuit.NAndCircuit.litCount\nBoolCircuit.NAndCircuit.litCount._mutual\nBoolCircuit.NAndCircuit.litCount._unsafe_rec\nBoolCircuit.NAndCircuit.litCount.match_1\nBoolCircuit.NAndCircuit.ofVar\nBoolCircuit.NAndCircuit.size\nBoolCircuit.NAndCircuit.size._mutual\nBoolCircuit.NAndCircuit.size._unsafe_rec\nBoolCircuit.NAndCircuit.toTreeCircuit\nBoolCircuit.NAndCircuit.toTreeCircuit._mutual\nBoolCircuit.NAndCircuit.toTreeCircuit._unsafe_rec\nBoolCircuit.NOrCircuit._sizeOf_inst\nBoolCircuit.NOrCircuit.constFalse\nBoolCircuit.NOrCircuit.depth\nBoolCircuit.NOrCircuit.depth._unsafe_rec\nBoolCircuit.NOrCircuit.eval\nBoolCircuit.NOrCircuit.eval._unsafe_rec\nBoolCircuit.NOrCircuit.eval.match_1\nBoolCircuit.NOrCircuit.litCount\nBoolCircuit.NOrCircuit.litCount._unsafe_rec\nBoolCircuit.NOrCircuit.litCount.match_1\nBoolCircuit.NOrCircuit.ofVar\nBoolCircuit.NOrCircuit.size\nBoolCircuit.NOrCircuit.size._unsafe_rec\nBoolCircuit.NOrCircuit.toTreeCircuit\nBoolCircuit.NOrCircuit.toTreeCircuit._unsafe_rec\nBoolCircuit.TreeCircuit._sizeOf_1\nBoolCircuit.TreeCircuit._sizeOf_2\nBoolCircuit.TreeCircuit._sizeOf_inst\nBoolCircuit.TreeCircuit.depth\nBoolCircuit.TreeCircuit.depth._unsafe_rec\nBoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1\nBoolCircuit.TreeCircuit.eval\nBoolCircuit.TreeCircuit.eval._unary\nBoolCircuit.TreeCircuit.eval._unsafe_rec\nBoolCircuit.TreeCircuit.eval.match_1\nBoolCircuit.TreeCircuit.ind.match_1_1\nBoolCircuit.TreeCircuit.length_le_sumSize.match_1_1\nBoolCircuit.TreeCircuit.litCount\nBoolCircuit.TreeCircuit.litCount._unsafe_rec\nBoolCircuit.TreeCircuit.maxDepth\nBoolCircuit.TreeCircuit.maxFanin\nBoolCircuit.TreeCircuit.maxFanin._unsafe_rec\nBoolCircuit.TreeCircuit.maxFaninL\nBoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1\nBoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1\nBoolCircuit.TreeCircuit.size\nBoolCircuit.TreeCircuit.size._unsafe_rec\nBoolCircuit.TreeCircuit.sumSize\nBoolCircuit.TreeCircuit.toNAnd\nBoolCircuit.TreeCircuit.toNAnd._mutual\nBoolCircuit.TreeCircuit.toNAnd._unsafe_rec\nBoolCircuit.TreeCircuit.toNAnd.match_1\nBoolCircuit.TreeCircuit.toNOr\nBoolCircuit.TreeCircuit.toNOr._unsafe_rec\nBoolCircuit.TreeCircuit.toNOr.match_1\nBoolCircuit.instDecidableEqLit\nBoolCircuit.instDecidableEqLit.decEq\nBoolCircuit.instDecidableEqLit.decEq.match_1\nBoolCircuit.instHashableLit\nBoolCircuit.instHashableLit.hash\nBoolCircuit.instHashableLit.hash.match_1\nBoolCircuit.instReprLit\nBoolCircuit.instReprLit.repr\nBoolCircuit.instReprTreeCircuit\nBoolCircuit.instReprTreeCircuit.repr._unsafe_rec\nBoolCircuit.instReprTreeCircuit.repr.match_1\nBranchingProgram.FiveCycleRecognizes\nBranchingProgram.Instr.IsPermutation\nBranchingProgram.Instr._sizeOf_1\nBranchingProgram.Instr._sizeOf_inst\nBranchingProgram.Instr.eval\nBranchingProgram.Instr.mk._flat_ctor\nBranchingProgram.Instr.ofPerm\nBranchingProgram.Instr.stepWith\nBranchingProgram.IsFiveCycle\nBranchingProgram.IsPermutation\nBranchingProgram._sizeOf_1\nBranchingProgram._sizeOf_inst\nBranchingProgram.append\nBranchingProgram.barrington\nBranchingProgram.barrington._unary\nBranchingProgram.barrington._unsafe_rec\nBranchingProgram.barrington.match_1\nBranchingProgram.barrington_recognizes.match_1_1\nBranchingProgram.commutatorProgram\nBranchingProgram.complementLast\nBranchingProgram.complementLast.match_1\nBranchingProgram.conj\nBranchingProgram.conjugator\nBranchingProgram.conjugatorFun\nBranchingProgram.conjugatorIndex\nBranchingProgram.conjugatorTable\nBranchingProgram.evalWith\nBranchingProgram.instAppend\nBranchingProgram.instDecidablePredIsFiveCycle\nBranchingProgram.length\nBranchingProgram.mk._flat_ctor\nBranchingProgram.sigma1\nBranchingProgram.sigma2\nBranchingProgram.yield\nBranchingProgramFamily.IsPermutation\nBranchingProgramFamily.IsPolyLength\nBranchingProgramFamily._sizeOf_1\nBranchingProgramFamily._sizeOf_inst\nBranchingProgramFamily.language\nBranchingProgramFamily.mk._flat_ctor\nComplexity.LogProg.bitsVal\nComplexity.LogProg.bitsVal._sunfold\nComplexity.LogProg.bitsVal._unsafe_rec\nComplexity.LogProg.bitsVal.match_1\nComplexity.LogProg.eq_of_bitsVal_eq.match_1_1\nComplexity.LogProg.incW\nComplexity.LogProg.incW._sunfold\nComplexity.LogProg.incW._unsafe_rec\nComplexity.LogProg.incW.match_1\nLanguage.InBWBP\nLanguage.InPBP\nRandomized.ClosedUnderAnswerIs\nRandomized.ClosedUnderAny\nRandomized.ClosedUnderMajority\nRandomized.ClosedUnderNot\nRandomized.ClosedUnderRace\nRandomized.InBPP\nRandomized.InBPPStrong\nRandomized.InBPPWeak\nRandomized.InCoRP\nRandomized.InRP\nRandomized.InZPP\nRandomized.VerifierModel._sizeOf_1\nRandomized.VerifierModel._sizeOf_inst\nRandomized.VerifierModel.mk._flat_ctor\nRandomized.anyVerifier\nRandomized.bitsEquiv\nRandomized.blockCount\nRandomized.blockVal\nRandomized.blocksEquiv\nRandomized.boolVerifier\nRandomized.majorityVerifier\nRandomized.polyLen\nRandomized.raceVerifier\nRandomized.randProb\nRandomized.randProb_blockCount.match_1_1\nRandomized.randProb_mem_eq_sum.match_1_2\nRandomized.weakAdv\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Encrypts\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters._sizeOf_1\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters._sizeOf_inst\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.mk._flat_ctor\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.chain\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decompose\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decomposeVec\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.digit\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.gadget\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.lift\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.mul\nTCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.nand\nTCSlib.Cryptography.LWE.Noise.Bounded\nTCSlib.Cryptography.LWE.Noise._sizeOf_1\nTCSlib.Cryptography.LWE.Noise._sizeOf_inst\nTCSlib.Cryptography.LWE.Noise.mk._flat_ctor\nTCSlib.Cryptography.LWE.Parameters._sizeOf_1\nTCSlib.Cryptography.LWE.Parameters._sizeOf_inst\nTCSlib.Cryptography.LWE.Parameters.mk._flat_ctor\nTCSlib.Cryptography.LWE.noisyValues\nTCSlib.Cryptography.LWE.sample\nTCSlib.Cryptography.TrapdoorFunctions.Lossy.decode\nTCSlib.Cryptography.TrapdoorFunctions.Lossy.digits\nTCSlib.Cryptography.TrapdoorFunctions.Lossy.encode\nTCSlib.Cryptography.TrapdoorFunctions.Lossy.gadget\n_private.TCSlib.Complexity.BranchingPrograms.Barrington.0.BranchingProgram.barrington.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.eval.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.litCount.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.eval.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.litCount.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.eval.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.sumSize_add_length_le.match_1_1\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNAnd.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNOr.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.instReprTreeCircuit.repr.match_1.splitter\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.List.map_unattach.match_1.splitter\n_private.TCSlib.Complexity.SpaceComplexity.Machines.Bin.0.Complexity.LogProg.bitsVal.match_1.splitter\n_private.TCSlib.Complexity.SpaceComplexity.Machines.Bin.0.Complexity.LogProg.incW.match_1.splitter"
  let want : List String := if payload.isEmpty then [] else payload.splitOn "\n"
  let env ← Lean.getEnv
  let mut byName : Std.HashMap String Lean.Name := {}
  for (n, _) in env.constants.toList do
    byName := byName.insert n.toString n
  let mut count : Nat := 0
  for s in want do
    let some n := byName[s]? | throwError "SEAL-HARNESS unknown constant {s}"
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if true then
      unless st == .irreducible do throwError "SEAL-VERIFY not irreducible: {s}"
    else
      unless st == .irreducible do
        Lean.Elab.Command.elabCommand
          (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    count := count + 1
  Lean.logInfo m!"SEAL-VERIFY base/Cryptography_AdvancedEncryption_Homomorphic_GSW_Branching/strict-B part 1: {count}"
