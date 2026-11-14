/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Encoding
import TCSlib.Cryptography.Authentication.Signatures.Lamport.TableCoins
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
import TCSlib.Cryptography.Authentication.Signatures.Lamport.AveragingExtra
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Statistics
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Experiment
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Advice
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Blocks
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Closing
import TCSlib.Cryptography.Authentication.Signatures.Lamport.InversionProbability
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Machine
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Seed
import TCSlib.Cryptography.Authentication.Signatures.Lamport.MachineSpec
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Nonabort
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Realization
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lamport's one-time signatures

[PS10, Protocol 137.1]: for a one-way function `f`,
- `Gen(1^n)` samples `x_i^b ← U_n` for `i ∈ [n]` and `b ∈ {0, 1}`, and outputs
  `sk = (x_i^b)` and `pk = (f(x_i^b))`;
- `Sign_sk(m)` outputs `σ = (x_1^{m_1}, …, x_n^{m_n})`;
- `Ver_pk(m, σ)` accepts iff `f(σ_i) = f(x_i^{m_i})` for all `i`.

Theorem 137.2: if `f` is one-way, the scheme is one-time secure.

**The encoding.**
- `f` is a function family with `n`-bit inputs at parameter `n` (`lamportOWF`), given with a
  polynomial-time evaluator `E` on `⟨1^n, x⟩` that agrees with `f` on `n`-bit `x` (`hfE`, the
  form of `FunFamily.Easy`).
- The secret key is `Gen`'s `2n²` coins. Segment `i` (bits `2ni` to `2ni + 2n − 1`) is
  `x_i^0 ‖ x_i^1`.
- The public key is the tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩`, and a signature is the
  concatenation of the `n` revealed preimages: `n²` bits.
- The three algorithms are instances of the ch. 2–4 layer's block loop (`blockEncFun`), run over
  the message bits.

**Deviations, declared once here.**
- **`Ver` tests lengths first.** It rejects unless the message has `n` bits and the signature
  `n²`. So `E` is only ever evaluated on `n`-bit preimage candidates, where it agrees with `f`. An
  evaluator is unconstrained elsewhere, and a `Ver` evaluating it there could accept forgeries
  that do not invert `f`.
- **The one-way function is strong** ([PS10, Definition 27.3], `FunFamily.StrongOneWay`), the
  notes' "one-way function"; by §2.4 a weak one suffices.

## Contents

* `Signatures.Lamport.Encoding`: injectivity of the cryptographic tuple encoding.
* `Signatures.Lamport.Planted`: the typed planted experiment and safe-run coupling.
* `Signatures.Lamport.TableCoins`: the equivalence between key tapes and typed tables.
* `Signatures.Lamport.Averaging`: finite favourable-pair counting.
* `Signatures.Lamport.AveragingExtra`: optional-query counting and fixed-position selection.
* `Signatures.Lamport.Statistics`: independent-coordinate averaging.
* `Signatures.Lamport.Experiment`: the typed honest and planted probability bounds.
* `Signatures.Lamport.Advice`: binary advice and bounded decoding for the best position.
* `Signatures.Lamport.Blocks`: updating a fixed-width serialized tuple block.
* `Signatures.Lamport.Closing`: negligibility under the linear reduction loss.
* `Signatures.Lamport.InversionProbability`: transport to the actual machine inversion probability.
* `Signatures.Lamport.Machine`: the polynomial-time planting handler.
* `Signatures.Lamport.Seed`: the fair-bit and random-table seed equivalence.
* `Signatures.Lamport.MachineSpec`: functional contracts for planting, signing and extraction.
* `Signatures.Lamport.Nonabort`: nonaborting one-query runs have a safe query.
* `Signatures.Lamport.Realization`: T1 realization with an explicit coin equivalence.

## Main definitions

* `Authentication.lamportOWF`: `f` as a `FunFamily`.
* `Authentication.lamport`: Protocol 137.1 as a `SignatureScheme`, with correctness proved.

## Main results

* The ordinary `lamportHalf_eq`, emission and string-function equations expose the algorithms.
* `Authentication.lamportOWF_inLen`, `lamportOWF_outLen`, `lamportOWF_f`: the function-family fields.
* `Authentication.lamport_msgLen`, `lamport_sigLen`, `lamport_gen`, `lamport_sign`, `lamport_ver`:
  the signature-scheme data fields.
* `Authentication.lamportVerFun_sign`: correctness, `Ver` accepts honest signatures.
* `Authentication.lamport_oneTimeSecure` (Thm 137.2): one-time security from strong one-wayness.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §5.4, Protocol 137.1 and Theorem 137.2 (book pp. 136–138).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.PrivateKeyScheme (encodeList)

/-! ### Blocks and block loops -/

/-- The preimage `x_i^b` inside the segment `x_i^0 ‖ x_i^1` of `2n` bits. -/
def lamportHalf (n : ℕ) (b : Bool) (s : List Bool) : List Bool := if b then s.drop n else s.take n

/-- The selected preimage is the suffix after `n` bits for `true`, and the first `n` bits
for `false`. -/
theorem lamportHalf_eq (n : ℕ) (b : Bool) (s : List Bool) :
    lamportHalf n b s = if b then s.drop n else s.take n := rfl

/-- A half of a `2n`-bit segment has `n` bits. -/
theorem length_lamportHalf {n : ℕ} (b : Bool) {s : List Bool} (hs : s.length = 2 * n) :
    (lamportHalf n b s).length = n := by
  cases b <;> simp [lamportHalf, hs] <;> omega

/-- The concatenation of `q` blocks of `B` bits has `q · B` bits. -/
theorem length_flatten_ofFn {B : ℕ} : ∀ {q : ℕ} (g : Fin q → List Bool),
    (∀ i, (g i).length = B) → (List.ofFn g).flatten.length = q * B
  | 0, _, _ => by simp
  | q + 1, g, hg => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hg 0,
      length_flatten_ofFn (fun i => g i.succ) (fun i => hg i.succ), Nat.succ_mul]
    omega

/-- Segment `i` of the concatenation of `B`-bit blocks `g 0, …, g (q − 1)` is `g i`. -/
theorem coinBlock_flatten_ofFn {q B : ℕ} (g : Fin q → List Bool) (hg : ∀ i, (g i).length = B)
    (i : Fin q) : coinBlock B i (List.ofFn g).flatten = g i := by
  rw [coinBlock_flatten (List.ofFn g) (fun c hc => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    exact hg j) i (by simp)]
  simp

/-- **The block loop over a message** (`blockEncFun` with one-bit blocks): its output is the
tuple of the emissions on the layouts `⟨⟨⟨u, ⟨pk, [m_i]⟩⟩, []⟩, segment i⟩`. -/
theorem blockEncFun_ofFn (G : List Bool → List Bool) (B : PolyExpr) (u pk : List Bool) {q : ℕ}
    (m : Fin q → Bool) (r : List Bool) :
    blockEncFun G (.const 1) B (blockState u pk (List.ofFn m) r) =
      encodeList (List.ofFn fun i : Fin q =>
        G (NUPPT.layout u (pairEncode pk [m i]) [] (coinBlock (B.eval u.length) i r))) := by
  have hlen : (List.ofFn m).length ≤ (blockState u pk (List.ofFn m) r).length := by
    simp only [blockState_eq, length_pairEncode, List.length_ofFn]
    omega
  rw [blockEncFun_eq]
  rw [blockEncFun_spec G (.const 1) B u pk (blockState u pk (List.ofFn m) r).length
    (List.ofFn m) r (by simpa using hlen)]
  simp only [PolyExpr.eval_const]
  rw [blockList_ofFn G _ u pk q m r _ (by simp only [List.length_ofFn] at hlen; omega)]

/-- **The tuple flattener** (`decListFun pairSndD`): on `⟨[], encodeList l⟩` it concatenates `l`. -/
theorem decListFun_pairSndD (l : List (List Bool)) :
    decListFun pairSndD (pairEncode [] (encodeList l)) = l.flatten := by
  have hlen : l.length ≤ (pairEncode [] (encodeList l)).length := by
    have := length_le_length_encodeList l
    simp only [length_pairEncode]
    omega
  rw [decListFun_eq]
  rw [decListFun_spec pairSndD [] _ l hlen]
  simp

/-! ### The algorithms as string functions -/

/-- `f(x)` on the layout `⟨⟨⟨1^n, y⟩, α⟩, x⟩`: `E(⟨1^n, x⟩)`. -/
def lamportEvalEmit (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  E (pairEncode (NUPPT.inParam v) (NUPPT.inCoins v))

/-- The evaluation emission applies `E` to the parameter paired with the current coin block. -/
theorem lamportEvalEmit_eq (E : List Bool → List Bool) (v : List Bool) :
    lamportEvalEmit E v = E (pairEncode (NUPPT.inParam v) (NUPPT.inCoins v)) := rfl

/-- `Gen`'s emission on the layout `⟨⟨⟨1^n, y⟩, α⟩, x^0 ‖ x^1⟩`: the pair `⟨f(x^0), f(x^1)⟩`. -/
def lamportPairEmit (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairEncode (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).take (NUPPT.inParam v).length)))
    (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).drop (NUPPT.inParam v).length)))

/-- The key-generation emission pairs the images of the first and second preimage blocks. -/
theorem lamportPairEmit_eq (E : List Bool → List Bool) (v : List Bool) :
    lamportPairEmit E v =
      pairEncode (E (pairEncode (NUPPT.inParam v)
          ((NUPPT.inCoins v).take (NUPPT.inParam v).length)))
        (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).drop (NUPPT.inParam v).length))) := rfl

/-- `Sign`'s emission on the layout `⟨⟨⟨1^n, ⟨pk, [b]⟩⟩, α⟩, x^0 ‖ x^1⟩`: the preimage `x^b`. -/
def lamportSelEmit (v : List Bool) : List Bool :=
  if (pairSndD (NUPPT.inArg v)).headD false then (NUPPT.inCoins v).drop (NUPPT.inParam v).length
  else (NUPPT.inCoins v).take (NUPPT.inParam v).length

/-- The signing emission chooses the second or first preimage block according to the message
bit in the argument. -/
theorem lamportSelEmit_eq (v : List Bool) :
    lamportSelEmit v =
      if (pairSndD (NUPPT.inArg v)).headD false then
        (NUPPT.inCoins v).drop (NUPPT.inParam v).length
      else (NUPPT.inCoins v).take (NUPPT.inParam v).length := rfl

/-- `Ver`'s selection on the layout `⟨⟨⟨1^n, ⟨pk, [b]⟩⟩, α⟩, ⟨⟨y^0, y^1⟩, []⟩⟩` (a block of the
public key): `y^b`. -/
def lamportPkEmit (v : List Bool) : List Bool :=
  if (pairSndD (NUPPT.inArg v)).headD false then pairSndD (pairFstD (NUPPT.inCoins v))
  else pairFstD (pairFstD (NUPPT.inCoins v))

/-- The public-key emission chooses the second or first image in the current encoded block
according to the message bit. -/
theorem lamportPkEmit_eq (v : List Bool) :
    lamportPkEmit v =
      if (pairSndD (NUPPT.inArg v)).headD false then pairSndD (pairFstD (NUPPT.inCoins v))
      else pairFstD (pairFstD (NUPPT.inCoins v)) := rfl

/-- The length of a public-key block `⟨⟨y^0, y^1⟩, []⟩` with `L`-bit images: `6L + 6`. -/
def lamportPkBlock (L : PolyExpr) : PolyExpr := .add (.mul (.const 6) L) (.const 6)

/-- The public-key block polynomial is `6L + 6`. -/
theorem lamportPkBlock_eq (L : PolyExpr) :
    lamportPkBlock L = .add (.mul (.const 6) L) (.const 6) := rfl

/-- `Gen` on the layout `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩` with `2n²` coins `ρ`: `⟨pk, ρ⟩`, where `pk` is the
tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩` over the `2n`-bit segments of `ρ`. -/
def lamportGenFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode
    (blockEncFun (lamportPairEmit E) (.const 1) (.mul (.const 2) .var)
      (blockState (NUPPT.inParam z) [] (List.replicate (NUPPT.inParam z).length true)
        (NUPPT.inCoins z)))
    (NUPPT.inCoins z)

/-- The generator word pairs the public-key block-loop output with the original preimage tape. -/
theorem lamportGenFun_eq (E : List Bool → List Bool) (z : List Bool) :
    lamportGenFun E z =
      pairEncode
        (blockEncFun (lamportPairEmit E) (.const 1) (.mul (.const 2) .var)
          (blockState (NUPPT.inParam z) [] (List.replicate (NUPPT.inParam z).length true)
            (NUPPT.inCoins z)))
        (NUPPT.inCoins z) := rfl

/-- `Sign` on the layout `⟨⟨⟨1^n, ⟨sk, m⟩⟩, α⟩, r⟩`: the concatenation of the `x_i^{m_i}`. -/
def lamportSignFun (z : List Bool) : List Bool :=
  decListFun pairSndD (pairEncode []
    (blockEncFun lamportSelEmit (.const 1) (.mul (.const 2) .var)
      (blockState (NUPPT.inParam z) [] (pairSndD (NUPPT.inArg z)) (pairFstD (NUPPT.inArg z)))))

/-- The signing word concatenates the preimage blocks selected by the message bits. -/
theorem lamportSignFun_eq (z : List Bool) :
    lamportSignFun z =
      decListFun pairSndD (pairEncode []
        (blockEncFun lamportSelEmit (.const 1) (.mul (.const 2) .var)
          (blockState (NUPPT.inParam z) [] (pairSndD (NUPPT.inArg z))
            (pairFstD (NUPPT.inArg z))))) := rfl

/-- `Ver` on `⟨1^n, ⟨pk, ⟨m, σ⟩⟩⟩`: `[true]` iff `m` has `n` bits, `σ` has `n²` bits, and the
images of the `n`-bit blocks of `σ` are the public-key entries selected by `m`. -/
def lamportVerFun (L : PolyExpr) (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  [(decide ((pairFstD (pairSndD (pairSndD w))).length = (pairFstD w).length) &&
      decide ((pairSndD (pairSndD (pairSndD w))).length =
        (pairFstD w).length * (pairFstD w).length)) &&
    decide (blockEncFun (lamportEvalEmit E) (.const 1) .var
        (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
          (pairSndD (pairSndD (pairSndD w)))) =
      blockEncFun lamportPkEmit (.const 1) (lamportPkBlock L)
        (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w))) (pairFstD (pairSndD w))))]

/-- Verification conjoins the message and signature length tests with equality of the
signature-image word and the selected public-key word. -/
theorem lamportVerFun_eq (L : PolyExpr) (E : List Bool → List Bool) (w : List Bool) :
    lamportVerFun L E w =
      [(decide ((pairFstD (pairSndD (pairSndD w))).length = (pairFstD w).length) &&
          decide ((pairSndD (pairSndD (pairSndD w))).length =
            (pairFstD w).length * (pairFstD w).length)) &&
        decide (blockEncFun (lamportEvalEmit E) (.const 1) .var
            (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
              (pairSndD (pairSndD (pairSndD w)))) =
          blockEncFun lamportPkEmit (.const 1) (lamportPkBlock L)
            (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
              (pairFstD (pairSndD w))))] := rfl

/-! ### Efficiency -/

section Efficiency

variable {E : List Bool → List Bool} (hE : PolyTimeComputable E)

include hE in
/-- `f(x)` on a layout is polynomial-time. -/
theorem polyTimeComputable_lamportEvalEmit : PolyTimeComputable (lamportEvalEmit E) :=
  hE.comp (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)

include hE in
/-- `Gen`'s emission is polynomial-time. -/
theorem polyTimeComputable_lamportPairEmit : PolyTimeComputable (lamportPairEmit E) := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hp := hu.pairEncode NUPPT.polyTimeComputable_inCoins
  have h := (hE.comp (hu.pairEncode ((polyTimeComputable_pairTakePoly .var).comp hp))).pairEncode
    (hE.comp (hu.pairEncode ((polyTimeComputable_pairDropPoly .var).comp hp)))
  convert h using 1
  funext v
  simp [lamportPairEmit, Function.comp_apply]

/-- `Sign`'s emission is polynomial-time. -/
theorem polyTimeComputable_lamportSelEmit : PolyTimeComputable lamportSelEmit := by
  have hp := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have h := polyTimeComputable_ite
    (polyTimeComputable_headD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))
    ((polyTimeComputable_pairDropPoly .var).comp hp)
    ((polyTimeComputable_pairTakePoly .var).comp hp)
  convert h using 1
  funext v
  simp [lamportSelEmit, Function.comp_apply]

/-- `Ver`'s selection is polynomial-time. -/
theorem polyTimeComputable_lamportPkEmit : PolyTimeComputable lamportPkEmit := by
  have hc := NUPPT.polyTimeComputable_inCoins
  have h := polyTimeComputable_ite
    (polyTimeComputable_headD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp hc)
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp hc)
  convert h using 1

include hE in
/-- `Gen` is polynomial-time. -/
theorem polyTimeComputable_lamportGenFun : PolyTimeComputable (lamportGenFun E) := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hst := hu.pairEncode ((polyTimeComputable_const []).pairEncode
    ((polyTimeComputable_unary.comp hu).pairEncode NUPPT.polyTimeComputable_inCoins))
  have h := ((blockEncFun_poly (polyTimeComputable_lamportPairEmit hE) (.const 1)
    (.mul (.const 2) .var)).comp hst).pairEncode NUPPT.polyTimeComputable_inCoins
  refine h.congr fun z => ?_
  simp only [lamportGenFun_eq, blockState_eq, Function.comp_apply]

/-- `Sign` is polynomial-time. -/
theorem polyTimeComputable_lamportSignFun : PolyTimeComputable lamportSignFun := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hArg := NUPPT.polyTimeComputable_inArg
  have hst := hu.pairEncode ((polyTimeComputable_const []).pairEncode
    ((polyTimeComputable_pairSndD.comp hArg).pairEncode (polyTimeComputable_pairFstD.comp hArg)))
  have h := (decListFun_poly polyTimeComputable_pairSndD).comp
    ((polyTimeComputable_const []).pairEncode
      ((blockEncFun_poly polyTimeComputable_lamportSelEmit (.const 1)
        (.mul (.const 2) .var)).comp hst))
  refine h.congr fun z => ?_
  simp only [lamportSignFun_eq, blockState_eq, Function.comp_apply]

include hE in
/-- `Ver` is polynomial-time: two length tests (`polyTimeComputable_lenEq`) and an equality of
two block loops (`polyTimeComputable_pairEq`).

**Proof sketch.** Project the parameter, public key, message and signature from the input.
Compare the message length with `n` and the signature length with `n²`, representing the latter
bound by a unary square. The two polynomial-time block loops produce the images of the
signature blocks and the public-key entries selected by the message. Compare these two words
and conjoin the result with the length tests. -/
theorem polyTimeComputable_lamportVerFun (L : PolyExpr) :
    PolyTimeComputable (lamportVerFun L E) := by
  have hu := polyTimeComputable_pairFstD
  have hpk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hm := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hσ := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have h₁ : PolyTimeComputable fun w =>
      [decide ((pairFstD (pairSndD (pairSndD w))).length = (pairFstD w).length)] := by
    convert polyTimeComputable_lenEq.comp (hm.pairEncode hu) using 1
    funext w
    simp [Function.comp_apply]
  have h₂ : PolyTimeComputable fun w =>
      [decide ((pairSndD (pairSndD (pairSndD w))).length =
        (pairFstD w).length * (pairFstD w).length)] := by
    convert polyTimeComputable_lenEq.comp
      (hσ.pairEncode ((polyTimeComputable_unaryPoly (.mul .var .var)).comp hu)) using 1
    funext w
    simp [Function.comp_apply]
  have hX := (blockEncFun_poly (polyTimeComputable_lamportEvalEmit hE) (.const 1) .var).comp
    (hu.pairEncode ((polyTimeComputable_const []).pairEncode (hm.pairEncode hσ)))
  have hY := (blockEncFun_poly polyTimeComputable_lamportPkEmit (.const 1)
    (lamportPkBlock L)).comp
    (hu.pairEncode ((polyTimeComputable_const []).pairEncode (hm.pairEncode hpk)))
  have h₃ : PolyTimeComputable fun w =>
      [decide (blockEncFun (lamportEvalEmit E) (.const 1) .var
          (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
            (pairSndD (pairSndD (pairSndD w)))) =
        blockEncFun lamportPkEmit (.const 1) (lamportPkBlock L)
          (blockState (pairFstD w) [] (pairFstD (pairSndD (pairSndD w)))
            (pairFstD (pairSndD w))))] := by
    refine (polyTimeComputable_pairEq.comp (hX.pairEncode hY)).congr fun w => ?_
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
    apply congrArg (fun b : Bool => [b])
    apply decide_eq_decide.mpr
    simp only [blockState_eq]
  exact polyTimeComputable_and (polyTimeComputable_and h₁ h₂) h₃

/-! ### The machines -/

/-- The machine `Gen`, with `2n²` coins. -/
noncomputable def lamportGen : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_lamportGenFun hE) (.mul (.mul (.const 2) .var) .var)

/-- The machine `Sign`, deterministic. -/
noncomputable def lamportSign : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_lamportSignFun (.const 0)

/-- Lamport's generator uses the coin polynomial `2n²`. -/
theorem lamportGen_coins : (lamportGen hE).coins = .mul (.mul (.const 2) .var) .var := by
  unfold lamportGen
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- The generator's coin tape has `2n²` bits at parameter `n`. -/
theorem lamportGen_coinLen (n : ℕ) : (lamportGen hE).coinLen n = 2 * n * n := by
  rw [NUPPT.coinLen_eq, lamportGen_coins]
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]

/-- Lamport's generator coin tapes are equivalent to its row-major preimage tables. -/
noncomputable def lamportCoinTables (n : ℕ) : (lamportGen hE).Coins n ≃ LamportFill.Table n :=
  (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n)) (Equiv.refl Bool)).trans
    (LamportFill.tableCoins n)

/-- The coin-table equivalence first casts the tape width to `2n²`, then groups its blocks. -/
theorem lamportCoinTables_eq (n : ℕ) :
    lamportCoinTables hE n =
      (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n)) (Equiv.refl Bool)).trans
        (LamportFill.tableCoins n) := rfl

/-- The inverse coin-table equivalence serializes the table and casts back to the generator's
declared coin length. -/
theorem lamportCoinTables_symm (n : ℕ) (T : LamportFill.Table n) :
    (lamportCoinTables hE n).symm T =
      (Equiv.arrowCongr (finCongr (lamportGen_coinLen hE n).symm) (Equiv.refl Bool))
        ((LamportFill.tableCoins n).symm T) := rfl

/-- The coin tape for table `T` is exactly its row-major secret word. -/
theorem ofFn_lamportCoinTables_symm (n : ℕ) (T : LamportFill.Table n) :
    List.ofFn ((lamportCoinTables hE n).symm T) = LamportFill.secretWord T := by
  rw [lamportCoinTables_symm, ofFn_arrowCongr_finCongr, LamportFill.ofFn_tableCoins_symm]

/-- Serializing the table of a generator coin tape recovers that tape's word. -/
theorem secretWord_lamportCoinTables (n : ℕ) (ρ : (lamportGen hE).Coins n) :
    LamportFill.secretWord (lamportCoinTables hE n ρ) = List.ofFn ρ := by
  rw [← ofFn_lamportCoinTables_symm, Equiv.symm_apply_apply]

/-- Lamport's deterministic signer uses the zero coin polynomial. -/
theorem lamportSign_coins : lamportSign.coins = .const 0 := by
  unfold lamportSign
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- `Gen` on coins `ρ`: `⟨pk, ρ⟩`, `pk` the tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩` over the
`2n`-bit segments `x_i^0 ‖ x_i^1` of `ρ`. -/
theorem runAt_lamportGen (n : ℕ) (ρ : (lamportGen hE).Coins n) :
    (lamportGen hE).runAt n [] ρ =
      pairEncode (encodeList (List.ofFn fun i : Fin n =>
          pairEncode
            (E (pairEncode (List.replicate n true) (lamportHalf n false
              (coinBlock (2 * n) i (List.ofFn ρ)))))
            (E (pairEncode (List.replicate n true) (lamportHalf n true
              (coinBlock (2 * n) i (List.ofFn ρ)))))))
        (List.ofFn ρ) := by
  rw [NUPPT.runAt_eq]
  unfold lamportGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [lamportGenFun, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate]
  rw [show blockState (List.replicate n true) [] (List.replicate n true) (List.ofFn ρ) =
    blockState (List.replicate n true) [] (List.ofFn fun _ : Fin n => true) (List.ofFn ρ) by simp,
    blockEncFun_ofFn]
  simp [lamportPairEmit, lamportHalf]

/-- `Sign` on `⟨sk, m⟩`: the concatenation of the halves `x_i^{m_i}` of the `2n`-bit segments
of `sk`. -/
theorem runAt_lamportSign (n : ℕ) (sk : List Bool) (m : Fin n → Bool)
    (r : lamportSign.Coins n) :
    lamportSign.runAt n (pairEncode sk (List.ofFn m)) r =
      (List.ofFn fun i : Fin n => lamportHalf n (m i) (coinBlock (2 * n) i sk)).flatten := by
  rw [NUPPT.runAt_eq]
  unfold lamportSign
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [lamportSignFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode,
    pairSndD_pairEncode]
  rw [blockEncFun_ofFn, decListFun_pairSndD]
  congr 1
  simp [lamportSelEmit, lamportHalf]

end Efficiency

/-! ### The scheme -/

variable (L : PolyExpr) (f : ∀ n, (Fin n → Bool) → (Fin (L.eval n) → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hfE : ∀ n (x : Fin n → Bool), E (NUPPT.advInput n (List.ofFn x)) = List.ofFn (f n x))

/-- **The one-way function of Protocol 137.1** as a function family: `n`-bit inputs and
`L(n)`-bit outputs at parameter `n`. -/
def lamportOWF : FunFamily where
  inLen := .var
  outLen := L
  f := f

/-- Lamport's function family has input-length polynomial `n`. -/
theorem lamportOWF_inLen : (lamportOWF L f).inLen = .var := rfl

/-- Lamport's function family retains the supplied output-length polynomial `L`. -/
theorem lamportOWF_outLen : (lamportOWF L f).outLen = L := rfl

/-- Lamport's function family retains the supplied family `f`. -/
theorem lamportOWF_f : (lamportOWF L f).f = f := rfl

include hfE in
/-- On `n`-bit inputs, `E` returns `L(n)` bits (it agrees with `f`). -/
theorem length_lamportEval {n : ℕ} {x : List Bool} (hx : x.length = n) :
    (E (pairEncode (List.replicate n true) x)).length = L.eval n := by
  have h := hfE n (padFin n x)
  have hx' := Collection.ofFn_padFin_of_le (le_of_eq hx)
  simp only [hx, Nat.sub_self, List.replicate_zero, List.append_nil] at hx'
  rw [hx'] at h
  simp only [NUPPT.advInput_eq] at h
  rw [h, List.length_ofFn]

include hfE in
/-- **Correctness**: `Ver` accepts `Sign`'s signature under the generated keys.

**Proof sketch.** `runAt_lamportGen` and `runAt_lamportSign` unfold the keys and the signature.
The length tests pass (`length_flatten_ofFn`). On both sides of `Ver`'s equality, the block loop
is a tuple over the message bits (`blockEncFun_ofFn`). Block `i` of the signature is
`x_i^{m_i}` (`coinBlock_flatten_ofFn`); block `i` of the public key is the pair
`⟨f(x_i^0), f(x_i^1)⟩`, of `6L + 6` bits (`length_lamportEval`). Both entries are `f(x_i^{m_i})`. -/
theorem lamportVerFun_sign (n : ℕ) (m : Fin n → Bool) (rg : (lamportGen hE).Coins n)
    (rs : lamportSign.Coins n) :
    lamportVerFun L E (atParam n (pairEncode (pairFstD ((lamportGen hE).runAt n [] rg))
      (pairEncode (List.ofFn m) (List.ofFn (padFin (n * n) (lamportSign.runAt n
        (pairEncode (pairSndD ((lamportGen hE).runAt n [] rg)) (List.ofFn m)) rs)))))) =
      [true] := by
  rw [runAt_lamportGen]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [runAt_lamportSign]
  have hρ : (List.ofFn rg).length = 2 * n * n := by
    refine (List.length_ofFn (f := rg)).trans
      (((lamportGen hE).coinLen_eq n).trans ?_)
    simp only [lamportGen, NUPPT.coins_ofPolyTimeUniform,
      PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  have hseg : ∀ i : Fin n, (coinBlock (2 * n) i (List.ofFn rg)).length = 2 * n := by
    intro i
    apply length_coinBlock
    rw [hρ]
    have := i.isLt
    nlinarith
  have hsel : ∀ i : Fin n, (lamportHalf n (m i) (coinBlock (2 * n) i (List.ofFn rg))).length = n :=
    fun i => length_lamportHalf _ (hseg i)
  have hσ := length_flatten_ofFn _ hsel
  have hpad := Collection.ofFn_padFin_of_le (le_of_eq hσ)
  simp only [hσ, Nat.sub_self, List.replicate_zero, List.append_nil] at hpad
  rw [hpad]
  have hy : ∀ (b : Bool) (i : Fin n), (E (pairEncode (List.replicate n true)
      (lamportHalf n b (coinBlock (2 * n) i (List.ofFn rg))))).length = L.eval n :=
    fun b i => length_lamportEval L f E hfE (length_lamportHalf b (hseg i))
  have hpk : ∀ i : Fin n, (pairEncode (pairEncode
      (E (pairEncode (List.replicate n true) (lamportHalf n false
        (coinBlock (2 * n) i (List.ofFn rg)))))
      (E (pairEncode (List.replicate n true) (lamportHalf n true
        (coinBlock (2 * n) i (List.ofFn rg)))))) []).length =
      (lamportPkBlock L).eval n := by
    intro i
    simp only [length_pairEncode, hy, lamportPkBlock, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, List.length_nil]
    ring
  simp only [lamportVerFun, atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, List.length_ofFn, hσ, decide_true, Bool.true_and, List.cons.injEq,
    and_true, decide_eq_true_eq]
  have hflat : ∀ g : Fin n → List Bool,
      encodeList (List.ofFn g) = (List.ofFn fun i => pairEncode (g i) []).flatten := by
    intro g
    rw [encodeList_eq_flatMap]
    simp [List.flatMap_def, List.map_ofFn, Function.comp_def]
  rw [hflat, blockEncFun_ofFn, blockEncFun_ofFn]
  congr 1
  congr 1
  funext i
  simp only [lamportEvalEmit, lamportPkEmit, NUPPT.inParam_layout, NUPPT.inCoins_layout,
    NUPPT.inArg_layout, pairSndD_pairEncode, List.headD_cons, PolyExpr.eval_var,
    List.length_replicate]
  rw [coinBlock_flatten_ofFn _ hsel i, coinBlock_flatten_ofFn _ hpk i]
  cases m i <;> simp [lamportHalf]

include hfE in
/-- **Lamport's one-time signature scheme** [PS10, Protocol 137.1] for `f` with evaluator `E`:
`n`-bit messages, `n²`-bit signatures. -/
noncomputable def lamport : SignatureScheme where
  msgLen := .var
  sigLen := .mul .var .var
  gen := lamportGen hE
  sign := lamportSign
  ver := lamportVerFun L E
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sign_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  ver_poly := polyTimeComputable_lamportVerFun hE L
  correct := fun n m rg rs => lamportVerFun_sign L f E hE hfE n m rg rs

/-- Lamport signs messages of length `n`. -/
theorem lamport_msgLen : (lamport L f E hE hfE).msgLen = .var := rfl

/-- Lamport's signature-length polynomial is `n²`. -/
theorem lamport_sigLen : (lamport L f E hE hfE).sigLen = .mul .var .var := rfl

/-- Lamport uses its preimage-pair generator as the scheme's key generator. -/
theorem lamport_gen : (lamport L f E hE hfE).gen = lamportGen hE := rfl

/-- Lamport uses its deterministic selected-preimage signer. -/
theorem lamport_sign : (lamport L f E hE hfE).sign = lamportSign := rfl

/-- Lamport uses its length-guarded block verifier. -/
theorem lamport_ver : (lamport L f E hE hfE).ver = lamportVerFun L E := rfl

include hfE in
/-- On a serialized preimage table, key generation returns its public images and the table
itself [PS10, Protocol 137.1]. -/
theorem runAt_lamportGen_table (n : ℕ) (T : LamportFill.Table n)
    (ρ : (lamportGen hE).Coins n) (hρ : List.ofFn ρ = LamportFill.secretWord T) :
    (lamportGen hE).runAt n [] ρ =
      pairEncode (LamportFill.publicWord (LamportFill.tablePublic (f n) T))
        (LamportFill.secretWord T) := by
  have hrow (i : Fin n) :
      (List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).length = 2 * n := by
    simp only [List.length_append, List.length_ofFn]
    omega
  have hhalf (i : Fin n) (b : Bool) :
      lamportHalf n b (coinBlock (2 * n) i (LamportFill.secretWord T)) =
        List.ofFn (T (i, b)) := by
    rw [LamportFill.secretWord_eq, coinBlock_flatten_ofFn _ hrow i]
    cases b <;> simp [lamportHalf_eq]
  have hE' (x : Fin n → Bool) :
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x) := by
    simpa only [NUPPT.advInput_eq] using hfE n x
  rw [runAt_lamportGen, hρ, LamportFill.publicWord_eq]
  congr 1
  apply congrArg encodeList
  apply congrArg List.ofFn
  funext i
  rw [hhalf i false, hhalf i true, hE', hE',
    LamportFill.tablePublic_eq, LamportFill.tablePublic_eq]

/-- On a serialized preimage table, signing returns the typed signature selected from
that table, independently of its signing coins [PS10, Protocol 137.1]. -/
theorem runAt_lamportSign_table (n : ℕ) (T : LamportFill.Table n) (m : Fin n → Bool)
    (r : lamportSign.Coins n) :
    lamportSign.runAt n (pairEncode (LamportFill.secretWord T) (List.ofFn m)) r =
      List.ofFn (LamportFill.tableSignature T m) := by
  rw [runAt_lamportSign, LamportFill.ofFn_tableSignature]
  have hrow (i : Fin n) :
      (List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).length = 2 * n := by
    simp only [List.length_append, List.length_ofFn]
    omega
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [LamportFill.secretWord_eq, coinBlock_flatten_ofFn _ hrow i]
  cases m i <;> simp [lamportHalf_eq]

include hE hfE in
/-- On the canonical layout of a table, the generator string function returns its public
images paired with its secret serialization [PS10, Protocol 137.1]. -/
theorem lamportGenFun_table (n : ℕ) (T : LamportFill.Table n) :
    lamportGenFun E (NUPPT.layout (List.replicate n true) [] [] (LamportFill.secretWord T)) =
      pairEncode (LamportFill.publicWord (LamportFill.tablePublic (f n) T))
        (LamportFill.secretWord T) := by
  have h := runAt_lamportGen_table L f E hE hfE n T
    ((lamportCoinTables hE n).symm T) (ofFn_lamportCoinTables_symm hE n T)
  rw [NUPPT.runAt_eq] at h
  rw [ofFn_lamportCoinTables_symm (E := E) hE n T] at h
  unfold lamportGen at h
  rw [NUPPT.runAtL_ofPolyTimeUniform] at h
  simpa only [NUPPT.layout_eq, NUPPT.advInput_eq] using h

/-- On the canonical signing layout, the signing string function returns the selected
preimage vector [PS10, Protocol 137.1]. -/
theorem lamportSignFun_table (n : ℕ) (T : LamportFill.Table n) (m : Fin n → Bool) :
    lamportSignFun (NUPPT.layout (List.replicate n true)
      (pairEncode (LamportFill.secretWord T) (List.ofFn m)) [] []) =
        List.ofFn (LamportFill.tableSignature T m) := by
  let r : lamportSign.Coins n := fun _ => false
  have hr : List.ofFn r = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [List.length_ofFn, NUPPT.coinLen_eq, lamportSign_coins, PolyExpr.eval_const]
  have h := runAt_lamportSign_table n T m r
  rw [NUPPT.runAt_eq] at h
  unfold lamportSign at h
  rw [NUPPT.runAtL_ofPolyTimeUniform, hr] at h
  simpa only [NUPPT.layout_eq, NUPPT.advInput_eq] using h

include hfE in
/-- Verification of a typed public table accepts exactly when each signature block maps
to the image selected by the corresponding message bit [PS10, Protocol 137.1].

**Proof sketch.** Both length guards pass. The two block loops are tuple encodings of
the signature-block images and selected public images. Injectivity of the tuple encoding
and of bit-vector serialization turns their equality into coordinatewise equality. -/
theorem lamportVerFun_publicWord_iff (n : ℕ)
    (Y : (Fin n × Bool) → Fin (L.eval n) → Bool) (m : Fin n → Bool)
    (σ : Fin (n * n) → Bool) :
    lamportVerFun L E (atParam n (pairEncode (LamportFill.publicWord Y)
      (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true] ↔
      ∀ i, f n (LamportFill.signatureBlock σ i) = Y (i, m i) := by
  have hb : FunFamily.blocks n n σ = fun i => LamportFill.signatureBlock σ i := by
    funext i k
    rw [FunFamily.blocks_apply, LamportFill.signatureBlock_eq]
  have hσ := FunFamily.ofFn_blocks_symm n n (FunFamily.blocks n n σ)
  rw [Equiv.symm_apply_apply, hb] at hσ
  have hsig (i : Fin n) : (List.ofFn (LamportFill.signatureBlock σ i)).length = n :=
    List.length_ofFn
  have hpk (i : Fin n) :
      (pairEncode (pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) []).length =
        (lamportPkBlock L).eval n := by
    simp only [length_pairEncode, List.length_ofFn, List.length_nil, lamportPkBlock_eq,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    ring
  have hE' (x : Fin n → Bool) :
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x) := by
    simpa only [NUPPT.advInput_eq] using hfE n x
  simp only [lamportVerFun_eq, atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, List.length_ofFn, decide_true, Bool.true_and,
    List.cons.injEq, and_true, decide_eq_true_eq]
  rw [LamportFill.publicWord_flatten, hσ, blockEncFun_ofFn, blockEncFun_ofFn]
  have hleft : (fun i : Fin n =>
      lamportEvalEmit E (NUPPT.layout (List.replicate n true) (pairEncode [] [m i]) []
        (coinBlock n i (List.ofFn fun j => List.ofFn (LamportFill.signatureBlock σ j)).flatten))) =
        fun i => List.ofFn (f n (LamportFill.signatureBlock σ i)) := by
    funext i
    simp only [lamportEvalEmit_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout]
    rw [coinBlock_flatten_ofFn _ hsig i, hE']
  have hright : (fun i : Fin n =>
      lamportPkEmit (NUPPT.layout (List.replicate n true) (pairEncode [] [m i]) []
        (coinBlock ((lamportPkBlock L).eval n) i
          (List.ofFn fun j => pairEncode
            (pairEncode (List.ofFn (Y (j, false))) (List.ofFn (Y (j, true)))) []).flatten))) =
        fun i => List.ofFn (Y (i, m i)) := by
    funext i
    rw [coinBlock_flatten_ofFn _ hpk i]
    simp only [lamportPkEmit_eq, NUPPT.inArg_layout, NUPPT.inCoins_layout,
      pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons]
    cases m i <;> rfl
  simp only [PolyExpr.eval_var, List.length_replicate]
  rw [hleft, hright, LamportReduction.encodeList_ofFn_eq_iff]
  constructor
  · intro h i
    exact List.ofFn_injective (congrFun h i)
  · intro h
    funext i
    exact congrArg List.ofFn (h i)


/-- Machine codecs with equal move decoders, entry encoders and timeout values are equal. -/
private theorem lamport_codec_ext {ι α : Type} {spec : OracleSpec ι}
    (a b : MachineCodec spec α) (hd : a.decodeMove = b.decodeMove)
    (he : a.encodeEntry = b.encodeEntry) (ht : a.timeout = b.timeout) : a = b := by
  cases a
  cases b
  cases hd
  cases he
  cases ht
  rfl

/-- Lamport's forger codec is the canonical bit codec with query width `n`, answer width
`n²` and final width `n+n²`. -/
theorem lamport_forgerCodec (n : ℕ) :
    (lamport L f E hE hfE).forgerCodec n =
      bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n) := by
  apply lamport_codec_ext
  · funext w
    rw [SignatureScheme.forgerCodec_decodeMove, bitCodec_decodeMove]
    simp only [lamport_msgLen, lamport_sigLen, PolyExpr.eval_var, PolyExpr.eval_mul]
  · funext e
    rw [SignatureScheme.forgerCodec_encodeEntry, bitCodec_encodeEntry]
  · rw [SignatureScheme.forgerCodec_timeout, bitCodec_timeout]
    simp only [lamport_msgLen, lamport_sigLen, PolyExpr.eval_var, PolyExpr.eval_mul]

-- Probability proofs read their laws rather than reducing the sample interpreter.
run_cmd do
  for n in [``ProbComp.expect, ``ProbComp.sample, ``OracleComp.bind] do
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless status == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))

/-- Against a serialized key table, every Lamport signing call has exactly the deterministic
selected-preimage law. The equality holds for every function of the answer and state. -/
theorem lamport_signImpl_expect (n : ℕ) (T : LamportFill.Table n)
    (i : Fin 1) (m : Fin n → Bool) (s : Unit)
    (G : (Fin (n * n) → Bool) × Unit → ℝ) :
    ProbComp.expect
        ((lamport L f E hE hfE).signImpl n (LamportFill.secretWord T) i m s) G =
      ProbComp.expect (LamportFill.tableSigner T i m s) G := by
  rw [SignatureScheme.signImpl_eq, LamportFill.tableSigner_eq]
  simp only [QueryImpl.ofComp_apply, ProbComp.expect_bind, ProbComp.expect_pure,
    lamport_sign, lamport_sigLen, PolyExpr.eval_mul, PolyExpr.eval_var,
    runAt_lamportSign_table, padFin_ofFn]
  exact ProbComp.expect_const _ _

/-- Logging preserves the equality between actual Lamport signing and typed table signing,
including the full appended query and answer log. -/
theorem lamport_loggedSignImpl_expect (n : ℕ) (T : LamportFill.Table n)
    (i : Fin 1) (m : Fin n → Bool)
    (s : Unit × QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)))
    (G : (Fin (n * n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))) → ℝ) :
    ProbComp.expect
        (((lamport L f E hE hfE).signImpl n (LamportFill.secretWord T)).withLog i m s) G =
      ProbComp.expect ((LamportFill.tableSigner T).withLog i m s) G := by
  simp only [QueryImpl.withLog_apply, ProbComp.expect_bind]
  exact lamport_signImpl_expect (L := L) (f := f) (E := E) (hE := hE) (hfE := hfE)
    n T i m s.1 (fun ys =>
      ProbComp.expect (.pure (ys.1, (ys.2, s.2 ++ [⟨i, m, ys.1⟩]))) G)

include hfE in
/-- The actual one-query Lamport forgery game has exactly the typed honest-table success
probability [PS10, Definition 136.2 and proof of Theorem 137.2].

**Proof sketch.** Reindex key-generation coins by the table equivalence and use the generator
reader to identify public and secret keys. The signing machine ignores its signing coins, so
its call expectation is the deterministic table signer's expectation; the simulation
congruence theorem lifts this equality to the logged forger execution. The one-query
transcript reader identifies its output and first-query log. Finally the verifier reader
identifies acceptance with coordinatewise verification, and the freshness reader identifies
absence from the log with inequality to the optional query. -/
theorem lamport_forgeGame_accept_eq_honestProbability (A : NUPPT) (n : ℕ) :
    accept ((lamport L f E hE hfE).forgeGame A 1 n) =
      LamportFill.honestProbability (f n)
        (fun Y r => A.toCompOn
          (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
          n 1 (LamportFill.publicWord Y) r) := by
  classical
  rw [accept_eq, SignatureScheme.forgeGame_eq]
  simp only [ProbComp.prob_bind, ProbComp.prob_pure, decide_eq_true_eq,
    lamport_gen, lamport_forgerCodec]
  rw [← ProbComp.expect_sample_equiv (lamportCoinTables hE n).symm,
    LamportFill.honestProbability_eq]
  apply congrArg (ProbComp.expect (ProbComp.sample (LamportFill.Table n)))
  funext T
  have hgen := runAt_lamportGen_table
    (L := L) (f := f) (E := E) (hE := hE) (hfE := hfE) n T
    ((lamportCoinTables hE n).symm T) (ofFn_lamportCoinTables_symm hE n T)
  rw [hgen, pairFstD_pairEncode, pairSndD_pairEncode]
  apply congrArg (ProbComp.expect (ProbComp.sample (A.Coins n)))
  funext r
  let codec := bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n)
  let tree := A.toCompOn codec n 1
    (LamportFill.publicWord (LamportFill.tablePublic (f n) T)) r
  have hcost : tree.CostBoundedBy (fun _ => 1) 1 :=
    A.toCompOn_costBoundedBy codec n 1 _ r
  have hsim (G : (Fin (n + n * n) → Bool) ×
      (Unit × QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))) → ℝ) :=
    ProbComp.expect_simulate_congr
      (((lamport L f E hE hfE).signImpl n (LamportFill.secretWord T)).withLog)
      ((LamportFill.tableSigner T).withLog)
      (fun i m s H => lamport_loggedSignImpl_expect
        (L := L) (f := f) (E := E) (hE := hE) (hfE := hfE) n T i m s H)
      tree ((), []) G
  rw [hsim, LamportFill.honest_transcript T tree hcost, ProbComp.expect_pure]
  simp only [SignatureScheme.accepts_iff, lamport_ver,
    lamportVerFun_publicWord_iff (L := L) (f := f) (E := E) (hfE := hfE),
    LamportFill.tablePublic_eq,
    LamportFill.honestSuccess_iff, LamportFill.honestOutput_eq]
  apply if_congr ?_ rfl rfl
  apply and_congr_right
  intro _
  exact LamportFill.fresh_firstLog_iff T tree _


/-- For every positive parameter, some fixed position with a fair planted bit gives
reduction success at least the actual one-query forgery probability divided by `2n`
[PS10, averaging step in the proof of Theorem 137.2].

**Proof sketch.** Read the actual forgery game as the typed honest probability, then apply
the counted favorable-pair bound and select a position at least as good as its average. -/
theorem lamport_exists_best_position (A : NUPPT) (n : ℕ) (hn : 0 < n) :
    ∃ i : Fin n, accept ((lamport L f E hE hfE).forgeGame A 1 n) / (2 * (n : ℝ)) ≤
      ProbComp.expect (ProbComp.sample Bool) (fun c =>
        LamportFill.redProbability (f n)
          (fun Y r => A.toCompOn
            (bitCodec (fun _ : Fin 1 => n) (fun _ => n * n) (n + n * n))
            n 1 (LamportFill.publicWord Y) r) (i, c)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [lamport_forgeGame_accept_eq_honestProbability]
  exact LamportFill.exists_best_position (f n) _
    (fun Y r => A.toCompOn_costBoundedBy _ n 1 (LamportFill.publicWord Y) r)

/-- **Theorem 137.2: Lamport's scheme is one-time secure** [PS10, Theorem 137.2] when `f` is a
(strong) one-way function.

**Proof sketch** (the source's reduction, with its probability coupling explicit).
1. Fix a forger `A` making at most one signing query, and let `ε(n)` be its forgery probability.
   Work at `n ≥ 1`; the zero parameter is a finite exception for negligibility. The inverter
   `B` receives `1^n` and `y = f(x)` for a uniform `n`-bit `x`.
2. For the averaging argument, choose `i ← [n]` and a fair bit `c`, generate the other key
   entries, and put `y` at position `(i,c)`. Answer query `m` only when `m_i ≠ c`; otherwise
   abort, since the planted preimage is unknown. A valid forgery with `m'_i = c` reveals
   `σ'_i` with `f(σ'_i) = y`.
3. Couple this experiment to an honest execution, choosing `(i,c)` independently of that
   honest execution. The reduction agrees with it whenever it avoids revealing the planted
   preimage. For a successful honest run with query `m` and fresh forged message `m'`, the
   jointly favorable pairs satisfy `m_i ≠ c = m'_i`. Their fraction is
   `#{i : m_i ≠ m'_i}/(2n) ≥ 1/(2n)`. With no query, their fraction is exactly `1/2`.
   This counts the joint event without asserting independence after conditioning on non-abort.
4. Averaging over successful honest runs gives inversion probability at least `ε(n)/(2n)`.
   A best position at each length is at least as good as the uniform-position average; supply
   it as `O(log n)` bits of non-uniform advice and sample only the fair bit `c`. Thus the
   machine need not sample an exactly uniform element of `[n]` from a fixed finite coin tape.
5. T1 (`Games.exists_handlerMachine`) realizes the handler on `⟨y,1^i⟩`, using a fair
   bit, a complete sampled table, and the forger's coins. A successful nonaborting typed run
   has a safe query, so the handler's real output is the extracted preimage. Bounded decoding
   expands the `Nat.size n`-bit best-position advice to unary; `NUPPT.exists_withAdvice`
   supplies it without changing the coin polynomial. One-wayness makes this fixed machine's
   inversion probability negligible. Since `ε(n) ≤ 2n·inv_B(n)` for `n ≥ 1`, polynomial-factor
   closure proves one-time security, with zero handled by the finite exception.

For zero-query successful runs the extraction fraction is `1/2`, rather than just `1/(2n)`. -/
theorem lamport_oneTimeSecure (hf : (lamportOWF L f).StrongOneWay) :
    (lamport L f E hE hfE).OneTimeSecure := by
  classical
  apply LamportReduction.oneTimeSecure_of_inversion_lower
    (lamport L f E hE hfE) (lamportOWF L f) hf
  intro A
  have hW (n : ℕ) : (lamportPkBlock L).eval n = 6 * L.eval n + 6 := by
    rw [lamportPkBlock_eq]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  have hEval (n : ℕ) (x : Fin n → Bool) :
      E (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (f n x) := by
    simpa only [NUPPT.advInput_eq] using hfE n x
  obtain ⟨B, hB⟩ := LamportFill.exists_realization_machine L (lamportPkBlock L) f
    E (lamportGenFun E) lamportSignFun hE
    (polyTimeComputable_lamportGenFun hE) polyTimeComputable_lamportSignFun
    hW hEval (lamportGenFun_table L f E hE hfE) lamportSignFun_table
    coinBlock_flatten_ofFn A
  have hbest (n : ℕ) (hn : 0 < n) : ∃ i : Fin n,
      accept ((lamport L f E hE hfE).forgeGame A 1 n) / (2 * (n : ℝ)) ≤
        ProbComp.expect (ProbComp.sample Bool)
          (fun c => LamportFill.redProbability (f n)
            (LamportFill.machineForger L A n) (i, c)) := by
    simpa only [LamportFill.machineForger_eq_fun] using
      lamport_exists_best_position L f E hE hfE A n hn
  let idx : ℕ → ℕ := fun n => if hn : 0 < n then (Classical.choose (hbest n hn)).val else 0
  have hidx_le (n : ℕ) : idx n ≤ n := by
    dsimp only [idx]
    split_ifs with hn
    · exact (Classical.choose (hbest n hn)).isLt.le
    · exact Nat.zero_le n
  obtain ⟨C, hCcoins, hC⟩ := LamportFill.exists_withIndexAdvice B idx hidx_le
  refine ⟨C, fun n hn => ?_⟩
  have hnpos : 0 < n := hn
  let i : Fin n := Classical.choose (hbest n hnpos)
  have hi := Classical.choose_spec (hbest n hnpos)
  have hidx : idx n = i.val := by
    dsimp only [idx]
    rw [dif_pos hnpos]
  obtain ⟨φ, hφ⟩ := hB n
  let e : ((Bool × LamportFill.Table n) × A.Coins n) ≃ C.Coins n :=
    φ.trans (NUPPT.coinsCongr hCcoins.symm n)
  have hreal (y : Fin (L.eval n) → Bool) (T : LamportFill.Table n) (c : Bool)
      (r : A.Coins n)
      (hs : LamportFill.RedSuccess (f n) (LamportFill.machineForger L A n) y T r (i, c)) :
      ∃ x' : Fin n → Bool,
        C.runAt n (List.ofFn y) (e ((c, T), r)) = List.ofFn x' ∧ f n x' = y := by
    obtain ⟨x', hout, hfx⟩ := hφ i y T c r hs
    refine ⟨x', ?_, hfx⟩
    change C.runAt n (List.ofFn y)
      (NUPPT.coinsCongr hCcoins.symm n (φ ((c, T), r))) = List.ofFn x'
    rw [LamportFill.runAt_indexAdvice hCcoins idx hC, hidx]
    exact hout
  have hInv := LamportFill.fairBit_redProbability_le_invProbAt (lamportOWF L f)
    n A C i (LamportFill.machineForger L A n) e hreal
  exact hi.trans (by simpa only [lamportOWF_f] using hInv)

end TCSlib.Cryptography.Authentication
