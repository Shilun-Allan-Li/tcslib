/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Defs
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lamport's one-time signatures (statement phase)

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

## Main definitions

* `Authentication.lamportOWF`: `f` as a `FunFamily`.
* `Authentication.lamport`: Protocol 137.1 as a `SignatureScheme`, with correctness proved.

## Main results

* `Authentication.lamportVerFun_sign`: correctness, `Ver` accepts honest signatures.
* `Authentication.lamport_oneTimeSecure` (Thm 137.2, stated; a `sorry` under the source's sketch).

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

/-- A half of a `2n`-bit segment has `n` bits. -/
theorem length_lamportHalf {n : ℕ} (b : Bool) {s : List Bool} (hs : s.length = 2 * n) :
    (lamportHalf n b s).length = n := by
  cases b <;> simp [lamportHalf, hs] <;> omega

/-- A coin segment that lies inside the string has its full length. -/
theorem length_coinBlock {B i : ℕ} {r : List Bool} (h : (i + 1) * B ≤ r.length) :
    (coinBlock B i r).length = B := by
  have h' : i * B + B ≤ r.length := by rw [← Nat.succ_mul]; exact h
  simp only [coinBlock, List.length_take, List.length_drop]
  omega

/-- The concatenation of `q` blocks of `B` bits has `q · B` bits. -/
theorem length_flatten_ofFn {B : ℕ} : ∀ {q : ℕ} (g : Fin q → List Bool),
    (∀ i, (g i).length = B) → (List.ofFn g).flatten.length = q * B
  | 0, _, _ => by simp
  | q + 1, g, hg => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hg 0,
      length_flatten_ofFn (fun i => g i.succ) (fun i => hg i.succ), Nat.succ_mul]
    omega

/-- Segment `i` of a concatenation of `B`-bit blocks is block `i`. -/
theorem coinBlock_flatten {B : ℕ} : ∀ (l : List (List Bool)), (∀ c ∈ l, c.length = B) →
    ∀ (i : ℕ) (hi : i < l.length), coinBlock B i l.flatten = l[i]
  | [], _, _, hi => by simp at hi
  | c :: cs, hl, 0, _ => by
    have hc : c.length = B := hl c (by simp)
    simp [coinBlock, ← hc]
  | c :: cs, hl, i + 1, hi => by
    have hc : c.length = B := hl c (by simp)
    have hrest := coinBlock_flatten cs (fun d hd => hl d (by simp [hd])) i (by simpa using hi)
    simp only [List.getElem_cons_succ, ← hrest, coinBlock, List.flatten_cons]
    rw [show (i + 1) * B = c.length + i * B by rw [hc, Nat.succ_mul]; ring, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

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
    simp only [blockState, length_pairEncode, List.length_ofFn]
    omega
  unfold blockEncFun
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
  unfold decListFun
  rw [decListFun_spec pairSndD [] _ l hlen]
  simp

/-- A string of `ℓ` bits is the list of its padded reading at `ℓ`. -/
theorem ofFn_padFin_of_length {ℓ : ℕ} {w : List Bool} (h : w.length = ℓ) :
    List.ofFn (padFin ℓ w) = w := by
  subst h
  exact List.ext_getElem (by simp) fun i _ h₂ => by simp [padFin, List.getElem?_eq_getElem h₂]

/-! ### The algorithms as string functions -/

/-- `f(x)` on the layout `⟨⟨⟨1^n, y⟩, α⟩, x⟩`: `E(⟨1^n, x⟩)`. -/
def lamportEvalEmit (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  E (pairEncode (NUPPT.inParam v) (NUPPT.inCoins v))

/-- `Gen`'s emission on the layout `⟨⟨⟨1^n, y⟩, α⟩, x^0 ‖ x^1⟩`: the pair `⟨f(x^0), f(x^1)⟩`. -/
def lamportPairEmit (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairEncode (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).take (NUPPT.inParam v).length)))
    (E (pairEncode (NUPPT.inParam v) ((NUPPT.inCoins v).drop (NUPPT.inParam v).length)))

/-- `Sign`'s emission on the layout `⟨⟨⟨1^n, ⟨pk, [b]⟩⟩, α⟩, x^0 ‖ x^1⟩`: the preimage `x^b`. -/
def lamportSelEmit (v : List Bool) : List Bool :=
  if (pairSndD (NUPPT.inArg v)).headD false then (NUPPT.inCoins v).drop (NUPPT.inParam v).length
  else (NUPPT.inCoins v).take (NUPPT.inParam v).length

/-- `Ver`'s selection on the layout `⟨⟨⟨1^n, ⟨pk, [b]⟩⟩, α⟩, ⟨⟨y^0, y^1⟩, []⟩⟩` (a block of the
public key): `y^b`. -/
def lamportPkEmit (v : List Bool) : List Bool :=
  if (pairSndD (NUPPT.inArg v)).headD false then pairSndD (pairFstD (NUPPT.inCoins v))
  else pairFstD (pairFstD (NUPPT.inCoins v))

/-- The length of a public-key block `⟨⟨y^0, y^1⟩, []⟩` with `L`-bit images: `6L + 6`. -/
def lamportPkBlock (L : PolyExpr) : PolyExpr := .add (.mul (.const 6) L) (.const 6)

/-- `Gen` on the layout `⟨⟨⟨1^n, y⟩, α⟩, ρ⟩` with `2n²` coins `ρ`: `⟨pk, ρ⟩`, where `pk` is the
tuple of the pairs `⟨f(x_i^0), f(x_i^1)⟩` over the `2n`-bit segments of `ρ`. -/
def lamportGenFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode
    (blockEncFun (lamportPairEmit E) (.const 1) (.mul (.const 2) .var)
      (blockState (NUPPT.inParam z) [] (List.replicate (NUPPT.inParam z).length true)
        (NUPPT.inCoins z)))
    (NUPPT.inCoins z)

/-- `Sign` on the layout `⟨⟨⟨1^n, ⟨sk, m⟩⟩, α⟩, r⟩`: the concatenation of the `x_i^{m_i}`. -/
def lamportSignFun (z : List Bool) : List Bool :=
  decListFun pairSndD (pairEncode []
    (blockEncFun lamportSelEmit (.const 1) (.mul (.const 2) .var)
      (blockState (NUPPT.inParam z) [] (pairSndD (NUPPT.inArg z)) (pairFstD (NUPPT.inArg z)))))

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
  simp [lamportPairEmit, Function.comp]

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
  simp [lamportSelEmit, Function.comp]

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
  convert h using 1

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
  convert h using 1

include hE in
/-- `Ver` is polynomial-time: two length tests (`polyTimeComputable_lenEq`) and an equality of
two block loops (`polyTimeComputable_pairEq`). -/
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
    simp [Function.comp]
  have h₂ : PolyTimeComputable fun w =>
      [decide ((pairSndD (pairSndD (pairSndD w))).length =
        (pairFstD w).length * (pairFstD w).length)] := by
    convert polyTimeComputable_lenEq.comp
      (hσ.pairEncode ((polyTimeComputable_unaryPoly (.mul .var .var)).comp hu)) using 1
    funext w
    simp [Function.comp]
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
    convert polyTimeComputable_pairEq.comp (hX.pairEncode hY) using 1
    funext w
    simp [blockState, Function.comp]
  exact polyTimeComputable_and (polyTimeComputable_and h₁ h₂) h₃

/-! ### The machines -/

/-- The machine `Gen`, with `2n²` coins. -/
noncomputable def lamportGen : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_lamportGenFun hE) (.mul (.mul (.const 2) .var) .var)

/-- The machine `Sign`, deterministic. -/
noncomputable def lamportSign : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_lamportSignFun (.const 0)

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
  simp only [lamportGenFun, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput, pairFstD_pairEncode,
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
  simp only [lamportSignFun, NUPPT.inParam, NUPPT.inArg, NUPPT.advInput, pairFstD_pairEncode,
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

include hfE in
/-- On `n`-bit inputs, `E` returns `L(n)` bits (it agrees with `f`). -/
theorem length_lamportEval {n : ℕ} {x : List Bool} (hx : x.length = n) :
    (E (pairEncode (List.replicate n true) x)).length = L.eval n := by
  have h := hfE n (padFin n x)
  rw [ofFn_padFin_of_length hx] at h
  simp only [NUPPT.advInput] at h
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
    simp only [List.length_ofFn]
    rfl
  have hseg : ∀ i : Fin n, (coinBlock (2 * n) i (List.ofFn rg)).length = 2 * n := by
    intro i
    apply length_coinBlock
    rw [hρ]
    have := i.isLt
    nlinarith
  have hsel : ∀ i : Fin n, (lamportHalf n (m i) (coinBlock (2 * n) i (List.ofFn rg))).length = n :=
    fun i => length_lamportHalf _ (hseg i)
  have hσ := length_flatten_ofFn _ hsel
  rw [ofFn_padFin_of_length hσ]
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
  simp only [lamportVerFun, atParam, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, List.length_ofFn, hσ, decide_true, Bool.true_and, List.cons.injEq,
    and_true, decide_eq_true_eq]
  have hflat : ∀ g : Fin n → List Bool,
      encodeList (List.ofFn g) = (List.ofFn fun i => pairEncode (g i) []).flatten := by
    intro g
    rw [encodeList_eq_flatMap]
    simp [List.flatMap, List.map_ofFn, Function.comp_def]
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

/-- **Theorem 137.2: Lamport's scheme is one-time secure** [PS10, Theorem 137.2] when `f` is a
(strong) one-way function.

**Proof sketch** (the source's).
1. Fix a forger `A` with one signing query, and let `ε(n)` be its forgery probability. The
   inverter `B` gets `1^n` and `y = f(x)` for a uniform `n`-bit `x`.
2. `B` picks `i ← [n]` and `c ← {0, 1}`, generates a key pair, and replaces `f(x_i^c)` by `y`.
   It runs `A` on the public key. It answers `A`'s query `m` when `m_i = 1 − c`, and aborts
   otherwise (it does not know `f^{-1}(y)`).
3. If `A` outputs a valid `(m', σ')` with `m'_i = c`, then `f(σ'_i) = y`, and `B` outputs `σ'_i`.
4. The planted `y` is distributed as every other entry of the public key, so `(i, c)` is
   independent of `A`'s view. The query avoids the abort with probability `1/2`. A forgery
   differs from the query in some position, which is `i` with probability at least `1/n`.
   Altogether `B` inverts with probability at least `ε(n)/(2n)`.
5. `f` is one-way, so `ε(n)/(2n)` is negligible, and so is `ε`. `B` is a machine by T1
   (`Games.exists_handlerMachine`): `advIn` builds the public key from `y = z` and the seed,
   the handler answers or aborts, and `out` returns the planted signature component `σ′_i`.

If `A` makes no query, the abort never happens and the bound improves to `ε(n)/(2n)` as well. -/
theorem lamport_oneTimeSecure (hf : (lamportOWF L f).StrongOneWay) :
    (lamport L f E hE hfE).OneTimeSecure := by
  sorry

end TCSlib.Cryptography.Authentication
