/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid
import TCSlib.Cryptography.SecureComputation.GarblingSecurity
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.ClassP.BinaryArith.Words

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Yao's protocol in the OT-hybrid model (statement phase)

[PS10, Protocol 162.6]: Alice garbles a circuit for `f` and sends it with the keys of her input
bits; for each of Bob's input bits the parties run an oblivious transfer in which Bob obtains the
key of his bit; Bob evaluates the garbled circuit, sends the result to Alice, and both output it.
[PS10, Theorem 163.7]: the protocol is honest-but-curious secure. By the ruling of 2026-11-05,
both are stated here in the OT-hybrid model of [Gol04, §7.3] (`HybridProtocol otFunctionality`,
`Hybrid.lean`); the real protocol follows by composition with Protocol 160.4, which is not in
this file.

**The circuits** (`YaoCircuit`). The source garbles "a canonical circuit representation of `f`".
Here that is a uniform family of fan-in-two circuits `C_n` (`DAGCircuit`) of polynomial size, on
`inA(n) + inB(n)` inputs, with a list of `outLen(n)` output vertices. Alice's input bits are
vertices `0, …, inA − 1`, Bob's are vertices `inA, …, inA + inB − 1`. Uniformity (a
polynomial-time map from `1^n` to the description `encodeCircuit`) is what lets Alice, Bob and
the simulators build the circuit in polynomial time. The functionality gives both parties the
values of `C_n(x, y)` at the output vertices (`yaoFunctionality`).

**The garbling** is Construction 158.a of `Garbling.lean` with nested special encryption
(`GarblingSpecial.lean`), keys of `n` bits, and the randomness read from fixed blocks of Alice's
coins (`yaoSeed`): the keys, `2n` coins per row, and a shift `λ_i` per gate.

**The protocol** (`yaoHybrid`). `inB(n) · n` ideal bit-OTs, then two messages:
- call `(i, t)` gives Bob bit `t` of the key of his wire `inA + i` for his bit `y_i`;
- Alice sends the garbled tables, the keys of her input bits, and the key pair `(k⁰, k¹)` of every
  output vertex;
- Bob evaluates the garbled circuit with `runWith` and `evalGate`, decodes each output key by
  comparison with its pair, and sends the bits; under D8 the last mover's message is its output,
  and Alice outputs the message she received.

**Deviations from [PS10].**
- **The OT-hybrid model** (ruling of 2026-11-05), with the ideal calls first (`Hybrid.lean`). The
  source's proof simulates the OT transcripts with Proposition 161.5's simulators; here a party's
  view holds its OT outputs instead, and the composition theorem supplies the rest.
- **Bit OTs.** `otFunctionality` transfers one bit, so the source's OT of a key pair `(k_{i,0},
  k_{i,1})` is `n` bit OTs with the same choice bit `y_i` (the source: "it is straightforward to
  generalize this construction to handle `n`-bit values").
- **The row order: a random XOR shift.** Row `a` of gate `i` sits at the position of `a ⊕ λ_i`
  in a fixed enumeration of the assignments, for a uniform `λ_i` (`xorShift`). The source shuffles
  each table uniformly, but the `24` orders of four rows cannot be sampled exactly from a fixed
  number of coin bits. A uniform shift makes the position of the row that opens uniform and
  independent of the inputs, which is what the simulation uses (the point-and-permute idea of
  [BMR90]).
- **Output decoding.** The source does not say how Bob reads the output from the output keys.
  Here Alice sends each output vertex's key pair, and Bob maps `k⁰ ↦ 0`, `k¹ ↦ 1` (`decodeOut`).
- **Output vertices are sinks** (`YaoCircuit.outs_sink`). The decoding pairs reveal both keys of
  every output vertex, so if a gate read an output vertex `o`, Bob could open its table on both
  values of `o`. For `f(x) = (x₀, x₀ ∧ x₁)` with output vertices `x₀` and `g = x₀ ∧ x₁`, Bob
  holds both keys of `x₀`, opens the row `(1, x₁)` of `g`, and decodes `x₁` even when `x₀ = 0`.
  One identity gate per output brings any circuit to this form.
- **Lengths.** Inputs and outputs have polynomial lengths `inA(n)`, `inB(n)`, `outLen(n)` (the
  source: `x, y ∈ {0,1}^n`); the security parameter `n` is the key length.
- **Correctness** needs, besides a good garbling, distinct keys on each output vertex
  (`yaoHybrid_correct`); both hold except with negligible probability (`yaoSeed_good_whp`).
- **A joint PRF.** The two encryption layers use two PRFs `G₁`, `G₂` (`GarblingSpecial.lean`), and
  a wire's key can key both. The security theorem assumes the pair is pseudorandom under one key
  (`yaoHybrid_simulators`); the source uses one scheme for both layers.

## Main definitions

* `SecureComputation.encodeCircuit`: the description of a circuit with an output list.
* `SecureComputation.YaoCircuit`, `YaoCircuit.output`, `yaoFunctionality`: the circuit family and
  the functionality it computes.
* `SecureComputation.readBits`, `assignIdx`, `xorShift`, `yaoCoins`, `yaoSeed`: the garbling's
  randomness from Alice's coins.
* `SecureComputation.decodeMsgs`: the inverse of `Strategy.encodeMsgs`.
* `SecureComputation.yaoTables`, `yaoKeysA`, `yaoPairs`, `yaoMsg`: Alice's message.
* `SecureComputation.yaoBobTables`, `yaoBobInit`, `yaoBobValues`, `decodeOut`, `yaoBobOut`: Bob's
  evaluation.
* `SecureComputation.yaoAlice`, `yaoBob`, `yaoMain`, `yaoCall`, `yaoHybrid`: Protocol 162.6 in the
  OT-hybrid model.

## Main results

* `SecureComputation.encodeCircuit_injective`, `decodeMsgs_encodeMsgs` (proved): the encodings.
* `SecureComputation.yaoBobOut_yaoMsg` (proved): Bob's evaluation of a good garbling with distinct
  output keys gives `f(x, y)`.
* `SecureComputation.yaoHybrid_answersB_getD` (proved): Bob's OT answers are his keys.
* `SecureComputation.yaoHybrid_correct` (proved): both parties output `f(x, y)` in the hybrid
  execution when the garbling is good with distinct output keys.
* `SecureComputation.yaoSeed_good_whp`, `yaoHybrid_polyTime`, `yaoHybrid_simulators` (stated;
  `sorry`s under sketches): the garbling is good w.h.p., the protocol is efficient, and the
  simulators of Theorem 163.7.
* `SecureComputation.yaoHybrid_hbcSecure` (Theorem 163.7 in the OT-hybrid model, proved from the
  two previous results).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Protocol 162.6 and Theorem 163.7 (book pp. 156–164).
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, §7.3 (oracle-aided protocols and their composition).
* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*, STOC 1990,
  pp. 503–513 (the point-and-permute row order).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party computation*,
  Journal of Cryptology 22(2), 2009, pp. 161–188 (the simulator with one active key per wire).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography BoolCircuit

/-! ### Circuit descriptions with an output list -/

/-- **The description of a circuit with an output list** [PS10, Protocol 162.6, "a canonical
circuit representation of `f`"]: the pair of the circuit's description `DAGCircuit.encode` (the
number of inputs, the gates and the output vertex, numbers in unary) and the encoded list of the
output vertices in unary, `⟨C, ⟨o₀, ⟨o₁, …⟩⟩⟩`. The gates are encoded by `DAGGate.encode`. -/
def encodeCircuit {m k : ℕ} (C : DAGCircuit m) (outs : Fin k → ℕ) : List Bool :=
  pairEncode C.encode (Strategy.encodeMsgs (List.ofFn fun j => encodeNat (outs j)))

/-- The description of a circuit with an output list is
`⟨encode C, encodeMsgs [encodeNat o₀, …, encodeNat o_{k−1}]⟩`. -/
theorem encodeCircuit_eq {m k : ℕ} (C : DAGCircuit m) (outs : Fin k → ℕ) :
    encodeCircuit C outs =
      pairEncode C.encode (Strategy.encodeMsgs (List.ofFn fun j => encodeNat (outs j))) := rfl

/-- Encoded message lists of equal length are equal only if the lists are. -/
private theorem encodeMsgs_inj : ∀ {l l' : List (List Bool)}, l.length = l'.length →
    Strategy.encodeMsgs l = Strategy.encodeMsgs l' → l = l'
  | [], [], _, _ => rfl
  | a :: l, b :: l', hlen, h => by
    rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons] at h
    have h₁ := congrArg pairFstD h
    have h₂ := congrArg pairSndD h
    rw [pairFstD_pairEncode, pairFstD_pairEncode] at h₁
    rw [pairSndD_pairEncode, pairSndD_pairEncode] at h₂
    rw [h₁, encodeMsgs_inj (by simpa using hlen) h₂]

/-- The unary code is injective (`decodeNat_encodeNat`). -/
private theorem encodeNat_inj {a b : ℕ} (h : encodeNat a = encodeNat b) : a = b := by
  have ha := decodeNat_encodeNat a []
  have hb := decodeNat_encodeNat b []
  rw [h, hb] at ha
  exact (Prod.mk.inj (Option.some.inj ha)).1.symm

/-- **The description of a circuit with an output list is injective**: equal descriptions come
from equal circuits and equal output lists (`DAGCircuit.encode_injective`, the injectivity of the
pairing and of the unary code). -/
theorem encodeCircuit_injective {m k : ℕ} {C C' : DAGCircuit m} {outs outs' : Fin k → ℕ}
    (h : encodeCircuit C outs = encodeCircuit C' outs') : C = C' ∧ outs = outs' := by
  have h₁ := congrArg pairFstD h
  have h₂ := congrArg pairSndD h
  rw [encodeCircuit_eq, encodeCircuit_eq, pairFstD_pairEncode, pairFstD_pairEncode] at h₁
  rw [encodeCircuit_eq, encodeCircuit_eq, pairSndD_pairEncode, pairSndD_pairEncode] at h₂
  refine ⟨DAGCircuit.encode_injective m h₁, funext fun j => encodeNat_inj ?_⟩
  have h₃ := List.ofFn_injective (encodeMsgs_inj (by simp) h₂)
  exact congrFun h₃ j

/-! ### Uniform circuit families with output lists -/

/-- **A uniform circuit family for Yao's protocol** [PS10, Protocol 162.6, "a canonical circuit
representation of `f`"; §6.2.1, fan-in two]: for each `n`, a fan-in-two circuit `C_n` on
`inA(n) + inB(n)` inputs (Alice's input bits first, then Bob's) with `outLen(n)` output vertices,
none of them read by a gate, of size at most `sizeBound(n)`; and a polynomial-time map sends `1^n`
to the description of `C_n` with its output list. The circuit's own `output` field is not used.

**Deviations.** The output vertices must be sinks (see the module docstring: the decoding pairs
reveal both keys of an output vertex). Uniformity makes the parties efficient; the source fixes a
circuit for `f` without discussing how it is computed. -/
structure YaoCircuit where
  /-- Alice's input length. -/
  inA : PolyExpr
  /-- Bob's input length. -/
  inB : PolyExpr
  /-- The output length. -/
  outLen : PolyExpr
  /-- A polynomial bound on the circuits' sizes. -/
  sizeBound : PolyExpr
  /-- The circuit at parameter `n`: Alice's inputs are vertices `0, …, inA − 1`, Bob's follow. -/
  circ : ∀ n, DAGCircuit (inA.eval n + inB.eval n)
  /-- The output vertices at parameter `n`. -/
  outs : ∀ n, Fin (outLen.eval n) → ℕ
  /-- The output vertices are vertices of the circuit. -/
  outs_lt : ∀ n j, outs n j < (circ n).size
  /-- No gate reads an output vertex. -/
  outs_sink : ∀ n j, ∀ g ∈ (circ n).gates, outs n j ∉ g.args
  /-- The circuits have fan-in two (and are well formed). -/
  fanin : ∀ n, (circ n).IsFaninTwo
  /-- The circuits have polynomial size. -/
  size_le : ∀ n, (circ n).size ≤ sizeBound.eval n
  /-- The family is uniform: a polynomial-time map sends `1^n` to the description of `C_n`. -/
  uniform : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n, E (List.replicate n true) = encodeCircuit (circ n) (outs n)

namespace YaoCircuit

variable (Y : YaoCircuit)

/-- **The function computed by the family**: on Alice's input `x` and Bob's input `y`, bit `j` is
the value of `C_n(x, y)` at the output vertex `o_j`. -/
def output (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) :
    Fin (Y.outLen.eval n) → Bool :=
  fun j => ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false

/-- Bit `j` of the output is the value of `C_n(x, y)` at the output vertex `o_j`. -/
theorem output_apply (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool)
    (j : Fin (Y.outLen.eval n)) :
    Y.output n x y j = ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false := rfl

end YaoCircuit

/-- **The functionality of a Yao circuit family** [PS10, Protocol 162.6, "A and B output the
result `f(x, y)`"]: Alice's input has `inA(n)` bits, Bob's `inB(n)`, and both parties receive the
`outLen(n)` bits `C_n(x, y)` at the output vertices. Its field equations are
`yaoFunctionality_inA`, …, `yaoFunctionality_f`. -/
def yaoFunctionality (Y : YaoCircuit) : Functionality where
  inA := Y.inA
  inB := Y.inB
  outA := Y.outLen
  outB := Y.outLen
  f n x y := (Y.output n x y, Y.output n x y)

attribute [simps (config := { isSimp := false }) inA inB outA outB f] yaoFunctionality

/-! ### The garbling from Alice's coins -/

/-- **`len` bits of a string from position `off`**: bit `t` is the string's bit `off + t`, or
`false` past its end. -/
def readBits (w : List Bool) (off len : ℕ) : Fin len → Bool := fun t => w.getD (off + t) false

/-- Bit `t` of `readBits w off len` is bit `off + t` of `w` (`false` past its end). -/
theorem readBits_apply (w : List Bool) (off len : ℕ) (t : Fin len) :
    readBits w off len t = w.getD (off + t) false := rfl

/-- **The index of an assignment**: the assignment `a` of `len` positions read as a binary number,
position `0` the least significant bit, `Σ_t a_t · 2^t`. It is below `4` for at most two
positions. -/
def assignIdx {len : ℕ} (a : Fin len → Bool) : ℕ :=
  (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0

/-- The index of an assignment is the fold `b₀ + 2 (b₁ + 2 (⋯))` of its bits. -/
theorem assignIdx_eq {len : ℕ} (a : Fin len → Bool) :
    assignIdx a = (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 := rfl

/-- **The XOR shift by `λ`**: the permutation `a ↦ a ⊕ λ` of the assignments of `len` positions,
an involution. It is the row order of the garbled tables ([BMR90]'s point-and-permute; declared
deviation from [PS10, §6.2.3]'s uniform shuffle, see the module docstring). -/
def xorShift {len : ℕ} (l : Fin len → Bool) : Equiv.Perm (Fin len → Bool) :=
  Function.Involutive.toPerm (fun a p => xor (a p) (l p)) fun a => funext fun p => by
    show xor (xor (a p) (l p)) (l p) = a p
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The XOR shift by `λ` maps `a` to `a ⊕ λ`, position by position. -/
theorem xorShift_apply {len : ℕ} (l a : Fin len → Bool) :
    xorShift l a = fun p => xor (a p) (l p) := rfl

/-- The inverse XOR shift is the same pointwise XOR operation. -/
theorem xorShift_symm_apply {len : ℕ} (l a : Fin len → Bool) :
    (xorShift l).symm a = fun p => xor (a p) (l p) := rfl

/-- **Alice's number of coins**: `10 · S(n) · n + 2 · S(n)` for the size bound `S`; `2 · S(n) · n`
for the keys, `8 · S(n) · n` for the row coins (at most four rows of `2n` coins per gate), and
`2 · S(n)` for the shifts. -/
def yaoCoins (Y : YaoCircuit) : PolyExpr :=
  .add (.mul (.mul (.const 10) Y.sizeBound) .var) (.mul (.const 2) Y.sizeBound)

/-- Alice's coin-count expression is `10 S(n)n + 2 S(n)` syntactically. -/
theorem yaoCoins_eq (Y : YaoCircuit) :
    yaoCoins Y = .add (.mul (.mul (.const 10) Y.sizeBound) .var)
      (.mul (.const 2) Y.sizeBound) := rfl

/-- Alice has `10 · S(n) · n + 2 · S(n)` coins. -/
theorem yaoCoins_eval (Y : YaoCircuit) (n : ℕ) :
    (yaoCoins Y).eval n = 10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n := rfl

/-- **The garbling's randomness from Alice's coins** [PS10, §6.2.2–6.2.3: random key pairs,
encryption coins, shuffled rows], at key length `n`, with `S = sizeBound(n)`:
- the key of vertex `v` for the bit `b`: the `n` coins from `(b · S + v) · n`;
- the coins of row `a` of gate `i`: the `2n` coins from `2 S n + (4 i + idx(a)) · 2n`, split in
  halves (the outer and inner layer's coins);
- the row order of gate `i`: the XOR shift by the coins from `10 S n + 2 i`.

For a fan-in-two circuit of size at most `S` these blocks are disjoint, so uniform coins give
independent uniform keys and row coins, and uniform shifts.

**Deviation.** The row order is a uniform XOR shift, not a uniform permutation (module docstring).
-/
def yaoSeed (Y : YaoCircuit) (n : ℕ) (r : List Bool) :
    GarbleSeed (Y.circ n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) :=
  (fun v b => readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n,
    fun i a => (readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n)) n,
      readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n) + n) n),
    fun i => xorShift (readBits r (10 * Y.sizeBound.eval n * n + 2 * i) _))

/-- The key of vertex `v` for the bit `b` is the `n` coins from `(b · S + v) · n`. -/
theorem yaoSeed_fst (Y : YaoCircuit) (n : ℕ) (r : List Bool) (v : Fin (Y.circ n).size)
    (b : Bool) :
    (yaoSeed Y n r).1 v b = readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n := rfl

/-- The coins of row `a` of gate `i` are the two `n`-bit halves of the `2n` coins from
`2 S n + (4 i + idx(a)) · 2n`. -/
theorem yaoSeed_snd_fst (Y : YaoCircuit) (n : ℕ) (r : List Bool)
    (i : Fin (Y.circ n).gates.length) (a : Fin ((Y.circ n).gates[i]).args.length → Bool) :
    (yaoSeed Y n r).2.1 i a =
      (readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n)) n,
        readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n) + n) n) := rfl

/-- The row order of gate `i` is the XOR shift by the coins from `10 S n + 2 i`. -/
theorem yaoSeed_snd_snd (Y : YaoCircuit) (n : ℕ) (r : List Bool)
    (i : Fin (Y.circ n).gates.length) :
    (yaoSeed Y n r).2.2 i = xorShift (readBits r (10 * Y.sizeBound.eval n * n + 2 * i) _) := rfl

/-- The key of a vertex `v` of the circuit for the bit `b` is the `n` coins from
`(b · S + v) · n`. -/
theorem keyAt_yaoSeed (Y : YaoCircuit) (n : ℕ) (r : List Bool) {v : ℕ}
    (hv : v < (Y.circ n).size) (b : Bool) :
    keyAt (Y.circ n) (yaoSeed Y n r) v b =
      readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n := by
  rw [keyAt_eq, dif_pos hv, yaoSeed_fst]

/-! ### Message lists -/

/-- Decoding with fuel: at most `k` components, stopping at the empty string. -/
private def decodeMsgsFuel : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | k + 1, w => if w = [] then [] else pairFstD w :: decodeMsgsFuel k (pairSndD w)

/-- **Decoding a message list**, the inverse of `Strategy.encodeMsgs`: the first component of the
string, then the decoding of the second, until the empty string (at most `|w|` components). -/
def decodeMsgs (w : List Bool) : List (List Bool) := decodeMsgsFuel w.length w

/-- Decoding any word gives `[]` when the word is empty, and otherwise its first pair
component followed by the decoding of its second component, including on malformed words.

**Proof sketch.** The second projection of a nonempty word is strictly shorter, by the
public pairing-length lemma. Induct on the fuel to compare the local decoder with the
existing word-list decoder whenever the fuel is at least the word length. The defining fuel
is therefore sufficient. The public empty and nonempty equations of the word-list decoder
give the asserted step without exposing the private fuel function. -/
theorem decodeMsgs_eq (w : List Bool) :
    decodeMsgs w = if w = [] then [] else pairFstD w :: decodeMsgs (pairSndD w) := by
  have hFuel : ∀ (k : ℕ) (v : List Bool), v.length ≤ k →
      decodeMsgsFuel k v = BinArith.decWords v := by
    intro k
    induction k with
    | zero =>
      intro v hv
      have hvnil : v = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hv)
      subst v
      rw [decodeMsgsFuel, BinArith.decWords_nil]
    | succ k ih =>
      intro v hv
      by_cases hvnil : v = []
      · subst v
        rw [decodeMsgsFuel, if_pos rfl, BinArith.decWords_nil]
      · rw [decodeMsgsFuel, if_neg hvnil, BinArith.decWords_of_ne hvnil]
        exact congrArg (List.cons (pairFstD v))
          (ih (pairSndD v)
            (Nat.le_of_lt_succ ((BinArith.length_pairSndD_lt hvnil).trans_le hv)))
  have hdecode : ∀ v : List Bool, decodeMsgs v = BinArith.decWords v :=
    fun v => hFuel v.length v (Nat.le_refl v.length)
  by_cases hw : w = []
  · subst w
    rw [if_pos rfl, hdecode [], BinArith.decWords_nil]
  · rw [if_neg hw, hdecode w, BinArith.decWords_of_ne hw, hdecode (pairSndD w)]

/-- An encoded list of `k` messages has at least `k` bits. -/
private theorem length_le_length_encodeMsgs :
    ∀ l : List (List Bool), l.length ≤ (Strategy.encodeMsgs l).length
  | [] => le_refl _
  | m :: l => by
    rw [Strategy.encodeMsgs_cons, length_pairEncode, List.length_cons]
    have := length_le_length_encodeMsgs l
    omega

/-- With enough fuel, decoding an encoded list gives the list back. -/
private theorem decodeMsgsFuel_encodeMsgs :
    ∀ (l : List (List Bool)) (k : ℕ), l.length ≤ k →
      decodeMsgsFuel k (Strategy.encodeMsgs l) = l
  | [], 0, _ => rfl
  | [], _ + 1, _ => by simp [decodeMsgsFuel]
  | _ :: _, 0, h => absurd h (by simp)
  | m :: l, k + 1, h => by
    rw [Strategy.encodeMsgs_cons, decodeMsgsFuel, if_neg (pairEncode_ne_nil _ _),
      pairFstD_pairEncode, pairSndD_pairEncode,
      decodeMsgsFuel_encodeMsgs l k (by simpa using h)]

/-- **Decoding inverts the message-list encoding**: `decodeMsgs (encodeMsgs l) = l`. -/
theorem decodeMsgs_encodeMsgs (l : List (List Bool)) :
    decodeMsgs (Strategy.encodeMsgs l) = l :=
  decodeMsgsFuel_encodeMsgs l _ (length_le_length_encodeMsgs l)

/-- The empty string decodes to the empty list. -/
theorem decodeMsgs_nil : decodeMsgs [] = [] := rfl

/-! ### Alice's message -/

variable (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)

/-- **The garbled tables** [PS10, Protocol 162.6, "A generates a garbled circuit … and sends the
circuit"]: gate by gate, the garbled table of `yaoSeed` with nested special encryption, each
table an encoded list of rows, and the tables an encoded list. -/
noncomputable def yaoTables (n : ℕ) (r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun i : Fin (Y.circ n).gates.length =>
    Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) i))

/-- The garbled tables are the encoded list of the encoded garbled tables. -/
theorem yaoTables_eq (n : ℕ) (r : List Bool) :
    yaoTables Y E₁ E₂ n r = Strategy.encodeMsgs (List.ofFn fun i : Fin (Y.circ n).gates.length =>
      Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) i)) :=
  rfl

/-- **Alice's input keys** [PS10, Protocol 162.6, "the input keys corresponding to the bits of
`x`"]: the encoded list of the keys `k_v^{x_v}` of her input vertices `v < inA(n)`, for her
input `xs`. -/
def yaoKeysA (n : ℕ) (xs r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun v : Fin (Y.inA.eval n) =>
    List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) v (xs.getD v false)))

/-- Alice's input keys are the encoded list of `k_v^{x_v}` for `v < inA(n)`. -/
theorem yaoKeysA_eq (n : ℕ) (xs r : List Bool) :
    yaoKeysA Y n xs r = Strategy.encodeMsgs (List.ofFn fun v : Fin (Y.inA.eval n) =>
      List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) v (xs.getD v false))) := rfl

/-- **The decoding pairs**: for each output index `j`, the pair `⟨k_{o_j}^0, k_{o_j}^1⟩` of the
keys of the output vertex `o_j`, as an encoded list.

**Deviation.** Not in [PS10], which does not say how Bob reads the output (module docstring). -/
def yaoPairs (n : ℕ) (r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun j : Fin (Y.outLen.eval n) =>
    pairEncode (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false))
      (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true)))

/-- The decoding pairs are the encoded list of `⟨k_{o_j}^0, k_{o_j}^1⟩`. -/
theorem yaoPairs_eq (n : ℕ) (r : List Bool) :
    yaoPairs Y n r = Strategy.encodeMsgs (List.ofFn fun j : Fin (Y.outLen.eval n) =>
      pairEncode (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false))
        (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true))) := rfl

/-- **Alice's message** [PS10, Protocol 162.6, first step]: `⟨tables, ⟨her input keys, decoding
pairs⟩⟩`, for her input `xs` and her coins `r`. -/
noncomputable def yaoMsg (n : ℕ) (xs r : List Bool) : List Bool :=
  pairEncode (yaoTables Y E₁ E₂ n r) (pairEncode (yaoKeysA Y n xs r) (yaoPairs Y n r))

/-- Alice's message is `⟨tables, ⟨input keys, decoding pairs⟩⟩`. -/
theorem yaoMsg_eq (n : ℕ) (xs r : List Bool) :
    yaoMsg Y E₁ E₂ n xs r =
      pairEncode (yaoTables Y E₁ E₂ n r) (pairEncode (yaoKeysA Y n xs r) (yaoPairs Y n r)) := rfl

/-! ### Bob's evaluation -/

/-- **The tables Bob reads**: at a gate vertex `v ≥ inA + inB`, the decoded list of rows of the
`(v − inA − inB)`-th encoded table of the message; none at an input vertex. -/
def yaoBobTables (n : ℕ) (msg : List Bool) (v : ℕ) : List (List Bool) :=
  if Y.inA.eval n + Y.inB.eval n ≤ v then
    decodeMsgs ((decodeMsgs (pairFstD msg)).getD (v - (Y.inA.eval n + Y.inB.eval n)) [])
  else []

/-- Bob's table at `v` is the decoded `(v − inA − inB)`-th table at a gate vertex, and empty at
an input vertex. -/
theorem yaoBobTables_eq (n : ℕ) (msg : List Bool) (v : ℕ) :
    yaoBobTables Y n msg v = if Y.inA.eval n + Y.inB.eval n ≤ v then
      decodeMsgs ((decodeMsgs (pairFstD msg)).getD (v - (Y.inA.eval n + Y.inB.eval n)) [])
    else [] := rfl

/-- **Bob's input keys** [PS10, Protocol 162.6, "using the keys for all input wires"]: at Alice's
vertex `v < inA(n)`, the `v`-th key of the message; at his vertex `inA(n) + i`, bits `i · n` to
`i · n + n − 1` of his OT answers `ans`. -/
def yaoBobInit (n : ℕ) (msg ans : List Bool) : List (Fin n → Bool) :=
  List.ofFn fun v : Fin (Y.inA.eval n + Y.inB.eval n) =>
    if (v : ℕ) < Y.inA.eval n then padFin n ((decodeMsgs (pairFstD (pairSndD msg))).getD v [])
    else readBits ans (((v : ℕ) - Y.inA.eval n) * n) n

/-- Bob's input keys: Alice's `v`-th key from the message at `v < inA`, his answer bits from
`(v − inA) · n` otherwise. -/
theorem yaoBobInit_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobInit Y n msg ans = List.ofFn fun v : Fin (Y.inA.eval n + Y.inB.eval n) =>
      if (v : ℕ) < Y.inA.eval n then padFin n ((decodeMsgs (pairFstD (pairSndD msg))).getD v [])
      else readBits ans (((v : ℕ) - Y.inA.eval n) * n) n := rfl

/-- **Bob's garbled evaluation** [PS10, Protocol 162.6, "B evaluates the circuit"; §6.2.3, "attempt
to decrypt all four rows"]: `runWith` over the gates of `C_n` from his input keys, each gate opened
by `evalGate` on the table he read at its vertex. -/
def yaoBobValues (n : ℕ) (msg ans : List Bool) : List (Fin n → Bool) :=
  runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ n) (yaoBobTables Y n msg) vs.length g vs)
    (Y.circ n).gates (yaoBobInit Y n msg ans)

/-- Bob's garbled evaluation is `runWith` of `evalGate` on his tables from his input keys. -/
theorem yaoBobValues_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobValues Y E₁ E₂ n msg ans =
      runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ n) (yaoBobTables Y n msg) vs.length g vs)
        (Y.circ n).gates (yaoBobInit Y n msg ans) := rfl

/-- **Decoding an output key** by its pair `p = ⟨k⁰, k¹⟩`: `k⁰ ↦ false`, `k¹ ↦ true`, anything
else `↦ false`.

**Deviation.** Not in [PS10] (module docstring). -/
def decodeOut (k p : List Bool) : Bool :=
  if k = pairFstD p then false else decide (k = pairSndD p)

/-- Decoding an output key: `false` if it is the first key of the pair, otherwise whether it is
the second. -/
theorem decodeOut_eq (k p : List Bool) :
    decodeOut k p = if k = pairFstD p then false else decide (k = pairSndD p) := rfl

/-- The first key of a pair decodes to `false`. -/
theorem decodeOut_fst (k₀ k₁ : List Bool) : decodeOut k₀ (pairEncode k₀ k₁) = false := by
  rw [decodeOut, pairFstD_pairEncode, if_pos rfl]

/-- The second key of a pair of distinct keys decodes to `true`. -/
theorem decodeOut_snd (k₀ k₁ : List Bool) (h : k₁ ≠ k₀) :
    decodeOut k₁ (pairEncode k₀ k₁) = true := by
  rw [decodeOut, pairFstD_pairEncode, pairSndD_pairEncode, if_neg h, decide_eq_true rfl]

/-- **Bob's result** [PS10, Protocol 162.6, last step]: for each output index `j`, the key his
evaluation reaches at the output vertex `o_j`, decoded by the `j`-th pair of the message. -/
def yaoBobOut (n : ℕ) (msg ans : List Bool) : List Bool :=
  List.ofFn fun j : Fin (Y.outLen.eval n) =>
    decodeOut (List.ofFn ((yaoBobValues Y E₁ E₂ n msg ans).getD (Y.outs n j) default))
      ((decodeMsgs (pairSndD (pairSndD msg))).getD j [])

/-- Bob's result: bit `j` decodes the key at `o_j` by the `j`-th decoding pair. -/
theorem yaoBobOut_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobOut Y E₁ E₂ n msg ans = List.ofFn fun j : Fin (Y.outLen.eval n) =>
      decodeOut (List.ofFn ((yaoBobValues Y E₁ E₂ n msg ans).getD (Y.outs n j) default))
        ((decodeMsgs (pairSndD (pairSndD msg))).getD j []) := rfl

/-! ### The protocol -/

/-- **Alice in Protocol 162.6** [PS10] (the prover's role, `Defs.lean`'s convention), on common
input `1^n`, private input `⟨x, answers⟩` (her answers are empty: OT gives the sender `⊥`) and
coins `r`: on the empty history, her message `yaoMsg`; on a nonempty history, its first message,
which is her output ("A and B output the result"). Her coins are `yaoCoins`. -/
noncomputable def yaoAlice : Strategy where
  next x z r hist := match hist with
    | [] => yaoMsg Y E₁ E₂ x.length (pairFstD z) r
    | m :: _ => m
  coins := yaoCoins Y

/-- On the empty history Alice sends `yaoMsg` at `|x|` for her input `pairFstD z`. -/
theorem yaoAlice_next_nil (x z r : List Bool) :
    (yaoAlice Y E₁ E₂).next x z r [] = yaoMsg Y E₁ E₂ x.length (pairFstD z) r := rfl

/-- On a nonempty history Alice returns its first message. -/
theorem yaoAlice_next_cons (x z r m : List Bool) (hist : List (List Bool)) :
    (yaoAlice Y E₁ E₂).next x z r (m :: hist) = m := rfl

/-- Alice's coin polynomial is `yaoCoins`. -/
theorem yaoAlice_coins : (yaoAlice Y E₁ E₂).coins = yaoCoins Y := rfl

/-- **Bob in Protocol 162.6** [PS10] (the verifier's role), on common input `1^n` and private
input `⟨y, answers⟩`: his result `yaoBobOut` on the first message received and his answers. He
moves last, so his message is also his output. He uses no coins. -/
def yaoBob : Strategy where
  next x z _ hist := yaoBobOut Y E₁ E₂ x.length (hist.headD []) (pairSndD z)
  coins := .const 0

/-- Bob's message is `yaoBobOut` at `|x|` on the first message received and his answers. -/
theorem yaoBob_next (x z r : List Bool) (hist : List (List Bool)) :
    (yaoBob Y E₁ E₂).next x z r hist =
      yaoBobOut Y E₁ E₂ x.length (hist.headD []) (pairSndD z) := rfl

/-- Bob uses no coins. -/
theorem yaoBob_coins : (yaoBob Y E₁ E₂).coins = .const 0 := rfl

/-- **The message phase of Protocol 162.6** [PS10]: two messages, Alice first; Alice sends the
garbled circuit and her keys, Bob returns `f(x, y)`. Its fields are `yaoMain_P`, …,
`yaoMain_verifierFirst`. -/
noncomputable def yaoMain : Protocol where
  P := yaoAlice Y E₁ E₂
  V := yaoBob Y E₁ E₂
  rounds := .const 2
  verifierFirst := false

attribute [simps (config := { isSimp := false }) P V rounds verifierFirst] yaoMain

/-- **Bob's output in the message phase**: Bob's result on Alice's message and his answers. -/
theorem yaoMain_outV (w zA zB : List Bool)
    (r : (yaoMain Y E₁ E₂).ExecCoins (yaoMain Y E₁ E₂).P w) :
    (yaoMain Y E₁ E₂).outV (yaoMain Y E₁ E₂).P w zA zB r =
      yaoBobOut Y E₁ E₂ w.length (yaoMsg Y E₁ E₂ w.length (pairFstD zA) (List.ofFn r.1))
        (pairSndD zB) := rfl

/-- **Alice's output in the message phase**: the message Bob sent, his result. -/
theorem yaoMain_outP (w zA zB : List Bool)
    (r : (yaoMain Y E₁ E₂).ExecCoins (yaoMain Y E₁ E₂).P w) :
    (yaoMain Y E₁ E₂).outP w zA zB r =
      yaoBobOut Y E₁ E₂ w.length (yaoMsg Y E₁ E₂ w.length (pairFstD zA) (List.ofFn r.1))
        (pairSndD zB) := rfl

/-- **The OT call index**: call `j < inB(n) · n` transfers bit `t` of the keys of Bob's wire
`inA + i`, for `(i, t) = finProdFinEquiv⁻¹ j`, that is `j = i · n + t`. -/
def yaoCall (n : ℕ) (j : Fin (Y.inB.eval n * n)) : Fin (Y.inB.eval n) × Fin n :=
  finProdFinEquiv.symm j

/-- The OT call index is `finProdFinEquiv⁻¹`. -/
theorem yaoCall_eq (n : ℕ) (j : Fin (Y.inB.eval n * n)) :
    yaoCall Y n j = finProdFinEquiv.symm j := rfl

/-- Call `finProdFinEquiv (i, t)` (that is `i · n + t`) has index `(i, t)`. -/
theorem yaoCall_finProdFinEquiv (n : ℕ) (i : Fin (Y.inB.eval n)) (t : Fin n) :
    yaoCall Y n (finProdFinEquiv (i, t)) = (i, t) := by
  rw [yaoCall, Equiv.symm_apply_apply]

/-- **Protocol 162.6 in the OT-hybrid model** [PS10, Protocol 162.6; Gol04, §7.3]: `inB(n) · n`
ideal bit OTs, then `yaoMain`. In call `(i, t)` Alice's input is bit `t` of the two keys of
Bob's wire `inA + i` (from her coins, through `yaoSeed`), Bob's is his bit `y_i`. Its fields are
`yaoHybrid_main`, `yaoHybrid_calls`, `yaoHybrid_callA`, `yaoHybrid_callB`.

**Deviation.** The source's OT of a key pair is `n` bit OTs with the same choice bit (module
docstring). -/
noncomputable def yaoHybrid : HybridProtocol otFunctionality where
  main := yaoMain Y E₁ E₂
  calls := .mul Y.inB .var
  callA n _ r j c := keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + (yaoCall Y n j).1)
    (decide ((c : ℕ) = 1)) (yaoCall Y n j).2
  callB n y _ j _ := y.getD (yaoCall Y n j).1 false

attribute [simps (config := { isSimp := false }) main calls] yaoHybrid

/-- Alice's input to call `j = (i, t)` is `c ↦ k_{inA + i}^{c = 1}[t]`. -/
theorem yaoHybrid_callA (n : ℕ) (xs r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 2) :
    (yaoHybrid Y E₁ E₂).callA n xs r j c =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + (yaoCall Y n j).1) (decide ((c : ℕ) = 1))
        (yaoCall Y n j).2 := rfl

/-- Bob's input to call `j = (i, t)` is his bit `y_i`. -/
theorem yaoHybrid_callB (n : ℕ) (ys r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 1) :
    (yaoHybrid Y E₁ E₂).callB n ys r j c = ys.getD (yaoCall Y n j).1 false := rfl

/-! ### Correctness -/

/-- Reading a list of a function at an index of the function's domain. -/
private theorem getD_ofFn' {α : Type} {k : ℕ} (f : Fin k → α) (i : Fin k) (d : α) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- **Bob reads the garbled tables**: on Alice's message, the tables Bob reads are the garbled
tables `tableAt` of her garbling, at every vertex. -/
theorem yaoBobTables_yaoMsg (n : ℕ) (xs r : List Bool) :
    yaoBobTables Y n (yaoMsg Y E₁ E₂ n xs r) =
      tableAt (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) := by
  funext v
  rw [tableAt_eq, yaoBobTables_eq, yaoMsg_eq, yaoTables_eq, pairFstD_pairEncode,
    decodeMsgs_encodeMsgs]
  by_cases h1 : Y.inA.eval n + Y.inB.eval n ≤ v
  · rw [if_pos h1]
    by_cases h2 : v - (Y.inA.eval n + Y.inB.eval n) < (Y.circ n).gates.length
    · rw [dif_pos ⟨h1, h2⟩, List.getD_eq_getElem _ _ (by simpa using h2), List.getElem_ofFn,
        decodeMsgs_encodeMsgs]
    · rw [dif_neg (fun h => h2 h.2), List.getD_eq_default _ _ (by simp; omega), decodeMsgs_nil]
  · rw [if_neg h1, dif_neg (fun h => h1 h.1)]

/-- **Bob's input keys are the input keys of `(x, y)`**: on Alice's message for `x`, and answers
that hold, at bits `i · n + t`, the bits of the keys `k_{inA + i}^{y_i}`, Bob's input keys are
`inputKeys` of `x ‖ y`.

**Proof sketch.** Vertex by vertex. At Alice's vertex `v < inA`, the second component of the
message decodes to her keys (`decodeMsgs_encodeMsgs`), and its `v`-th entry is `k_v^{x_v}`
(`padFin_ofFn`), with `x_v = (x ‖ y)_v` (`Fin.append_left`). At Bob's vertex `inA + i`, the
answer bits `i · n + t` are the bits of `k_{inA + i}^{y_i}` by hypothesis, with
`y_i = (x ‖ y)_{inA + i}` (`Fin.append_right`). -/
theorem yaoBobInit_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool)
    (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t) :
    yaoBobInit Y n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      inputKeys (Y.circ n) (yaoSeed Y n r) (Fin.append x y) := by
  rw [inputKeys_eq, yaoBobInit_eq]
  congr 1
  funext v
  rw [yaoMsg_eq, pairSndD_pairEncode, pairFstD_pairEncode, yaoKeysA_eq, decodeMsgs_encodeMsgs]
  by_cases hv : (v : ℕ) < Y.inA.eval n
  · rw [if_pos hv, getD_ofFn' _ ⟨v, hv⟩, padFin_ofFn, getD_ofFn' x ⟨v, hv⟩]
    have hx := Fin.append_left x y ⟨v, hv⟩
    rw [show Fin.castAdd (Y.inB.eval n) ⟨(v : ℕ), hv⟩ = v from Fin.ext rfl] at hx
    rw [hx]
  · rw [if_neg hv]
    have hi : (v : ℕ) - Y.inA.eval n < Y.inB.eval n := by omega
    have hy := Fin.append_right x y ⟨v - Y.inA.eval n, hi⟩
    rw [show Fin.natAdd (Y.inA.eval n) ⟨(v : ℕ) - Y.inA.eval n, hi⟩ = v from
      Fin.ext (by simp; omega)] at hy
    rw [hy]
    funext t
    have hv' : Y.inA.eval n + ((v : ℕ) - Y.inA.eval n) = v := by omega
    rw [readBits_apply, hans ⟨v - Y.inA.eval n, hi⟩ t, Fin.val_mk, hv']

/-- **Bob's evaluation is the garbled evaluation**: on Alice's message and answers holding the
keys of Bob's bits, Bob's values are `garbledValues` of her garbling from the input keys of
`x ‖ y`. -/
theorem yaoBobValues_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t) :
    yaoBobValues Y E₁ E₂ n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      garbledValues (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r)
        (inputKeys (Y.circ n) (yaoSeed Y n r) (Fin.append x y)) := by
  rw [yaoBobValues_eq, yaoBobTables_yaoMsg, yaoBobInit_yaoMsg Y E₁ E₂ n x y r ans hans,
    garbledValues_eq]

/-- **Bob computes `f(x, y)`** [PS10, Protocol 162.6, "B evaluates the circuit to compute the
output `f(x, y)`"; Claim 159.a]: on Alice's message for `x`, with answers holding the keys of
Bob's bits `y`, if the garbling is good and every output vertex has two distinct keys, Bob's
result is `C_n(x, y)` at the output vertices.

**Proof sketch.** Bob's tables are the garbled tables and his input keys those of `x ‖ y`
(`yaoBobTables_yaoMsg`, `yaoBobInit_yaoMsg`), so his evaluation is `garbledValues`
(`yaoBobValues_yaoMsg`). By `garbledValues_getD` it reaches the key `k_o^{v_o}` of each output
vertex `o`'s value. The `j`-th decoding pair is `⟨k_o^0, k_o^1⟩`, and with distinct keys
`decodeOut` returns `v_o` (`decodeOut_fst`, `decodeOut_snd`). -/
theorem yaoBobOut_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true) :
    yaoBobOut Y E₁ E₂ n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans = List.ofFn (Y.output n x y) := by
  rw [yaoBobOut_eq, yaoBobValues_yaoMsg Y E₁ E₂ n x y r ans hans]
  congr 1
  funext j
  rw [garbledValues_getD _ _ _ hgood _ _ (Y.outs_lt n j), yaoMsg_eq, pairSndD_pairEncode,
    pairSndD_pairEncode, yaoPairs_eq, decodeMsgs_encodeMsgs, getD_ofFn', YaoCircuit.output_apply]
  cases ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false
  · exact decodeOut_fst _ _
  · exact decodeOut_snd _ _ fun h => hdist j (List.ofFn_injective h).symm

/-- Concatenating singleton lists: `[g₀ 0] ++ ⋯ ++ [g_{k−1} 0] = [g₀ 0, …, g_{k−1} 0]`. -/
private theorem flatten_ofFn_one {k l : ℕ} (hl : l = 1) (g : Fin k → Fin l → Bool) :
    (List.ofFn fun j => List.ofFn (g j)).flatten = List.ofFn fun j => g j ⟨0, by omega⟩ := by
  subst hl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, ih (fun j => g j.succ), List.ofFn_succ (n := k)]
    simp

/-- **Bob's OT answers are the keys of his bits**: in the hybrid execution, bit `i · n + t` of
Bob's answers is bit `t` of the key `k_{inA + i}^{y_i}` of his wire `inA + i` for his bit `y_i`
(`otFunctionality_f_snd`). -/
theorem yaoHybrid_answersB_getD (n : ℕ) (xs ys rA rB : List Bool) (i : Fin (Y.inB.eval n))
    (t : Fin n) :
    ((yaoHybrid Y E₁ E₂).answersB n xs ys rA rB).getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n rA) (Y.inA.eval n + i) (ys.getD i false) t := by
  have h := flatten_ofFn_one (k := Y.inB.eval n * n) (l := otFunctionality.outB.eval n) rfl
    fun j => (otFunctionality.f n ((yaoHybrid Y E₁ E₂).callA n xs rA j)
      ((yaoHybrid Y E₁ E₂).callB n ys rB j)).2
  have hj : i * n + t = (finProdFinEquiv (i, t) : ℕ) := by
    rw [finProdFinEquiv_apply_val]; ring
  -- `answersB` through its body (requested shared lemma `HybridProtocol.answersB_eq`)
  show (List.ofFn fun j : Fin (Y.inB.eval n * n) => List.ofFn (otFunctionality.f n
      ((yaoHybrid Y E₁ E₂).callA n xs rA j) ((yaoHybrid Y E₁ E₂).callB n ys rB j)).2).flatten.getD
      (i * n + t) false = _
  rw [h, hj, getD_ofFn', otFunctionality_f_snd]
  show keyAt (Y.circ n) (yaoSeed Y n rA)
    (Y.inA.eval n + (yaoCall Y n (finProdFinEquiv (i, t))).1)
    (decide (((if ys.getD (yaoCall Y n (finProdFinEquiv (i, t))).1 false then 1 else 0 :
      Fin 2) : ℕ) = 1)) (yaoCall Y n (finProdFinEquiv (i, t))).2 = _
  rw [yaoCall_finProdFinEquiv]
  cases ys.getD i false <;> rfl

/-- `yaoBobOut_yaoMsg` at a parameter `L` equal to `n` (for the common input `1^n`, whose length
is `n` only propositionally). -/
private theorem yaoBobOut_yaoMsg_of_eq {L n : ℕ} (hL : L = n) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true) :
    yaoBobOut Y E₁ E₂ L (yaoMsg Y E₁ E₂ L (List.ofFn x) r) ans = List.ofFn (Y.output n x y) := by
  subst hL
  exact yaoBobOut_yaoMsg Y E₁ E₂ L x y r ans hans hgood hdist

/-- **Correctness of Protocol 162.6 in the OT-hybrid model** [PS10, Protocol 162.6, "A and B
output the result `f(x, y)`"; the output clause of Theorem 163.7]: in the hybrid execution with
common input `1^n`, inputs `x`, `y` and coins `r`, if Alice's garbling is good and every output
vertex has two distinct keys, Bob's output and Alice's output are both `f(x, y)`.

**Deviation.** The source needs no hypothesis on the output keys, since it does not say how Bob
decodes them. Equal keys on an output vertex (probability `2^{-n}` each) make the decoding
ambiguous; `yaoSeed_good_whp` bounds both failure events.

**Proof sketch.** Bob's answers hold the keys of his bits (`yaoHybrid_answersB_getD`), and his
private input decodes to them (`HybridProtocol.pairSndD_privB`), Alice's to `x`. The message
phase gives Bob the output `yaoBobOut` on Alice's message (`yaoMain_outV`), which is `f(x, y)`
(`yaoBobOut_yaoMsg`, transported along `|1^n| = n`), and Alice outputs what Bob sent
(`yaoMain_outP`). -/
theorem yaoHybrid_correct (n : ℕ) (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
    (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool) (r : (yaoHybrid Y E₁ E₂).Coins n)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r.1)))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) true) :
    (yaoHybrid Y E₁ E₂).main.outV (yaoHybrid Y E₁ E₂).main.P (List.replicate n true)
        ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        r = List.ofFn ((yaoFunctionality Y).f n x y).2 ∧
      (yaoHybrid Y E₁ E₂).main.outP (List.replicate n true)
        ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        r = List.ofFn ((yaoFunctionality Y).f n x y).1 := by
  have key := yaoBobOut_yaoMsg_of_eq Y E₁ E₂ (List.length_replicate (n := n) (a := true)) x y
    (List.ofFn r.1)
    ((yaoHybrid Y E₁ E₂).answersB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
    (fun i t => by rw [yaoHybrid_answersB_getD, getD_ofFn']) hgood hdist
  refine ⟨?_, ?_⟩
  · show (yaoMain Y E₁ E₂).outV (yaoMain Y E₁ E₂).P (List.replicate n true) _ _ r = _
    rw [yaoMain_outV, HybridProtocol.pairFstD_privA, HybridProtocol.pairSndD_privB]
    exact key
  · show (yaoMain Y E₁ E₂).outP (List.replicate n true) _ _ r = _
    rw [yaoMain_outP, HybridProtocol.pairFstD_privA, HybridProtocol.pairSndD_privB]
    exact key

/-! ### Theorem 163.7 in the OT-hybrid model -/

section Security

variable (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hGE₁ hGE₂ in
/-- **Alice's garbling is good, with distinct output keys, with high probability** [PS10, §6.2.3,
"all but one row will evaluate to `⊥`" (Claim 159.a)]: with nested special encryption from two
PRFs `G₁`, `G₂` evaluated by `E₁`, `E₂`, there is a negligible `δ` such that for every `n`, on
uniform coins for Alice, the garbling `yaoSeed` fails to be good, or gives some output vertex two
equal keys, with probability at most `δ(n)`.

**Proof sketch.** Write `S = sizeBound(n)`.
1. *The coin blocks are disjoint.* Vertices are below `size(C_n) ≤ S`, gates below `S`, and a
   fan-in-two gate has at most four assignments, with indices below `4` (`assignIdx`). So the
   keys, the row coins and the shifts of `yaoSeed` read disjoint blocks of Alice's coins: the keys
   and row coins are independent and uniform, and independent of the shifts.
2. *Goodness.* The argument of `uprob_not_good_le` applies to this distribution. At gate `i` and
   assignment `a`, the row of `a` decrypts under `a`'s keys to the right key
   (`nestedSpecial_decCorrect`), so `Good` fails there only if the row of some `a'' ≠ a`
   decrypts under `a`'s keys. The arguments are distinct vertices below the gate's own, so that
   row's keys, plaintext and coins are independent and uniform. By `nestedSpecial_wrongKeyBot`
   the event has probability at most `δ₀(n)`, whatever the row order. At most `12` such events
   per gate and `S` gates give `12 · S · δ₀(n)`.
3. *Distinct output keys.* The two keys of an output vertex are independent uniform `n`-bit
   strings, equal with probability `2^{-n}`: at most `outLen(n) · 2^{-n}` in all.
4. `δ(n) = 12 · S(n) · δ₀(n) + outLen(n) · 2^{-n}` is negligible (a polynomial times a negligible
   function, `Negligible.add`). -/
theorem yaoSeed_good_whp (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, uprob (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
      ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
        ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
          keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤ δ n := by
  sorry

/-- **Protocol 162.6 in the OT-hybrid model runs in polynomial time** (the efficiency clause of
[PS10, Definition 155.1], `HybridProtocol.PolyTime`, ruling of 2026-11-05) when `E₁` and `E₂`
are polynomial-time.

**Proof sketch.** Write `S = sizeBound(n)`.
1. *Alice* (`Strategy.Efficient`). On the empty history: compute the description of `C_n` from
   `1^n` by the uniformity map and decode it; read keys, row coins and shifts from her coins;
   encrypt at most four rows per gate with `E₁` and `E₂`; pair the tables, her input keys and the
   decoding pairs. The enumeration `Finset.univ.toList` of the assignments of at most two
   positions is a constant table. On a nonempty history: copy the first message. A uniform
   machine with coin polynomial `yaoCoins` computes this.
2. *Bob.* Decode the three lists (`decodeMsgs`), recompute `C_n`, and run `runWith` with
   `evalGate`: each decryption checks lengths before calling `E₁` or `E₂` (`spDecStr`), and each
   output key is compared with its pair. This is polynomial in `n` and the message length.
3. *The calls.* Alice's input to call `(i, t)` is two coins at positions computed from `n`,
   `inA(n)` and `S` (`keyAt_yaoSeed`); Bob's is one bit of his input.
4. *The messages.* Whatever `E₁`, `E₂` return, a row has at most `7n + 4` bits (`take` and
   `zipWith` cap the pads), so Alice's message has `O((S + inA(n) + outLen(n)) · n)` bits after
   the pairings; Bob's has `outLen(n)` bits. Neither depends on the answers. -/
theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    (yaoHybrid Y E₁ E₂).PolyTime (yaoFunctionality Y) := by
  sorry

include hGE₁ hGE₂ in
/-- **The simulators of Theorem 163.7, in the OT-hybrid model** [PS10, Theorem 163.7]: with
nested special encryption from two PRFs `G₁`, `G₂` with polynomial-time evaluators `E₁`, `E₂`,
which are also jointly pseudorandom under one key, there are non-uniform PPT simulators `S_A`,
`S_B` such that for every non-uniform PPT distinguisher there is a negligible `ε` bounding, for
all `n`, `x`, `y`, its advantage between the hybrid real and ideal samplers on both sides.

**Deviation: the joint PRF hypothesis `hG₁₂`** (the pair `k ↦ (G₁(k, ·), G₂(k, ·))` is one PRF;
it implies `hG₁` and `hG₂`). [PS10] doubly encrypts with one scheme. Here the two layers use two
PRFs (`nestedSpecial`), and a wire's key keys `G₂` where the wire is a first argument and `G₁`
where it is a second or only one. The hybrid of step 3 then needs encryptions of both schemes
under one unknown key. A reduction to the security of `G₁` alone cannot produce the `G₂`-pads
under that key, nor conversely; the two separate PRF assumptions do not give their security
under a shared key in general.

**Proof sketch.** Write `f = f(x, y)`. Alice's view in the hybrid execution is
`⟨1^n, ⟨x, []⟩, r_A, [m_B]⟩` (her OT answers are empty), Bob's is `⟨1^n, ⟨y, ans⟩, [], [m_A]⟩`
with `ans` the bits of the keys `k_{inA + i}^{y_i}` (`yaoHybrid_answersB_getD`). Let `Bad` be the
event that the garbling is not good or some output vertex has two equal keys; by
`yaoSeed_good_whp` it has probability at most `δ(n)`, and off `Bad` both outputs are `f`
(`yaoHybrid_correct`).
1. *`S_A(1^n, ⟨x, f⟩)`*, with `yaoCoins(n)` coins `r`: the view `⟨1^n, ⟨x, []⟩, r, [f]⟩`. The
   source's `S_A` also simulates the OT transcripts with Proposition 161.5's simulator; in the
   hybrid model there are none. Off `Bad`, `m_B = f` and Bob outputs `f`, so the real and ideal
   samplers agree outside an event of probability at most `δ(n)`; every distinguisher has
   advantage at most `δ(n)`, for all inputs.
2. *`S_B(1^n, ⟨y, f⟩)`*, with `yaoCoins(n)` coins: read a seed `s = yaoSeed` and let the active
   key of every wire be `k_w = k_w^0`. The fake garbled circuit has the real enumeration and
   shifts, but every row of gate `i` encrypts the active key `k_{inA + inB + i}` under that row's
   argument keys. Alice's input keys are the active keys, and so are Bob's answers. The pair of
   output `j` is `⟨k_o^0, k_o^1⟩` if `f_j = 0` and `⟨k_o^1, k_o^0⟩` otherwise, so the active key
   decodes to `f_j`. This is the source's "garbled circuit that always outputs `f(x, y)`", in the
   one-active-key form of [LP09]. `S_B` outputs `⟨1^n, ⟨y, ans'⟩, [], [m'_A]⟩`.
3. *Bob's side, the hybrid over gates* [PS10, "using a hybrid argument …"].
   - `H₀` is the real sampler.
   - In `H₁`, wire `w` with value `v_w` on `(x, y)` has active key `a_w = k_w^{v_w}` and inactive
     key `ι_w = k_w^{1−v_w}`, and gate `i` the shift `λ_i ⊕ v_{args}`. This is a bijection of
     Alice's coins, so `H₁ = H₀`. In these terms the opened row of every gate is the row of the
     all-active assignment; its position is uniform, given by the shift. Bob holds only active
     keys, and the active key of output `j` decodes to `f_j`.
   - `H₂,ᵢ` makes the rows of the gates below `i` encrypt the active output key. Then
     `H₂,₀ = H₁`, and `H₂,|gates|` is `S_B`'s output up to renaming the keys.
   - `H₂,ᵢ ≈ H₂,ᵢ₊₁`: the rows that change are encrypted under an inactive key `ι_u` of an
     argument `u` of gate `i`: in the outer layer if `u` is the first argument, else in the inner
     one. In `H₂,ᵢ`, `ι_u` is only an encryption key, of rows of the gates that read `u`:
     - it is no plaintext: if `u` is a gate, it precedes gate `i` and its table is already fake;
     - it is in no decoding pair: no gate reads an output vertex (`YaoCircuit.outs_sink`);
     - it is not among Alice's keys or Bob's answers, which are active.

     A distinguisher between the two gives one against the multi-message security of
     Algorithm 157.2 under `ι_u`: the reduction samples everything else and obtains the rows
     under `ι_u` from its challenge, with plaintexts `ι_{inA + inB + i}` versus
     `a_{inA + inB + i}` for the changed rows. For the inner layer this is Claim 157.a (i)
     (`specialScheme_multiMessageSecure`, `n`-bit messages with `G₁`). For the outer layer it is
     the same claim for `(4n + 2)`-bit messages with `G₂`. Since `ι_u` may key both layers, the
     reduction needs the two schemes' ciphertexts under one key: the same proof, with the
     joint PRF `hG₁₂` replaced by a random function (not yet stated in the library).
   - The reductions are non-uniform: their advice at `n` is the worst inputs `(x, y)` and the
     hybrid index. This makes the bound `2 · S(n) · ε_MM(n)` uniform over the inputs.
   - Bob's real output pair adds `Bad`: the total is `δ(n) + 2 · S(n) · ε_MM(n)`, negligible.
4. *Efficiency of the simulators.* `S_A` copies its input and coins. `S_B` builds `C_n` with the
   uniformity map and encrypts with `E₁` and `E₂`; both are uniform PPT machines. -/
theorem yaoHybrid_simulators (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
        (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool),
        distAdv ((yaoHybrid Y E₁ E₂).realA (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv ((yaoHybrid Y E₁ E₂).realB (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  sorry

include hGE₁ hGE₂ in
/-- **Theorem 163.7 in the OT-hybrid model** [PS10, Theorem 163.7; Gol04, §7.3]: for a uniform
fan-in-two circuit family whose output vertices are sinks, and nested special encryption from two
pseudorandom function families `G₁`, `G₂` with polynomial-time evaluators `E₁`, `E₂`, jointly
pseudorandom under one key, Protocol 162.6 in the OT-hybrid model is an honest-but-curious secure
protocol for the family's functionality. The real protocol (composition with Protocol 160.4) is
not in this file.

**Deviation.** The joint PRF hypothesis `hG₁₂` (see `yaoHybrid_simulators`).

Proved from `yaoHybrid_polyTime` and `yaoHybrid_simulators`. -/
theorem yaoHybrid_hbcSecure (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    (yaoHybrid Y E₁ E₂).HBCSecure (yaoFunctionality Y) :=
  ⟨yaoHybrid_polyTime Y E₁ E₂ hE₁ hE₂,
    yaoHybrid_simulators Y E₁ E₂ G₁ G₂ hGE₁ hGE₂ hE₁ hE₂ hG₁ hG₂ hG₁₂⟩

end Security

end TCSlib.Cryptography.SecureComputation
