/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.OneWayLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# String machine for Lamport's planted experiment

## Main definitions

* `advIn` replaces one fixed-width public-key block with a planted image.
* `run` signs from the sampled tape and records whether the planted half was requested.
* `out` extracts one signature block unless the run aborted.
* `handler` packages these string functions for T1.

The generator and signer are parameters, so this module does not import its consumer.
The generator is expected to return `⟨pk, tape⟩`; the signer is expected to implement the
deterministic Lamport string function. Their mathematical contracts belong to the consumer.

## Main results

All string functions are polynomial-time; every public definition has an equation reader.
This draft does not yet prove the planted-table functional contracts or a security bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 137.1 and proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportMachine

open Complexity Turing TCSlib.Cryptography.Games

/-- The context's unary parameter is its first component. -/
def u (v : List Bool) : List Bool := pairFstD v
/-- `u v = pairFstD v`. -/
theorem u_eq (v : List Bool) : u v = pairFstD v := rfl
/-- The unary parameter projection is polynomial-time. -/
theorem u_poly : PolyTimeComputable u := polyTimeComputable_pairFstD

/-- The context's challenge is the first component of its reduction input. -/
def y (v : List Bool) : List Bool := pairFstD (pairFstD (pairSndD v))
/-- `y v = fst (fst (snd v))`. -/
theorem y_eq (v : List Bool) : y v = pairFstD (pairFstD (pairSndD v)) := rfl
/-- The challenge projection is polynomial-time. -/
theorem y_poly : PolyTimeComputable y :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)

/-- The planted position is the second component of the reduction input, encoded in unary. -/
def pos (v : List Bool) : List Bool := pairSndD (pairFstD (pairSndD v))
/-- `pos v = snd (fst (snd v))`. -/
theorem pos_eq (v : List Bool) : pos v = pairSndD (pairFstD (pairSndD v)) := rfl
/-- The position projection is polynomial-time. -/
theorem pos_poly : PolyTimeComputable pos :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)

/-- The handler seed is the second component of the context's second component. -/
def seed (v : List Bool) : List Bool := pairSndD (pairSndD v)
/-- `seed v = snd (snd v)`. -/
theorem seed_eq (v : List Bool) : seed v = pairSndD (pairSndD v) := rfl
/-- The seed projection is polynomial-time. -/
theorem seed_poly : PolyTimeComputable seed :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- The planted half is the first seed bit, defaulting to false. -/
def bit (v : List Bool) : Bool := (seed v).headD false
/-- `bit v = (seed v).headD false`. -/
theorem bit_eq (v : List Bool) : bit v = (seed v).headD false := rfl
/-- The planted bit is polynomial-time as a one-bit output. -/
theorem bit_poly : PolyTimeComputable (fun v => [bit v]) :=
  polyTimeComputable_headD.comp seed_poly

/-- The sampled preimage tape is the seed after its planted bit. -/
def tape (v : List Bool) : List Bool := (seed v).drop 1
/-- `tape v = (seed v).drop 1`. -/
theorem tape_eq (v : List Bool) : tape v = (seed v).drop 1 := rfl
/-- Removing the planted bit is polynomial-time. -/
theorem tape_poly : PolyTimeComputable tape := polyTimeComputable_tail.comp seed_poly

/-- A canonical context exposes its unary parameter. -/
theorem u_seedIn (n : ℕ) (z ω : List Bool) :
    u (seedIn n z ω) = List.replicate n true := by
  rw [u_eq, seedIn_eq, pairFstD_pairEncode]

/-- A canonical context with input `⟨challenge,index⟩` exposes its challenge. -/
theorem y_seedIn (n : ℕ) (challenge index ω : List Bool) :
    y (seedIn n (pairEncode challenge index) ω) = challenge := by
  simp only [y_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- A canonical context with input `⟨challenge,index⟩` exposes its unary position. -/
theorem pos_seedIn (n : ℕ) (challenge index ω : List Bool) :
    pos (seedIn n (pairEncode challenge index) ω) = index := by
  simp only [pos_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- A canonical context exposes its seed. -/
theorem seed_seedIn (n : ℕ) (z ω : List Bool) : seed (seedIn n z ω) = ω := by
  simp only [seed_eq, seedIn_eq, pairSndD_pairEncode]

/-- A seed beginning with `c` supplies the planted half `c`. -/
theorem bit_seedIn (n : ℕ) (z ρ : List Bool) (c : Bool) :
    bit (seedIn n z (c :: ρ)) = c := by
  rw [bit_eq, seed_seedIn, List.headD_cons]

/-- A seed beginning with `c` leaves exactly the sampled preimage tape after it. -/
theorem tape_seedIn (n : ℕ) (z ρ : List Bool) (c : Bool) :
    tape (seedIn n z (c :: ρ)) = ρ := by
  rw [tape_eq, seed_seedIn]
  rfl

/-- Taking as many bits of `xs` as there are symbols in a polynomial-time word `a`
is polynomial-time. This is the variable-prefix primitive's public lambda form. -/
theorem take_poly {a xs : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hxs : PolyTimeComputable xs) :
    PolyTimeComputable (fun v => (xs v).take (a v).length) := by
  refine ((polyTimeComputable_pairTakePoly .var).comp (ha.pairEncode hxs)).congr ?_
  intro v
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]

/-- Dropping as many bits of `xs` as there are symbols in a polynomial-time word `a`
is polynomial-time. This is the variable-prefix primitive's public lambda form. -/
theorem drop_poly {a xs : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hxs : PolyTimeComputable xs) :
    PolyTimeComputable (fun v => (xs v).drop (a v).length) := by
  refine ((polyTimeComputable_pairDropPoly .var).comp (ha.pairEncode hxs)).congr ?_
  intro v
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]

/-- A fixed polynomial width, encoded as a unary word of length `W(|u|)`. -/
def width (W : PolyExpr) (v : List Bool) : List Bool := List.replicate (W.eval (u v).length) true
/-- `width W v = 1^(W(|u v|))`. -/
theorem width_eq (W : PolyExpr) (v : List Bool) :
    width W v = List.replicate (W.eval (u v).length) true := rfl
/-- A polynomial width is polynomial-time in the context. -/
theorem width_poly (W : PolyExpr) : PolyTimeComputable (width W) :=
  (polyTimeComputable_unaryPoly W).comp u_poly

/-- The unary offset to block `i` at width `W(n)` has `i · W(n)` symbols. -/
def offset (W : PolyExpr) (v : List Bool) : List Bool :=
  List.replicate ((pos v).length * W.eval (u v).length) true
/-- `offset W v = 1^(|pos v| · W(|u v|))`. -/
theorem offset_eq (W : PolyExpr) (v : List Bool) :
    offset W v = List.replicate ((pos v).length * W.eval (u v).length) true := rfl
/-- Block offsets are polynomial-time by the existing unary multiplication machine. -/
theorem offset_poly (W : PolyExpr) : PolyTimeComputable (offset W) := by
  refine (OneWay.polyTimeComputable_unaryMulPair.comp (pos_poly.pairEncode (width_poly W))).congr ?_
  intro v
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    width_eq, offset_eq, List.length_replicate]

/-- The first preimage at the selected position consists of `n` bits after offset `2ni`. -/
def first (v : List Bool) : List Bool :=
  ((tape v).drop (offset (.mul (.const 2) .var) v).length).take (u v).length
/-- `first` is the first `n`-bit half of the selected preimage pair. -/
theorem first_eq (v : List Bool) : first v =
    ((tape v).drop (offset (.mul (.const 2) .var) v).length).take (u v).length := rfl
/-- Selecting the first preimage is polynomial-time. -/
theorem first_poly : PolyTimeComputable first :=
  take_poly u_poly (drop_poly (offset_poly _) tape_poly)

/-- The second preimage is the next `n` bits after offset `2ni+n`. -/
def second (v : List Bool) : List Bool :=
  ((tape v).drop ((offset (.mul (.const 2) .var) v).length + (u v).length)).take (u v).length
/-- `second` is the second `n`-bit half of the selected preimage pair. -/
theorem second_eq (v : List Bool) : second v =
    ((tape v).drop ((offset (.mul (.const 2) .var) v).length + (u v).length)).take (u v).length := rfl
/-- Selecting the second preimage is polynomial-time. -/
theorem second_poly : PolyTimeComputable second := by
  refine (take_poly u_poly (drop_poly ((offset_poly _).append u_poly) tape_poly)).congr ?_
  intro v
  simp only [second_eq, List.length_append]

/-- The ordinary generated public key on the sampled tape. -/
def honestPk (G : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairFstD (G (NUPPT.layout (u v) [] [] (tape v)))
/-- `honestPk G` runs `G` on the sampled preimage tape and reads its public-key component. -/
theorem honestPk_eq (G : List Bool → List Bool) (v : List Bool) : honestPk G v =
    pairFstD (G (NUPPT.layout (u v) [] [] (tape v))) := rfl
/-- Generating the ordinary public key is polynomial-time when `G` is. -/
theorem honestPk_poly {G : List Bool → List Bool} (hG : PolyTimeComputable G) :
    PolyTimeComputable (honestPk G) :=
  polyTimeComputable_pairFstD.comp (hG.comp (NUPPT.polyTimeComputable_layout u_poly
    (polyTimeComputable_const []) (polyTimeComputable_const []) tape_poly))

/-- The replacement public-key block is `⟨⟨y,E(x¹)⟩,[]⟩` for bit false and
`⟨⟨E(x⁰),y⟩,[]⟩` for bit true. -/
def replacement (E : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairEncode (pairEncode
    (if bit v then E (pairEncode (u v) (first v)) else y v)
    (if bit v then y v else E (pairEncode (u v) (second v)))) []
/-- The replacement block plants the challenge in the selected half. -/
theorem replacement_eq (E : List Bool → List Bool) (v : List Bool) : replacement E v =
    pairEncode (pairEncode
      (if bit v then E (pairEncode (u v) (first v)) else y v)
      (if bit v then y v else E (pairEncode (u v) (second v)))) [] := rfl
/-- Building the replacement public-key block is polynomial-time when `E` is. -/
theorem replacement_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (replacement E) :=
  ((polyTimeComputable_ite bit_poly (hE.comp (u_poly.pairEncode first_poly)) y_poly).pairEncode
    (polyTimeComputable_ite bit_poly y_poly (hE.comp (u_poly.pairEncode second_poly)))).pairEncode
      (polyTimeComputable_const [])

/-- The adversary's public key replaces one width-`W(n)` block of the ordinary generated key
with the planted block. [PS10, proof of Theorem 137.2]. -/
def advIn (W : PolyExpr) (E G : List Bool → List Bool) (v : List Bool) : List Bool :=
  (honestPk G v).take (offset W v).length ++ replacement E v ++
    (honestPk G v).drop ((offset W v).length + (width W v).length)
/-- `advIn` keeps the prefix and suffix around the planted block. -/
theorem advIn_eq (W : PolyExpr) (E G : List Bool → List Bool) (v : List Bool) :
    advIn W E G v = (honestPk G v).take (offset W v).length ++ replacement E v ++
      (honestPk G v).drop ((offset W v).length + (width W v).length) := rfl
/-- Planting one public-key block is polynomial-time.

**Proof sketch.** Compute both unary offsets by the existing multiplication primitive,
take the prefix and drop the suffix, then concatenate the replacement block between them. -/
theorem advIn_poly (W : PolyExpr) {E G : List Bool → List Bool}
    (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) :
    PolyTimeComputable (advIn W E G) := by
  refine (((take_poly (offset_poly W) (honestPk_poly hG)).append (replacement_poly hE)).append
    (drop_poly ((offset_poly W).append (width_poly W)) (honestPk_poly hG))).congr ?_
  intro v
  simp only [advIn_eq, List.length_append]

/-- The context of a query or finalization input is its first component. -/
def context (w : List Bool) : List Bool := pairFstD w
/-- `context w = fst w`. -/
theorem context_eq (w : List Bool) : context w = pairFstD w := rfl
/-- The context of an activation is polynomial-time. -/
theorem context_poly : PolyTimeComputable context := polyTimeComputable_pairFstD

/-- The current abort state is the first component of the second input component. -/
def state (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- `state w = fst (snd w)`. -/
theorem state_eq (w : List Bool) : state w = pairFstD (pairSndD w) := rfl
/-- The current state projection is polynomial-time. -/
theorem state_poly : PolyTimeComputable state :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The query message is the second component after the state and oracle index. -/
def message (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
/-- `message w = snd (snd (snd w))`. -/
theorem message_eq (w : List Bool) : message w = pairSndD (pairSndD (pairSndD w)) := rfl
/-- The query message projection is polynomial-time. -/
theorem message_poly : PolyTimeComputable message :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The context of a canonical handler query is its original seed context. -/
theorem context_input {k : ℕ} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    context (PolyHandler.input n z ω s i x) = seedIn n z ω := by
  simp only [context_eq, PolyHandler.input_eq, seedIn_eq, pairFstD_pairEncode]

/-- A canonical handler query exposes its state. -/
theorem state_input {k : ℕ} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    state (PolyHandler.input n z ω s i x) = s := by
  simp only [state_eq, PolyHandler.input_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- A canonical handler query exposes its message. -/
theorem message_input {k : ℕ} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    message (PolyHandler.input n z ω s i x) = x := by
  simp only [message_eq, PolyHandler.input_eq, pairSndD_pairEncode]

/-- A query is blocked precisely when its selected message bit is the planted bit. -/
def blocked (w : List Bool) : Bool :=
  decide (((message w).drop (pos (context w)).length).headD false = bit (context w))
/-- `blocked` tests equality of the query bit at the planted position and the planted half. -/
theorem blocked_eq (w : List Bool) : blocked w =
    decide (((message w).drop (pos (context w)).length).headD false = bit (context w)) := rfl
/-- Testing whether a query requests the planted half is polynomial-time. -/
theorem blocked_poly : PolyTimeComputable (fun w => [blocked w]) := by
  have hq := polyTimeComputable_headD.comp (drop_poly (pos_poly.comp context_poly) message_poly)
  have hb := bit_poly.comp context_poly
  refine (polyTimeComputable_pairEq.comp (hq.pairEncode hb)).congr ?_
  intro w
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, blocked_eq,
    List.cons.injEq, and_true]

/-- A handler query returns the ordinary sampled-tape signature and sets the persistent
abort bit if the planted half was requested. Continuing after an abort is harmless because
finalization returns no candidate. [PS10, proof of Theorem 137.2]. -/
def run (S : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode
    (S (NUPPT.layout (u (context w)) (pairEncode (tape (context w)) (message w)) [] []))
    [(state w).headD false || blocked w]
/-- The query answer uses the sampled tape and records the disjunction of old and new aborts. -/
theorem run_eq (S : List Bool → List Bool) (w : List Bool) : run S w =
    pairEncode
      (S (NUPPT.layout (u (context w)) (pairEncode (tape (context w)) (message w)) [] []))
      [(state w).headD false || blocked w] := rfl
/-- Query answering and the abort-state update are polynomial-time when `S` is. -/
theorem run_poly {S : List Bool → List Bool} (hS : PolyTimeComputable S) :
    PolyTimeComputable (run S) :=
  (hS.comp (NUPPT.polyTimeComputable_layout (u_poly.comp context_poly)
    ((tape_poly.comp context_poly).pairEncode message_poly)
    (polyTimeComputable_const []) (polyTimeComputable_const []))).pairEncode
      (polyTimeComputable_or (polyTimeComputable_headD.comp state_poly) blocked_poly)

/-- The final output is empty after an abort; otherwise it is block `i` of the forged signature
(the adversary's word begins with the `n` message bits). [PS10, proof of Theorem 137.2]. -/
def out (w : List Bool) : List Bool :=
  if (state w).headD false then [] else
    (((pairSndD (pairSndD w)).drop (u (context w)).length).drop
      (offset .var (context w)).length).take (u (context w)).length
/-- Finalization suppresses aborted runs and extracts the selected signature block otherwise. -/
theorem out_eq (w : List Bool) : out w =
    if (state w).headD false then [] else
      (((pairSndD (pairSndD w)).drop (u (context w)).length).drop
        (offset .var (context w)).length).take (u (context w)).length := rfl
/-- Finalization is polynomial-time by three variable-prefix operations and one branch. -/
theorem out_poly : PolyTimeComputable out :=
  polyTimeComputable_ite (polyTimeComputable_headD.comp state_poly) (polyTimeComputable_const [])
    (take_poly (u_poly.comp context_poly)
      (drop_poly ((offset_poly .var).comp context_poly)
        (drop_poly (u_poly.comp context_poly)
          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))))

/-- The planted Lamport handler has one abort bit and `1+2n²` seed bits, with the fair planted
half first. It signs at most one query and extracts one candidate preimage. -/
def handler (W : PolyExpr) (E G S : List Bool → List Bool)
    (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) (hS : PolyTimeComputable S) :
    PolyHandler 1 (fun _ => .var) (fun _ => .mul .var .var) where
  stateLen := .const 1
  seedLen := .add (.const 1) (.mul (.mul (.const 2) .var) .var)
  init := fun _ _ => false
  run := run S
  poly := run_poly hS
  advIn := advIn W E G
  advIn_poly := advIn_poly W hE hG
  out := out
  out_poly := out_poly

variable (W : PolyExpr) (E G S : List Bool → List Bool)
  (hE : PolyTimeComputable E) (hG : PolyTimeComputable G) (hS : PolyTimeComputable S)

/-- The handler state-length polynomial is the constant one. -/
theorem handler_stateLen : (handler W E G S hE hG hS).stateLen = .const 1 := rfl
/-- The handler seed-length polynomial is `1+2n²`. -/
theorem handler_seedLen : (handler W E G S hE hG hS).seedLen =
    .add (.const 1) (.mul (.mul (.const 2) .var) .var) := rfl
/-- Every bit of the initial abort state is false. -/
theorem handler_init (n : ℕ) (i : Fin ((handler W E G S hE hG hS).stateLen.eval n)) :
    (handler W E G S hE hG hS).init n i = false := rfl
/-- The handler's query function is `run S`. -/
theorem handler_run : (handler W E G S hE hG hS).run = run S := rfl
/-- The handler's adversary-input function is the planted public-key function. -/
theorem handler_advIn : (handler W E G S hE hG hS).advIn = advIn W E G := rfl
/-- The handler's output function is the signature-block extractor. -/
theorem handler_out : (handler W E G S hE hG hS).out = out := rfl

end TCSlib.Cryptography.Authentication.LamportMachine
