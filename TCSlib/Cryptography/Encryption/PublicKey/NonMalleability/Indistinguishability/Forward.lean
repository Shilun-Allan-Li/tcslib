/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Forwarding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Forwarding handlers and log readers

Both reductions of [PS10, Theorem 175.9] run the adversary once against the reduction's own
oracles: every query is **forwarded** unchanged to the outer oracle of the same index, and only
the finalization differs. That handler is `Games.fwdHandler`, with one outer call per inner query
and an empty state, so that T2 (`Games.exists_interactiveHandlerMachine`) makes it a machine. Its
answers are the outer oracle's (`Games.fwdHandler_impl`), so simulating it is running the
adversary against the outer oracles (`simulate_fwdHandler_impl`).

It also provides the readers of an encoded outer log: `logEmit G L` concatenates `G` of the
successive suffixes of the nested log `L` (iterate and emit, `Games.iterEmit`), is polynomial-time
for polynomial-time `G` (`polyTimeComputable_logEmit`), and on an encoded log is the concatenation
of `G`'s values on the entries (`logEmit_encodeLog`). The readers of a finalization input are the
published `Games.InteractiveHandler.rU`, `rZ`, `rW`, `rL` (with their `_finInput` lemmas) and
`finA`.

## Main definitions

* `NMCCA2.logEmit`: concatenated readings of the suffixes of an encoded log.

## Main results

* `NMCCA2.simulate_fwdHandler_impl`: simulating the forwarding handler.
* `NMCCA2.polyTimeComputable_logEmit`, `NMCCA2.logEmit_encodeLog`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.9 (book p. 175).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable {k : ℕ}

/-! ### Simulating the forwarding handler -/

section Forward

variable (din dout : Fin k → PolyExpr) (seedLen : PolyExpr) (advIn : List Bool → List Bool)
  (advIn_poly : PolyTimeComputable advIn) (outLen finCall : PolyExpr)
  (finRun : List Bool → List Bool) (finRun_poly : PolyTimeComputable finRun)

/-- **Simulating the forwarding handler is running the computation:** for every computation
`c` against the oracles and every state `s`, `simulate (H.impl n z ω) c s = c.bind (fun a =>
pure (a, s))`.

**Proof sketch.** Induction on `c`, with `Games.fwdHandler_impl` at each query. -/
theorem simulate_fwdHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt din dout n) α)
    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).stateLen.eval n) → Bool) :
    simulate ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).impl n z ω) c s = c.bind fun a => .pure (a, s) := by
  induction c with
  | pure a => rw [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    rw [simulate_query, fwdHandler_impl, OracleComp.query_bind, OracleComp.query_bind]
    congr 1
    funext y
    rw [OracleComp.pure_bind]
    exact ih y

end Forward

/-! ### Readers of an encoded log -/

/-- **Concatenated readings of an encoded log:** `G` applied to the successive suffixes
`L, snd L, snd (snd L), …` of the nested log `L = ⟨e₁, ⟨e₂, ⟨…, []⟩⟩⟩`, for `|L| + 1` steps, and
concatenated: iterate and emit (`Games.iterEmit`) with the step `pairSndD`,
`logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
def logEmit (G : List Bool → List Bool) (L : List Bool) : List Bool :=
  iterEmit pairSndD G (L.length + 1) L

/-- `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`
(`Games.iterEmit_eq`). -/
theorem logEmit_eq (G : List Bool → List Bool) (L : List Bool) :
    logEmit G L = (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L) := by
  rw [logEmit, iterEmit_eq]

/-- **The readings of an encoded log are polynomial-time** when `G` is
(`Games.polyTimeComputable_iterEmit` with the step `pairSndD`, which never lengthens a word). -/
theorem polyTimeComputable_logEmit {G : List Bool → List Bool} (hG : PolyTimeComputable G) :
    PolyTimeComputable (logEmit G) :=
  (polyTimeComputable_iterEmit polyTimeComputable_pairSndD hG 0
    fun y => (length_pairSndD_le y).trans (le_max_left _ _)).congr fun L => by rw [logEmit]

section LogEmit

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- An encoded log is at least as long as its number of entries. -/
private theorem length_le_length_encodeLog (codec : MachineCodec spec α) (h : QueryLog spec) :
    h.length ≤ (codec.encodeLog h).length := by
  induction h with
  | nil => exact Nat.zero_le _
  | cons e t ih =>
    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons]
    omega

/-- **The readings of an encoded log are the readings of its entries:** if `G [] = []` and `G`
reads only the first entry of a nonempty log, `G ⟨⟦e⟧, t⟩ = g e`, then
`logEmit G (codec.encodeLog h) = h.flatMap g`.

**Proof sketch.** `Games.iterEmit_encode` with the encoding `codec.encodeLog`: `pairSndD` drops
the first entry of an encoded log (`MachineCodec.encodeLog_cons`) and fixes the empty one, and
`|h| ≤ |L|` (`length_le_length_encodeLog`). -/
theorem logEmit_encodeLog (codec : MachineCodec spec α) (G : List Bool → List Bool)
    (g : (Σ i, spec.dom i × spec.rng i) → List Bool) (hnil : G [] = [])
    (hcons : ∀ e t, G (pairEncode (codec.encodeEntry e) t) = g e) (h : QueryLog spec) :
    logEmit G (codec.encodeLog h) = h.flatMap g := by
  rw [logEmit]
  refine iterEmit_encode pairSndD G codec.encodeLog g h ?_ (fun e _ t => ?_) ?_
    (fun e _ t => ?_) _ (Nat.le_succ_of_le (length_le_length_encodeLog codec h))
  · rw [MachineCodec.encodeLog_nil]
    exact pairSndD_of_pairDecode_eq_none pairDecode_nil
  · rw [MachineCodec.encodeLog_cons, pairSndD_pairEncode]
  · rw [MachineCodec.encodeLog_nil]
    exact hnil
  · rw [MachineCodec.encodeLog_cons]
    exact hcons e _

end LogEmit

end TCSlib.Cryptography.Composability.NMCCA2
