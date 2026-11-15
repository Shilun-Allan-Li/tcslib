/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The forgery game of a MAC with a deterministic tag

Step 3 of the proof of [PS10, Theorem 135.4], on the game side: when a MAC's tagging algorithm
returns, on the key of the generator coins `rg`, a tag `g rg m` that does not depend on its own
coins, and verification accepts `(m, σ)` exactly when `g rg m = σ`, the forgery probability is the
average over the coins `rg` of the probability that the forger forges against the tagging oracle of
the function `g rg` (`accept_forgeGame_eq`). The forger's codec is the bit codec
(`forgerCodec_eq_bitCodec`).

## Main results

* `PRFMAC.forgerCodec_eq_bitCodec`: the forger codec of a MAC is the bit codec.
* `PRFMAC.accept_forgeGame_eq`: the forgery game with a deterministic tag.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 134.2 and Theorem 135.4 (book pp. 134–135).
-/

namespace TCSlib.Cryptography.Authentication.PRFMAC

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-- **The MAC forger codec is the bit codec** with message-length queries, tag-length answers and
a message-plus-tag-length output: `M.forgerCodec n = bitCodec (fun _ => msgLen(n))
(fun _ => tagLen(n)) (msgLen(n) + tagLen(n))`.

**Proof sketch.** Codec extensionality (`MachineCodec.ext_of_fields`) on the published decoding,
entry-encoding and timeout equations (`forgerCodec_decodeMove`, `forgerCodec_encodeEntry`,
`forgerCodec_timeout`) and those of the bit codec. -/
theorem forgerCodec_eq_bitCodec (M : MAC) (n : ℕ) :
    M.forgerCodec n =
      bitCodec (fun _ : Fin 1 => M.msgLen.eval n) (fun _ : Fin 1 => M.tagLen.eval n)
        (M.msgLen.eval n + M.tagLen.eval n) := by
  apply MachineCodec.ext_of_fields
  · funext w
    exact (M.forgerCodec_decodeMove n w).trans
      (bitCodec_decodeMove (fun _ : Fin 1 => M.msgLen.eval n)
        (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n) w).symm
  · funext e
    exact (M.forgerCodec_encodeEntry n e).trans
      (bitCodec_encodeEntry (fun _ : Fin 1 => M.msgLen.eval n)
        (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n) e).symm
  · exact (M.forgerCodec_timeout n).trans
      (bitCodec_timeout (fun _ : Fin 1 => M.msgLen.eval n)
        (fun _ : Fin 1 => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n)).symm

/-- **The forgery game with a deterministic tag** [PS10, Definition 134.2]: if, on the key of the
generator coins `rg`, tagging `m` returns `g rg m` whatever its coins, and verification accepts
`(m, σ)` exactly when `g rg m = σ`, then
`Pr[forgeGame A b n] = 𝔼_rg 𝔼_r Pr[FnForge (g rg) | simulate (fnImpl (g rg)).withLog (A.toComp … r)
((), [])]`.

**Proof sketch.** Unfold the game (`forgeGame_eq`, `prob_bind`) and the codec
(`forgerCodec_eq_bitCodec`). Each call of the logged tagging oracle draws tag coins and returns
`g rg m` (`tagImpl_eq`, `htag`), so it has the law of the logged `fnImpl (g rg)`
(`expect_const`), and so do whole runs (`expect_simulate_congr`). The winning test is `FnForge` by
`hacc`. -/
theorem accept_forgeGame_eq (M : MAC) (A : NUPPT) (b n : ℕ)
    (g : M.gen.Coins n → (Fin (M.msgLen.eval n) → Bool) → (Fin (M.tagLen.eval n) → Bool))
    (htag : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (rt : M.tag.Coins n),
      padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode (M.gen.runAt n [] rg) (List.ofFn m))
        rt) = g rg m)
    (hacc : ∀ rg (m : Fin (M.msgLen.eval n) → Bool) (σ : Fin (M.tagLen.eval n) → Bool),
      M.Accepts n (M.gen.runAt n [] rg) m σ ↔ g rg m = σ) :
    accept (M.forgeGame A b n) =
      expect (sample (M.gen.Coins n)) fun rg => expect (sample (A.Coins n)) fun r =>
        expect (simulate (fnImpl (g rg)).withLog
            (A.toComp (bitCodec (fun _ : Fin 1 => M.msgLen.eval n) (fun _ => M.tagLen.eval n)
              (M.msgLen.eval n + M.tagLen.eval n)) n b r) ((), []))
          (fun res => if FnForge (g rg) res.1 res.2.2 then (1 : ℝ) else 0) := by
  rw [accept_eq, MAC.forgeGame_eq, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind, forgerCodec_eq_bitCodec,
    expect_simulate_congr (M.tagImpl n (M.gen.runAt n [] rg)).withLog (fnImpl (g rg)).withLog
      (fun i x s G => ?_)]
  · refine congrArg _ (funext fun res => ?_)
    rw [prob_pure]
    exact if_congr (by rw [decide_eq_true_iff, fnForge_iff, hacc]) rfl rfl
  · simp only [QueryImpl.withLog_apply, MAC.tagImpl_eq, QueryImpl.ofComp_apply, fnImpl_apply,
      expect_bind, expect_pure, OracleComp.pure_bind, htag, expect_const]

end TCSlib.Cryptography.Authentication.PRFMAC
