# Read-only Primitives T2 proof plan

This is a bounded source review, **not an elaborated proposal or an implementation**. No Primitives source, overlay or Git state was changed, and no Lean process was run for this plan. `review_mig1_brief` remains the sole Primitives editor.

## Snapshot fidelity

The requested immutable baseline is `campaign/fills/mig1/landing/review-primitives/milestone2-source.lean.txt`, SHA256 `2e3fab6f6a992653fe9b3f01aa789f08204f4e02a975a30b4fc2410df4dbe45e`, verified by reading that file. A current-source read during the ongoing admin-frame work had full SHA256 `2990e07cfafaa95798cd0091bdaf706be6bc23f1c7d7ad9d9242e80628cf166d`; it is a read snapshot, not a frozen final Primitives milestone. All eight reviewed proof blocks below were byte-identical to the immutable baseline. Line positions can move as the editor completes other families.

| Proof block | SHA256 of complete declaration block |
| --- | --- |
| `emitterP2_body_erase_left` | `4075de3916080a5572fb2d5d30fb47bc9ea98d2fa45f7603c6c43b751b19acee` |
| `emitterP2_body_erase_right` | `56a1ee4b3e26fb5a260a6ab3414b6a8ea436d07384f590d16ae86c4cfda0301f` |
| `lenParse_first` | `ef5ab0562916013e0cc75aca7296db7f9d42b138cc0b043249b2d6abc3bc3784` |
| `lenSuffix_run` | `c11d05cce0cb58552a7bafb3a3810bb61afda6a5154a0a6350e04074325e361c` |
| `fwdMap_first` | `76c8f237efb3f0d5c8e69e0e2f2a9b78151533701725b6cb82f9d1670bec78e9` |
| `fwdMap_block` | `00b3d5cc9c66b2885dcec5be5b6e26dfe32aaf4e4ed233e87e01f30962503d43` |
| `emitterToken_double` | `170ac028ec091af105d0e6036cfe6e7c04812b49b2a3caf26e002afb234101be` |
| `emitterToken_separator` | `7a0053b2ab5b6e6165978c3a5e6809839fa02f69f2d4eabf26dfdfb42b3aed3f` |

## Smallest complete erase-family sharing

Use one **private, actual-body-specific direction lemma**, placed immediately before the existing left/right consumers. A Boolean direction selects the existing bank index, state constructor and source word inside the proof. It requires no new generic host, executable definition, table, import, public API or mathematical premise. The two current consumer headers remain literal, with proof bodies specializing the direction to false/true.

The following is the proposed complete mathematical statement; it is intentionally not accompanied by an untested Lean proof:

```lean
private lemma emitterP2_body_erase (right : Bool)
    (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State)
    (w s u v : List Bool) (ok : Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    let tag : Fin 3 → EmitterP2State C.State D.State :=
      fun q => if right then .eraseRight ok q else .eraseLeft ok q
    ∃ t ≤ 2 * ((if right then v else u).length + 1),
      B.tm.runFrom
          (Cfg.ofWords (input := w) (tag 0) (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (tag 2)
          (emitterP2Words C.k D.k s
            (if right then u else []) (if right then [] else v)) ∧
      splitSafe B.tm .anchor
        (Cfg.ofWords (input := w) (tag 0) (emitterP2Words C.k D.k s u v)) t
```

This shares the substantive first-return/relocation proof, rather than only wrapping the two existing full proofs in a case split. Keep one `emitterP2_erase_first` call and one `emitterP2_phase` call:

1. Locally let `active := if right then v else u`. Select `slot` between the existing first right/left bank indices, and construct an injective `emb : Fin 3 ↪ EmitterP2State ...` from the existing `eraseRight ok`/`eraseLeft ok` constructors. Prove injectivity and avoidance of `anchor` by the two constructor cases. These are proof-local values, not new data definitions.
2. Use the cleared layout `emitterP2Words ... s (if right then u else []) (if right then [] else v)` for the ambient tapes, with all heads zero. Establish one frame equation for arbitrary source control `q` and active word `a`. Its target layout is `emitterP2Words ... s (if right then u else a) (if right then a else v)`.
3. **Do not retain the old frame `change` as a hidden read of `Cfg.ofWords`.** First prove locally, with the five published `Cfg.ofWords` field equations,
   `emitterP2EraseCfg w a q 0 = Cfg.ofWords (input := w) q (fun _ : Fin 1 => a)`.
   Rewrite that equality, then use the existing opaque same-home `emitterP2_one_frame` and the corresponding `emitterP2_update_left`/`emitterP2_update_right` equation. The only direction split is in these small frame/index facts. The start-frame specialization at `a = active` and the blank endpoint can be normalized separately by cases on `right`; the common phase call remains outside those cases.
4. Obtain the **observed first return** from `emitterP2_erase_first w active`. Instantiate `emitterP2_phase` with `good q := q ≠ 2`. Its strict-prefix guard is exactly the first-return guard; the whole host table agrees on those states by the existing literal left/right branches of `emitterP2BodyTM`, with direction cases only in that local agreement proof.
5. Rewrite the phase's start/end with the frame equations and return the same witness `t`, unchanged bound and `splitSafe` fact. The two consumers are specializations; normalize their Boolean cases without modifying their headers or machine definitions.

The guard in step 4 is load-bearing. In the actual host, control `eraseLeft ok 2` dispatches into the right eraser, while `eraseRight ok 2` dispatches into output or candidate advance. These are live dispatch states, not absorbing host states. Consequently the isolated eraser's deadline must not be used as a host clock in place of its first-return witness. Empty words also retain the existing positive-time first return; no nonemptiness premise is needed.

`emitterP2_one_frame` and the update equations have old bodies containing implicit/explicit definition reads. Reusing their unchanged, same-home statements opaquely follows the bounded review scope; this plan does not certify their legacy bodies. If the editor independently changes those bodies for another assigned factoring leaf, include those changed bodies in its strong seal and use the public configuration/`Function.update` equations there. No new generic frame or host is needed merely to finish the erase pair.

## Other requested variant checks

* `lenParse_first` is a **one-step parser transition**: store one input bit in finite control, move the native input head, keep countdown cells fixed. `lenSuffix_run` is an **existential multi-step suffix comparison** with a decreasing captured-cell counter, rejection at a zero counter and a final Boolean output. Both already use `lenAction_apply` for the applicable single action. These are different contracts, not two presentations of one proof.
* `fwdMap_first` supplies the first aligned parser step. `fwdMap_block` explicitly rewrites by `fwdMap_first` before handling its second bit, buffer append, separator dispatch or rejection. The requested common scaffold is already used; a second variant wrapper would not remove an independent duplicate proof. This does not excuse unrelated field-reader issues in the block proof.
* `emitterToken_double` reads the next input bit, emits it twice and advances the input exactly once, choosing its next phase from that bit. `emitterToken_separator` starts at the separator phase, appends the fixed delimiter `[false, true]` and preserves the native input position. Their shared two-step run rewrites are existing public equations; their actions, input premises and endpoints differ. This bounded reading gives no reason to introduce an additional parameterized proof solely for those two rewrites.

The cross-file `emitter_first_entry`/`emCall_first_entry` proposal remains pending Seyoon. This erase factoring uses the existing local eraser first-return theorem and does not clone, replace or silently approve that separate generic first-entry API. None of the proposed proof statements or normalization steps was elaborated in this read-only review; the owning agent must check one proof block at a time under its actual seals and retain failures.
