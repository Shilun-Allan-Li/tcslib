# Actual first-header endpoint → H5 start: bounded pre-ship PASS

**DRAFT — not ready to dispatch.** This checks the real first-header data handoff and instantiates
the existing H5 contract. It implements no F6 target, full prefix, universal machine, host or new
API. No source/admission/import, Git state, shared snapshot or cache was changed.

`Final-native.lean.txt` and `Final-sealed.lean.txt` both pass: **0 errors, 0 warnings**, 2.68/2.73 s.
Their SHA-256 values are respectively
`9d32b5c98510f976efcc4ed6a287bb0eeb3238e24075fd46a2a3b7057c7e2a31` and
`295bc8d5af869136baedb41cb27b8ccacd3e7cc0302611abc03d27873b98c28e`.

## Real presentation, without assumed prefix premises

Fix `K` and a native machine **`M : MultiTapeTM (K+3) Bool S` before either input word**.
For `z=pairEncode u v`, `ℓ=2|u|+2`, and `rt=bufferTape (replicate ℓ true)`, the new component:

1. Proves `|z|=ℓ+|v|`, `0<ℓ`, and **`z.drop ℓ=v`**, using the published pairing/doubling
   equations and `List.drop_left`.
2. Reuses the **exact frozen first-header proof body**, obtaining the actual fixed row `A`
   from its real `A.initCfg z`, with first return at **`2ℓ+3`**, physical input position **`ℓ+1`**,
   blank bank tapes, zero heads, last ruler and empty output.
3. Proves the following **full configuration equality**, for any fixed injection function:

   ```lean
   (A.runFrom (A.initCfg z) (2*ℓ+3)).mapState (fun _ => inj M.q₀ false) =
     rulerHostCfg ℓ hz ((M.initCfg v).state.map fun q => inj q false)
       (M.initCfg v) rt 0
   ```

   It checks state, physical input, every tape/cell, every head and output through public
   `Cfg.mapState_*`, `rulerHostCfg_*`, `rulerHostCfg_fields`, `initCfg_eq` and `Cfg.init_*`
   equations. The bank is the first `K+3` tapes; the ruler is **last at index `K+3`** among
   **`K+4`** physical tapes. No input payload is copied.
4. Discharges the entire H5 ruler window, **including both boundary cells**:
   `rt (0+p)=bufferTape (replicate ℓ true) p` for `-1≤p≤ℓ`. It derives the false initial
   boundary tag from **`(M.initCfg v).inputPos.val=1`**, rather than assuming a presentation.

`header_handoff` retains the actual header row's strict `RewindPhase.done` return cut. The
`mapState` above is an **explicit state-only endpoint reset / label view**. It is not a run,
cost-free dispatch or cut of an outer seam. Applying that constant map to the entire header
trajectory would not prove a first entry at the H5 label. A real outer seam must dispatch at the
proved header exit and account for its step. The H5 entry here is **`inj M.q₀ false`**; no claim
that it equals the host's native `q₀` is made or needed.

## Uniform H5 application

`host_after_header` obtains actual witnesses of **`exists_rulerHostTM M`** (InputDevice:1226):
`Q`, its instances, `H`, `inj`, and positive coefficient `C` are chosen **before `u,v,t`**.
It supplies every presentation premise from the facts above at **`M.initCfg v`**, and retains:

- A time `t'` with `t≤t'≤C*(ℓ+1)*t`, and the exact hosted endpoint/tag at source time `t`.
- H5's explicit implication from source liveness before `t` to host liveness before `t'`.
- At each host time, a source time with exactly matching bank tapes/heads and output; unchanged
  ruler contents and ruler head within **`[-1,ℓ]`**.
- Exact visited-set equality on every bank tape and the ruler visited-set subset of `[-1,ℓ]`.

The run starts from the actual header endpoint **after the stated control reset**, not from an
arbitrary assumed configuration. It is still a standalone H5 run, not a run of the complete
header-plus-dispatch-plus-host machine. **No source first halt is assumed or proved**, and no
arbitrary-machine space bound or R1′ return is asserted. The positive coefficient is supplied by
the public H5 contract; its implementation is not unfolded to guess a numeric value.

## Executed guards, controls and receipts

The guard is before all four theorem docs/headers, including the reused first-header theorem.
It seals **35 ordinary foreign definitions** (the previous 34 plus `Turing.dbl`), disabling default
simp definitions `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`. Removing the exact guard
restores native bytes. All **four roots and four compiled descendants** have standard axioms;
the fresh type/value inventory finds twelve direct ordinary foreign definitions, all guarded.
Reducible projections are classified as abbreviations. This does not re-audit imported theorem
proofs. All explicit rewrite/simplification arguments were inspected: only local definitions/
hypotheses and published equations/theorems occur; no foreign ordinary definition is named as
an unfolding argument.

Fresh paired controls for all 35 guards give **70 kernel-checked unsealed passes**, versus sealed
exit1 with **exactly 70** identified `rfl` failures. The exact multiplicity/identity checker passes
and rejects four synthetic corrupted-evidence cases. No unsafe reducibility or admitted failed
control is used.

All **six** managed plain wrapper attempts, copied inputs, raw outputs and receipts are retained.
The first sealed handoff attempt failed with six local normalization errors: an already-closed
length goal, append association already in the desired form, an unexpanded local length, a local
record projection before update rewriting, and rewriting the concrete start alias. V2 corrected
these without changing any statement or adding premises; it passed, as do both authoritative final
inputs. Failed-run `sorryAx` output is not a passing claim. Initial setup also stopped before Lean
for a missing old layout manifest; the actual immutable final probe hashes were pinned instead.

Context: supplied frozen API worktree `wt-natbits` / head `1160c18f03fd318f0dec25738790935fa61379d4`,
read-only complete `oleans-mra2`, local budget three/machine five, sequential managed elaborations.
No Git identifier/merge status is newly attested. All eleven recorded source/compiled pins remain
unchanged. Only Hierarchy is imported; no `.olean` output was requested, no library source/cache/
shared snapshot was edited, and no screen, replay, commit or push occurred. `verify.py`,
`verification.json`, `compiled-inventory.json`, control checker
and raw receipts retain the exact evidence. No concrete reader/type gap was found **for this
component**; full route readiness and remaining interface questions are not decided here.
