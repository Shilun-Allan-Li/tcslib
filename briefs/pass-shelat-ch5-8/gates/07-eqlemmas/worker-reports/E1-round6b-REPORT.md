## #210 round 6b: report

The new head is **037075b01ca348266d50735cd22526a96fc131bf** on `wip/eqlemmas` (one commit on top of c304994ed7a25108db7f019cf2e258a972db9b12), unpushed and with a clean tree. The source scan now finds **0** explicit unfolds of other files' definitions in the declarations this PR adds or changes, and nothing is left. Logs are in `$SP/e1/final6b/` (`$SP` = /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad).

### Check
- **Scanner:** #195's gate 04 scanner (copied to `tools/`). Its collector builds a table of every TCSlib constant from the oleans of the 37 PR files (`candidates2/tcslib-constants.tsv`).
  - It flags every name in an `unfold`/`delta` or in a `rw`/`simp`/`dsimp`/… lemma list that resolves to another module's definition, and every proof term that uses a generated `X.eq_N`/`eq_def` of one.
  - Multi-line lists are followed through.
  - `show`/`change` are left to the seal, which round 6 found clean.
- **Restriction:** hits are kept only inside the 175 PR-touched declarations from `touched.py` (`touched.tsv`).
- **Before:** 18 hits in 11 touched declarations (`hits-touched.tsv`), plus 2 proof-term equation-lemma references that duplicate them (`decListFun.eq_1`, `padStr.eq_1`).
- **After:** 0 (`scan-final.log`, `hits-touched-final.tsv`).

### Hits fixed
| Declaration (file) | Was | Now |
|---|---|---|
| `outV_pullback_cheat` (NP) | `simp only [Protocol.outV, Protocol.transcriptWith, …]` | new `Protocol.outV_eq`, `Protocol.transcriptWith_eq` (Interaction) |
| `zkSim_runAt` (ZK Encryption) | `encDist`, `NUPPT.runAt`, `advInput`, `layout`, `inParam`, `inCoins` | `encDist_apply`, `runAt_eq`, `runAtL_eq`, `advInput_eq`, `layout_eq`, `inParam_eq`, `inCoins_eq` |
| `bitwise` (PublicKey) | `decListFun`, `coinBlock` | new `decListFun_eq`, `coinBlock_eq` (BlockEncryptor) |
| `bitwise_pkEncDist_coinBlocks` (PublicKey) | `simp only [multiDist]` | new `multiDist_eq` (PublicKeyLemmas) |
| `acceptProb_bitwise_pkEncDist` (PublicKey) | `unfold acceptProb` | `acceptProb_def` |
| `SingleBitSecure.bitwise` (PublicKey) | `unfold distAdv` | `distAdv_def` |
| `padStr_eq_ofFn_fUniversal_f` (Universal) | `rw [padStr]` | new `padStr_eq` (CollectionsLemmas) |
| `TrapdoorCollection.glPad` (HardCoreCollection) | `simp only [glPadInvFun, …]` | new `glPadInvFun_eq` (HardCoreLemmas) |
| `Collection.OneWay.glPad` (HardCoreCollection) | `unfold Collection.invProbAt` | existing `Collection.invProbAt_eq` |
| `yaoRaw'_layout` (OneWayYao) | `NUPPT.layout` | `NUPPT.layout_eq` |
| `fiber_le` (Collections) | false positive: its local `let P` resolved to `Complexity.P` | local renamed `Pev`, so the scan is clean |

**Side change for file size.** HardCoreLemmas would have gone over 1000 lines with `glPadInvFun_eq`. I inlined the length proof of `NUPPT.wrap_coinLen` (added by this PR, used only there) into `wrapCoinsEquiv` and `wrapCoinsEquiv_symm_ofFn`, and removed `wrap_coinLen`. The file is now 1000 lines.

### Re-checks
- **Replay:** all 64 modules downstream of the 6b edits plus `audits/pass-shelat/Checks`, rc 0 (`replay-head.log`). I re-ran it after the last edit; the log header shows c304994 because the edits were committed after the run, from the same working tree.
- **`decls.tsv` against 16a7d02d:** 95 ADDED, 36 CHANGED, 2 REMOVED (the `Uniform` move); no statement change in 6b.
- **`decls-6b.tsv` against c304994:** 7 ADDED (the new equations); 1 REMOVED (`wrap_coinLen`).
- **Axioms** for the new equations and the changed definitions (`probes/Axioms6b.log`): standard only, no `sorryAx`.
- **Lint:** no new findings. Collections and PublicKey still carry their approved size lines.
- **Probes:** I re-ran them because `wrapCoinsEquiv`'s body changed.
  - `Final6Pass`: rc 0.
  - `Final6Control`: 30 of 30 fail sealed.
  - `Final6OpenControl`: rc 0.
