# Gate 06 C3: three-pair disposition review

Source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; actual base `eee107e92a7db11f1f8c98a5c2867304f57ddc54`.
**All three raw reference pairs remain retained and nonzero. No new/touched reference is
identified by this source/context review.** This is neither extractor acceptance nor a gate,
seal or merge pass. R2 raw native result is rc0/0 errors and END reports 54 modules, 2,881
roots and **3 pairs**; root's complete extractor validation remains separate.

| Exact root | Reference | Parent home / actual reference home | Disposition |
|---|---|---|---|
| `Complexity.BinArith.polyTimeComputable_chunkW` | `Turing.pairDecode.eq_4` | `TCSlib.Complexity.TuringMachine.Encoding` / same | Existing `simp [..., pairDecode]`; unchanged header/proof/context. Already among 110 and corrected 48 observation keys. |
| `_private.TCSlib.Cryptography.Asymptotic.BlockEncryptor.0.TCSlib.Cryptography.length_decListStep_le` | `Turing.pairDecode.eq_4` | `TCSlib.Complexity.TuringMachine.Encoding` / same | Existing private step-length proof; historical eqn-term row713 and declaration rows34/37. Retain separately: not among the 110 seal-failure blocks. |
| `TCSlib.Cryptography.gi_statZK` | `Complexity.NUPPT.coinLen.eq_1` | `TCSlib.Complexity.Randomized.PPT` / `TCSlib.Cryptography.Asymptotic.EnsemblesLemmas` | Existing `rw [NUPPT.coinLen, hc, giSimCoins_eval]`; unchanged header/proof/context. Already among 110 and corrected 48 observation keys. |

All three full source contracts/headers/proofs and relevant source binding commands compare
byte-identically to the actual base. Encoding, PPT and EnsemblesLemmas are whole-file identical
base→head; preserve the distinction between a definition's parent home and an equation's
materialization/reference home. The earlier coin-home/operative-context review supplies the
uniform tape-renaming context; it does not create the existing `coinLen` rewrite. The JSON
contains all six raw name/home fields, raw log rows, complete source blocks and hashes.

Exact historical qualification, **without changing frozen artifacts**: cleanup-b-decls row31
and cleanup-b.tsv row29 spell `_root_.Complexity.NUPPT.computes_iff_uprob`. Removing only the
explicit `_root_.` qualifier gives the current exact fully qualified name in the same file.
This is not fuzzy suffix matching. Thus original helper proposal **61/49** receives a companion
qualification **62 historical / 48 newly observed keys = prior35 + PolyTimeModel13**. Both
Encoding failure candidates were already historically linked. The private Block C3 pair is
also historical; the two declaration aliases identify one physical private source root.
The initial 764 inventory, helper and earlier review remain unchanged.

No pair is excluded, waived, reduced to zero or silently repaired. No helper/extractor/native,
Lean/cache/build, source/records/Git mutation or new job occurred. Existing debt repairs and
future proof/fill work stay behind the existing gates and standing post-S2 order.

Raw R2 log SHA256: `0551212d778a277822c0b953d405f01446b8bc35798bc60af7afeda41e961a39`.
Review JSON SHA256: `6f9359dfbda842930a6352e372609494c81e6fa33affd84f1b730058fe0f2a1b`. Full input/source/history pins are in the JSON.

**Not yet clear to merge — these are retained C3 dispositions; extractor validation, gate outcomes and user decisions remain separate.**
