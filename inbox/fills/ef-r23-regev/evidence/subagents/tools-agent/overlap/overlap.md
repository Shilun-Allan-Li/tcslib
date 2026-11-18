# Overlap search, fill ef-r23-regev (series 1+2, head daaf5e65f)

tools-agent, 2026-11-18. Searches: `/home/user/ef-r23/tools/agent/overlap_search.sh`. Every command, its
hit count and its hits (at most 60 per search) are in `search.log` here, and the one-line counts are in
`run-summary.txt`. Trees searched: base `5ed465f6` and PR #377 `7563734a` (`git grep`, `TCSlib/`), Mathlib
sources under `.lake/packages/mathlib/Mathlib` (plain `grep`), and Lean core `Init` v4.25.0. Read-only. No Lean
was run, so every relation below is textual and **unverified in Lean**. Paths are at the base unless they say
#377.

## Summary

No declaration at base or at #377 duplicates the new general-modulus toolkit or the shift reduction.

- No `addMod`, `modAdd`, `vecAdd*`, `% q` or `modContext`-like helper exists under `Encoding/`,
  `ClassP/BinaryArith/` or `LWE/` (0 hits each, at base and at #377).
- `BinArith.mod` is never composed as `mod ∘ add` at base. `ModularArithmetic.addMod` is the first such
  composition.
- No `NUPPT` or `RealizesOn` occurs in `Encryption/*/Regev/` at base or at #377 (0 hits).
- The new files are the first machine-level reductions for Regev.

The near relatives are the dyadic (modulo `2^W`) analogues and the reduction patterns that the new files
already cite.

## Series 1: `Encoding.ModularArithmetic`

| New declaration(s) | Near relative (path:line) | Relation |
|---|---|---|
| `addMod`, `addMod_pairEncode`, `addMod_natToList`, `polyTimeComputable_addMod` | `Encoding/DyadicArithmetic.lean:61` `addPoly` (and `:87` `addPoly_pairEncode`, `:109` `addPoly_natCast_pairEncode`, `:122` `polyTimeComputable_addPoly`) | The dyadic analogue: modulo `2^W` with the width given by a `PolyExpr`. `addMod` reads a general modulus from the input. The module doc says this, and it is a different map, not a duplicate. |
| `addMod` (its body) | `ClassP/BinaryArith/Div.lean:55` `BinArith.mod`, `:62` `mod_pairEncode` (simp, on `Nat.bits` numerals), `:245` `polyTimeComputable_mod`; `CoinSampling/Efficiency.lean:218-221` (a list-level reader `BinArith.mod (pairEncode a b) = Nat.bits (bitsVal a % bitsVal b)`) | Building blocks, reused rather than restated: the new file introduces no `mod` reader of its own (it reads the scalar map through `toLE_eq_natBits`, `Encoding/BinaryArith.lean:72`). Not checked in Lean whether it goes through `Div.lean:62` or the Efficiency reader. |
| `addMod` (mod of add) | `Complexity/Randomized/Primality.lean:81,92,113` (`BinArith.add ⟨[true], BinArith.mod …⟩`: add **of** mod); `Randomized/ZeroPEval.lean:410` `valW = BinArith.mod ⟨rawValW, sK⟩`, `:443`; `ZeroPRun.lean:238` | Other compositions of `add` and `mod`, for other purposes and in the other order. None is a reusable `(a+b) mod q` map. |
| `vecAddStep`, `vecAddModWords`, `vecAddModWords_length`, `polyTimeComputable_vecAdd*`, `vecAddModWords_encodeVector` | `Encoding/DyadicLinearAlgebra.lean:50` `dotStep`, `:120` `dotWords`, `:137` `dotWords_length`, `:157` `polyTimeComputable_dotWords` | The same counted-loop layout (`BinArith.forLoop`, a `⟨ctx, ⟨x, ⟨y, out⟩⟩⟩` state, a `_fst` context lemma, a `_length_le` envelope). It computes a dot product modulo `2^W`, not coordinatewise addition. Parallel structure, no duplication. |
| `subsetSumStep`, `subsetSumModWords`, `subsetSumModWords_encodeMatrix` (`encodeVector w (Aᵀ *ᵥ r)`) | `Encoding/DyadicLinearAlgebra.lean:271` `matVecStep`, `:342` `matVecPoly`, `:395` `matVecPoly_encodeMatrix` (`encodeVector … (A.mulVec v)`) | The closest relative: `matVecPoly` is `A *ᵥ v` modulo `2^W` over rows, while `subsetSumModWords` is `Aᵀ *ᵥ r` for bits `r` modulo a general `q`, as sums of selected rows. The output representations are the same (`Modular.encodeVector`). |
| `subsetSum*` (name) | `HardcoreBit/PairwiseIndependence.lean:287` `subsetSum` (`∑ j ∈ L, s j`, a mathematical sum over a group) and `:294` `subsetSumHom` | Same word, unrelated object (Goldreich–Levin, not encoded). The new names are `subsetSumStep`/`subsetSumModWords` in a different namespace, so they do not clash (clash scan: 0 same-short-name declarations). |
| `vecAddModWords_encodeVector`, `subsetSumModWords_encodeVector` | `Encoding/Modular.lean:51` `encodeVector`, `:57` `encodeVector_eq`, `:65` `encodeMatrix`; `Encoding/BooleanVector.lean:144` (`expandPoly … = Modular.encodeVector`) | The representation the results are stated in, with the existing pattern "machine output = `encodeVector`". |
| `modContext`, `modContext_eq`, `modContext_length`, `listToNat_modulusNumeral` | none found (`*Context`/`*Ctx`/`modulusNumeral`: 0 hits; `natToList (w+1) q`: 0 hits). Ingredients: `Candidates/Arithmetic.lean:107` `length_natToList`, `:143` `listToNat_natToList` | New glue. `listToNat_modulusNumeral` is `listToNat_natToList` at `N = q < 2^(w+1)`, a one-line specialisation; the new file proves it exactly so. Possible inline candidate. |
| (Mathlib) | `Mathlib/Data/ZMod/Basic.lean`: `ZMod.val_add` (3 hits for `val_add*`); Lean core `Init`: `Nat.add_mod` (1 hit); Mathlib `Data/Matrix`: `mulVec_add`/`vecMul_add`/`mulVec_single` (5 hits). No `mulVec` over `ZMod` on encodings (0) | Standard lemmas the correctness proofs may use; no encoded version in Mathlib. |

## Series 2: `Encryption.Symmetric.Regev.Asymptotic`

| New declaration(s) | Near relative (path:line) | Relation |
|---|---|---|
| `shiftAdvice`, `shiftPre`, `shiftPre_shiftAdvice`, `exists_shiftMachine` | `Encryption/Symmetric/Regev/Basic.lean:46` `shift` (the mathematical shift); `Encryption/Symmetric/Regev/Experiments.lean:116` `distAdv_encrypt_le` (the concrete two-hybrid bound) | The machine-level realisation of `shift`. It turns the per-κ reduction of `distAdv_encrypt_le` into one `NUPPT`. No base machine for it (NUPPT/RealizesOn in `Encryption/*/Regev/`: 0 hits). |
| `exists_shiftMachine` (construction) | `Asymptotic/Realization.lean:239` `NUPPT.exists_realizesOn_of_preTarget_id`, `:220` `exists_realizesOn_of_preTarget`, `:132` `RealizesOn.distinguisherL_eq`, `:113` `RealizesOn.coins_eq` | The realisation API it uses, as the docstring says. `Asymptotic/Realization.lean` does not exist at #377 (#377 and the base share merge-base `38123ccbebef`; the file came in on the base side). |
| `exists_shiftMachine` (coin transport) | `Complexity/Randomized/PPT.lean:256` `NUPPT.coinsCongr`, `:266` `runAt_coinsCongr`; `Asymptotic/EnsemblesLemmas.lean:85` `EnsembleLemmas.acceptProb_coins_equiv` (used at the new file's `:264-265`), `:92` `acceptProb_coins_fst`; also `Asymptotic/ReductionSupport.lean:221` (a second public `acceptProb_coins_equiv` in `TCSlib.Cryptography`), `Pseudorandom/NextBit.lean:86` (a private copy); `Encryption/PrivateKey/EnsembleSecurity.lean:60` `acceptProb_distinguisherL_congr` | The new file uses the EnsemblesLemmas version, the existing public lemma. The ReductionSupport/NextBit copies are pre-existing duplication, not introduced by the fill. `Fin.append`/`finSumFinEquiv` coin splits are not needed (coins are `D.coins`, transported by `coinsCongr`). |
| `singleMessageSecure_of_dlweAssumption` (worst-message advice) | `Encryption/PrivateKey/FromPRG.lean:295` `prgScheme_singleMessageSecure`, with `:307` `Finset.exists_max_image` and `:321-322` `NUPPT.exists_withAdvice`; `Complexity/Randomized/Closure.lean:358` `NUPPT.exists_withAdvice`; Mathlib `Finset.exists_max_image` (2 hits) | The averaging pattern the docstring cites. The new proof takes `Finset.exists_max_image` per κ (new file `:296`) and puts the worst message into the advice of the single machine `exists_shiftMachine F μstar D`, instead of calling `exists_withAdvice` twice as FromPRG does. Same idea, different packaging. |
| `singleMessageSecure_of_dlweAssumption` (statement) | `Encryption/PrivateKey/EnsembleSecurity.lean:90` `PrivateKeyScheme.SingleMessageSecure`, `:96` `singleMessageSecure_iff` | The repository's single-message notion for `PrivateKeyScheme`. The Regev theorem is stated directly over the raw `LWE.Family` and encoded encryptions; the module doc notes that no `PrivateKeyScheme` bridge is claimed. A later bridge could target `SingleMessageSecure`. |
| `exists_shiftMachine`, `singleMessageSecure_of_dlweAssumption` (DLWE consumers) | `Pseudorandom/Generators/LWE/Basic.lean:86` `pseudorandom_under_DLWE` (the same encoded machine, no pre-processing); `LWE/Assumption.lean:136` `DLWEAssumption`, `:142` `dlweAssumption_iff` | The only other base consumer of `DLWEAssumption` with a machine. It applies the assumption to `D` itself, with no reduction machine. |
| GSW analogue (#377) | #377 `AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean:96` `encodeView`, `:216` `ReductionEfficient` (hypothesis A4), `:226` `reductionEfficient_iff`, `:295` `indCPA_of_dlweAssumption`; base/#377 `GSW/Security.lean:113` `reduction`, `:248` `distAdv_encrypt_le` | The GSW asymptotic layer on #377 **assumes** reduction efficiency (`ReductionEfficient`, "a domination statement, not a machine construction") and encodes views with `encodeView = encodeChallenge ++ encodeCiphertext`. The Regev file **proves** the corresponding machine (`exists_shiftMachine`). The two use the same `LWE.encodeChallenge` / `F.advantageAt` interface. `reductionMachine`: 0 hits on either tree. No name overlap. When #377 lands, its A4 could perhaps be discharged by the same method. That is an observation, not a claim. |
| `shiftAdviceBound`, `shiftAdviceBound_eval`, `shiftAdvice_length(_le)` | `LWE/Assumption.lean:85-95` (`Family`'s challenge-length polynomial `samplesBound * (dimensionBound + 1) * residueBits` with an `rfl` reader) | Same style: a syntactic `PolyExpr` bound with an evaluation reader. The new bound is the advice length, a different polynomial. |

## Not found (0 hits; see search.log)

`vecAdd*`, `addMod`/`modAdd`, `% q` in Encoding/BinaryArith/LWE, `modContext`-like helpers,
`natToList (w+1) q`, NUPPT/RealizesOn in `Encryption/*/Regev/`, `finSumFinEquiv` with coins, `reductionMachine`,
and Mathlib `mulVec` over `ZMod` on encodings. The counts are the same on base and #377, except
`exists_realizesOn*` / `RealizesOn.*` (3/6 at base, 0 at #377), `DLWEAssumption` (10 at base, 16 at #377: the GSW
asymptotic file) and `Fin.append` with coins (17/16).
