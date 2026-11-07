# Shared-lemma PR: design and implementation status

**Status update, 2026-11-06 PST:** Q1–Q8 are ruled (§6 and the decision log). S1 and the
statement-only host are implemented in PR #227; gate 08 remains on HOLD pending the Codex follow-up audit of the H15, prose and tooling
repairs. H15 is registered in the campaign records; the checked repair head is
`84f35910912bd3d1cd520beea9469e0ed45ce504`. The proof is still reserved for the external S2 fill, not yet issued. Ask Codex or
Claude before preparing that fill. See `gates/08-shared/resolutions-r1.md` for current status.

The inventory, estimates and proposal below were originally drafted at the pinned base on
2026-11-07 (source-session date). They are historical design data, not a claim that S1 is still
unimplemented. The host's success/width wording is corrected below to agree with its unchanged
formal contract and the gate 08 findings.

- **Base read:** `origin/cryptography/pass-shelat-ch2-4` at
  `7018d13e243df4d8b54b99444c34c934199755f5` ("Records: post-landing work started"). Its Lean
  sources are those of the merged base after #224, #225 and #226.
- **Method.** Every declaration name and line number below was read from that commit
  (`git archive` into the scratch area, then `grep`). The import closures come from a script over
  the `import` lines of the same snapshot. Mathlib names were checked by grep in
  `.lake/packages/mathlib/Mathlib`, core names in the Lean v4.25.0 toolchain sources. Similarity
  figures ("1.00", "0.97") come from a normalized text comparison of the declaration bodies, with
  the unit prefixes (`dla_`, `dlc_`, `rsa_`, `rabin_`, `dlb_`, `fac_`) and the loop infixes
  (`ss`, `us`, `rb`) removed. No Lean was run.
- **Sources:** `duplication-ledger.md` (DL-23 to DL-29); the eight delivery reviews and their D1/D2
  sections; rsa's deferred edit E4 (`fills/factoring-candidates/review-rsa-evidence/edits/conditional-harvest-edits.diff`,
  with `harvest-stubs.lean` and `mk_harvest.py`); `policy.md`; `MAINTAINER-HANDOFF.md`;
  `fills/cleanup-part2/brief-draft.md`; `machine-library-design.md` §14.

## 0. Summary

Twenty-six groups of duplicated material were found across the eight landed units, the library and
Mathlib (§1). The proposal has three parts.

1. **PR S1, the shared-lemma PR** (the hand-off's "H1"). It holds proved lemmas only: no `sorry`,
   no new definitions and no target statement changes.
   - It publishes 18 new lemmas in tier 1 and up to 4 more in tier 2 (5 under Q5 (C)), in 8
     existing files.
   - Two private lemmas become public: `foldl_bits_eq` and `abs_uexp_sub_le` in `Sampling.lean`.
   - It deletes 2 public duplicates: `ColZK.pushesUniform_restrict` and `PublicKeyLemmas`'
     `abs_uexp_sub_le`.
   - It applies rsa's E4, which is clean at the base as text. It re-points the copies in the other
     seven landed fill files.
   - Net about −260 lines (−300 with tier 2). The replay covers 98 modules.
2. **PR S2, the host PR** (the hand-off's "H2"). It adds one statement-gated host,
   `polyTimeComputable_rejectBlocksL`, in `Candidates/Concrete.lean`, with registry row H15. It
   retires the four copied rejection loops of dl-a, dl-c, rsa and rabin. Net about −425 lines. The
   replay covers 8 modules.
3. **Clean-up part 2 additions.** These are re-points of copies that live in base files. Each one
   either touches a declaration that clean-up part 2 already rewrites, or touches a file that #195
   edits (§5.4).

Overall, S1 and S2 remove about 1,200 lines of copied material and add about 500 (net about −690).

## 1. Inventory

Format: *copy* = `file:line name` at the base. Paths are relative to `TCSlib/Cryptography/` unless
they start with `TCSlib/`. "Private" is marked (p). The **relation** column uses:
- **verbatim**: identical after renaming;
- **near-verbatim**: the same proof text with small edits;
- **same statement**: equal up to form, with a different proof.

### G1. The rejection-block trial loop (DL-27, DL-28, DL-29; four copies)

| Unit | Copies (all private) | Relation |
|---|---|---|
| dl-a | `Candidates/DiscreteLog.lean`: `dla_ssStart` 738, `dla_ssStep` 744, `dla_ssBlock` 749, `dla_ssAcc` 753, `dla_ssOut` 758, `dla_ssStep_poly` 761, `dla_ssBlock_poly` 773, `dla_ssAcc_poly` 783, `dla_ssOut_poly` 800, `dla_ssStep_iterate` 805, `dla_length_ssStep_le` 816, `dla_length_ssStep_ssStep_le` 823, `dla_length_ssStep_iterate_le` 830, `dla_ssFind_eq` 853, `dla_ssStart_poly` 907 (162 lines) | the first copy |
| dl-c | `Candidates/ElGamal.lean`: `dlc_ssStep` 818, `dlc_ssBlock` 823, `dlc_ssAcc` 827, `dlc_ssOut` 832, `dlc_ssLoop` 835, `dlc_ssStep_poly` 840, `dlc_ssBlock_poly` 850, `dlc_ssAcc_poly` 858, `dlc_ssOut_poly` 866, `dlc_ssStep_iterate` 870, the three `dlc_length_ssStep_*` 880/886/892, `dlc_ssLoop_poly` 906, `dlc_ssLoop_eq` 966, `dlc_numPoly_sample` 1009 (155 lines without G2) | step, block, out, acc, `_iterate` and the three length bounds are **verbatim** dl-a (1.00). `_poly` 0.90–0.92 (`congrArg … .mp` in place of `convert`). `dlc_ssLoop_eq` is `dla_ssFind_eq` generalized (any `u`, `ks`, `ms`, `c`), read through `sampleBelowL_eq_rejectBlocksL` |
| rsa | `Candidates/RSA.lean`: `rsa_usStart` 728, `rsa_usStep` 735, `rsa_usBlock` 741, `rsa_usOut` 757, `rsa_usStep_poly` 766, `rsa_usBlock_poly` 779, `rsa_usOut_poly` 856, `rsa_usStep_iterate` 861, the three `rsa_length_usStep_*` 872/880/887, `rsa_usLoop` 903, `rsa_usLoop_poly` 910, `rsa_usFind_eq` 933, `rsa_usStart_poly` 981 (162 lines). Kept, because they are rsa's test: `rsa_unitTest_eq` 703, `rsa_usGcd` 745, `rsa_usAcc` 750, `rsa_usAcc_poly` 809 | step, block, out, the `_poly` lemmas, `_iterate` and the length bounds are **verbatim** dl-a (1.00). `rsa_usLoop` writes the host's `match` as `Option.elim`. `rsa_usFind_eq` has the same statement shape as rabin's |
| rabin | `Candidates/Rabin.lean`: `rabin_rbStep` 577, `rabin_rbBlock` 583, `rabin_rbAcc` 587, `rabin_rbOut` 591, `rabin_rbLoop` 594, `rabin_rbStep_poly` 599, `rabin_rbBlock_poly` 612, `rabin_rbAcc_poly` 622, `rabin_rbOut_poly` 637, `rabin_rbStep_iterate` 641, the three `rabin_length_rbStep_*` 652/660/667, `rabin_rbLoop_poly` 680, `rabin_rbFind_eq` 695; consumers `rabin_spStart` 755, `rabin_spOut` 759, `rabin_spOut_eq` 766, `rabin_spOut_poly` 785 (136 + 44 lines) | step, out, `_iterate` and `_step_poly` are **verbatim** dl-a. block 0.95 and `block_poly` 0.64: the header is `⟨1^B, 1^k⟩`, and the test is a parameter `acc0`. `rabin_rbFind_eq` is the most general correctness lemma (any `E`, any header), so it is the template of the host |
| origin | `NumberTheory/Primality.lean` (p): `spStep` 704, `spOut` 709, `spAcc` 713, `spStep_iterate` 728, `length_spStep_le` 741, `length_spStep_spStep_le` 747, `length_spStep_iterate_le` 755 (consumer `exists_samplePrime_nuppt` 899) | the length triple is **near-verbatim** with all four copies (constant `2` in place of `4`). The state has two components, not three |

### G2. Search lemmas: `find?` and `findSome?` (DL-27, DL-28)

| Statement | Copies | Relation and existing forms |
|---|---|---|
| `findSome?` of a guarded map is `find?` then map | `dla_findSome?_ite` (DiscreteLog 700, p), `dlc_findSome?_ite` (ElGamal 920, p), `rsa_findSome?_ite` (RSA 661, p) | **verbatim** (1.00). It follows from core `List.findSome?_guard` + `List.map_findSome?` (`Init/Data/List/Find.lean` 94, 128), which `rabin_rbFind_eq` already cites. The general public form is `TCSlib.Cryptography.OneWay.findSome?_eq_bind_find?` (`Asymptotic/OneWayLemmas.lean` 217, outside `Concrete`'s closure) |
| a search over `[0, L)` whose test also demands `i < N` is the search over `[0, N)` | `dla_find?_range_lt` (DiscreteLog 714), `dlc_find?_range_lt` (ElGamal 933), `rsa_find?_range_lt` (RSA 676), `rabin_find?_range_lt` (Rabin 555), all p | **verbatim** (1.00). Near: `OneWay.find?_range_eq_map_find?_finRange` (OneWayLemmas 228), `Complexity.StateLoop.find?_range_eq_some` (`TCSlib/Complexity/Randomized/Build/StateLoop.lean` 170), core `List.find?_range_eq_some`/`_none` (`Init/Data/List/Nat/Range.lean` 254/258). None is a drop-in |
| 3-colouring searches | `ColZK.findSome?_map_option` (`ZeroKnowledge/ThreeColoring/ColZKLemmas.lean` 248, already `List.map_findSome?.symm` by landing edit E3), `ColZK.findSome?_range_eq_finRange` (253) | same statement as core (`List.map_findSome?`; `List.map_coe_finRange` + `List.findSome?_map`) |

### G3. `listToNat`: the defining-equation family (DL-23, DL-25, DL-27, DL-28, DL-29)

| Statement | Copies | Relation |
|---|---|---|
| `listToNat [] = 0` | `dla_listToNat_nil` (DiscreteLog 671), `dlc_listToNat_nil` (ElGamal 600), `rsa_listToNat_nil` (RSA 656) | **verbatim** |
| `⟦a ++ b⟧ = ⟦a⟧·2^{\|b\|} + ⟦b⟧` | `dla_listToNat_append` (DiscreteLog 656), `dlc_listToNat_append` (ElGamal 605), `rsa_listToNat_append` (RSA 2391), `rabin_listToNat_append` (Rabin 1568); `dlb_foldl_bits` (`Candidates/DiscreteLogHardcore.lean` 1950) with `dlb_listToNat_cons` (1961); source of record `TCSlib.Cryptography.foldl_bits_eq` (`Asymptotic/Sampling.lean` 318, p) | the four `_append` are **verbatim** (1.00); each inlines `foldl_bits_eq` as `key`. `dlb_foldl_bits` is **near-verbatim** `foldl_bits_eq` (0.81) |
| `listToNat [true] = 1` | `dlc_listToNat_true` (ElGamal 620), `rsa_listToNat_one` (RSA 651), `rabin_listToNat_one` (Rabin 728); inline `hone` in `fac_polyTimeComputable_isOne` (`Candidates/Factoring.lean` 223) | **near-verbatim** (`rw [listToNat_eq]; rfl`) |

`listToNat` is `TCSlib.Cryptography.NumberTheory.listToNat` (`NumberTheory/Primality.lean` 663), and
its only equation is `listToNat_eq` (667).

### G4. Numerals and widths: `natToList`, `subStr`, `mulStr` (DL-23, DL-27, DL-28, DL-29)

| Statement | Copies | Relation |
|---|---|---|
| `⟦⟦0⟧_k ++ w⟧ = ⟦w⟧` | `dlc_listToNat_zeros_append` (ElGamal 631), `rsa_listToNat_zeros_append` (RSA 2406), `rabin_listToNat_zeros_append` (Rabin 1583); `hval` inside `dla_drop_natToList_zero_append` | rsa = rabin **verbatim**; dlc 0.98 |
| width normalization `(⟦0⟧_W ++ b).drop \|b\| = ⟦⟦b⟧⟧_W` | `dla_drop_natToList_zero_append` (DiscreteLog 678), `dlc_drop_natToList_zero_append` (ElGamal 636), `rsa_drop_zeros_append` (RSA 2412), `rabin_drop_zeros_append` (Rabin 1588) | rsa = rabin **verbatim**; dla 0.95 (near-verbatim); dlc is the **same statement** restructured (0.37) |
| `⟦N mod 2^k⟧_k = ⟦N⟧_k` | `dlc_natToList_mod` (ElGamal 625), `fac_natToList_mod` (Factoring 1087, reversed); inline `hnum` in `dla_`/`rsa_`/`rabin_` width lemmas | **same statement** (0.63) |
| `subStr ⟨a, a⟩ = ⟦0⟧_{\|a\|}` | `dlc_subStr_self` (ElGamal 652), `rsa_subStr_self` (RSA 2433) | **near-verbatim** (0.97) |
| `⟦mulStr ⟨a, b⟩⟧ = ⟦a⟧·⟦b⟧` | `rsa_listToNat_mulStr` (RSA 1067), `rabin_listToNat_mulStr` (Rabin 2707); inline in `dlc_numPoly_mul` (ElGamal 692) | **near-verbatim** (0.97) |
| `⟦1^k⟧ = 2^k − 1` | `rsa_listToNat_ones` (RSA 1047) | one copy; requested by rsa (REPORT request) and used by E4 |
| `⟦0^j⟧ = 0` and leading zeros | `fac_foldl_replicate_false` (Factoring 185), `fac_natToList_lead` (193) | same content as the zeros-append row, in fold form |

### G5. Numeral constants

`rsa_listToNat_two`/`_three` (RSA 1057/1062); `rabin_listToNat_two`/`_three`/`_four`/`_five`/`_seven`
(Rabin 803/807/811/1080/1084); `dlb_listToNat_one`/`_two`/`_four` (DiscreteLogHardcore 1005–1007,
stated on `natToList`); the inline `(by rw [listToNat_eq]; rfl)` in `Factoring.lean` (about line 1346).
These are **same-statement** two-liners, each an instance of the published `listToNat_eq`.

### G6. Polynomial time in applied form, and transfer along pointwise equality (DL-10, DL-25, DL-27, DL-28, DL-29)

| Statement | Copies | Relation |
|---|---|---|
| `PolyTimeComputable fun x => g (f x)` | fills: `rsa_comp` (RSA 761, 42 uses), `rabin_comp` (Rabin 550, 56 uses), `dlb_ptc` (DiscreteLogHardcore 994, 46 uses). Base: private `ptc_comp` in `TCSlib/Complexity/Randomized/Closure.lean` 171 (27 uses), `Asymptotic/Collections.lean` 772, `Asymptotic/UniversalLemmas.lean` 66, `Asymptotic/Universal.lean` 346, `Asymptotic/EnsemblesLemmas.lean` 175. Public: `ColMachines.ptc_comp` (`ZeroKnowledge/ThreeColoring/Machines.lean` 93), `TCSlib.Cryptography.ptcComp` (`Asymptotic/HardCoreLoops.lean` 367) | **verbatim** (`hg.comp hf`); rsa = rabin 1.00, dlb 0.97 |
| `PolyTimeComputable f → (∀ x, f x = g x) → PolyTimeComputable g` | fills: `rsa_ptc_congr` (RSA 1081), and `ElGamal.lean`'s base private `polyTimeComputable_of_forall_eq` (1269, 3 occurrences); inline `(congrArg PolyTimeComputable (funext …)).mp` in dl-a, dl-c, rsa, rabin and dl-b. Public with the **reversed** hypothesis `∀ w, g w = f w`: `ColMachines.ptc_congr` (Machines 84), `ColSimMachine.ptc_congr` (`ThreeColoring/SimulatorMachine.lean` 58), `GI.ptc_congr` (`ZeroKnowledge/GraphIsomorphism/Efficiency.lean` 71); private: `ptc_congr` (`ZeroKnowledge/GraphIsomorphismZK/Simulator.lean` 126) | **same statement** (0.76); the base four are **verbatim** among themselves |

### G7. `2^{size m} ≤ 2m` (DL-25)

| Copy | Relation |
|---|---|
| `dlb_two_pow_size_le` (DiscreteLogHardcore 2717, p): `0 < m → 2 ^ Nat.size m ≤ 2 * m` | the statement |
| inline `hk2` in `statClose_sampleBelowL` (DiscreteLog 616) | **same statement**, inline |
| inline `h2` in `statClose_sampleEdgeIdx` (`ZeroKnowledge/ThreeColoring/Language.lean` 430, base) | **same statement**, inline |
| `h1` inside `rsa_two_pow_size_le` (RSA 448, a different statement) | the same step, `2^{size N − 1} ≤ N` |
| public `TCSlib.Cryptography.two_pow_permBits_le` (`Asymptotic/Permutations.lean` 452) | **same statement** through `permBits n := Nat.size n` (no `permBits` equation is published) |
| public `+1` forms `TCSlib.Cryptography.two_pow_size_le` (`Asymptotic/HardCoreGL.lean` 773) and `TCSlib.Cryptography.two_pow_size_le_two_mul_succ` (`ZeroKnowledge/Encoding.lean` 492) | the **same statement** as each other (a pre-existing public pair) |

Mathlib (`Mathlib/Data/Nat/Size.lean`) has `Nat.size_le` (92), `Nat.lt_size` (111),
`Nat.size_pos` (114) and `Nat.lt_size_self` (81), but not this bound.

### G8. `StatClose X Y 1` (DL-29)

`dla_statClose_one` (DiscreteLog 1139, p) and `rabin_statClose_one` (Rabin 1447, p): **verbatim**
(1.00). No public form exists.

### G9. `abs_uexp_sub_le` (DL-12, DL-28)

| Copy | Relation |
|---|---|
| `TCSlib.Cryptography.abs_uexp_sub_le` (`Asymptotic/Sampling.lean` 204, p) | source. Its proof reads `uexp` by `unfold uexp`: rule-10 row (b) in `gates/07-eqlemmas/evidence-r2/r6c/cleanup-b.tsv` |
| `TCSlib.Cryptography.abs_uexp_sub_le` (`Asymptotic/PublicKeyLemmas.lean` 842, public; **same full name**) | **near-verbatim** (0.97), with the same (b) row |
| `dlc_abs_uexp_sub_le` (ElGamal 1896, p) | **same statement** with `[Nonempty α]` in place of `0 ≤ c`; a different proof (`uexp_mono`, `uexp_const`) |

### G10. `PushesUniform` restrictions (DL-24, DL-25, DL-26)

| Copy | Relation |
|---|---|
| `dla_pushesUniform_restrict` (`Candidates/Concrete.lean` 569, p; codomain `Bool`) | **near-verbatim** with col-b's (0.84) |
| `ColZK.pushesUniform_restrict` (ColZKLemmas 59, public; any codomain `O`) | the general form |
| `TCSlib.Cryptography.pushesUniform_comp_injective` (`Asymptotic/MultiMessage.lean` 231, public; `J = Fin (q + 1)`) | the same proof, specialised. **The file is edited by #195** |
| `GIZK.pushesUniform_castLE` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean` 105), `ColProofs.pushesUniform_castLE` (`ThreeColoring/ProtocolProofs.lean` 382), `GI.pushesUniform_castLE` (`GraphIsomorphism/Proofs.lean` 611); all public, base | GI = ColProofs **verbatim**; GIZK 0.96 (any codomain). Each is the case `r = Fin.castLE h` |
| `dlb_cut` (DiscreteLogHardcore 2469) with `dlb_guess_pushesUniform` (2485) | the same argument (prefix of a uniform string) |

### G11. Coin strings along a length cast (DL-23, DL-28)

`fac_arrowCongr`/`fac_arrowCongr_ofFn` (Factoring 1598/1602, p) and `dlc_castEquiv`/`dlc_castEquiv_ofFn`
(ElGamal 1620/1624, p) are **near-verbatim** (0.91). Both are literally the Mathlib term
`Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)`, with `List.ofFn_congr`
(`Mathlib/Data/List/OfFn.lean` 47). The public relative is `TCSlib.Cryptography.finCastEquiv`/`ofFn_finCastEquiv`
(`Asymptotic/HardCoreLemmas.lean` 95/102, a `Fin.cast` body). It is not in either file's closure.

### G12. Four-move iterations (DL-26)

`ColRep.exec_four_mul` (`ZeroKnowledge/ThreeColoring/ColRepSound.lean` 101, public) against
`GI.exec_repViews` (`ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean` 72, public). They have
different statements; the induction step is the same argument (four `exec_succ`, `moverIsV_false`).
`ColRep.chView` (66) is the counterpart of `GI.PsOf` (130).

### G13. Tape windows and blocks (DL-9, DL-23, DL-26)

| Copy | Relation |
|---|---|
| `dla_take_drop_ofFn` with `dla_blockPos`/`dla_blockPos_injective` (Concrete 615/588/597, p) | the block-`t` window, `k ≤ B` |
| `ColZK.ofFn_drop_take`, `ofFn_drop_eq`, `ofFn_take_drop` (ColZKLemmas 216/225/235, public) | general windows at any offset |
| `ColRep.drop_take_ofFn_blockRead` (ColRepSound 195, public) | the castLE form |
| `fac_ofFn_halves` (Factoring 211, p) | half is `OneWay.ofFn_block_eq_take_drop` (`Asymptotic/OneWayLemmas.lean` 74) at `q = 2` |
| `fac_chunkEquiv` (Factoring 1186, p), `fac_blocks_eq_blocksE` (698, p) | the latter is **near-verbatim** the private `blocks_eq_blocksE` (`Asymptotic/OneWay.lean` 626); both belong to DL-9 (`FunFamily.blocks`, `Asymptotic/OneWay.lean` 243) |
| private `ofFn_chunk` (Primality 768); `EnsembleLemmas.take_drop_ofFn_blocks` | relatives |

### G14. Table positions

`ColZK.table_index_lt`/`table_index_inj` (ColZKLemmas 75/83, public) restate the range and the
injectivity of Mathlib's `finProdFinEquiv` (`Mathlib/Logic/Equiv/Fin/Basic.lean` 325, `@[simps]`,
`j + k·i` order); `dla_blockPos` likewise. **Same statement** up to order.

### G15. The unit sampler's total value (DL-29)

`rsa_one_mod_spec`/`rsa_getD_spec` (RSA 393/401, p) and `rabin_one_mod_spec`/`rabin_getD_spec`
(Rabin 1244/1252, p) are the **same statement**, with different proofs (0.60–0.77).

### G16. Arithmetic-bundle wrappers in applied form (DL-29)

`rsa_le_poly` (RSA 791) and `rabin_le_poly` (Rabin 815) are the **same statement** (0.67).
`rsa_prime_poly` (RSA 1155; any word `a`) and `rabin_prime_poly` (Rabin 823; `a = id`) are the
**same statement** (0.80). Relatives: `dlc_poly_le` (ElGamal 744, numeral-calculus form) and
`fac_polyTimeComputable_isOne` (Factoring 223).

### G17. `((e : ZMod 0)⁻¹).val ≤ 1`

`rsa_val_inv_zero_le` (RSA 2437) and `rabin_val_inv_zero_le` (Rabin 2701), both p: **verbatim** (1.00).

### G18. Averages under a statistical switch (DL-29)

`rabin_uexp_le` (Rabin 1887, p) and the device of `rsa_uprob_pi_eval` (RSA 2184, p) with
`rsa_step_ii`: the **same argument**.

### G19. Selecting a `DistinctPrimes` from two numbers (DL-27, DL-29)

`fac_pairDec`/`fac_pairDec_pq` (Factoring 1608/1625); `rsa_zsel`/`rsa_zOf`/`rsa_zOf_pq`/`rsa_zOf_self`
(RSA 1993/2013/2019/2027); `rabin_mkDP`/`_p`/`_q`/`rabin_zOf` (Rabin 2031–2046). All are private.
They share an idea, but the fallbacks differ (`some default`, `DistinctPrimes.default hk`, a given
`z0`).

### G20. The factor-check words (DL-29)

`rsa_fS`/`rsa_fQ`/`rsa_fTest` (RSA 2443/2448/2452) and `rabin_rS`/`rabin_rQ`/`rabin_rTest`
(Rabin 3558/3562/3566), all p: **near-verbatim** data definitions (0.90–0.99).

### G21. Zero padding

`rabin_pad`/`_eq`/`_poly` (Rabin 732/736/742) and `rabin_zpad`/`rabin_listToNat_zpad`/`rabin_length_zpad`/`rabin_zpad_poly`
(2715–2726), all p, against the width normalization of G4. Same purpose; different statements.

### G22. Guarded state iteration (DL-11, DL-25)

`dlb_stateIterate_poly` (DiscreteLogHardcore 1119, p) is the body of the public
`TCSlib.Cryptography.polyTimeComputable_stateIterate` (`Asymptotic/HardCoreLoops.lean` 70, outside
the closure) at `out = pairSndD`: **near-verbatim**.

### G23. Counting `true`s in `List.ofFn` (DL-25)

`dlb_count_ofFn` (DiscreteLogHardcore 1967, p) against the public `TCSlib.Cryptography.count_true_ofFn`
(`Asymptotic/HardCoreGL.lean` 75): **near-verbatim** (0.97). There is also the general
`List.count_ofFn` (`TCSlib/Programs/Util/List.lean` 396, on `main`, namespace `List`). None is in the
closure. Mathlib has none.

### G24. Numeral calculi on the arithmetic bundle (DL-25, DL-28)

These are the **same pattern**, not copies:
- `dlc_NumPoly` and its closure lemmas (ElGamal 656–806);
- dl-b's fixed-width layer `dlb_{mulMod,powMod,invMod,quot,rem}` with `_poly` and `_natToList`
  (DiscreteLogHardcore 1010–1077);
- `dlc_poly_take`/`dlc_poly_drop` (ElGamal 1023/1030) against `dlb_take_poly`/`dlb_drop_poly` (1088/1094);
- `dlc_numPoly_ite` against `dlb_ite_poly` (1108).

### G25. 3-colouring near-copies (DL-24)

- `ColZK.polyTimeComputable_next` (`ThreeColoring/ColZKMachine.lean` 196) has the proof of
  `ColSimMachine.reply_poly` (`SimulatorMachine.lean` 443) with the tape generic.
- `ColZK.distAdv_seed_to_coins` has the content of `distAdv_sunglassRed`
  (`Pseudorandom/Indistinguishability.lean` 130), which cannot be cited: `sunglassRed` has no
  published equations.
- `ColZK.field_encodeMsgs` (ColZKMachine 142) is `ColMachines.getD_eq_pairFstD_iterate`
  (Machines 949) reversed.

### G26. Injectivity of reading

`fac_listToNat_inj` (Factoring 1351, p; an iff, 4 lines from the public `natToList_length_listToNat`)
against the private `listToNat_inj` (Sampling 337; fold form). **Same statement**, different proof (0.16).

**Already resolved at landing** (not in scope):
- `rsa_appendEquiv` and `rabin_appendEquiv` are now Mathlib's `Fin.appendEquiv`;
- `rabin_pushesUniform_prod` is now `PushesUniform.prodMap`;
- `dlb_statClose_pi` is now `OneWay.statClose_pi`;
- `colRep_xor_poly` is now `StateLoop.xor_poly`;
- `eq_of_xor_eq_false` is now core `bne_eq_false_iff_eq`;
- `pushesUniform_blockRead`'s inline block bijection is now `EnsembleLemmas.blocks`;
- `ColZK.acceptProb_seed_to_coins` is now `acceptProb_bind`.

Each was checked absent at the base (0 occurrences), except `rabin_pushesUniform_prod`, which E2
kept with the new body.

## 2. Import graph: where a home can be

Each home must be in the import closure of every consumer, and must not import a consumer. The
closures were computed from the base's `import` lines.

| Candidate home | Reaches | Does not reach | Note |
|---|---|---|---|
| `TCSlib/Complexity/Randomized/Closure.lean` | all 7 candidate files, all 3-colouring fill files, and every base G6 copy (`Collections`, `UniversalLemmas`, `Universal`, `EnsemblesLemmas`, `HardCoreLoops`, `ThreeColoring/Machines`, `SimulatorMachine`, `GI/Efficiency`, `GIZK/Simulator`) | — | campaign-owned (not on `main`); the home ruled for DL-10 (G3-5) |
| `TCSlib/Complexity/ClassNP/PolyTime.lean` | everything | — | **a `main` file** (identical on `main`); about 341 downstream modules. Avoided |
| `TCSlib/Complexity/Randomized/Build/IterateFind.lean` | all candidate and 3-colouring files | — | campaign-owned |
| `NumberTheory/Primality.lean` | all 7 candidate files | 3-colouring (no consumer there) | 922 lines; it imports `Asymptotic/Sampling.lean` |
| `Candidates/Arithmetic.lean` | all 7 candidate files | 3-colouring | 385 lines |
| `Candidates/Concrete.lean` | the 6 downstream candidate files | 3-colouring, `Primality` | **Cycle:** `Concrete → Arithmetic → Primality`, so `Primality` can never cite a lemma in `Concrete` (see Q3) |
| `Asymptotic/Sampling.lean` | all candidate and 3-colouring files, `Primality`, `Permutations`, `Encoding`, `HardCoreGL`, `PublicKeyLemmas`, `Language` | — | 856 lines |
| `HardcoreBit/Basic.lean` | all candidate and 3-colouring files, `MultiMessage`, `GIZK/Closeness`, `ProtocolProofs`, `GI/Proofs` | — | 266 lines |
| `Asymptotic/HardCoreLemmas.lean`, `HardCoreGL.lean`, `PublicKeyLemmas.lean`, `EnsemblesLemmas.lean`, `ZeroKnowledge/Encoding.lean` | — | every candidate file | so their public lemmas (`finCastEquiv`, `count_true_ofFn`, `two_pow_size_le`, `abs_uexp_sub_le`, …) cannot be cited from the fills |
| `Asymptotic/OneWayLemmas.lean` | the candidate files except `Concrete` | `Concrete` | — |

**Overlap with the open #195** (`cryptography/pass-shelat-ch5-8-s2b`, 25 Lean files against its
merge base `3436321b`). #195 edits `Asymptotic/MultiMessage.lean` and
`ZeroKnowledge/Interaction.lean`, among others. S1 and S2 touch neither file. So the
`pushesUniform_comp_injective` re-point and any move of `exec_four_mul` into `Interaction.lean` go
to clean-up part 2, which runs after #195.

## 3. Homes, statements and decisions

The decision legend:
- **Publish**: new public API, so it needs a statement audit (Q1).
- **Cite**: cite an existing public lemma.
- **Leave**: leave private, for the reason given.
- **Defer**: clean-up part 2.

No new lemma carries `@[simp]`. Every docstring opens with a natural-language statement and gives
its formula (policy §1–§2). Lemmas with long proofs carry a `**Proof sketch.**` (§3). These are
glue lemmas with no textbook counterpart, so they carry no `[PS10, …]` tag. The host (§4) does.

### 3.1 Decisions

| Group | Decision | PR |
|---|---|---|
| G1 trial loop | **Publish** the host `polyTimeComputable_rejectBlocksL` (§4) and delete the four loops | S2 |
| G2 search | **Publish** `IterateFind.find?_range_and_lt` and `rejectBlocksL_eq_find?`. The three `findSome?_ite` go through the latter, which is proved from **core** `List.findSome?_guard`, `List.map_findSome?` and `Option.guard_apply`. **Leave** the two `ColZK` searches (already public one-liners) | S1 |
| G3 `listToNat` equations | **Publish** `listToNat_nil`, `listToNat_cons`, `listToNat_append` and `listToNat_singleton_true` in `Primality.lean`. Make `foldl_bits_eq` public in `Sampling.lean` (a visibility change) | S1 |
| G4 widths | **Publish** `natToList_mod_two_pow`, `listToNat_natToList_zero_append`, `natToList_zero_append_drop`, `subStr_self`, `listToNat_mulStr`, `listToNat_replicate_true` and `listToNat_replicate_false` in `Arithmetic.lean` | S1 |
| G5 constants | **Leave** (Q8). They are instances of the published `listToNat_eq`, not copied proofs. Record them in the ledger as accepted | — |
| G6 `comp'`/`congr` | **Publish** `PolyTimeComputable.comp'` and `.congr` in `Closure.lean`. Re-point the fill copies (`rsa_comp`, `rabin_comp`, `dlb_ptc`, `rsa_ptc_congr`, `polyTimeComputable_of_forall_eq`) in S1. **Defer** `Closure`'s own private `ptc_comp` and the base copies to clean-up part 2 (DL-10; §5.3 explains why) | S1 + C2 |
| G7 `2^{size}` | **Publish** `two_pow_size_le_two_mul` in `Sampling.lean`. Re-point `dlb_two_pow_size_le` and dl-a's `hk2` in S1. **Defer** `Language`'s `h2`, `two_pow_permBits_le` and the `+1` pair | S1 + C2 |
| G8 `statClose_one` | **Publish** in `Sampling.lean` | S1 |
| G9 `abs_uexp_sub_le` | **Publish**: make the `Sampling.lean` one public, with `rw [uexp_def]` in place of `unfold uexp`. Delete the `PublicKeyLemmas` copy (same full name, so its users resolve unchanged). Re-point `dlc_abs_uexp_sub_le`. This takes DL-12 over from clean-up part 2 and retires two (b) rows | S1 |
| G10 restrictions | **Publish** `HardcoreBit.pushesUniform_restrict` in `HardcoreBit/Basic.lean`. Re-point `dla_pushesUniform_restrict` and `ColZK.pushesUniform_restrict` (Q6). **Defer**: the `castLE` triple (as corollaries), `dlb_cut`, and `pushesUniform_comp_injective` (#195's file) | S1 + C2 |
| G11 casts | **Cite Mathlib**: `Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)` and `List.ofFn_congr`. Moving `finCastEquiv` would make `dlc_splitEquiv_symm_ofFn`'s `subst h; exact …` a definitional read of another file's definition. Mathlib definitions may reduce there (§5.5) | S1 |
| G12 four moves | **Leave** (public already). An optional move into `Interaction.lean` waits for #195 | C2 (optional) |
| G13 windows | **Defer** to clean-up part 2 item A with DL-9 (the `blocks` family). `ColZK.ofFn_drop_take` is the natural public form; a move to `Asymptotic/CollectionsHelpers.lean` would serve `Concrete` | C2 |
| G14 table positions | **Defer**: cite `finProdFinEquiv` (optional) | C2 |
| G15 unit fallback | **Publish** `sampleUnitL_getD_spec` in `RSA.lean` (tier 2, Q5) | S1 |
| G16 bundle wrappers | **Publish** `ArithmeticFP.le_poly` and `ArithmeticFP.prime_poly` in `Arithmetic.lean` (tier 2, Q5) | S1 |
| G17 `ZMod 0` inverse | **Publish** `val_inv_natCast_zmod_zero_le` in `Arithmetic.lean`, beside `xgcdStr_pairEncode` (tier 2, Q5) | S1 |
| G18 average switch | **Defer** `uexp_le_of_statClose` (`Sampling.lean`; tier 2, Q5) | C2 |
| G19 selectors | **Leave**. A public selector is a new definition with equation lemmas, and its fallback must be designed first | — |
| G20 factor-check words | **Leave**. They are the words of each reduction (rabin review, finding 5) | — |
| G21 padding | **Leave**. After S2, `rabin_pad` is used only by the restricted prime sampler | — |
| G22 state iteration | **Defer** to DL-11 (clean-up part 2 item A: move `polyTimeComputable_stateIterate` into `Complexity.StateLoop`) | C2 |
| G23 counting | **Defer**. Move `count_true_ofFn` to a low file, then re-point `dlb_count_ofFn` | C2 |
| G24 numeral calculi | **Leave** (Q8) | — |
| G25 3-colouring | **Defer** (re-derive `reply_poly` from `polyTimeComputable_next`). **Leave** `distAdv_seed_to_coins`, which needs `sunglassRed`'s equations (a request to that file's owner) | C2 |
| G26 injectivity | **Leave**: 4 lines from a published lemma, with one consumer | — |

"C2" means clean-up part 2.

### 3.2 Exact statements (S1)

**`TCSlib/Complexity/Randomized/Closure.lean`**, namespace `Complexity`, placed after `open Turing`
and before `namespace NUPPT` (line 87):

```lean
/-- **Composition in applied form**: if `g` and `f` are polynomial-time, so is `x ↦ g (f x)`.
This is `PolyTimeComputable.comp` stated without `Function.comp`, so that unification never has
to unfold a composite against a lambda (hand-off pitfall: such matches can unfold bundle string
functions). -/
theorem PolyTimeComputable.comp' {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun x => g (f x) :=
  hg.comp hf

/-- **Polynomial time transfers along pointwise equality**: if `f` is polynomial-time and
`f x = g x` for every `x`, then `g` is polynomial-time (Mathlib's `Continuous.congr`
orientation). -/
theorem PolyTimeComputable.congr {f g : List Bool → List Bool} (h : PolyTimeComputable f)
    (e : ∀ x, f x = g x) : PolyTimeComputable g :=
  (funext e : f = g) ▸ h
```

**`TCSlib/Complexity/Randomized/Build/IterateFind.lean`**, namespace `Complexity.IterateFind`,
beside `find?_congr_of_mem` (227):

```lean
/-- **A bounded search is a search over a shorter range**: for `N ≤ L`, searching `[0, L)` for
the first `i` with `i < N` and `p i` is searching `[0, N)` for the first `i` with `p i`:
`(List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p`.

**Proof sketch.** Write `L = N + d` (`List.range_add`, `List.find?_append`). On `[0, N)` the guard
`i < N` holds, so the two predicates agree (`find?_congr_of_mem`). On the shifted tail `N + [0, d)`
it fails, so that search is `none` (`List.find?_eq_none`), and `o <|> none = o`. -/
theorem find?_range_and_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p
```

**`NumberTheory/Primality.lean`**, namespace `TCSlib.Cryptography.NumberTheory`, beside
`listToNat_eq` (667). Each is proved from `listToNat_eq` and `List.foldl_*`, with `foldl_bits_eq`
from `Sampling.lean`, which is upstream. The file grows from 922 to about 952 lines.

```lean
/-- The empty word reads as `0`: `listToNat [] = 0`. -/
theorem listToNat_nil : listToNat [] = 0

/-- **Prepending a bit** (most significant first): `⟦b :: l⟧ = [b] · 2^{|l|} + ⟦l⟧`, with
`[b] = 1` if `b` and `0` otherwise. -/
theorem listToNat_cons (b : Bool) (l : List Bool) :
    listToNat (b :: l) = (if b then 1 else 0) * 2 ^ l.length + listToNat l

/-- **Concatenation** (most significant first): `⟦a ++ b⟧ = ⟦a⟧ · 2^{|b|} + ⟦b⟧`. -/
theorem listToNat_append (a b : List Bool) :
    listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b

/-- The one-bit word `[true]` reads as `1`. -/
theorem listToNat_singleton_true : listToNat [true] = 1
```

- **Audit point (`listToNat_cons`):** `(if b then 1 else 0)` matches dl-b's form and the fold. The
  alternative is `b.toNat`.

**`Asymptotic/Sampling.lean`**, namespace `TCSlib.Cryptography`. The file grows from 856 to about
885 lines.

```lean
/-- **The binary fold with an accumulator** (visibility change only; statement unchanged): the
fold of `listToNat` started at `a` is `a · 2^{|l|}` plus the fold started at `0`. -/
theorem foldl_bits_eq (l : List Bool) (a : ℕ) :
    l.foldl (fun a c => 2 * a + (if c then 1 else 0)) a =
      a * 2 ^ l.length + l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0

/-- **Averages of pointwise `c`-close functions are `c`-close** (visibility change; the proof
reads `uexp` through `uexp_def`): for `0 ≤ c` and `|f a − g a| ≤ c` for all `a`,
`|uexp f − uexp g| ≤ c`. -/
theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c

/-- **Any two samplers are `1`-close**: `StatClose X Y 1`, since both probabilities of every test
lie in `[0, 1]` (`statClose_iff`, `uprob_nonneg`, `uprob_le_one`). -/
theorem statClose_one {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) :
    StatClose X Y 1

/-- **A positive number is at least half the next power of two**: for `0 < m`,
`2 ^ Nat.size m ≤ 2 m` (the top bit of `m` is bit `size m − 1`: `Nat.lt_size`, `Nat.size_pos`). -/
theorem two_pow_size_le_two_mul {m : ℕ} (hm : 0 < m) : 2 ^ Nat.size m ≤ 2 * m
```

- **Audit point (name):** the name is kept out of Mathlib's `Nat` namespace (policy §1,
  Namespaces).

**`Candidates/Arithmetic.lean`**, namespace `TCSlib.Cryptography.Candidates`, beside
`natToList_length_listToNat` (161), `subStr_pairEncode` (291) and `mulStr_pairEncode` (274). The
file grows from 385 to about 460 lines.

```lean
/-- **A numeral keeps the low bits**: `⟦N mod 2^k⟧_k = ⟦N⟧_k`. -/
theorem natToList_mod_two_pow (k N : ℕ) : natToList k (N % 2 ^ k) = natToList k N

/-- **Leading zeros do not change the value**: `⟦⟦0⟧_k ++ w⟧ = ⟦w⟧`. -/
theorem listToNat_natToList_zero_append (k : ℕ) (w : List Bool) :
    listToNat (natToList k 0 ++ w) = listToNat w

/-- **Width normalization by truncation**: the last `W` bits of `⟦0⟧_W ++ b` are the
`W`-bit numeral of `⟦b⟧`, `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W` (the low `W` bits, also when
`⟦b⟧ ≥ 2^W`).

**Proof sketch.** The word `w = ⟦0⟧_W ++ b` reads as `⟦b⟧` (leading zeros), and splitting it after
its first `|b|` bits gives `⟦w⟧ = ⟦w.take |b|⟧ · 2^W + ⟦w.drop |b|⟧` (`listToNat_append`), where the
second summand is below `2^W`. So `⟦w.drop |b|⟧ = ⟦b⟧ mod 2^W`, and a word of length `W` is the
numeral of its value (`natToList_length_listToNat`, `natToList_mod_two_pow`). -/
theorem natToList_zero_append_drop (W : ℕ) (b : List Bool) :
    (natToList W 0 ++ b).drop b.length = natToList W (listToNat b)

/-- **Subtracting a word from itself** gives the zero numeral of its width:
`subStr ⟨a, a⟩ = ⟦0⟧_{|a|}`. -/
theorem subStr_self (a : List Bool) : subStr (pairEncode a a) = natToList a.length 0

/-- **The product word reads back exactly**: `⟦mulStr ⟨a, b⟩⟧ = ⟦a⟧ · ⟦b⟧` (the product fits in
`|a| + |b|` bits). -/
theorem listToNat_mulStr (a b : List Bool) :
    listToNat (mulStr (pairEncode a b)) = listToNat a * listToNat b

/-- **The all-ones word** `1^k` reads as `2^k − 1`. -/
theorem listToNat_replicate_true (k : ℕ) : listToNat (List.replicate k true) = 2 ^ k - 1

/-- **The all-zeros word** `0^k` reads as `0`. -/
theorem listToNat_replicate_false (k : ℕ) : listToNat (List.replicate k false) = 0
```

**`Candidates/Concrete.lean`**, namespace `TCSlib.Cryptography.Candidates`, beside
`rejectBlocksL_eq` (547):

```lean
/-- **Block rejection sampling as a search followed by the value read**: `rejectBlocksL E k B T r`
is the first trial `t < T` whose value `v_t = ⟦(r.drop (t B)).take k⟧` passes `E`, mapped to
`v_t` (core `List.findSome?_guard`, `List.map_findSome?`, `Option.guard_apply`). -/
theorem rejectBlocksL_eq_find? (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r =
      ((List.range T).find? fun t => decide (E (listToNat ((r.drop (t * B)).take k)))).map
        fun t => listToNat ((r.drop (t * B)).take k)
```

- **Proof correction (rule 10).** The stub in `harvest-stubs.lean` closes with
  `simp [Option.guard, ht]`. That passes a core definition to `simp`, which the 2026-10-23 rule
  forbids. The landed proof uses core's `Option.guard_apply` (`Init/Data/Option/Lemmas.lean` 668).

**`HardcoreBit/Basic.lean`**, namespace `TCSlib.Cryptography.HardcoreBit`, after `pushesUniform_fst`
(204). Add `import Mathlib.Logic.Equiv.Set` if `Equiv.Set.sumCompl` is not already reachable. The
file grows from 266 to about 292 lines.

```lean
/-- **Restricting a uniform table along an injection gives a uniform table**: for an injective
`r : J → I`, the map `R ↦ R ∘ r` pushes the uniform distribution on `I → O` to the uniform
distribution on `J → O`.

**Proof sketch.** Split `I` into the image of `r` and its complement (`Equiv.ofInjective`,
`Equiv.Set.sumCompl`). A table is the pair of its two restrictions (`Equiv.sumArrowEquivProdArrow`),
and `R ∘ r` is the first one (`pushesUniform_equiv`, `pushesUniform_fst`). -/
theorem pushesUniform_restrict {I J O : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype O] [Nonempty O] {r : J → I} (hr : Function.Injective r) :
    PushesUniform (fun R : I → O => fun j => R (r j))
```

**Tier 2** (Q5):

```lean
-- Candidates/RSA.lean, beside sampleUnitL_spec (387)
/-- **The total unit sampler gives a unit**: for `0 < N`, the value
`(sampleUnitL N k B T r).getD (1 % N)` is below `N` and coprime to `N` (`sampleUnitL_spec`, or the
fallback `1 mod N`). -/
theorem sampleUnitL_getD_spec {N : ℕ} (hN : 0 < N) (k B T : ℕ) (r : List Bool) :
    (sampleUnitL N k B T r).getD (1 % N) < N ∧
      Nat.Coprime ((sampleUnitL N k B T r).getD (1 % N)) N

-- Candidates/Arithmetic.lean, beside ArithmeticFP (250) and xgcdStr_pairEncode (353)
/-- **Comparisons are polynomial-time tests**: for polynomial-time words `a`, `b`, the bit
`[⟦a x⟧ ≤ ⟦b x⟧]` is polynomial-time (`H.le`, read through `leStr_pairEncode`). -/
theorem ArithmeticFP.le_poly (H : ArithmeticFP) {a b : List Bool → List Bool}
    (ha : PolyTimeComputable a) (hb : PolyTimeComputable b) :
    PolyTimeComputable fun x => [decide (listToNat (a x) ≤ listToNat (b x))]

/-- **Primality of a polynomial-time word is a polynomial-time test** (`H.prime`, `primeStr_eq`). -/
theorem ArithmeticFP.prime_poly (H : ArithmeticFP) {a : List Bool → List Bool}
    (ha : PolyTimeComputable a) : PolyTimeComputable fun x => [decide (listToNat (a x)).Prime]

/-- In `Z_0 = ℤ` the inverse of a natural number is its sign, so its value is at most `1`
(the `N = 0` case of `xgcdStr_pairEncode`'s inverse). -/
theorem val_inv_natCast_zmod_zero_le (e : ℕ) : ((e : ZMod 0)⁻¹).val ≤ 1
```

`uexp_le_of_statClose` (the statement of `rabin_uexp_le`) is deferred: it has one consumer, and
rsa uses the device inline.

All of these names were checked: none exists in TCSlib or Mathlib at the base. The one exception is
`pushesUniform_restrict`, which exists only as the `ColZK` copy that S1 removes (Q6).

**E4 compatibility.** rsa's E4 cites these names unqualified:
- `listToNat_nil`, `listToNat_singleton_true`, `listToNat_append`, `listToNat_replicate_true`,
  `listToNat_mulStr`, `listToNat_natToList_zero_append`, `natToList_zero_append_drop`, `subStr_self`;
- `rejectBlocksL_eq_find?`, `IterateFind.find?_range_and_lt`, `PolyTimeComputable.comp'`,
  `PolyTimeComputable.congr`.

`RSA.lean` sits in `TCSlib.Cryptography.Candidates` with `open Complexity Turing NumberTheory`, so
all of them resolve. That holds although the four `listToNat_*` live in `NumberTheory` rather than
in the stubs' `Candidates`. `git apply --check` of the E4 diff on the base `RSA.lean` is clean (text
only; −177/+64 lines).

## 4. The host: `polyTimeComputable_rejectBlocksL` (PR S2)

**Home:** `Candidates/Concrete.lean`, namespace `TCSlib.Cryptography.Candidates`, after
`rejectBlocksL_spec` (555). It is the file of `rejectBlocksL` (539), so the host's own proof may use
`rejectBlocksL_eq_find?`. Every consumer imports it: `DiscreteLog` and `Factoring` directly, and
`ElGamal`, `RSA` and `Rabin` through them. Registry: a new row **H15** in
`machine-library-design.md` §14 (records). This is the host of policy §1, **Hosts come first**.
- **Time:** its contract is `PolyTimeComputable`.
- **No head envelope:** this is a string-function host over the repetition host
  `Complexity.polyTimeComputable_iterateFind` (machine layer H14), so there is no head envelope to
  state.

### 4.1 Statement

```lean
/-- **Block rejection sampling is polynomial-time** (host H15) [PS10, Theorems 52.3, 53.2, 61.7
and 63.10: "the domain is easy to sample"]. Let `E a v` be a test on a parameter `a` and a value
`v`, decided on words by a polynomial-time bit `acc`, so that `acc ⟨w, b⟩ = [E ⟦w⟧ ⟦b⟧]`. Take
polynomial-time words `par z` (the parameter), `kw z`, `bw z` and `tw z`, whose lengths are the
trial width `k`, the block length `B` and the trial count `T`, and `c z` (the coins). Then some
polynomial-time `g` computes the sampler `rejectBlocksL (E ⟦par z⟧) k B T (c z)`:
- `g z = []` when every trial is rejected;
- otherwise `g z` is nonempty, and its tail reads as the accepted value and has at most `k` bits.

In particular `(rejectBlocksL …).getD 0 = ⟦(g z).tail⟧`. The statement is existential: the trial
loop that realizes it is internal, and no consumer reads it.

**Proof sketch.**
- **The loop.** The state is `⟨⟨⟨1^B, 1^k⟩, w⟩, ⟨1^T, r⟩⟩`. One step keeps the header, drops one
  bit of the counter and one block of `B` coins (`polyTimeComputable_tail`,
  `polyTimeComputable_pairDropPoly`). The test accepts iff the counter is nonempty and
  `acc ⟨w, first k coins⟩` holds (`polyTimeComputable_isNil`, `polyTimeComputable_pairTakePoly`).
  The payload is `true` followed by the first `k` coins.
- **Polynomial time.** One step at most doubles the length, and from the second step on the state
  only shrinks (`StateLoop.length_pairFstD_add_pairSndD_le`). So the repetition host
  `Complexity.polyTimeComputable_iterateFind`, with `R = var` and orbit bound `2n + 4`, makes the
  loop polynomial-time. Its `match` is split by its equation lemmas (`split`), never matched by
  definitional unfolding.
- **Correctness.** After `i` steps the coins have lost `i` blocks, so trial `i` reads the `k`-bit
  prefix of block `i`. The search over the first `|start| + 1 ≥ T` rounds is therefore the search
  over `[0, T)` (`IterateFind.find?_range_and_lt`), which is `rejectBlocksL` read as a search
  followed by its value (`rejectBlocksL_eq_find?`). -/
theorem polyTimeComputable_rejectBlocksL (E : ℕ → ℕ → Prop) [∀ a, DecidablePred (E a)]
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun x => [acc x])
    (hspec : ∀ w b : List Bool, acc (pairEncode w b) = decide (E (listToNat w) (listToNat b)))
    {par kw bw tw c : List Bool → List Bool} (hpar : PolyTimeComputable par)
    (hkw : PolyTimeComputable kw) (hbw : PolyTimeComputable bw) (htw : PolyTimeComputable tw)
    (hc : PolyTimeComputable c) :
    ∃ g : List Bool → List Bool, PolyTimeComputable g ∧ ∀ z,
      (g z).tail.length ≤ (kw z).length ∧
      rejectBlocksL (E (listToNat (par z))) (kw z).length (bw z).length (tw z).length (c z) =
        if g z = [] then none else some (listToNat (g z).tail)
```

### 4.2 Design choices for the statement audit

- **Existential output.** A public loop function would be a new definition. It would then need its
  own equation lemmas, and consumers would be tempted to read it. The existential publishes exactly
  what the four consumers use:
  - emptiness ↔ rejection;
  - the value read from the tail;
  - the length bound, which rabin's padding needs.

  `getD 0` follows by cases, since `[].tail = []` reads `0` (`listToNat_nil`).
- **A parameter-dependent test** `E : ℕ → ℕ → Prop`, decided on `⟨w, b⟩`:
  - dl-a and dl-c use `E a v := v < a` with `par` = the modulus numeral;
  - rsa uses `E a v := v < a ∧ v.Coprime a`;
  - rabin uses `E _ v := v.Prime ∧ P v` (the parameter is ignored).

  The test is given in the repetition host's convention (`acc : List Bool → Bool`,
  `PolyTimeComputable fun x => [acc x]`).
- **Lengths of words** `kw`, `bw`, `tw` rather than numbers. Every consumer has its sizes as unary
  words already:
  - `sizeStr ⟦m⟧`, whose length is `Nat.size` (`length_sizeStr`);
  - `1^n` from `inParam`;
  - `polyTimeComputable_unaryPoly rsaBlock` and `rabinTrials`.
- **Instances.** `rejectBlocksL (E (listToNat (par z)))` is a β-redex. Consumers `beta_reduce` the
  hypothesis before rewriting it against `sampleBelowL_eq_rejectBlocksL` or `sampleUnitL_eq`. The
  `DecidablePred` instance then agrees up to β (to be confirmed in the fill).

### 4.3 What each consumer cites

| Consumer | Published equations it reads | Re-proved | Deleted |
|---|---|---|---|
| dl-a (`DiscreteLog.lean`) | `sampleBelowL_eq_rejectBlocksL` (578, own file), `natToList_zero_append_drop`, `subStr_self`, `listToNat_nil`, `length_sizeStr` | `polyTimeComputable_expSampleRaw` (proof and sketch). Test `fun x => !decide (⟦pairFstD x⟧ ≤ ⟦pairSndD x⟧)` by `H.le` | the 15 `dla_ss*` (162 lines) |
| dl-c (`ElGamal.lean`) | `sampleBelowL_eq_rejectBlocksL` (**foreign**: published beside `sampleBelowL` in `DiscreteLog.lean`), `length_sizeStr` | `dlc_numPoly_sample` (it becomes `⟨fun z => (g z).tail, …⟩`) | `dlc_ss*`, `dlc_ssLoop*` (155 lines) |
| rsa (`RSA.lean`) | `sampleUnitL_eq` (383, own), `unitSampleStr_eq` (536, own), `sampleUnitL_spec` | `rsa_ptc_unitSampleStr`; the test `rsa_usAcc`/`rsa_usGcd`/`rsa_usAcc_poly`/`rsa_unitTest_eq` restated on `⟨w, b⟩` (rsa-specific, kept private) | the loop: `rsa_usStart`, `_usStep`, `_usBlock`, `_usOut`, `_usLoop`, the `_poly`/`_iterate`/length lemmas, `rsa_usFind_eq`, `rsa_usStart_poly` (162 lines) |
| rabin (`Rabin.lean`) | `rejectBlocksL` through the host only; `samplePrimePL` (477, own file); `rabin_oddAcc_spec`/`rabin_blumAcc_spec` as `hspec` (test `acc0 ∘ pairSndD`); its unit sampler through rsa's public `polyTimeComputable_unitSampleStr` (unchanged) | `rabin_spOut_eq`, `rabin_spOut_poly` (the padding uses the length clause) | the `rabin_rb*` loop and `rabin_rbFind_eq` (136 lines) |

`Primality.lean`'s private `spStep` host, the origin of all four copies, **cannot** cite the host:
`Concrete` imports `Arithmetic`, which imports `Primality`. See Q3 for the two-layer alternative.

## 5. PR plan

### 5.1 Order

1. **S1, the shared-lemma PR**, on `cryptography/pass-shelat-ch2-4`. It needs neither #195 nor
   gate 04, and its files are disjoint from #195's. It applies rsa's E4, as the rsa review planned
   for the case where rsa lands before H1.
2. **The S2 contract gate**, then **S2**, the host PR. S2 depends on S1 for `rejectBlocksL_eq_find?`,
   `find?_range_and_lt`, `natToList_zero_append_drop` and `PolyTimeComputable.comp'`/`.congr`.
3. **#195** is re-merged after each of S1 and S2. There are no textual conflicts: the downstream
   replay of its 25 files is enough.
4. **Clean-up part 2**, after #195 and gate 04, with the additions in §5.4.

### 5.2 Estimated lines per file

These are estimates from the measured spans of the deleted declarations. "+" counts new lemmas with
their docstrings.

**S1**

| File | Removed | Added | Result |
|---|---|---|---|
| `Complexity/Randomized/Closure.lean` | 0 | +14 | 456 → ~470 |
| `Complexity/Randomized/Build/IterateFind.lean` | 0 | +28 | 531 → ~559 |
| `Cryptography/NumberTheory/Primality.lean` | 0 | +30 | 922 → ~952 |
| `Cryptography/Asymptotic/Sampling.lean` | 0 (the `abs_uexp_sub_le` proof changes in place) | +29 | 856 → ~885 |
| `Cryptography/Candidates/Arithmetic.lean` | 0 | +75 (tier 2: +25) | 385 → ~460 (~485) |
| `Cryptography/HardcoreBit/Basic.lean` | 0 | +26 | 266 → ~292 |
| `Cryptography/Candidates/Concrete.lean` | −19 (`dla_pushesUniform_restrict`) | +14 | 691 → ~686 |
| `Cryptography/Asymptotic/PublicKeyLemmas.lean` | −15, plus docstring lines 41 and 67 | 0 | 856 → ~841 |
| `Cryptography/Candidates/DiscreteLog.lean` | −90: G2/G3/G4 helpers (73), `dla_statClose_one` (11), `hk2` (6) | +4 | 1446 → ~1360 |
| `Cryptography/Candidates/ElGamal.lean` | −107: numerals (49), G2 (33), `polyTimeComputable_of_forall_eq` (6), `dlc_abs_uexp_sub_le` (11), casts (8) | +8 | 2391 → ~2292 |
| `Cryptography/Candidates/RSA.lean` | E4 −177; tier 2: `rsa_getD_spec`/`_one_mod_spec` −19 and `rsa_le_poly`/`_prime_poly`/`_val_inv_zero_le` −25 | E4 +64; tier 2: `sampleUnitL_getD_spec` +13 | 2762 → ~2649 (~2618) |
| `Cryptography/Candidates/Rabin.lean` | −85: the G2/G3/G4/G6/G8 helpers; tier 2: `rabin_getD_spec`/`_one_mod_spec`/`_le_poly`/`_prime_poly`/`_val_inv_zero_le` −33 | +6 | 3813 → ~3734 (~3701) |
| `Cryptography/Candidates/Factoring.lean` | −22: `fac_natToList_mod`, `fac_foldl_replicate_false`, `fac_arrowCongr`/`_ofFn`, `hone` | +4 | 1851 → ~1833 |
| `Cryptography/Candidates/DiscreteLogHardcore.lean` | −29: `dlb_ptc` (46 uses renamed), `dlb_foldl_bits`, `dlb_listToNat_cons`, `dlb_two_pow_size_le` | +2 | 3091 → ~3064 |
| `Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas.lean` | −23 (Q6) | +2 | 328 → ~307 |

Net S1: about −260 lines (−300 with tier 2). The replay covers 98 modules (those downstream of the
15 changed files). The homes stay under 1000 lines (`Primality` ~952; `Concrete` ~876 after S2).
The files above 1000 (`DiscreteLog`, `ElGamal`, `DiscreteLogHardcore`, `Factoring`, `RSA`,
`Rabin`) are fill-owned files under the standing size rule, and S1 and S2 only shrink them.

**S2**

| File | Removed | Added | Result |
|---|---|---|---|
| `Candidates/Concrete.lean` | 0 | +190: the host with its docstring (~35), the private loop (~120), the proof (~35) | ~686 → ~876 |
| `Candidates/DiscreteLog.lean` | −162 | +12 | ~1360 → ~1210 |
| `Candidates/ElGamal.lean` | −155 | +5 | ~2292 → ~2142 |
| `Candidates/RSA.lean` | −162 | −13 net on the restated test and `rsa_ptc_unitSampleStr` | ~2649 → ~2474 |
| `Candidates/Rabin.lean` | −136 | −4 net on `rabin_spOut*` | ~3734 → ~3594 |

Net S2: about −425 lines. The replay covers 8 modules. S2 also carries docstring-only sketch
refreshes of six public declarations that name the private loop (Q7):
- `polyTimeComputable_expSampleRaw` (DiscreteLog 931);
- `polyTimeComputable_egGenRaw` (ElGamal 1109);
- `polyTimeComputable_egEncRaw` (ElGamal 1236);
- `polyTimeComputable_unitSampleStr` (RSA 1444);
- `polyTimeComputable_oddGenRaw` (Rabin 1099);
- `polyTimeComputable_blumGenRaw` (Rabin 1125).

### 5.3 Gates and checks per PR (the user decides the gate: Q1)

**S1**
- **Statement surface.** `decls2.py` against the base must show only:
  - **ADDED** (18 in tier 1, up to 4 in tier 2);
  - **REMOVED**: `ColZK.pushesUniform_restrict` (or kept as an alias, Q6), and the `PublicKeyLemmas`
    copy of `abs_uexp_sub_le`, whose name survives in `Sampling`;
  - visibility changes: `foldl_bits_eq` and `abs_uexp_sub_le`.

  It changes no target statement and adds no definition, so there is no equation-lemma obligation
  and no check-8 change. The statement audit covers the new statements (a gate round, or the
  clean-up audit: Q1).
- **Gated packs affected.** S1 adds public lemmas to files of packs 03a (`Closure`, `Sampling`),
  03l (`IterateFind`) and others. The re-staged 03d/03h–03k packs will see them, and whichever
  audit Q1 chooses covers them.
- **Checks** (as clean-up part 1):
  - replay with `downstream2.py`; `sorry` counts equal to the base's;
  - full axiom prints of the changed files;
  - a seal of every touched file, with names collected from the elaborated terms plus matchers,
    and controls;
  - the explicit-unfold scan;
  - `style_lint.py` and `campaign_style_lint.py --check8b`;
  - E4 re-checked against the real lemmas with rsa's 50-name seal.

**S2**
- **The host contract** is statement-gated before the PR merges (policy §1). The gate checks:
  - the statement of §4.1;
  - its docstring and its `[PS10, …]` tag;
  - the existential design;
  - the registry row H15.

  The proof is a harvest of rabin's `rabin_rb*` and `rabin_rbFind_eq`, generalized by the header
  word (Q4).
- **Checks** as S1, plus:
  - the six sketch refreshes (docstring-only);
  - a seal control that `polyTimeComputable_iterateFind.match_1` stays sealed (dl-a review
    finding 3).

### 5.4 Clean-up part 2: what changes in its brief

- **Item A, DL-10.** S1 publishes `PolyTimeComputable.comp'`/`.congr` in `Closure.lean`. Clean-up
  part 2 then deletes `Closure`'s private `ptc_comp` and re-points its 27 uses, and re-points the
  other G6 base copies (G6 has the list). The base `ptc_congr`s take the reversed hypothesis, so
  they re-point with `fun w => (h w).symm`.
  - **Why not in S1.** `ptc_comp`'s eight users in `Closure` are `Computes.polyTimeComputable`,
    `exists_comp`, `exists_compParam`, `exists_reparam`, `exists_reparam_advice`, `exists_seq`,
    `exists_split` and `exists_withAdvice`. Item C rewrites exactly these declarations
    (`simp [runAtL, advInput, coinLen, …]`). Touching them in S1 would bring their reads into S1's
    seal.
- **Item A, DL-12.** Done by S1: drop it.
- **New item N: base-file re-points of this design's deferred groups.**
  - G7: `Language.lean`'s `h2`; `two_pow_permBits_le` as a corollary; one of the public pair
    `two_pow_size_le`/`two_pow_size_le_two_mul_succ` kept and the other re-pointed.
  - G10: the `castLE` triple as corollaries of `HardcoreBit.pushesUniform_restrict`
    (`Fin.castLE_injective`, `Mathlib/Data/Fin/SuccPred.lean` 86); `dlb_cut`;
    `pushesUniform_comp_injective` (after #195).
  - G13 with DL-9.
  - G14.
  - G22 with DL-11.
  - G23.
  - G25.
  - G12, optionally (after #195).
  - G18, if Q5 defers it.
- **Item M (DL-21).** `Candidates/*` rows of the Mathlib overlap. These files are now landed and
  edited by S1/S2. Item M runs after S2 so that the two do not edit the same proofs.

### 5.5 Rule-10 consequences (no proof reads another file's definition)

1. **Every new lemma is proved through published equations only.** Each one sits beside its
   definition or reads it through that definition's lemma:
   - `listToNat_eq`, `natToList_eq`/`natToList_length_listToNat`, `subStr_pairEncode`,
     `mulStr_pairEncode`, `leStr_pairEncode`, `primeStr_eq`, `rejectBlocksL_eq`, `statClose_iff`;
   - `uexp_def`, which replaces `Sampling`'s `unfold uexp` (the (b) row at `Sampling.lean` 207; the
     `PublicKeyLemmas` row at 845 goes with its deletion);
   - `pushesUniform_equiv`/`_fst`.

   Core definitions are read only through their lemmas (`Option.guard_apply`, not
   `simp [Option.guard]`; the latter is in rsa's stub and in `rabin_rbFind_eq`, which S2 deletes).
2. **A citation must not create a read.**
   - Re-pointing `dlc_castEquiv` to `finCastEquiv` would turn `dlc_splitEquiv_symm_ofFn`'s
     `subst h; exact ofFn_splitCoins_symm …` into a definitional read of `HardCoreLemmas`'
     definition. Mathlib's `Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)` may reduce there,
     so G11 cites Mathlib.
   - In general, a deleted private definition that was read by `rfl`/`show` in its own file may be
     replaced only by a Mathlib/core term or a lemma, never by another file's definition.
3. **Statements only.**
   - dl-c reads `sampleBelowL` only through `sampleBelowL_eq_rejectBlocksL`.
   - rsa and rabin read their own samplers. rabin reads rsa's unit sampler only through
     `polyTimeComputable_unitSampleStr`.
   - No consumer unfolds `rejectBlocksL` (foreign to every consumer).
   - The host's existential hides its machine, so no consumer can read it.
4. **Matchers.** The host's proof splits the repetition host's `match` by `split` (the dl-a E1
   pattern). The seal includes `polyTimeComputable_iterateFind.match_1`.
5. **"Touched" is computed against the PR base.** It covers every changed file. S1 touches only the
   new lemmas, the deleted copies, the re-pointed fill declarations (which were seal-clean at
   landing) and `Sampling`'s `abs_uexp_sub_le` (fixed). It deliberately avoids `Closure`'s
   `ptc_comp` users (§5.4).

## 6. Questions for the user (recommended option first)

**Q1. How are S1's new public statements audited?**
- **(A) Recommended.** One statement-gate round, `08-shared`, covers S1's 18–22 new statements and
  2 visibility changes (proved) and S2's host contract (§4.1, before its proof). It is staged before either PR merges.
  S1 can be opened in parallel, and stays "Not yet clear to merge" until the round closes. S2
  needs a gate anyway, so S1 adds little to it.
- (B) S1 merges after the maintainer's review. Its statements ride in clean-up part 2's statement
  diff and gate; only S2's host gets a round now.
- (C) Two separate rounds: S1 now, S2's contract later.

**Q2. Fold the work into clean-up part 2?**
- **(A) Recommended.** No. S1 and S2 go first, as their own PRs; they need neither #195 nor
  gate 04. The clean-up part 2 brief is updated as in §5.4: DL-12 dropped, DL-10 reduced to the
  re-points, and new item N.
- (B) Fold S1 into clean-up part 2. That is one PR, but it waits for #195 and gate 04, and so do
  rsa's E4 and the fill re-points.
- (C) Fold clean-up part 2's item A (DL-9 to DL-15) into S1. S1 grows and changes the statements of
  packs 03h/03i/03k, which must then be re-staged first.

**Q3. Where does the host live?**
- **(A) Recommended.** In `Candidates/Concrete.lean` only: one public lemma (§4.1) with a private
  loop. It retires the four copies.
- (B) Two layers. A generic `Complexity.polyTimeComputable_blockSearch` goes in
  `Randomized/Repetition.lean` (a `find?` over fixed-width blocks, with no `rejectBlocksL`). The
  Concrete lemma becomes its corollary. Then `Primality.lean`'s private `spStep` host, the origin
  of the copies, can be retired too; `Primality` cannot import `Concrete` (§2). The cost is a
  second gated statement and a re-proof of `exists_samplePrime_nuppt`.

**Q4. Who writes S2's proof?**
- **(A) Recommended.** The maintainer, as a harvest after the contract gate. The proof exists: it is
  rabin's `rabin_rb*`/`rabin_rbFind_eq` generalized by a header word, plus dl-a's `split` step.
- (B) An external fill, with a brief, dispatched by the user.

**Q5. Tier-2 publications.**
- **(A) Recommended.** Include the verbatim or same-statement cross-unit copies in S1:
  `sampleUnitL_getD_spec`, `ArithmeticFP.le_poly`, `ArithmeticFP.prime_poly` and
  `val_inv_natCast_zmod_zero_le`. Defer `uexp_le_of_statClose` (one consumer) to clean-up part 2.
- (B) Tier 1 only in S1; all tier 2 to clean-up part 2.
- (C) All tier 2, including `uexp_le_of_statClose`, in S1.

**Q6. `ColZK.pushesUniform_restrict`** (public, landed with col-b; a copy of the new
`HardcoreBit.pushesUniform_restrict`)
- **(A) Recommended.** Delete it, re-point its two uses (ColZKLemmas 122 and 164) and update the
  module docstring. The statement diff shows it as REMOVED.
- (B) Keep it as a one-line alias.

**Q7. Proof sketches that name the deleted loops** (six public docstrings, §5.2)
- **(A) Recommended.** Docstring-only refresh in S2, under the standing sketch-refresh ruling.
  Statements are unchanged.
- (B) Leave them, and record "sketch refresh owed" for the next docstring window.

**Q8. Numeral constants (G5) and numeral calculi (G24)**
- **(A) Recommended.** Leave them private, and record them in the ledger as accepted. They are
  instances of published equations and fill-specific bundle readings, not copied proofs.
- (B) Publish a numeral calculus (dl-c's `dlc_NumPoly`, or dl-b's fixed-width layer) in
  `Arithmetic.lean` in clean-up part 2. Which one is a design choice to rule on then.

**Not yet clear to merge — design draft only; no PR exists; rulings Q1–Q8 pending.**
