# Sub-agent A — cleanup-stage1 notes

Worktree `/home/user/s1/wt-a` (check tree `01cc6259…`, detached at `2081fe574`). Files changed (pure
insertions only) and one new file:

| File | Targets |
|---|---|
| `TCSlib/Cryptography/Foundations/BitLists.lean` | S1-06, S1-07 (4 decls), S1-15 |
| `TCSlib/Cryptography/Asymptotic/Adversary.lean` | S1-09 |
| `TCSlib/Cryptography/Asymptotic/Sampling.lean` | S1-22 |
| `TCSlib/Cryptography/Authentication/Encoding.lean` | S1-11 (2 decls) |
| `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean` | S1-18, S1-19, S1-20, S1-26 |
| `TCSlib/Cryptography/ZeroKnowledge/InteractionWords.lean` (new) | S1-21 |
| `TCSlib/Cryptography/ZeroKnowledge.lean` (facade) | import after line 7, `## Contents` entry after line 41 |
| `TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean` | S1-27 (10 decls) |

25 declarations in all. Statements are the brief's text verbatim (two statements are broken over two
lines for the 100-character limit: `length_recordBits`, `EncodingMachines.length_padTo`; no token
changes). No `@[simp]`, no `sorry`, no new import in an existing non-facade file.

## Per target

### S1-06 `TCSlib.Cryptography.zipWith_xor_cancel_right` (BitLists, after `zipWith_xor_cancel_left`)
- Readers: core `List.zipWith_cons_cons`, `List.length_cons`, `List.length_nil`; Bool cases; core
  `List.zipWith` reduces only in the `[]` case's `rfl`. Tag: glue.
- Proof source: `Encryption/PrivateKey/EncryptThenTag/Lazy.lean:295` (`ETTGame.zipWith_xor_cancel`),
  restated by structural recursion with `rw` instead of `simp`.
- Reuse: TCSlib grep `zipWith xor (List.zipWith xor`, `zipWith_xor_cancel`, `zipWith_xor_xor` — hits are
  exactly the five listed copies plus the other orientation `zipWith_xor_cancel_left` (equal lengths,
  `(a ⊕ c) ⊕ a = c`, not this statement). Mathlib/core: `List.zipWith_zipWith_left/right` (generic
  reassociation, not a cancellation); no `zipWith xor` lemma. No E-DUP.
- Copy list confirmed (path:line at the check tree): `Encryption/PrivateKey/FromPRF.lean:174`,
  `Encryption/PrivateKey/FromPRG.lean:147`, `SecureComputation/SpecialEncryption.lean:101`,
  `Encryption/PrivateKey/EncryptThenTag.lean:338`, `Encryption/PrivateKey/EncryptThenTag/Lazy.lean:295`.
  No further copies found.

### S1-07 `TCSlib.Cryptography.recordBits`, `recordBits_none`, `recordBits_some`, `length_recordBits`
(BitLists, new section "Records of an optional bit vector" at the end of the file)
- Readers: the definition lands with `recordBits_none`, `recordBits_some` (`rfl`, one per
  constructor) and `length_recordBits` (cases, through the two case lemmas, `List.length_cons`,
  `List.length_replicate`, `List.length_ofFn`). Tag: glue.
- Proof source: `Encryption/PrivateKey/EncryptThenTag/Handler.lean:134–147`.
- Reuse: TCSlib grep `recordBits`, `false :: List.replicate`, `true :: List.ofFn` — hits are the two
  `recBits` families and, as a near relative only, the inline
  `(firstQ c).elim (false :: List.replicate (Lq.eval n) false) (true :: ·)` of
  `Encryption/PublicKey/BitwiseCPA/QueryHandler.lean:266`, `:345` and `Encryption/PublicKey/BitwiseCPA.lean:270`
  (an optional *word*, not an optional `Fin w → Bool`; not an instance). Mathlib/core: nothing.
- Copy list confirmed: `Encryption/PrivateKey/EncryptThenTag/Handler.lean:134`, `:139`, `:143`, `:147`;
  `Encryption/PrivateKey/OracleFromPRF/Handler.lean:109`, `:114`, `:117`, `:121`.

### S1-15 `TCSlib.Cryptography.getD_ofFn` (BitLists, after `headD_drop_ofFn`)
- Readers: `headD_drop`, `headD_drop_ofFn` (the brief's proof verbatim). Tag: glue.
- Reuse: no `List.getD_ofFn` in core, Batteries or Mathlib at this pin (grep). TCSlib hits: the listed
  copies (`getD_ofFn_lt'`, `getD_ofFn_lt` ×2, `ofFn_getD_lt`, `getD_ofFn'`, …).
- Copy list confirmed (every cited line read at the check tree, `copylist-check.txt`).
  **Further copy:** `SecureComputation/Yao/HybridProof/RowFromCoins.lean:416` (inline
  `List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h, Option.getD_some` chain, in
  `assignmentBit_of_perm`, `:408`). Near relative, not an instance: `Yao/HybridProof/BobIO.lean:164`
  (`outputWord_getD`, both branches of the `if`).

### S1-09 `TCSlib.Cryptography.FunFamily.ofFn_blocks_symm_eq_flatMap` (Adversary, after `FunFamily.ofFn_blocks`)
- Readers: `FunFamily.blocks_symm_apply` (own file), Mathlib `List.ofFn_mul`, `Fin.coe_divNat`,
  `Fin.coe_modNat`, core `List.flatMap_def`, `List.map_coe_finRange`, `List.ofFn_eq_map`, Nat
  arithmetic. Tag: glue (block encoding cited at `FunFamily.blocks`). Proof sketch included.
- Proof source: `Asymptotic/EnsemblesLemmas.lean:433` (statement) with the `divNat`/`modNat` arithmetic
  of `Asymptotic/OneWay.lean:380` (since `FunFamily.blocks_symm_apply` reads `divNat`/`modNat`, not the
  alias' `finProdFinEquiv.symm`).
- Reuse: grep `ofFn_blocks_symm`, `ofFn ((… blocks …).symm`. Hits: the copy
  `EnsembleLemmas.ofFn_blocks_symm` (`EnsemblesLemmas.lean:433`, through the alias) and the flatten form
  `FunFamily.ofFn_blocks_symm` (`OneWay.lean:380`, downstream, different conclusion);
  `HardCoreLoops.blocksStr` (`:84`, other bijection). No E-DUP.
- Copy list confirmed: `Asymptotic/EnsemblesLemmas.lean:433`.

### S1-22 `TCSlib.Cryptography.StatClose.of_uprob_ne` (Sampling, section StatClose after `StatClose.mono`)
- Readers: `statClose_iff`, `uprob_mono`, `uprob_or_le`, `OneWay.uprob_congr` (all in the closure).
  Tag: glue (PS10 Theorems 107.3 / 163.7 named as uses). Proof sketch included.
- Proof source: `Candidates/DDH.lean:145` (verbatim tactic script).
- Reuse: grep `of_uprob_ne`, `statClose_of_eq_off`, `StatClose X Y (uprob`, `coupling`,
  `abs_uprob_sub_le…`: only the listed copies. No E-DUP.
- Copy list confirmed: `Candidates/DDH.lean:145`; users `Encryption/PublicKey/ElGamal.lean:1154`;
  `SecureComputation/Yao/HybridProof/StatisticalSwitch.lean:46`, `:68`.
- Size: `Asymptotic/Sampling.lean` 936 → 965 lines (≤ 1000).

### S1-11 `TCSlib.Cryptography.Authentication.ofFn_splitBits_fst`, `…_snd` (P; Authentication/Encoding, after the `simps` attribute)
- Readers: `splitBits_fst`, `splitBits_snd` (own simps projections), core `List.ofFn_add`,
  `List.take_left'`, `List.drop_left'`, `List.length_ofFn`. Tag: glue.
- Proof source: `Hashing/FromDiscreteLog/Encoding.lean:45`, `:55`, re-done via `List.ofFn_add` as the brief
  says (the copies go through `ofFn_drop_take`, not in this home's closure).
- Reuse: grep `ofFn_splitBits`, `ofFn (splitBits`. Copies confirmed:
  `Hashing/FromDiscreteLog/Encoding.lean:45`, `:55`; `Authentication/MAC/FromPRF/Reduction.lean:140`,
  `:145`, `:147`. **Further copies:** `Authentication/Signatures/Lamport/MachineSpec.lean:259` (inline
  `hs : List.ofFn (splitBits a).2 = (List.ofFn a).drop n`) and
  `Authentication/Signatures/HashAndSign/CollisionHandler.lean:464` (inline
  `hp : (List.ofFn a).take (H.domLen.eval n) = List.ofFn (splitBits a).1`).

### S1-18 `Strategy.encodeMsgs_eq`, S1-19 `Strategy.encodeMsgs_eq_flatMap` (P), S1-20 `Strategy.iterate_pairSndD_encodeMsgs` (P), S1-26 `Strategy.msgAt_encodeMsgs` (P) (Interaction, after `pairFstD_encodeMsgs`)
- Readers: S1-18 `rfl` (own definition, its missing equation lemma). S1-19 `encodeMsgs_nil`,
  `encodeMsgs_cons`, `Turing.pairEncode_eq`, `List.flatMap_nil/cons`, `List.append_nil`. S1-20
  `encodeMsgs_nil/cons`, `pairSndD_pairEncode`, `pairSndD_of_pairDecode_eq_none`,
  `Turing.pairDecode_nil`, core iterate/drop lemmas. S1-26 `Strategy.iterate_pairSndD_encodeMsgs`,
  `pairFstD_encodeMsgs`, `List.headD_eq_head?_getD`, `List.head?_drop`, `List.getD_eq_getElem?_getD`.
  Tags: glue.
- Proof sources: S1-19 `ZeroKnowledge/ThreeColoring/Machines.lean:912` (with `pairEncode_eq` in place of
  its local `pairEncode_eq_append_nil`); S1-20 `ZeroKnowledge/ThreeColoring/Machines.lean:919`;
  S1-26 `SecureComputation/ComposeSecurity/Machines.lean:137` (verbatim rewrite chain).
- Reuse: grep for each name and conclusion shape; hits are exactly the listed copies (see
  `reuse-grep-1.txt`). `CommitmentLemmas.encodeMsgs_append` is a relative (append form), not a copy.
- Copy list confirmed: S1-18/19 `Randomness/Learning/Sample.lean:58`,
  `SecureComputation/ComposeSecurity/Machines.lean:150`, `ZeroKnowledge/ThreeColoring/Machines.lean:912`,
  `ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean:503`; S1-20 `ZeroKnowledge/ThreeColoring/Machines.lean:919`,
  `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean:101`; S1-26
  `SecureComputation/ComposeSecurity/Machines.lean:137`, `ZeroKnowledge/ThreeColoring/Protocol.lean:112`.

### S1-21 `Strategy.encodeMsgs_eq_encWords` (P; new `ZeroKnowledge/InteractionWords.lean`)
- Readers: `Strategy.encodeMsgs_eq_flatMap`, `Complexity.BinArith.encWords_def`. Tag: glue.
- Module: copyright block, imports exactly `TCSlib.Cryptography.ZeroKnowledge.Interaction` and
  `TCSlib.Complexity.ClassP.BinaryArith.Words`, the three options, docstring with
  `# The history encoding as a word list`, `## Main results`, `## References` ([PS10] line verbatim +
  "§4.4").
- Copy list confirmed: `SecureComputation/Yao/HybridProof/Lengths.lean:83`,
  `Composability/SequentialZK/Normalization.lean:40`.
- Facade: `ZeroKnowledge.lean` gets the import after line 7 and, after line 41, the entry
  ``* `InteractionWords` — the history encoding as a word list (`BinArith.encWords`).`` — the brief's
  text with the facade's backtick convention (the brief writes it inside a code span, where nested
  backticks are impossible). If the lead wants the literal un-backticked text, it is a one-line swap.

### S1-27 (EncodingMachines, new section before `end TCSlib.Cryptography.EncodingMachines`; all P)
`flatMap_range_ite`, `polyTimeComputable_flatMap_range`, `iterSnd_poly`, `zeros_poly`, `padTo` (def),
`padTo_eq`, `padTo_poly`, `length_padTo`, `getD_padTo`, `padTo_of_length`.
- Readers: own toolkit (`cstep_poly`, `cstep_iterate`, `cstep_horbit`, `cbound`, `ltTest_poly`,
  `unaryLength_poly`, `truncate_poly`, `loopState_zero/succ`, `polyTimeComputable_loopState`,
  `polyTimeComputable_of_getD`), `polyTimeComputable_iterateEmit`, `PolyTimeComputable.output_length_le`,
  `polyTimeComputable_ite`, `polyTimeComputable_const`, `polyTimeComputable_id`,
  `PolyTimeComputable.pairEncode/append/comp'/congr`, `pairFstD_pairEncode`, `pairSndD_pairEncode`,
  `length_pairEncode`, `length_pair_components_le`, `PolyExpr.eval_normal`, `PolyExpr.eval_mono`.
  `padTo` lands with `padTo_eq` (`rfl`); every other `padTo` proof goes through `padTo_eq`.
  Composition always in applied form (`comp'`), so no `Function.comp` unification.
- Proof sources: `flatMap_range_ite`, `polyTimeComputable_flatMap_range`: `ComposeSecurity/Machines.lean:61`,
  `:81`; `zeros_poly`, `getD_padTo`: `ThreeColoring/Machines.lean:292`, `:316`; `padTo_poly`,
  `length_padTo`, `padTo_eq`: `ComposeSecurity/Machines.lean:232`, `:239`, `:226`; `padTo_of_length`:
  `ComposeSecurity/Assembly.lean:98`.
  **`iterSnd_poly` re-proved through `polyTimeComputable_loopState`** (as required): that lemma needs a
  self-bound `|upd ⟨x, t⟩| ≤ B|x|` for *every* `t`, which the copies' update `t ↦ pairSndD t` does not
  satisfy, so the update is the second projection truncated to `|s x|` bits
  (`truncate_poly`, `unaryLength_poly`); along the loop the truncation is the identity because
  peeling never lengthens a word (`length_pair_components_le`). Proof sketch in the docstring.
- Reuse: name hits are the listed copies plus unrelated same-named items (private
  `Complexity…QuasiPolyHierarchy.flatMap_range_ite`, `:190`, other statement;
  `GI.zeros_poly`/`GIZK.zeros_poly`, `0^{|w|}`). Findings (not added elsewhere, reported for the lead):
  1. `Complexity.FormulaKit.polyTimeComputable_flatMap_range` (`TCSlib/Complexity/FormulaKit/Emit.lean:127`)
     is the same statement with the pair order swapped (instance in `pairFstD`, counter in `pairSndD`),
     and is **`sorry`** at the base (design §14 row H6). Not an E-DUP (admitted, other layout, not in
     the home's closure), but it is the obvious place a future Complexity fill could cite ours.
  2. `zeros_poly` has equi-general public forms outside the home's closure:
     `Games.EffFill.zeros_poly` (`Games/Efficiency/Strings.lean:152`, `z ↦ 0^{|f z|}`) and
     `EnsembleLemmas.polyTimeComputable_zeros` (`Asymptotic/EnsemblesLemmas.lean:212`,
     `z ↦ 0^{p(|u z|)}`); each is inter-derivable with ours by one length rewrite. Neither is imported
     by `EncodingMachines` (both are downstream of `Complexity.Randomized`, EnsemblesLemmas imports
     Adversary/Sampling), so it is not reachable at the home; kept as the brief says. (Question CS1-W-A2.)
  3. `padTo L w` equals Batteries' `List.takeD L w false` (Mathlib has `List.takeD_length`,
     `List.takeD_eq_take`, `List.takeD_left'`); different body (`takeD` is recursive). Kept as the brief
     defines it (the copies' body, so Stage 2 can re-point the two copies definitionally). (Question
     CS1-W-A3.)
- Copy list confirmed (every line read): `flatMap_range_ite` `ComposeSecurity/Machines.lean:61`,
  `ThreeColoring/Machines.lean:142`, `ThreeColoring/SimulatorMachine.lean:160`;
  `polyTimeComputable_flatMap_range` `ComposeSecurity/Machines.lean:81`, `ThreeColoring/Machines.lean:159`;
  `iterSnd_poly` `ComposeSecurity/Machines.lean:117`, `ThreeColoring/Machines.lean:190`; `zeros_poly`
  `ThreeColoring/Machines.lean:292`; `padTo` family `ComposeSecurity/Machines.lean:223`, `:226`, `:232`,
  `:239`, `ComposeSecurity/Assembly.lean:98`, `ThreeColoring/Machines.lean:303`, `:306`, `:312`, `:316`;
  re-derived `ofFn_padFin` `ComposeSecurity/Machines.lean:244`, `ThreeColoring/Machines.lean:327`.

## Name checks
`nameclash.txt`: every short name with a hit elsewhere in TCSlib/audits at the check base is declared
`protected` (S1-11, S1-19, S1-20, S1-26, S1-21, all of S1-27), matching the brief's `P` marks. The
unmarked ones (`zipWith_xor_cancel_right`, `recordBits`, `recordBits_none`, `recordBits_some`,
`length_recordBits`, `getD_ofFn`, `ofFn_blocks_symm_eq_flatMap`, `of_uprob_ne`, `encodeMsgs_eq`) have
no declaration of that short name anywhere in TCSlib/audits. No unmarked clash found.

## exact? probes
Not run (each probe needs the whole home closure under the single host lock, which was saturated by the
bootstrap); the reuse evidence is the grep searches above.

## Proof repairs during the fill
- S1-11 `ofFn_splitBits_fst`: core's `List.ofFn_add` states the first block with `Fin.castLE`, not
  `Fin.castAdd`; the remaining goal `ofFn (w ∘ castAdd b) = ofFn (w ∘ castLE _)` is closed by `rfl`
  (core `Fin.castAdd` reduces in a `rfl` step, allowed by Rule 10).
- S1-09: the `divNat`/`modNat` values are read with `simp only [Fin.coe_divNat]` /
  `simp only [Fin.coe_modNat]` (Mathlib lemmas, as in `OneWay.lean:380`), then `rw` arithmetic.
- S1-27: `getD_padTo`'s out-of-range step names `w[i]? = none` in a `have` (as the ThreeColoring copy);
  `iterSnd_poly` uses `List.length_take_le`.

## wtcheck runs (all with the prescribed command; raw logs in `logs/`, driver `runall.sh`)
| run | target | result |
|---|---|---|
| 1 | `TCSlib/Cryptography/Foundations/BitLists` | OK, rc 0, 0 errors, 0 sorry, no warnings |
| 2 | six targets (one invocation) | stopped by me while still waiting for the bootstrap (lead's note on 30-min background limits); no Lean run |
| 03 | `Asymptotic/Sampling` | OK, rc 0, 0 errors, 0 sorry |
| 03 | `Authentication/Encoding` | FAIL, 1 error (`Encoding.lean:44:56` unsolved goal, castAdd vs castLE) |
| 03 | `ZeroKnowledge/Interaction` | OK, rc 0, 0 errors, 0 sorry |
| 03 | `Asymptotic/Adversary` | OK, rc 0, 0 errors, 0 sorry |
| 03 | `ZeroKnowledge/InteractionWords` | OK, rc 0, 0 errors, 0 sorry |
| 03 | `ZeroKnowledge/EncodingMachines` | OK, rc 0, 0 errors, 0 sorry |
| 04 | `Authentication/Encoding` (after the `rfl` fix) | OK, rc 0, 0 errors, 0 sorry |
| 05 | `Probes/SealASampling`, `SealAInteraction`, `SealAInteractionWords`, `SealAEncodingMachines` | all OK, 0 errors |
| 06 | `Probes/SealACtl` (control) | rc 1, exactly 1 error, at the sealed negative (line 17) — as intended |

All logs are empty of warnings (no `sorry`, no linter output). Every home was checked after its last
edit (`final-sha256.txt` holds the final hashes). **Not checked by me:** the facade
`TCSlib/Cryptography/ZeroKnowledge.lean` (its closure is the whole ZK tree, downstream of the changed
`Interaction`/`Adversary`/`Sampling`/`BitLists`; that is the lead's sweep). Its change is one import and
one `## Contents` line; the new module's only full name `TCSlib.Cryptography.Strategy.encodeMsgs_eq_encWords`
exists nowhere else.

## Seal emulation (informal, not the canonical seals)
`probes/SealA*.lean` are copies of the four homes whose new declarations read foreign TCSlib
definitions, with one line `attribute [local irreducible] …` inserted after the options:
Sampling — `TCSlib.Cryptography.uprob`; Interaction — `Turing.pairEncode Turing.pairDecode
Complexity.pairFstD Complexity.pairSndD`; InteractionWords — `Turing.pairEncode
Complexity.BinArith.encWords TCSlib.Cryptography.Strategy.encodeMsgs`; EncodingMachines —
`Turing.pairEncode Turing.pairDecode Complexity.pairFstD Complexity.pairSndD
Complexity.PolyTimeComputable Complexity.PolyExpr.normal`. All four compile with 0 errors (whole file,
old and new declarations). Control `SealACtl.lean`: the sealed `rfl` reading of `pairEncode` fails
exactly once; the unsealed `rfl` and the sealed reader use (`EncodingMachines.padTo_eq`) pass.
BitLists, Adversary and Authentication/Encoding new declarations read no foreign TCSlib definition
(only their own `recordBits`, `FunFamily.blocks`, `splitBits` and core/Mathlib). The probes were
removed from the worktree after the runs (copies under `probes/`).

`rfl`/`simp` inventory of the new declarations: `rfl` only on own definitions (`encodeMsgs_eq`,
`recordBits_none/some`, `padTo_eq`) or core ones (`List.zipWith` on `[]`, `Option.getD` after
`split_ifs`, `Fin.castAdd` in S1-11); `simp` only in `flatMap_range_ite`'s zero case (no lemma
arguments), `simp only [Fin.coe_divNat]`/`[Fin.coe_modNat]`, and the copy's
`simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, decide_eq_true_eq]`.

## Questions / issues for the lead
- CS1-W-A1 (facade text): the `## Contents` entry is written with the facade's backticks
  (``* `InteractionWords` — … (`BinArith.encWords`).``) rather than the brief's literal code-span text.
- CS1-W-A2 (`zeros_poly`): equi-general public forms exist outside the home's closure
  (`Games.EffFill.zeros_poly`, `Games/Efficiency/Strings.lean:152`; `EnsembleLemmas.polyTimeComputable_zeros`,
  `Asymptotic/EnsemblesLemmas.lean:212`). Recommended: keep S1-27's `zeros_poly` (the only one reachable
  from `EncodingMachines`, needed by `padTo_poly`); Stage 2 may re-point `Games.EffFill.zeros_poly`
  to it if `Strings` ever imports `EncodingMachines` (it does not now).
- CS1-W-A3 (`padTo`): equals Batteries' `List.takeD L w false` extensionally. Recommended: keep the
  brief's body (identical to both copies, so Stage 2 can swap their bodies definitionally); record the
  relation for the ledger.
- FYI: `Complexity.FormulaKit.polyTimeComputable_flatMap_range` (`Complexity/FormulaKit/Emit.lean:127`) is
  the same statement with the pair order swapped and is `sorry` at the base.
- BitLists got two docstring bullets (one under `## Main definitions` for `recordBits`, one under
  `## Main results`), since it gains both a definition and theorems (brief: "bullets"); every other file
  got exactly one.
- Further copies for the Stage 2 table: S1-15 `SecureComputation/Yao/HybridProof/RowFromCoins.lean:416`
  (in `assignmentBit_of_perm`, `:408`); S1-11 `Authentication/Signatures/Lamport/MachineSpec.lean:259`,
  `Authentication/Signatures/HashAndSign/CollisionHandler.lean:464` (inline).
