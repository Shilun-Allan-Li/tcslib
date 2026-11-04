# External audit pack: the configuration codec's edge mode (PR #184, an API gate)

**Why this PR.** The general `savitch` (route (A), iterative deepening on the radius, ruled by the
user on 2026-10-27) runs the proved Savitch search once per radius `s`. One run asks whether some
reachable configuration has a work head on the window's boundary. If none does, the window is
exact and the accepting run decides. That check needs a logspace decider for the **edge codes**:
codes at radius `s` of window-bounded configurations with some work head at `±s`. The design note
is `campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md`. Its §7 records the pre-ship
decision, taken by the rule the user set on 2026-11-04: the decider is a fifth mode `edge` of the codec
machine `Complexity.Codec.CA`, because a separate decider would rebuild the codec's parse and
validity scan.

The files are Hydroxyi's `Codec` files. The edit is additive, under the 2026-10-27 authorization to
add the edge language beside the codec's deciders for the general `savitch` (FYI only, the user's
to send). The writer was ruled by the user: a maintainer API PR. #182 (gate 90) supplies the block
embedding the deepening machine will use; the deepening fill itself comes after both PRs.

**The PR:** #184 on `lean/codec-edge`, head `8d43e126345a9e94998b1b11f0eee315518ae73f`. It is stacked on #182's
head `940932752e598b4a452311465dee81adea46d17b` (gate 90 PASS) and holds three commits
(`evidence/patches/`): `d5881f9d` (the language, the check, the mode and its proof), `f3c43d92` (the
shape and the oracle read through stated lemmas, for rule 10) and `8d43e126` (`mem_edgeLang`). Against
`94093275` it changes seven files in `SpaceComplexity/Codec`: +646 −20 lines. Of the 20 removed lines:
- 16 are module-docstring lines rewritten to name the edge members ("the four code languages",
  the main-results lists, `Machine`'s description of the modes);
- 3 are `Machine` constructor and match lines extended in place;
- 1 is a one-line match reflowed (`freeze/Machine-extension.txt`). It will be retargeted to the campaign branch once #182 merges.

## What changed (verify)

| File | Added |
|---|---|
| `Word` | `W_eq` (`W N = hH N + 3 * N.k + 1`, by `rfl`), `cellOf_head` (a cell's head flag for tape `i` is `decide (C.workTapePos i = j - s)`, by `rfl`) |
| `Langs` | `edgeLang N`; `mem_edgeLang_iff` (its unfolding, `Iff.rfl`); `mem_edgeLang` (membership at `⟨x, ⟨bits c, bits s⟩⟩`, as its siblings); docstring entries |
| `Checks` | `EdgeChk N x s w`: `ValidChk |x| s w` and some tape `i` whose head flag is set in chunk `0` (offset `hH + 3i + 2`) or chunk `2s` (offset `W·2s + hH + 3i + 2`); `edgeChk_def`; `getD_cfgWord_head`; `edgeChk_iff` (the check recognizes exactly the codes of window-bounded configurations with a head at `±s`); `edgeLang_iff` (membership of `⟨x, ⟨w, bits s⟩⟩` is the check) |
| `Machine` | the mode `CMode.edge`; sites `CpId.Ue`/`Qe`/`Te`, `IcId.Eh`/`Ke`/`S1`/`S2`, `ScId.Ee`; labels `Lab.eStart`/`eK`/`eRd1`/`eFar`/`eRd2`/`eNext`/`eTest`; the table rows (below); after the validity scan, mode `edge` goes to `eStart` if `VAcc` holds, else to `rej`; `section EdgeTable`, 37 published equations for `CA`'s new rows, `goto` and the new sites |
| `Run` | `orc_eq` (the oracle, by `rfl`) |
| `Parse` | `Shape1.eq`, `Shape1.width` (the parsed shape's two conjuncts, as lemmas) |
| `Deciders` | `edge_round` (one tape: a set flag halts with `true`; otherwise the loop reaches `eTest` with the counter one lower), `edge_loop` (induction over tapes), `edge_tail` (from `vDone` the machine answers `decide (VAcc ∧ ∃ i, flag at chunk 0 ∨ flag at chunk 2s)`), `edgeLang_mem : edgeLang N ∈ LOGSPACE`; privates `upd_le`, `EdgeOK`, `edge_gd` |

The table (`Machine`, `section EdgeTable` states each row):

```
| .eStart => if N.k = 0 then .ret false else .clr rU (.cp .Ue)   -- U := A, then U += 2(hH + 2)
| .eK     => .clr rQ3 (icL N .Ke 0)                               -- Q3 := k
| .eRd1   => .call jBit .whole [rU] .acc .eFar                    -- the bit at U
| .eFar   => .clr rQ1 (.cp .Qe)                                   -- Q1 := U + 4W·s
| .eRd2   => .call jBit .whole [rQ1] .acc .eNext                  -- the bit at Q1
| .eNext  => .dec rQ3 .eTest
| .eTest  => .jz rQ3 .rej (icL N .S1 0)                           -- U += 6, next tape
```

A word bit `p` sits at virtual-input position `A + 2p`, so the offsets are doubled. The first tape's
flag `hH + 2` is at `A + 2(hH + 2)`, tapes are 6 apart (`2 · 3`), and chunk `2s` is `4W·s` further on
(`2 · 2s · W`).

**Freeze** (`evidence/freeze/`, `94093275` against `8d43e126`). Public declarations:
- `Word` 46 → 48, `Langs` 9 → 12, `Checks` 26 → 31, `Machine` 46 → 83, `Run` 25 → 26,
  `Parse` 16 → 18, `Deciders` 16 → 20; private 0 → 3 in `Deciders` only;
- nothing removed;
- the 15 changed statements are `Machine`'s inductives and site maps (`CMode`, `CpId`, `IcId`, `ScId`,
  `Lab`, `CA`, `cpDst`, `cpNext`, `cpSrc`, `icCount`, `icNext`, `icReg`, `scDst`, `scFactor`,
  `scNext`), each extended by constructors or match arms only (`Machine-extension.txt`).

**Census** (`evidence/census/`, `census-diff.txt`): Word 88 → 90, Langs 9 → 12, Checks 61 → 72,
Machine 955 → 1149, Run 46 → 47, Parse 217 → 138, Deciders 48 → 87. Parse's drop is CA's 87
equation lemmas (`CA.eq_N`). Lean creates them in the first module that needs them, which is now
Machine (its table equations), not Parse.

## Brief for the auditor

1. **The statement.** `edgeLang_mem : edgeLang N ∈ LOGSPACE`. Is `edgeLang` the language the
   deepening needs (design §3: no reachable edge code at radius `s` means the window is exact)? Check
   the boundary cases:
   - `N.k = 0`: no tape, so `edgeLang` is empty, and the machine answers `false` at `eStart`
     (`CA_eStart_of_zero`);
   - `s = 0`: every head in the window is at `0 = ±s`;
   - heads at `−s` versus `+s`;
   - malformed inputs: the validity scan rejects them.
2. **The check against the code layout.** Do chunk `0` and chunk `2s` hold cells `−s` and `+s`? Is
   tape `i`'s head flag at offset `hH + 3i + 2` (`cellOf_head`, `getD_cfgWord_head`, `edgeChk_iff`)?
   Does `edgeLang_iff` hold for every word `w`, not only for codes?
3. **The machine and its proof.** Are the new rows and sites right, including the doubled offsets
   and the per-tape count `icCount .Ke = N.k - 1 + 1`? Do `edge_round`, `edge_loop` and `edge_tail`
   prove what their names say, and stay within the bound `bnd N y` (`GuardLe`)? Does any existing
   mode's behaviour change? The only edited existing row is `vDone` in mode `edge`.
4. **Rule 10** (maintainer API proofs, `evidence/rule10/`). `scripts/mkseal_edge.py` writes three
   sealed copies; each elaborates with 0 diagnostics:
   - `LangsSealed`: `mem_edgeLang` under a seal of `pairEncode`, `Cfg.InWindow` and `cfgCode`;
   - `ChecksSealed`: the edge section under a seal of 8 definitions;
   - `DecidersSealed`: `section Edge` under a seal of 32 definitions, including `astep`, `arun`,
     `AHalt`, `PreS`, `CA` and its site maps, `orc`, `Shape1`, `EdgeChk` and `edgeLang`.

   All three also erase `Action.apply`, `Cfg.init` and `MultiTapeTM.initCfg` from `simp`. The union
   is 37 definitions (`union.txt`). Controls: unsealed, 73 of 74 pass (the recursive `vword`'s delta
   goal fails, and its equation control passes); sealed, all 74 fail. The proofs read other files'
   definitions only through published equations: the new `CA_*`/site equations, `orc_eq`,
   `Shape1.eq`/`width`, `W_eq`, `cellOf_head`, `edgeChk_def` and `mem_edgeLang_iff`, plus #182's
   step equations. Is anything else unfolded or closed by reduction?
5. **Duplication.** The screen (`evidence/screen/`) covers all 16 `Codec` files: 171 → 186
   declarations, 58 → 83 pairs, 25 new and none gone (`pairdiff.txt`). All 25 are the edge member
   of the code languages' families. `edgeLang`, `mem_edgeLang`, `edgeLang_iff` and `edgeLang_mem`
   reproduce their siblings, which already formed 31 pairs at the base. They are ledgered as
   **CL-1** (`campaign/duplication-ledger.md`), accepted by the user (2026-11-04) for the dedup
   window. Are the counts and the ledger's description right? Does anything else copy existing
   material?
6. **Names** (`evidence/api-search/`, every origin ref). No ref other than this PR's branch declares
   the new names. `namesakes.txt` lists four same-named declarations in other namespaces, with other
   statements (`BoolCircuit.….edgeLang`, `mem_edgeLang`, two `orc_eq`). It shows that the one file
   opening both `Codec` and one of their parent namespaces uses none of them. Should any be renamed?
7. **Lint** (`evidence/lint/`). `campaign_style_lint` over `SpaceComplexity` gives 0 FAIL and 83 WARN
   at both base and head. The check-8 list changes as follows:
   - `Langs` gains `edgeLang`; its lemmas are named as the siblings', `mem_edgeLang`;
   - `Machine` falls from 27 to 17, since the table equations sit beside `CA`, `goto` and the site
     maps;
   - `Word` loses `W`.

   `style_lint` gives 0 findings on all seven files, at base and head.

## Repository-side attestations (verify or challenge)

- **Elaboration chain** (`evidence/elab-chain/`, `scripts/elab_chain.sh`). All 16 `Codec` modules
  were compiled in dependency order with `lean -o` into a copy-on-write clone of #182's compiled
  head. Each gives 0 diagnostics (`chain.log`; `Machine` takes 71 s). The census, the sealed copies
  and the controls ran against the same clone.
- **Axioms** (`evidence/census/NewAx-head.out`, 16 theorems). 14 depend on
  `[propext, Classical.choice, Quot.sound]`; `cellOf_head` and `Shape1.eq` depend on
  `[propext, Quot.sound]`.
- **Replay: not yet written.** This PR's base is #182's branch. #181 merges first, then #182 with its
  merged-tree replay (as ruled). Then this PR is retargeted, merged with the campaign, and given a
  merged-tree replay of its downstream closure from #182's post-merge snapshot.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/91-codec-edge-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `codec-edge-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
