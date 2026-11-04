## The configuration codec's edge mode

The general `savitch` deepens the radius `s` of the configuration-graph search until no reachable
configuration has a work head on the window's boundary. This PR adds the decider for that test:
**`Complexity.Codec.edgeLang_mem : edgeLang N ∈ LOGSPACE`**, for `edgeLang N`, the codes at radius
`s` of window-bounded configurations with some work head at `±s`.

It is a fifth mode `edge` of the codec machine `CA`. After the validity scan, a loop over the
tapes reads each tape's head flag in the first and the last cell of the code word.

| File | Added |
|---|---|
| `Codec/Word` | `W_eq`, `cellOf_head` |
| `Codec/Langs` | `edgeLang`, `mem_edgeLang_iff`, `mem_edgeLang` |
| `Codec/Checks` | `EdgeChk`, `edgeChk_def`, `getD_cfgWord_head`, `edgeChk_iff`, `edgeLang_iff` |
| `Codec/Machine` | `CMode.edge`, the new sites and labels, the table rows, and 37 published equations for them (`section EdgeTable`) |
| `Codec/Run`, `Codec/Parse` | `orc_eq`; `Shape1.eq`, `Shape1.width` |
| `Codec/Deciders` | `edge_round`, `edge_loop`, `edge_tail`, `edgeLang_mem` |

The changes are additive. Existing inductives and site maps gain constructors and match arms, and
no existing statement or mode changes. Seven files, +646 −20; the removals are docstring lines that
now name the edge members, plus three lines extended in place and one reflowed.

**Stacked on** `lean/arm-embed` (the block-embedding PR). It will be retargeted to
`complexity/arora-barak-ch3-4` once that merges, then replayed on the merged tree.

**Gate 91** (`campaign/gates/91-codec-edge-api/`):
- every `Codec` module elaborates with 0 diagnostics;
- the rule-10 seal holds (three sealed copies; 37 definitions, controls 73/74 unsealed and 0/74 sealed);
- freeze and census are in the gate folder;
- axioms are within `[propext, Classical.choice, Quot.sound]`;
- lint shows 0 FAIL, unchanged from base;
- the screen finds 25 new pairs, all the edge member of the code languages' families, ledgered as
  CL-1.

Design: `campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md`, §7.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
