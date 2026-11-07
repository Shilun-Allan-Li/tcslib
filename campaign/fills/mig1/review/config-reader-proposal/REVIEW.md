# Configuration field-reader proposal — bounded pre-ship checks

**Proposal only; no public API or campaign source change.** The ten left/right readers
are the subject of the root maintainer's pending user question. The five `captureCfg`
readers are an additional, unapproved proposal. This task neither executes the fill
delivery nor grants permission to change its scope.

The requested attributes elaborate in their respective **home import contexts**:

```lean
-- In TuringMachine/Simulation.lean, beside the existing definitions:
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  Turing.FinTM.leftCfg
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  Turing.FinTM.rightCfg

-- In TuringMachine/Build/Wrappers.lean, beside the existing definition:
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  Turing.captureCfg
```

The exact namespaces matter: `leftCfg` and `rightCfg` are under **`Turing.FinTM`**;
`captureCfg` is under **`Turing`**. Lean prohibits adding `[simps]` to an imported
declaration. Therefore the successful probes copy just the existing definitions
**verbatim** into their original home import contexts and preserve their fully
qualified names. They do not copy or elaborate the rest of either source module.
The three definition bodies were compared with the pinned snapshot source. The
initial unsuccessful imported-attribute diagnostic is retained separately.

## Exact 15 proposed names and formulas

For the first five rows, let `L = Turing.FinTM.leftCfg f c tapes heads`, with source
`c : Cfg k Bool S x` and inactive right bank of size `l`. For the next five,
`R = Turing.FinTM.rightCfg f c tapes heads`, with source of size `l` and inactive left
bank of size `k`. The displayed `i` is a tape index and `a : ℤ` a cell.

| Proposed public name | Exact field formula (with those aliases) |
|---|---|
| `Turing.FinTM.leftCfg_state` | `L.state = c.state.map f` |
| `Turing.FinTM.leftCfg_inputPos` | `L.inputPos = c.inputPos` |
| `Turing.FinTM.leftCfg_workTapes` | `L.workTapes i a = Fin.addCases c.workTapes tapes i a` |
| `Turing.FinTM.leftCfg_workTapePos` | `L.workTapePos i = Fin.addCases c.workTapePos heads i` |
| `Turing.FinTM.leftCfg_output` | `L.output = c.output` |
| `Turing.FinTM.rightCfg_state` | `R.state = c.state.map f` |
| `Turing.FinTM.rightCfg_inputPos` | `R.inputPos = c.inputPos` |
| `Turing.FinTM.rightCfg_workTapes` | `R.workTapes i a = Fin.addCases tapes c.workTapes i a` |
| `Turing.FinTM.rightCfg_workTapePos` | `R.workTapePos i = Fin.addCases heads c.workTapePos i` |
| `Turing.FinTM.rightCfg_output` | `R.output = c.output` |

For the final five, let `C = Turing.captureCfg emb ret pre out₀ c`, with source bank
size `k`, and `i : Fin (k+1)`.

| Proposed public name | Exact field formula (with that alias) |
|---|---|
| `Turing.captureCfg_state` | `C.state = some ((c.state.map emb).getD ret)` |
| `Turing.captureCfg_inputPos` | `C.inputPos = c.inputPos` |
| `Turing.captureCfg_workTapes` | `C.workTapes i a = (if h : i.val < k then c.workTapes ⟨i.val,h⟩ else FinTM.bufferTape (pre ++ c.output)) a` |
| `Turing.captureCfg_workTapePos` | `C.workTapePos i = if h : i.val < k then c.workTapePos ⟨i.val,h⟩ else ((pre ++ c.output).length : ℤ)` |
| `Turing.captureCfg_output` | `C.output = out₀` |

All five arguments/fields are retained as shown in the raw `#check` headers, including
unused frame arguments. Work-tape equations are **pointwise** in both tape and cell,
and head equations pointwise in tape. `generated-readers.json` preserves the exact
Lean-printed headers, including implicit parameters, universes and motives.

## Executed results and limits

- **Same-home generation: PASS.** Ten Simulation readers and five Wrappers readers
  elaborate with zero errors/warnings. All 15 names are public and absent from the
  simp set; the probe checks all forward/backward and pre/post origins. Ten left/right
  axiom prints contain only `propext, Quot.sound`; all five capture prints have no axioms.
- **Conditional sealed consumers: PASS.** With all three original definitions locally
  irreducible, the exact 15 field equations taken as explicit hypotheses reconstruct
  all three configurations. Separate cases discharge a physical-output goal hidden
  behind `d = captureCfg …` and the last capture head's length formula. All five
  consumer axiom prints use standard axioms or fewer. No proposed reader is silently
  assumed to exist in the imported library.
- **Controls: PASS as controls.** Six direct reduction proofs (output and heads for each
  original definition) close unsealed. The identical controls with all three originals
  sealed produce **exactly six expected `rfl` failures**, including the implicit capture
  output case. No controls or axioms from a failed elaboration certify a result.
- The first failed diagnostic is preserved as `GeneratedReaders-attempt1.lean.txt` and
  matching log. It used incorrect left/right namespaces, tried to add `[simps]` to
  imported declarations, and omitted the command-to-CoreM lift for metadata inspection.
  The successful probes correct those setup issues; no statement weakening was needed.

The separate physical output and captured word are significant: the host output is
**`out₀`**, while its capture tape and head depend on **`pre ++ c.output`**. The output
reader is needed even where that field was previously read implicitly by `rfl` after a
run/configuration equality. Head readers alone do not cover that read.

All six runs were sequential through `leanelab.sh` on the complete `oleans-mlin2` tree,
with the pinned toolchain and shared slot locks. `receipt.json` records actual exits,
times, source/log SHA-256 values, snapshot/worktree pin, definition hashes, source blob
pins and limitations. Every recorded source/log hash was rechecked.

This establishes syntax, exact scope and bounded conditional use. It does **not**
establish a complete checkpoint seal, approve new API, implement the readers, review
the delivered proof, run a replay/screen/cache step, dispatch work, or push anything.
