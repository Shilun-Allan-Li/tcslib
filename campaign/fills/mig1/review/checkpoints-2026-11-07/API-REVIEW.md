# cp02 independent API review

2026-11-07; source inspection only. Read the current `Simulation.lean`, cp02's source
copies/report, and its Composition/Wrappers argument inventories as data. No delivered
scripts were executed. No Lean, screens, source edits, or Git mutations were performed.

**Not yet clear to merge.** E1 is a real reader gap. The ten configuration-field equations
below give a concrete approval scope. The separate exclusion of `branchTM` also remains
unresolved; cp02's reported seal is explicitly partial with respect to these definitions.

## Configuration readers: concrete proposed scope

Home: `TCSlib/Complexity/TuringMachine/Simulation.lean`, namespace `Turing.FinTM`, immediately
beside `leftCfg` and `rightCfg` (current lines 195/206; cp02 lines 196/207). Preserve both
definitions, their signatures, imports, and all existing `simp` attributes.

The current tree and cp02 have public `leftCfg_apply`/`rightCfg_apply`, `_step`, and `_run`,
but no field readers or `simps` attributes on these configurations. A repository search
found no existing `leftCfg_state`/`rightCfg_state`, `_inputPos`, `_workTapes`, `_workTapePos`,
or `_output`. The run equations at time zero reduce to an identity of the embedded
configuration; they do not expose any field. The other APIs do not supply that missing
projection information either.

For the **left family**, use exactly these common parameters:

```lean
{k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
(c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
```

The proposed equations are:

| Name, prefixed `Turing.FinTM.` | Exact conclusion |
| --- | --- |
| `leftCfg_state` | `(leftCfg f c tapes heads).state = c.state.map f` |
| `leftCfg_inputPos` | `(leftCfg f c tapes heads).inputPos = c.inputPos` |
| `leftCfg_workTapes` | `∀ (i : Fin (k + l)) (a : ℤ), (leftCfg f c tapes heads).workTapes i a = (Fin.addCases c.workTapes tapes) i a` |
| `leftCfg_workTapePos` | `∀ i : Fin (k + l), (leftCfg f c tapes heads).workTapePos i = (Fin.addCases c.workTapePos heads) i` |
| `leftCfg_output` | `(leftCfg f c tapes heads).output = c.output` |

For the **right family**, the common parameters change only to
`c : Cfg l Bool S x`, `tapes : Fin k → ℤ → Option Bool`, and `heads : Fin k → ℤ`:

| Name, prefixed `Turing.FinTM.` | Exact conclusion |
| --- | --- |
| `rightCfg_state` | `(rightCfg f c tapes heads).state = c.state.map f` |
| `rightCfg_inputPos` | `(rightCfg f c tapes heads).inputPos = c.inputPos` |
| `rightCfg_workTapes` | `∀ (i : Fin (k + l)) (a : ℤ), (rightCfg f c tapes heads).workTapes i a = (Fin.addCases tapes c.workTapes) i a` |
| `rightCfg_workTapePos` | `∀ i : Fin (k + l), (rightCfg f c tapes heads).workTapePos i = (Fin.addCases heads c.workTapePos) i` |
| `rightCfg_output` | `(rightCfg f c tapes heads).output = c.output` |

The index/cell binders can be theorem parameters, as `simps` normally generates. These
formulas expose every field and handle arbitrary inactive tapes/heads, halted states, and
noninjective state maps; no extra premises are needed. They are definitional in their home.
Use the house `simps` generator with explicit projections
`state inputPos workTapes workTapePos output` and `config := { isSimp := false }`, matching
the existing configuration-reader pattern later in this file. No global simplification
change is proposed. Give the generated family a prose comment stating the formulas.

Eight equations (omitting `_workTapes`) cover the fields explicitly requested by E1. All ten
are the recommended scope because this is a structure-valued definition and the policy
calls for its complete field family. The tape equations also support exact configuration
reconstruction without leaving another reader gap.

## How the reported consumers would read the fields

The cp02 argument inventories contain one distinct Composition entry and six Wrappers
entries. These are an inventory of distinct reported uses, not a count of source occurrences
or a complete definitional-closure census:

| Consumer | Required field information |
| --- | --- |
| `condTM_computes_iff` | `rightCfg_state`, `rightCfg_output` |
| `timedCondTM_computes` | both `_state` and `_output`, through nested embeddings |
| `timed_control_heads` | `leftCfg_workTapePos` |
| `timedReady_dispatch` | both `_state` and `_inputPos` |
| `timed_read_heads` | `leftCfg_state` |

There are implicit reads too: `timed_branch_heads := rfl` uses both head layouts, while
output proofs passed directly as `hc.2`, `hb.2`, or `ho` depend on the embedded output
equations. Repairs must use the new readers explicitly for those conversions as well as
remove `leftCfg`/`rightCfg` from tactic arguments. Selected/inactive bank cases then use
the existing Mathlib `Fin.addCases_left`/`Fin.addCases_right` equations. No additional
selected-bank API is indicated by these uses.

## `branchTM`: separate, still unprobed

cp02's report says the tape count and state type occur in types and that “no equation can
replace” their definitional read. That is not an acceptable general reason to exclude an
ordinary `def` from a rule-10 seal. Published bundle-shape equations and explicit transport
can express dependent conversions; a whole-bundle equation would be another mechanism.
`branchTM` is not a reducible abbreviation.

There is also an operational read: `condTM_computes_iff` supplies
`(fun _ _ _ => rfl)` to `rightCfg_run`. The controller's table is wired to
`branchTM M₁ M₂ false`, while the source run uses `branchTM M₁ M₂ (p x)`. That proof
currently relies on the foreign definition's table being independent of the Boolean.
Shape readers alone do not publish this behavior.

Existing `branchTM_computes` and `branchTM_spaceUsed` describe completed computation and
total space; they do not provide arbitrary-start raw run correspondence or bundle-shape
equations. cp02's two new initialization readers are private and supply neither a public
replacement for this behavior nor a general shape API.

A narrower candidate than exposing the entire constructor is, in the same home:

```lean
theorem branchTM_k (M₁ M₂ : FinTM Bool) (b : Bool) :
    (branchTM M₁ M₂ b).k = M₁.k + M₂.k

theorem branchTM_State (M₁ M₂ : FinTM Bool) (b : Bool) :
    (branchTM M₁ M₂ b).State = M₁.State ⊕ M₂.State

theorem branchTM_runFrom_independent (M₁ M₂ : FinTM Bool) (b b' : Bool)
    {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x) (t : ℕ) :
    (branchTM M₁ M₂ b).tm.runFrom c t =
      (branchTM M₁ M₂ b').tm.runFrom c t
```

These are **unelaborated candidate contracts**, not approved or sufficient-by-test APIs.
The intended consumer proof runs the controller's existing false-tag machine in lockstep
and then rewrites its raw run using the independence theorem. Any dependent typing in the
consumer must use the shape readers and explicit transport. A fresh sealed consumer proof
must establish that this actually removes every `branchTM` read; hidden reads in headers,
`change`, `rfl`, and theorem arguments must all be inventoried.

A full constructor equation would expose shape and transition table together, but is
broader than this need and than the normal machine run/contract surface. Prefer probing
the run-contract candidate. Its precise final API and pre-ship proof remain follow-up
work; this review does not resolve the third exclusion or certify F-A acceptance. All new
public readers require Seyoon's approval before implementation.
