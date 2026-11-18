# Reader-only generic projection additions

These are insertion FRAGMENTS, not standalone modules. No Lean/lake/proof-check command or
live source edit was made. All25 bodies are `:= rfl`; they introduce no algorithm, sampler,
efficient value, instance, global attribute or import. Max line width93.

## Insertion points

1. **FEScheme.readers.lean.inc**: insert in
   `TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Defs/Efficient.lean`,
   immediately after the complete `structure FEScheme ... where` and before the final
   `end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption`.
   The fragment opens/closes the relative `namespace FEScheme` and declares
   `{C : FnClass} (S : FEScheme C)`.
2. **Simulator.readers.lean.inc**: insert in
   `.../FunctionalEncryption/Defs/Simulator.lean`, after the efficient `structure Simulator`
   and before its final outer `end ...FunctionalEncryption.FEScheme.Raw`.
   The outer `{C : FnClass} (S : FEScheme.Raw C)` variables are still available;
   `variable {S} (Sim : Simulator S)` makes S implicit for these readers.
3. **SASimulator.readers.lean.inc**: insert in
   `.../FunctionalEncryption/SemiAdaptive/Simulator.lean`, after efficient
   `structure SASimulator` and before its final outer `end ...FEScheme.Raw`.
   Same implicit-S pattern, relative namespace SASimulator.

Do not nest these fragments inside another same-name namespace. They intentionally rely on
the existing outer namespace/context instead of opening the full absolute namespace again.
No PG reader is added: its existing toRaw_MIdx/TIdx/L1/L0/rec/eval readers are reused.

## Intended headers and type review

FEScheme.toRaw_{G,cprm,MPK,MSK,SK,CT,DecOut,embed,setupCore,encCore,keyCore,dec,encMPK,encSK,encCT}
state whole-field equalities. Inherited fields have definitionally the same dependent
parameter families after projection, so no transport, cast or rederivation was introduced.
Simulator/SASimulator.toRaw_{St,encSt,setupCore,encCore,keyCore} likewise compare the original
inherited functions. These are supported by the actual `extends ...Raw` declarations read
in place; no proposed header was found structurally ill-typed in static review. They are
still UNELABORATED proposals until root checks them.

Exact?/apply? was not run because root owns Lean. The rfl bodies intentionally use only
raw projection/inherited-field reduction. No semantic algorithm definition is unfolded.
These are precisely the public projection equations needed by later consumers/Rule10 seals.

## Searches before drafting

Read complete current Defs/Raw, Defs/Efficient, Defs/Simulator and SemiAdaptive/Simulator.
Ran both name and conclusion-shape rg searches across TCSlib, pinned Mathlib and core Lean:

- every requested `toRaw_<field>` name, including G/cprm/typed families/cores/codecs/St/encSt;
- `toRaw.<field> = ...` for the same whole-field projection conclusion shapes;
- full FEScheme.toRaw_ / Simulator.toRaw_ / SASimulator.toRaw_ name prefixes.

No existing requested header/conclusion was found. Existing PartialGarbling readers and
concrete assembly `..._toRaw` readers are nearest relatives, not duplicates: those concern
other structures or complete concrete bundles. Per-name log is reader-searches.tsv.

## ML source NoScopeEscapes update

| Source insertion | Full declaration namespace | Additions | NoScopeEscapes / boundary effect |
|---|---|---:|---|
| Defs/Efficient.lean | TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme |15| Theorems only; all requested projection readers; no root declaration or namespace leak. |
| Defs/Simulator.lean | TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator |5| Theorems only; existing raw/efficient type names unchanged. |
| SemiAdaptive/Simulator.lean | TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator |5| Theorems only; stateful algorithm and efficiency fields unchanged. |
| All fragments | Scoped relative namespace closed in each fragment |25| No modified old header, proof assumption, global simp, new axiom, new efficiency value, new sampler/machine, or frozen-file edit. |

This update belongs with the M0 generic-interface reader inventory. The older static header
snapshot is not regenerated while the root is editing; include these25 in the final-HEAD
inventory/StmtDump/seals only after insertion and checking.
