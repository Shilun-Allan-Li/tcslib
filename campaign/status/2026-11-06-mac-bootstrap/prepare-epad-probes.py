"""Write inspected E-PAD probe sources; this script does not run Lean.

The four metadata walks and first-equation control were read in full before
reuse from the checksummed delivery. No delivered shell/Python tool is run.
The parameter-abstracted equation control and module census are maintainer additions.
"""

from pathlib import Path
import hashlib
import json
import os


records = Path(__file__).resolve().parents[3]
scratch = Path(os.environ["TCSLIB_SCRATCH"])
delivery = scratch / "deliveries/epad-5fd7ecd68e4a/extracted/evidence"
data = json.loads((scratch / "gate-source-exports/summary.json").read_text())["115-epad-fill"]
evidence = records / "campaign/gates/115-epad-fill/evidence/current"
for name in ("seal", "axioms", "elaboration"):
    (evidence / name).mkdir(exist_ok=True)
receipt = {"head": data["head"], "reviewed_delivery_probe_sha256": {}}
for name in ("EPadAxioms", "EPadForeignDefs", "EPadSimpDefs", "EPadCites"):
    original = delivery / "probes" / (name + ".lean")
    source = original.read_text()
    receipt["reviewed_delivery_probe_sha256"][name] = hashlib.sha256(original.read_bytes()).hexdigest()
    directory = "axioms" if name == "EPadAxioms" else "seal"
    (evidence / directory / (name + ".lean.txt")).write_text(source)

source = (Path(data["head_export"]) / "TCSlib/Complexity/SpaceComplexity/Padding.lean").read_text()
names = (delivery / "seal/seal-list-final.txt").read_text().splitlines()
assert len(names) == len(set(names)) == 36
attributes = "attribute [local irreducible]\n  " + "\n  ".join(names) + "\n"
attributes += "attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n"
anchor = "open Turing\n"
assert source.count(anchor) == 1
(evidence / "seal/EPadSealed.lean.txt").write_text(source.replace(anchor, anchor + "\n" + attributes))
(evidence / "seal/seal-list.txt").write_text("\n".join(names) + "\n")
(evidence / "seal/delivery-not-sealed.txt").write_text((delivery / "seal/not-sealed-final.txt").read_text())

# Check the first equation both pointwise and abstracted over its parameters.
control = (delivery / "seal/EPadSealControlUnsealed-final.lean").read_text()
imports = "\n".join(line for line in source.splitlines() if line.startswith("import ")) + "\n\n"
start = control.index("open Lean Elab Command Term Meta in")
stop = control.index("#epad_seal_rfl Complexity.LOGSPACE")
command = control[start:stop]
whole = r'''open Lean Elab Command Term Meta in
elab "#epad_abstract_rfl " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM do
    let some eqs ← Meta.getEqnsFor? n | throwError "no equations for {n}"
    let original ← inferType (← mkConstWithLevelParams eqs[0]!)
    let ty ← forallTelescope original fun xs target => do
      unless target.isAppOfArity ``Eq 3 do throwError "not an equality for {n}"
      mkEq (← mkLambdaFVars xs target.appFn!.appArg!) (← mkLambdaFVars xs target.appArg!)
    let ok ← try
        Term.withoutErrToSorry do
          let pf ← Term.elabTermEnsuringType (← `(by rfl)) ty
          Term.synthesizeSyntheticMVarsNoPostponing
          let _ ← instantiateMVars pf
        pure true
      catch _ => pure false
    if ok then logInfo m!"abstract rfl closes: {n}"
    else throwError m!"abstract rfl FAILS: {n}"

'''
calls = "\n".join("#epad_seal_rfl " + n + "\n#epad_abstract_rfl " + n for n in names) + "\n"
for label, attrs in (("Unsealed", ""), ("Sealed", attributes)):
    (evidence / "seal" / ("Controls" + label + ".lean.txt")).write_text(
        imports + command + whole + attrs + "\n" + calls)

matcher = "Complexity.LogProg.alignedPair_loop.match_1"
(evidence / "seal/MatcherLimitation.lean.txt").write_text(
    imports + command + "\n#epad_seal_rfl " + matcher + "\n" +
    "attribute [local irreducible] " + matcher + "\n#epad_seal_rfl " + matcher + "\n")
(evidence / "seal/AbbrevEliminatorAttributes.lean.txt").write_text(
    imports + "\n" + "\n".join("attribute [local irreducible] " + n for n in (
        "Complexity.LogProg.ARM", "Complexity.LogProg.AConf", "Complexity.LogProg.BankS",
        "Complexity.LogProg.Ins.casesOn")) + "\n")

public = r'''import TCSlib.Complexity.SpaceComplexity.Padding

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some target := env.getModuleIdx? `TCSlib.Complexity.SpaceComplexity.Padding
    | throwError "Padding is missing from the imported module table"
  let names := env.constants.toList.filterMap fun (n, ci) =>
    if env.getModuleIdxFor? n == some target && !isPrivateName n then some (n, ci) else none
  for (n, ci) in names.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive" | .quotInfo _ => "quotient"
    logInfo m!"PUBLIC_CONSTANT {n} kind={kind} internal={n.isInternalDetail}"
'''
(evidence / "axioms/PublicConstants.lean.txt").write_text(public)
sanity = r'''import TCSlib.Complexity.SpaceComplexity.Padding

set_option autoImplicit false
open Turing Complexity

-- Zero padding permits every original member.
example (L : Language Bool) (x : List Bool) (hx : x ∈ L) :
    pairEncode x [] ∈ padLang L (fun _ => 0) := by
  exact mem_padLang_iff.mpr ⟨x, hx, rfl⟩

-- At degree zero the padding length is the constant coefficient, including x = [].
example (L : Language Bool) (C : ℕ) (hx : ([] : List Bool) ∈ L) :
    pairEncode [] (List.replicate C true) ∈ padLang L (fun n => C * (n + 1) ^ 0) := by
  apply mem_padLang_iff.mpr
  exact ⟨[], hx, by rw [pow_zero, Nat.mul_one]⟩

-- Empty languages cannot acquire members by padding.
example (pad : ℕ → ℕ) (y : List Bool) :
    y ∉ padLang (fun _ => False : Language Bool) pad := by
  intro h
  obtain ⟨x, hx, _⟩ := mem_padLang_iff.mp h
  exact hx
'''
(evidence / "elaboration/Sanity.lean.txt").write_text(sanity)
(evidence / "elaboration/PaddingPreflight.lean.txt").write_text(
    source + "\n" + sanity.replace("import TCSlib.Complexity.SpaceComplexity.Padding\n", "") +
    "\n#print axioms Complexity.mem_SPACE_padLang\n#print axioms Complexity.padLang\n" +
    "#print axioms Complexity.mem_padLang_iff\n")
(evidence / "seal/input-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("Wrote E-PAD probes only; no elaboration was run.")
