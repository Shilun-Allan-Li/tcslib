from pathlib import Path
import json
O=Path('/private/tmp/ab34-nat-reader-closure-refinement');P=O/'project';A=O/'attempt1-controls';A.mkdir(exist_ok=False)
for n in ['ControlsNative.lean.txt','ControlsSealed.lean.txt','guard-context.json']:(A/n).write_bytes((O/n).read_bytes())
line='attribute [local irreducible] Nat.bit Turing.codeBitsNat Turing.incFixed\n';s=(O/'ControlsNative.lean.txt').read_text();s=s.replace('`Nat.bit, `Turing.codeBitsNat, `Turing.incFixed','`Nat.bit, `Turing.codeBitsNat');assert s.endswith('end NatReaderOpacity\n');s=s[:-len('end NatReaderOpacity\n')]
extra='''
theorem NatClosureIncFixed_nil : Turing.incFixed [] = none := rfl

theorem NatClosureIncFixed_false_cons (w : List Bool) :
    Turing.incFixed (false :: w) = some (true :: w) := rfl

run_cmd do
  let env ← getEnv
  for (n, mode) in [(`NatClosureIncFixed_nil, "nil_equation"),
      (`NatClosureIncFixed_false_cons, "false_cons_equation")] do
    let some _ := env.find? n | logInfo m!"CONTROL|Turing.incFixed|{mode}|FAIL"; continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    if axs.any (fun a => a.toString.endsWith "sorryAx") then
      logInfo m!"CONTROL|Turing.incFixed|{mode}|FAIL"
    else
      logInfo m!"CONTROL|Turing.incFixed|{mode}|PASS|kernelChecked={n}"
end NatReaderOpacity
'''
s+=extra
for name,sealed in [('ControlsNative',False),('ControlsSealed',True)]:
 out=s.replace('section NatReaderOpacity\n','section NatReaderOpacity\n'+line,1) if sealed else s;(O/(name+'.lean.txt')).write_text(out);(P/(name+'.lean')).write_text(out)
assert (O/'ControlsNative.lean.txt').read_text()==(O/'ControlsSealed.lean.txt').read_text().replace(line,'',1)
context=json.loads((O/'guard-context.json').read_text());context['fresh_paired_control_identities']=context['fresh_paired_control_identities'][:4]+[{'definition':'Turing.incFixed','mode':'nil_equation','kernel_name':'NatClosureIncFixed_nil','exact_control':'theorem NatClosureIncFixed_nil : Turing.incFixed [] = none := rfl'},{'definition':'Turing.incFixed','mode':'false_cons_equation','kernel_name':'NatClosureIncFixed_false_cons','exact_control':'theorem NatClosureIncFixed_false_cons (w : List Bool) :\n    Turing.incFixed (false :: w) = some (true :: w) := rfl'}];context['failed_control_preparation_preserved']='attempt1-controls plus original-attempt1 receipts/logs: generic reflected incFixed body rfl fails natively, so does not establish effective controls. Replaced with native-checked constructor equations; no transparency override.';(O/'guard-context.json').write_text(json.dumps(context,indent=2)+'\n');print('Prepared revised six paired controls; incFixed uses concrete native constructor equations, no reducibility override.')
