from pathlib import Path
import json,re
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4]
changes=json.loads((OUT/'changes.json').read_text());ctx=json.loads((OUT/'context.json').read_text())
old=ROOT/'campaign/gates/106-sg1-dedup/review/round2-findings-review'
(OUT/'run-probe.py').write_text((old/'run-probe.py').read_text().replace('tcslib-g106-r2-fp-','tcslib-g106-r3-closure-'))
names=['Turing.MultiTapeTM.step','Turing.MultiTapeTM.runFrom','Turing.MultiTapeTM.initCfg','Turing.Cfg.init','Turing.Action.apply','Turing.Cfg.inputSymbol','Turing.Cfg.workTapeSymbols','Turing.moveInputPos','Turing.FinTM.ComputesInTime','Turing.FinTM.ComputesFunInTime','Turing.FinTM.Computes','Turing.MultiTapeTM.spaceUsed','Turing.MultiTapeTM.spaceUsedByTape','Turing.MultiTapeTM.visitedByTapeHead','Complexity.PolyTimeComputable','Complexity.pairMapSnd','Turing.pairEncode','Turing.pairDecode']
attrs='attribute [local irreducible] '+' '.join(names)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
(OUT/'guard-definitions.txt').write_text('\n'.join(names)+'\n');(OUT/'guard-attributes.txt').write_text(attrs)
meta='''\nopen Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let wanted : List String := WANTED
  let kind := fun (ci : ConstantInfo) => match ci with
    | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (env.getModuleIdxFor? n).isSome then continue
    match n with
    | .str _ base => if wanted.contains base then roots := roots.push n
    | _ => pure ()
  if roots.size != wanted.length then throwError "Root count mismatch: {roots.size}/{wanted.length}"
  for n in roots.qsort Name.lt do logInfo m!"ROOT|{n}|private={isPrivateName n}"
  let mut selected : Array Name := #[]
  for (n, _) in env.constants.toList do
    if roots.any (fun r => r.isPrefixOf n) then selected := selected.push n
  for n in selected.qsort Name.lt do
    let some ci := env.find? n | throwError "missing {n}"
    let axs ← liftCoreM <| Lean.collectAxioms n
    logInfo m!"PROOFAX|{n}|kind={kind ci}|{(axs.qsort Name.lt).toList}"
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    let mut seen : Array Name := #[]
    for c in used do
      if seen.contains c then continue
      seen := seen.push c
      match env.getModuleIdxFor? c, env.find? c with
      | some j, some info =>
        let owner := env.header.moduleNames[j.toNat]!
        if (`TCSlib).isPrefixOf owner then
          logInfo m!"CITED|{n}|{c}|{owner}|kind={kind info}|private={isPrivateName c}"
          if let .defnInfo di := info then
            let hint := match di.hints with
              | .abbrev => "abbrev" | .opaque => "opaque" | .regular _ => "regular"
            logInfo m!"FOREIGNDEF|{n}|{c}|{owner}|hints={hint}"
      | none, some (.defnInfo _) => logInfo m!"HOMEDEF|{n}|{c}"
      | _, _ => pure ()
'''
for rel,row in ctx['files'].items():
 tag=row['archive_tag'];raw=(OUT/(tag+'-after.lean.txt')).read_text();selected=[r for r in changes if r['file']==rel];sealed=raw
 for r in selected:
  token=r['new_doc']+'\n'+r['header']+'\n'+r['new_body'];assert sealed.count(token)==1,(tag,r['name'])
  wrapped='section SG1ClosureSeal_'+r['name']+'\n'+attrs+token+'end SG1ClosureSeal_'+r['name']+'\n'
  sealed=sealed.replace(token,wrapped)
 appendix=meta.replace('WANTED',json.dumps([r['name'] for r in selected]))
 (OUT/(tag+'-metadata-appendix.lean.txt')).write_text(appendix)
 (OUT/(tag+'-native.lean.txt')).write_text(raw+appendix)
 (OUT/(tag+'-sealed.lean.txt')).write_text(sealed+appendix)
for mode in ['unsealed','sealed']:
 s=(old/('Controls-'+mode+'-v4.lean.txt')).read_text()
 start=s.index('  let names : List Name :=');end=s.index('\n  let mut index :=',start)
 s=s[:start]+'  let names : List Name := ['+',\n    '.join('`'+n for n in names)+']'+s[end:]
 s=s.replace('g106_poly_controls','g106_closure_controls').replace('G106PolyRflControl','G106ClosureRflControl')
 s=re.sub(r'(?m)^attribute \[local irreducible\].*\n','',s)
 header='import TCSlib.Complexity.ClassNP.NP\n'
 assert s.startswith(header);s=s[len(header):]
 prefix=attrs if mode=='sealed' else 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
 (OUT/('Controls-'+mode+'-v1.lean.txt')).write_text(header+prefix+s)
(OUT/'control-definitions.txt').write_text('\n'.join(names)+'\n')
(OUT/'check-controls.py').write_text((old/'check-controls.py').read_text())
(OUT/'setup-attempt1.error.txt').write_text('Initial nested Python heredoc generator had a host-language triple-quote syntax error before any file or source mutation. Rewritten as the retained standalone prepare.py; no Lean was started for that failed setup.\n')
print('Prepared exact full-module native/13-section sealed copies and18-definition paired controls.')
