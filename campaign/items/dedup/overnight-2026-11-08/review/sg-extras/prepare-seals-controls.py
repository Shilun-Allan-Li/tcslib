from pathlib import Path
import hashlib,json
O=Path('/private/tmp/ab34-overnight-sg1-extras');rows=json.loads((O/'chunk-mappings.json').read_text())
control='''
open Lean Elab Command Meta
run_cmd do
  let names : List Name := NAMES
  let mut index := 0
  for n in names do
    let some (.defnInfo di) := (← getEnv).find? n | throwError "not a definition {n}"
    for mode in ["point", "abstract"] do
      index := index + 1
      let pair ← liftTermElabM do
        let levels := di.levelParams.map Level.param
        let head := mkConst n levels
        let solve := fun (lhs rhs : Expr) => do
          let goalType ← mkEq lhs rhs
          let goal ← mkFreshExprSyntheticOpaqueMVar goalType
          try
            goal.mvarId!.refl
            let value ← instantiateMVars goal
            pure (some (← instantiateMVars goalType, value))
          catch ex =>
            logInfo m!"CONTROL|{n}|{mode}|FAIL"
            logError m!"RFL_CONTROL|{n}|{mode}|{ex.toMessageData}"
            pure none
        if mode == "abstract" then
          solve head di.value
        else
          forallTelescope di.type fun xs resultType => do
            let mut lhs := mkAppN head xs
            let mut rhs := (mkAppN di.value xs).headBeta
            match resultType.getAppFn with
            | .const ``Turing.FinTM _ =>
              lhs := mkProj ``Turing.FinTM 0 lhs
              rhs := mkProj ``Turing.FinTM 0 rhs
            | .const ``Turing.Cfg _ =>
              lhs := mkProj ``Turing.Cfg 0 lhs
              rhs := mkProj ``Turing.Cfg 0 rhs
            | .const ``Turing.MultiTapeTM _ =>
              lhs := mkProj ``Turing.MultiTapeTM 0 lhs
              rhs := mkProj ``Turing.MultiTapeTM 0 rhs
            | .const ``Turing.Action _ =>
              lhs := mkProj ``Turing.Action 0 lhs
              rhs := mkProj ``Turing.Action 0 rhs
            | _ => pure ()
            match ← solve lhs rhs with
            | none => pure none
            | some (type, value) =>
              pure (some (← mkForallFVars xs type, ← mkLambdaFVars xs value))
      match pair with
      | none => pure ()
      | some (type, value) =>
        let declName := Name.mkSimple s!"PREFIX_{index}_{mode}"
        liftCoreM <| addDecl (.thmDecl {
          name := declName, levelParams := di.levelParams, type := type, value := value })
        logInfo m!"CONTROL|{n}|{mode}|PASS|kernelChecked={declName}"
'''
inventory=[];jobs=[];identities=[]
for key,attempt,path in [('SafeRun','attempt3','TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean'),('HardnessLeaves','attempt1','TCSlib/Complexity/CookLevin/Hardness.lean')]:
 lines=(O/f'inventory-{key}-{attempt}.log').read_text().splitlines();guards=json.loads(next(l.split('|',1)[1] for l in lines if l.startswith('GUARDS|')));simps=json.loads(next(l.split('|',1)[1] for l in lines if l.startswith('SIMPDEFS|')));defs=[json.loads(l.split('|',1)[1]) for l in lines if l.startswith('DEF|')]
 inventory.append({'context':key,'guards':guards,'default_simp_definitions_removed':simps,'all_definition_records':defs,'projection_kernel_abbrev_exclusions':sorted({r['name'] for r in defs if r['foreign'] and not r['ordinary_guard']}),'imported_theorem_values_traversed':False})
 scoped=(O/(key+'-scope-native.lean.txt')).read_text();mine=[r for r in rows if r['path']==path];pos=scoped.index(mine[0]['new_chunk']);namespace='Turing' if key=='SafeRun' else 'Complexity'
 base='section ExtraOpacity\n'+(('attribute [-simp] '+' '.join(simps)+'\n') if simps else '')
 guard='attribute [local irreducible] '+' '.join(guards)+'\n'
 for variant in ['native','sealed']:
  text=scoped[:pos]+base+(guard if variant=='sealed' else '')+scoped[pos:]
  ending='end '+namespace+'\n';assert text.endswith(ending);text=text[:-len(ending)]+'end ExtraOpacity\n'+ending
  label=key+'Scope'+variant.title();(O/(key+'-scope-'+variant+'-instrumented.lean.txt')).write_text(text);(O/'native-project'/(label+'.lean')).write_text(text);jobs.append({'job':key+'-scope-'+variant,'file':label+'.lean','expected_exit':0,'expected_errors':0})
 original=(O/'source'/(path+'.txt')).read_text();imports='\n'.join(l for l in original.splitlines() if l.startswith('import '))+'\nimport Lean\nset_option maxHeartbeats 0\n'
 ids=[]
 for i,n in enumerate(guards):
  for j,mode in enumerate(['point','abstract']):ids.append({'definition':n,'mode':mode,'kernel_name':f'Overnight{key}Rfl_{2*i+j+1}_{mode}'})
 identities.append({'context':key,'identities':ids})
 payload=control.replace('NAMES','['+', '.join('`'+n for n in guards)+']').replace('PREFIX','Overnight'+key+'Rfl')
 for variant in ['native','sealed']:
  text=imports+base+(guard if variant=='sealed' else '')+payload+'\nend ExtraOpacity\n';label=key+'Controls'+variant.title();(O/(key+'-controls-'+variant+'.lean.txt')).write_text(text);(O/'native-project'/(label+'.lean')).write_text(text);jobs.append({'job':key+'-controls-'+variant,'file':label+'.lean','expected_exit':0 if variant=='native' else 1,'expected_errors':0 if variant=='native' else len(ids)})
(O/'definition-inventories.json').write_text(json.dumps(inventory,indent=2)+'\n');(O/'control-identities.json').write_text(json.dumps(identities,indent=2)+'\n');(O/'scope-control-jobs.json').write_text(json.dumps(jobs,indent=2)+'\n')
print(json.dumps({'contexts':[{r['context']:len(r['guards'])} for r in inventory],'expected_positive':sum(len(r['identities']) for r in identities),'expected_negative':sum(len(r['identities']) for r in identities),'whole_chunks_guarded':5}))
