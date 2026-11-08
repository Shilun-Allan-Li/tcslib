from pathlib import Path
import json,re
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');P=O/'native-project'
lines=(O/'probes/APIInventory__attempt1.log').read_text().splitlines()
guards=json.loads(next(l.split('|',1)[1] for l in lines if l.startswith('GUARDS|')));simps=json.loads(next(l.split('|',1)[1] for l in lines if l.startswith('SIMPDEFS|')))
defs=[json.loads(l.split('|',1)[1]) for l in lines if l.startswith('DEF|')]
api=(W/'TCSlib/Complexity/TuringMachine/CfgFacts.lean').read_text().replace('import TCSlib.Complexity.TuringMachine.StateRenaming\n','import TCSlib.Complexity.TuringMachine.StateRenaming\nimport Lean\n')
a=api.index('/-- A one-step run from any configuration');m=re.search(r'^  rw \[MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero\]\n',api,re.M);assert m;b=m.end()
base='section RO1Opacity\n'+(('attribute [-simp] '+' '.join(simps)+'\n') if simps else '')
guard='attribute [local irreducible] '+' '.join(guards)+'\n'
variants={}
for variant in ['Native','Sealed']:
 s=api[:a]+base+(guard if variant=='Sealed' else '')+api[a:b]+'end RO1Opacity\n'+api[b:]
 variants[variant]=s;(O/('APIScope'+variant+'.lean.txt')).write_text(s);(P/('APIScope'+variant+'.lean')).write_text(s)
assert variants['Sealed'].replace(guard,'')==variants['Native']
code=Path('/private/tmp/ab34-overnight-sg1-extras/prepare-seals-controls.py').read_text();control=code.split("control='''",1)[1].split("'''",1)[0]
payload=control.replace('NAMES','['+', '.join('`'+n for n in guards)+']').replace('PREFIX','RO1APIRfl')
imports='import TCSlib.Complexity.TuringMachine.StateRenaming\nimport Lean\nset_option maxHeartbeats 0\n'
for variant in ['Native','Sealed']:
 s=imports+base+(guard if variant=='Sealed' else '')+payload+'\nend RO1Opacity\n'
 (O/('APIControls'+variant+'.lean.txt')).write_text(s);(P/('APIControls'+variant+'.lean')).write_text(s)
(O/'api-seal-inventory.json').write_text(json.dumps({'guards':guards,'default_simp_definitions_removed_in_both_variants':simps,'all_definition_records':defs,'ordinary_guard_count':len(guards),'projection_kernel_abbrev_exclusions':sorted({d['name'] for d in defs if d['foreign'] and not d['ordinary_guard']}),'imported_theorem_values_traversed':False,'entire_API_doc_header_and_body_guarded':True,'instrumented_native_recovered_by_deleting_single_guard_line':True,'expected_positive_controls':2*len(guards),'expected_negative_controls':2*len(guards),'control_identities':[{'definition':n,'mode':mode,'kernel_name':f'RO1APIRfl_{2*i+j+1}_{mode}'} for i,n in enumerate(guards) for j,mode in enumerate(['point','abstract'])]},indent=2)+'\n')
print('Prepared complete API-scope native/sealed copies and fresh',2*len(guards),'positive +',2*len(guards),'negative controls; no Lean started.')
