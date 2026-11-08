from pathlib import Path
import json
O=Path('/private/tmp/ab34-overnight-sat-import-proposal');E=Path('/private/tmp/ab34-overnight-sg1-extras');rows=json.loads((O/'chunk-mappings.json').read_text());lines=(O/'inventory-SATProposal-attempt1.log').read_text().splitlines();receipt=json.loads((O/'inventory-SATProposal-attempt1.json').read_text());assert receipt['exit']==receipt['errors']==0
guards=json.loads(next(l.split('|',1)[1] for l in lines if l.startswith('GUARDS|')));simps=json.loads(next(l.split('|',1)[1] for l in lines if l.startswith('SIMPDEFS|')));defs=[json.loads(l.split('|',1)[1]) for l in lines if l.startswith('DEF|')]
inventory={'context':'SATProposal','guards':guards,'default_simp_definitions_removed':simps,'all_definition_records':defs,'projection_kernel_abbrev_exclusions':sorted({r['name'] for r in defs if r['foreign'] and not r['ordinary_guard']}),'imported_theorem_values_traversed':False};(O/'definition-inventories.json').write_text(json.dumps([inventory],indent=2)+'\n')
scoped=(O/'SATProposal-scope-native.lean.txt').read_text();pos=scoped.index(rows[0]['new_chunk']);base='section ExtraOpacity\n'+(('attribute [-simp] '+' '.join(simps)+'\n') if simps else '');guard='attribute [local irreducible] '+' '.join(guards)+'\n';jobs=[]
for variant in ['native','sealed']:
 text=scoped[:pos]+base+(guard if variant=='sealed' else '')+scoped[pos:];ending='end Complexity\n';assert text.endswith(ending);text=text[:-len(ending)]+'end ExtraOpacity\n'+ending;label='SATProposalScope'+variant.title();(O/('SATProposal-scope-'+variant+'-instrumented.lean.txt')).write_text(text);(O/'native-project'/(label+'.lean')).write_text(text);jobs.append({'job':'SATProposal-scope-'+variant,'file':label+'.lean','expected_exit':0,'expected_errors':0})
s=(E/'prepare-seals-controls.py').read_text();a=s.index("control='''")+len("control='''");b=s.index("'''\ninventory",a);control=s[a:b];control=control.replace('NAMES','['+', '.join('`'+n for n in guards)+']').replace('PREFIX','OvernightSATProposalRfl')
original=(O/'proposed-source/TCSlib/Complexity/ClassNP/SAT.lean.txt').read_text();imports='\n'.join(l for l in original.splitlines() if l.startswith('import '))+'\nimport Lean\nset_option maxHeartbeats 0\n'
ids=[]
for i,n in enumerate(guards):
 for j,mode in enumerate(['point','abstract']):ids.append({'definition':n,'mode':mode,'kernel_name':f'OvernightSATProposalRfl_{2*i+j+1}_{mode}'})
(O/'control-identities.json').write_text(json.dumps([{'context':'SATProposal','identities':ids}],indent=2)+'\n')
for variant in ['native','sealed']:
 text=imports+base+(guard if variant=='sealed' else '')+control+'\nend ExtraOpacity\n';label='SATProposalControls'+variant.title();(O/('SATProposal-controls-'+variant+'.lean.txt')).write_text(text);(O/'native-project'/(label+'.lean')).write_text(text);jobs.append({'job':'SATProposal-controls-'+variant,'file':label+'.lean','expected_exit':0 if variant=='native' else 1,'expected_errors':0 if variant=='native' else len(ids)})
(O/'scope-control-jobs.json').write_text(json.dumps(jobs,indent=2)+'\n')
s=(E/'run-scopes-controls.py').read_text().replace('/private/tmp/ab34-overnight-sg1-extras',str(O)).replace('PASS5 whole-body scopes in2contexts;44positive kernel declarations+44exact negative controls','PASS4 hypothetical SAT declarations in1context;fresh positive and negative controls').replace('ALL8_SCOPE_CONTROL_JOBS_PASS','ALL4_SCOPE_CONTROL_JOBS_PASS');(O/'run-scopes-controls.py').write_text(s)
print(json.dumps({'guards':len(guards),'positive_controls':len(ids),'negative_controls':len(ids),'whole_declarations':4}))
