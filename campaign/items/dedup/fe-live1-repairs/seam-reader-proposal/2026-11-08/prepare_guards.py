from pathlib import Path
import json,re,hashlib
out=Path(__file__).resolve().parent;p=out/'project';bounds=json.loads((out/'HYP-BOUNDARIES.json').read_text());union=json.loads((out/'GUARD-UNION.json').read_text())['regular'];hyp=(out/'source/Hardness-HYP.lean.txt').read_text();stop=hyp.index('/-- Native query argument words:');prefix=hyp[:stop];sealed=prefix;maps=[]
for short in ['clFresh_idle','clPrepared_idle']:
 b=next(b for b in bounds if b['root'].endswith('.'+short));defs=sorted(d['name'] for d in b['foreign_definition_mentions'] if d['hints']!='abbrev' and not d['projection']);removed=sorted(d['name'] for d in b['foreign_definition_mentions'] if d['hints']!='abbrev' and not d['projection'] and (d['simp'] or d['unfold']));start=prefix.index('private lemma '+short+' ');doc=prefix.rfind('/--',0,start);end=prefix.find('\n/--',start);end=len(prefix) if end==-1 else end;block=prefix[doc:end];assert sealed.count(block)==1;attrs=('attribute [-simp] '+' '.join(removed)+'\n') if removed else '';wrapped='section\n'+attrs+'attribute [local irreducible] '+' '.join(defs)+'\n'+block+'\nend\n';sealed=sealed.replace(block,wrapped);maps.append({'root':b['root'],'guard_heads':defs,'removed_active_simp_unfold_entries':removed,'complete_literal_target_block_sha256':hashlib.sha256(block.encode()).hexdigest(),'target_lines':len(block.splitlines()),'complete_body':True})
sealed+='\nend Complexity\n';(p/'ConsumersSealed.lean').write_text(sealed);(out/'source/consumers-sealed.lean.txt').write_text(sealed)
controls=json.loads((out/'inputs/control-templates.json').read_text());assert set(union)<=set(controls)
preamble='''import TCSlib.Complexity.CookLevin.Hardness
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Turing Turing.FinTM
private def blankCfg : Cfg 0 Bool Unit [] :=
  {state := some (), inputPos := 0, workTapes := fun i => Fin.elim0 i,
   workTapePos := fun i => Fin.elim0 i, output := []}
'''
blocks='\n'.join(''.join(controls[n]) for n in sorted(union));control_map=[]
for side in ['Unsealed','Sealed']:
 attrs=''
 if side=='Sealed':
  removed=sorted(n for n,d in union.items() if d['simp'] or d['unfold']);attrs=('attribute [-simp] '+' '.join(removed)+'\n' if removed else '')+'attribute [local irreducible] '+' '.join(sorted(union))+'\n'
 source=preamble+attrs+'\n'+blocks;(p/f'Controls{side}.lean').write_text(source);(out/'source'/f'controls-{side.lower()}.lean.txt').write_text(source)
 markers=[(i+1,l.split('|')[1],l.split('|')[2]) for i,l in enumerate(source.splitlines()) if l.startswith('-- CONTROL|')]
 for ix,(line,name,kind) in enumerate(markers):control_map.append({'side':side,'name':name,'kind':kind,'start_line':line,'end_line':markers[ix+1][0]-1 if ix+1<len(markers) else len(source.splitlines())})
(out/'GUARD-MAP.json').write_text(json.dumps({'consumer_roots':maps,'producer_guard_heads':['Turing.Action.mapState'],'union_count':len(union),'guard_context':'Full exact literal HYP prefixes; complete target bodies in individually scoped sections; preceding definitions and theorems are unsealed; source ends after clPrepared_idle.','control_pairs':len(union),'control_goal_count_per_side':2*len(union)},indent=2)+'\n');(out/'CONTROL-MAP.json').write_text(json.dumps(control_map,indent=2)+'\n')
plan=[['09-both-complete-consumer-seals','ConsumersSealed.lean','oleans-hyp'],['10-controls24-unsealed','ControlsUnsealed.lean','oleans-hyp'],['11-controls24-sealed','ControlsSealed.lean','oleans-hyp','expect-fail']];(out/'guard-plan.json').write_text(json.dumps(plan,indent=2)+'\n');print('Prepared fresh guards:',[(r['root'],len(r['guard_heads'])) for r in maps],'; union',len(union))
