from pathlib import Path
import json,hashlib,subprocess,os,re
O=Path('/private/tmp/ab34-continuation-triage');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');W=Path('/Users/seyoonr/.codex/worktrees/ab34-overnight-all8/tcslib-arora-barak-ch3-4');J=lambda p:json.loads(p.read_text());d=J(O/'candidate-dispositions.json');b=J(O/'input-bindings.json');ref=b['verified_full_Git_commit'];env=dict(os.environ);env['GIT_OPTIONAL_LOCKS']='0';h=lambda x:hashlib.sha256(x).hexdigest();inv=J(R/'campaign/items/dedup/overnight-2026-11-08/review/nat-reader/selected-declaration-inventory.json')['rows'];by={}
for r in inv:by.setdefault(r['path'],[]).append(r['as_written_name'])
groups={'M1':['CodeSimulator.lean','NatBits.lean'],'M2':['CodeSimulator.lean','NatBits.lean'],'M3':['Zone.lean'],'M4':['Zone.lean'],'M5':['ZoneTape.lean'],'M6':['ZoneTape.lean'],'M7':['Simulation.lean'],'M8':['Simulation.lean'],'M9':['Embed.lean'],'M10':['Embed.lean'],'M11':['Encoding.lean'],'M12':['Encoding.lean']}
for r in d['rows']:
 if r['id'] not in groups:continue
 for path,names in by.items():
  if Path(path).name not in groups[r['id']]:continue
  text=(W/path).read_text();ls=text.splitlines();locs=[]
  for name in names:
   hits=[i+1 for i,l in enumerate(ls) if re.search(r'\b(?:theorem|lemma|def|abbrev)\s+'+re.escape(name)+r'(?=[\s:{(])',l)]
   if not hits:hits=[i+1 for i,l in enumerate(ls) if name in l]
   assert hits,(path,name);locs.append({'name':name,'first_decl_or_literal_line':hits[0]})
  r['source'].append({'source_path':path,'source_pin':ref,'locations':locs,'bounded_source_group':'existing43 selected declarations, no new semantic enumeration'})
 if r['id']=='M2':r['reason']+=' Final #247 additionally repairs codeBitsNat through codeBitsNat_eq in that same full target; both readers are already present.'
sourcepaths={x['source_path'] for r in d['rows'] for x in r['source']};assert all(r['source'] for r in d['rows']);out=[]
for path in sorted(sourcepaths):
 raw=(W/path).read_bytes();blob=hashlib.sha1(('blob '+str(len(raw))+'\0').encode()+raw).hexdigest();actual=subprocess.check_output(['git','-C',str(W),'rev-parse',ref+':'+path],env=env).decode().strip();assert actual==blob;out.append({'path':path,'source_pin':ref,'bytes':len(raw),'SHA256':h(raw),'Git_blob':blob,'physical_source_matches_pinned_Git':True})
b['full_source_pointers']=out;b['selected43_existing_source_inventory']={'path':'campaign/items/dedup/overnight-2026-11-08/review/nat-reader/selected-declaration-inventory.json','SHA256':h((R/'campaign/items/dedup/overnight-2026-11-08/review/nat-reader/selected-declaration-inventory.json').read_bytes())}
(O/'candidate-dispositions.json').write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');(O/'input-bindings.json').write_text(json.dumps(b,indent=2)+'\n');print(json.dumps({'rows':len(d['rows']),'all_rows_have_current_source_and_record_pointers':True,'source_files_byte_Git_bound':len(out),'prospective':ref,'eligible_new_complete_implementation':0}))
