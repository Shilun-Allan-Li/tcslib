from pathlib import Path
import json,hashlib,re,subprocess,os,collections
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');E=os.environ|{'GIT_OPTIONAL_LOCKS':'0'};HEAD='d64dff4fbef865d815c6a561ce8037ea1bae07a2';BASE='9b5dcf46408db681bcbc721930ef2203fa6bc47d';NAT='e16049ad20823b3e6abba171e328489746062080'
H=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git','-C',str(R),*a],env=E)
def save(n,a):(O/n).write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
def tree(pin):
 rows=[]
 for line in git('ls-tree','-r',pin).decode().splitlines():
  meta,path=line.split('\t',1)
  if path.endswith('.lean'):
   mode,kind,blob=meta.split();assert kind=='blob';rows.append((path,blob))
 assert len(rows)==1003
 raw=subprocess.check_output(['git','-C',str(R),'cat-file','--batch'],input=('\n'.join(b for _,b in rows)+'\n').encode(),env=E);at=0;data={};inventory=[]
 for path,blob in rows:
  en=raw.index(b'\n',at);h=raw[at:en].split();assert h[:2]==[blob.encode(),b'blob'];n=int(h[2]);body=raw[en+1:en+1+n];assert raw[en+1+n:en+2+n]==b'\n';at=en+2+n;data[path]=body.decode();inventory.append({'path':path,'blob':blob,'bytes':n,'sha256':H(body)})
 assert at==len(raw)
 return data,inventory
src,inv=tree(HEAD);base,binv=tree(BASE);nat,ninv=tree(NAT)
feowners=['TCSlib/Complexity/ClassNP/EXP.lean','TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean','TCSlib/Complexity/CookLevin/Hardness.lean','TCSlib/Complexity/TuringMachine/Build/InputCall.lean'];inp='TCSlib/Complexity/TuringMachine/Build/InputLength.lean';hard=feowners[2]
assert {p for p in src if src[p]!=base[p]}==set(feowners);assert src[inp]==base[inp]
assert {p for p in nat if nat[p]!=base[p]}=={'TCSlib/Complexity/TuringMachine/CodeSimulator.lean'}
# Exact nine complete slice/header freeze, including capture's explicit final LF.
C=R/'campaign/gates/121-fe-live1-cleanup/review';freeze=J(C/'source-freeze/SOURCE-FREEZE.json');assert len(freeze['targets'])==9
reverse={p:src[p] for p in feowners};slicechecks=[]
for x in freeze['targets']:
 assert x['BASE']['literal_header']==x['HEAD']['literal_header'];row={'path':x['path'],'name':x['name']}
 for side,data in [('BASE',base),('HEAD',src)]:
  m=x[side];sl=data[x['path']][m['source_start_offset']:m['source_end_offset']];cap=(C/m['full_chunk_capture']).read_text();assert H(sl.encode())==m['full_chunk_SHA256'] and cap==sl+'\n'
  row[side]={'source_slice_sha256':H(sl.encode()),'capture_sha256':H(cap.encode()),'slice_bytes':len(sl.encode()),'capture_bytes':len(cap.encode()),'capture_equals_slice_plus_one_LF':True}
 old=base[x['path']][x['BASE']['source_start_offset']:x['BASE']['source_end_offset']];new=src[x['path']][x['HEAD']['source_start_offset']:x['HEAD']['source_end_offset']];assert reverse[x['path']].count(new)==1;reverse[x['path']]=reverse[x['path']].replace(new,old);slicechecks.append(row)
assert all(reverse[p]==base[p] for p in feowners)
# Current 127 exactly two existing-reader line substitutions; literal rest unchanged.
p='TCSlib/Complexity/TuringMachine/CodeSimulator.lean';n=nat[p];old=base[p];before=['  change Nat.bit true (codeBitsNat w.length.bits + 1) = _','  simp only [Nat.bit, Bool.toNat_true]'];after=['  rw [← codeBitsNat_eq]','  simp only [Nat.bit_val, Bool.toNat_true]']
# The exact old source spelling is taken from the actual diff, never invented from a short source pin.
diff=git('diff','--no-ext-diff',BASE,NAT,'--',p).decode();minus=[x[1:] for x in diff.splitlines() if x.startswith('-') and not x.startswith('---')];plus=[x[1:] for x in diff.splitlines() if x.startswith('+') and not x.startswith('+++')];assert len(minus)==len(plus)==2
reverted=n
for a,b in zip(plus,minus):assert reverted.count(a)==1;reverted=reverted.replace(a,b)
assert reverted==old
# Complete snapshots of only the relevant owners/readers, as .lean.txt DATA.
readerpaths=['TCSlib/Complexity/TuringMachine/Deterministic.lean','TCSlib/Complexity/TuringMachine/Configuration.lean','TCSlib/Complexity/TuringMachine/StateRenaming.lean','TCSlib/Complexity/TuringMachine/CfgFacts.lean','TCSlib/Complexity/TuringMachine/Finite.lean','TCSlib/Complexity/TuringMachine/Build/Seam.lean','TCSlib/Complexity/TuringMachine/Build/Scan.lean','TCSlib/Complexity/TuringMachine/Build/Convention.lean']
captures=[]
for pin,data,paths in [(HEAD,src,feowners+[inp]+readerpaths),(NAT,nat,[p])]:
 for path in paths:
  dest=O/'source'/pin/(path+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(data[path]);captures.append({'source_commit':pin,'path':path,'capture':str(dest.relative_to(O)),'bytes':len(data[path].encode()),'sha256':H(data[path].encode())})
# Bounded census of every raw explicit step-closing line in five exposed/touched owners.
rawrows=[];idle=[]
for path in feowners+[inp]:
 decl='';lines=src[path].splitlines()
 for line,s in enumerate(lines,1):
  m=re.match(r'(?:(?:private|protected|noncomputable)\s+)*(?:def|lemma|theorem|abbrev)\s+(\S+)',s)
  if m:decl=m[1]
  if re.search(r'\b(?:unfold|delta|simp|simpa|dsimp)\b.*\b(?:MultiTapeTM\.)?step\b',s):rawrows.append({'path':path,'line':line,'declaration':decl,'text':s,'classification':'EXPLICIT_OPERATIONAL_STEP_READER_CANDIDATE_NOT_AUTOMATIC_COPY_OR_FIX'})
 assert path!=hard or len([x for x in rawrows if x['path']==path])==58
# Source-complete idle declarations, not an assertion that every operational body is now clear.
pat=re.compile(r'(?m)^(?:(?:private|protected|noncomputable)\s+)*(?:def|lemma|theorem|abbrev)\s+(\S+)')
ms=list(pat.finditer(src[hard]));idle5={'clCopy_idle','clCmp_idle','clWipe_idle','clFresh_idle','clInput_idle'}
for i,m in enumerate(ms):
 name=m[1]
 if not name.endswith('_idle'):continue
 en=ms[i+1].start() if i+1<len(ms) else len(src[hard]);chunk=src[hard][m.start():en]
 if not re.search(r'\b(?:unfold|simp|simpa)\b.*\bMultiTapeTM\.step\b',chunk):continue
 hit=next(x for x in rawrows if x['path']==hard and x['declaration']==name)
 idle.append({'name':name,'line':hit['line'],'direct_five_in_audit':name in idle5,'whole_chunk_sha256':H(chunk.encode()),'exact_current_source':HEAD+':'+hard,'proposal_prefix':'rw [MultiTapeTM.step_of_some hc]','limit':'For the seven extra idle sites, Action.apply/controlAction and other explicit foreign arguments also need complete-source review; prefix substitution alone is not a full-seal claim.'})
assert len(idle)==12 and {x['name'] for x in idle if x['direct_five_in_audit']}==idle5
# Static import closure witnesses show existing field readers are visible, without new imports.
adj={path:[v.replace('.','/')+'.lean' for l in s.splitlines() if l.startswith('import ') for v in l.split()[1:] if v.startswith('TCSlib.')] for path,s in src.items()}
def route(a,b):
 todo=collections.deque([a]);prev={a:None}
 while todo:
  q=todo.popleft()
  if q==b:
   ret=[]
   while q is not None:ret.append(q);q=prev[q]
   return list(reversed(ret))
  for v in adj.get(q,[]):
   if v not in prev:prev[v]=q;todo.append(v)
 return None
routes={path:{r:route(path,r) for r in readerpaths} for path in [hard,inp]}
assert routes[hard]['TCSlib/Complexity/TuringMachine/StateRenaming.lean']
assert routes[hard]['TCSlib/Complexity/TuringMachine/CfgFacts.lean'] is None
assert routes[inp]['TCSlib/Complexity/TuringMachine/Configuration.lean']
# Existing published transition reader absence is a bounded name/source check, not a mathematical impossibility.
scan=src['TCSlib/Complexity/TuringMachine/Build/Scan.lean'];fold_named=[{'path':path,'line':i,'text':l} for path,s in src.items() for i,l in enumerate(s.splitlines(),1) if re.match(r'^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+\S*inputFoldTM\S*',l)]
assert not any('tr_' in x['text'].split(':',1)[0] for x in fold_named)
save('source1003-freeze-and-import-bindings.json',{'pass':True,'source':HEAD,'BASE':BASE,'gate127_source':NAT,'all1003_FE_HEAD_sources':inv,'nine_full_slice_checks':slicechecks,'reverse_all9_recovers_entire_four_BASE_owners':True,'InputLength_full_source_BASE_exact':True,'gate127_exact_two_line_diff':diff,'gate127_reverse_two_lines_recovers_entire_BASE_owner':True,'full_captures':captures,'existing_import_routes':routes,'no_new_Lean_or_source_mutation':True})
save('uncapped-five-owner-step-census.json',{'source':HEAD,'scope':feowners+[inp],'raw_candidate_count':len(rawrows),'raw_candidates':rawrows,'count_by_owner':dict(collections.Counter(x['path'] for x in rawrows)),'same_named_idle_family12':idle,'limits':'All matches of the stated line-level pattern in these five whole pinned sources. Not an exhaustive semantic/library census, unique-copy count, new debt approval or proof every candidate has the same fix. Existing multi-line explicit arguments and implicit conversions require separate complete-source review.','inputFoldTM_named_theorems_across1003':fold_named,'minimal_missing_reader_observation':'No published named/generated .bwd tr reader was found. Scan535 definition rows are literal data; run_ofCfg645 is a different initialized forward-run contract. A new public row equation would be a human API decision if no larger existing contract removes the read.'})
print('PASS d64four-owner9chunk freeze, exact127two-line freeze, existing reader import routes; bounded raw90 step candidates /Hardness12 idle sites')
