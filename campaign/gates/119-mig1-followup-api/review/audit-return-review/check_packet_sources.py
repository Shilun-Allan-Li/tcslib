from pathlib import Path,PurePosixPath
import datetime,hashlib,json,re,subprocess
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G=R/'campaign/gates/119-mig1-followup-api';OUT=G/'review/audit-return-review';SCR=Path('/private/tmp/tcslib-g119-audit-return-yd2o4o0q');D=json.loads((G/'dispatch.json').read_text());commands=[]
def digest(b):return hashlib.sha256(b).hexdigest()
def git(args,root=R,allow=()):
 cmd=['git','-C',str(root),*args];p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE);commands.append(dict(command=cmd,exit=p.returncode,stdout_bytes=len(p.stdout),stdout_sha256=digest(p.stdout),stderr_utf8=p.stderr.decode()));assert p.returncode==0 or p.returncode in allow,(cmd,p.stderr.decode());return p.stdout,p.returncode
for rev in [D['lean'],D['records'],'3023dc1408c3d216fc07a7cbba9ae30135b861ed','1160c18f03fd318f0dec25738790935fa61379d4','626b1a81ddd33f4b0e0dabd4e874a16a0fe71724']:
 assert git(['rev-parse','--verify',rev+'^{commit}'])[0].decode().strip()==rev;git(['cat-file','-e',rev+'^{commit}'])
base='3023dc1408c3d216fc07a7cbba9ae30135b861ed';head=D['lean'];records=D['records'];git(['diff','--quiet','1160c18f03fd318f0dec25738790935fa61379d4',base,'--','*.lean']);git(['diff','--quiet','626b1a81ddd33f4b0e0dabd4e874a16a0fe71724',head,'--','*.lean']);git(['merge-base','--is-ancestor',base,head]);changed=git(['diff','--name-only',base,head,'--','*.lean'])[0].decode().splitlines();assert len(changed)==5
order=git(['show',records+':campaign/gates/119-mig1-followup-api/BUNDLE-FILES.txt'])[0].decode().splitlines();assert len(order)==len(set(order))==640
for path in order:
 pp=PurePosixPath(path);assert not pp.is_absolute() and '..' not in pp.parts and '\x00' not in path and '\n' not in path
queries=[(head if path.startswith('TCSlib/') else records)+':'+path for path in order]
p=subprocess.run(['git','-C',str(R),'cat-file','--batch'],input=('\n'.join(queries)+'\n').encode(),stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert p.returncode==0;batch=p.stdout;offset=0;blobs={};objects={}
for path in order:
 end=batch.index(b'\n',offset);parts=batch[offset:end].decode().split();assert len(parts)==3 and parts[1]=='blob';size=int(parts[2]);start=end+1;data=batch[start:start+size];assert batch[start+size:start+size+1]==b'\n';offset=start+size+1;data.decode('utf-8');blobs[path]=data;objects[path]=parts[0]
assert offset==len(batch)
bundle=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/stage/119-mig1-followup-api-final/119-mig1-followup-api-bundle.md');raw=bundle.read_bytes();raw.decode('utf-8');assert len(raw)==D['bytes'] and digest(raw)==D['sha256'];matches=list(re.finditer(rb'^## ===== ([^\n]+) =====\n\n',raw,re.M));assert len(matches)==640 and [m[1].decode() for m in matches]==order
entries=[];empty=[];json_count=0
for i,(path,match) in enumerate(zip(order,matches)):
 blob=blobs[path];rendered=blob if blob.endswith(b'\n') else blob+b'\n'
 if path.endswith(('.lean','.py')):rendered=b'```\n'+rendered+b'```\n'
 expected=b'## ===== '+path.encode()+b' =====\n\n'+rendered+(b'\n' if i+1<len(matches) else b'');actual=raw[match.start():matches[i+1].start() if i+1<len(matches) else len(raw)];assert actual==expected,path
 if not blob:empty.append(path)
 if path.endswith('.json'):json.loads(blob);json_count+=1
 entries.append(dict(path=path,pin=head if path.startswith('TCSlib/') else records,git_blob=objects[path],bytes=len(blob),sha256=digest(blob),rendered_segment_bytes=len(actual),exact_rendered_match=True))
assert json_count==184
# Source lexical count. Strings/comments are removed; no source or supplied scripts are executed.
def code_lines(text):
 depth=0;string=False;escape=False;out=[]
 for rawline in text.splitlines():
  line=[];i=0
  while i<len(rawline):
   c=rawline[i]
   if depth:
    if rawline.startswith('/-',i):depth+=1;i+=2
    elif rawline.startswith('-/',i):depth-=1;i+=2
    else:i+=1
    continue
   if string:
    if escape:escape=False
    elif c=='\\':escape=True
    elif c=='"':string=False
    line.append(' ');i+=1;continue
   if rawline.startswith('--',i):break
   if rawline.startswith('/-',i):depth=1;i+=2;continue
   if c=='"':string=True;line.append(' ');i+=1;continue
   line.append(c);i+=1
  out.append(''.join(line))
 assert depth==0
 return out
pat=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b(?:\s+([^\s(:{\[]+))?')
sourcefiles={path:blob.decode() for path,blob in blobs.items() if path.startswith('TCSlib/') and path.endswith('.lean')}
family={
'TCSlib/Complexity/TuringMachine/Finite.lean':['exists_first_entry_of_fixed'],
'TCSlib/Complexity/TuringMachine/Build/Loop.lean':['emCall_first_entry'],
'TCSlib/Complexity/TuringMachine/Build/Primitives.lean':['emitter_first_entry','catalogFirstEntry','splitEmbed_cut'],
'TCSlib/Complexity/TuringMachine/Build/Catalog.lean':['f2_catalogFirstEntry','f2_splitEmbed_cut'],
'TCSlib/Complexity/CookLevin/Hardness.lean':['clFirst','clBank_first','clCopy_first','clRow_first','clCmp_first'],
'TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean':['xr_firstArrival',"xr_firstArrival'"]}
rows=[];quotes=[]
for path,names in family.items():
 text=sourcefiles[path];rawlines=text.splitlines();decls=[]
 for n,line in enumerate(code_lines(text),1):
  m=pat.match(line)
  if m:decls.append(dict(line=n,kind=m[1],name=m[2] or '<anonymous>',private='private' in line.split(m[1],1)[0]))
 expected_counts={'Finite.lean':27,'Loop.lean':204,'Primitives.lean':288,'Catalog.lean':504,'Hardness.lean':544,'ExhaustiveReplay.lean':183};assert len(decls)==expected_counts[Path(path).name],(path,len(decls))
 for name in names:
  matches2=[d for d in decls if d['name'].rsplit('.',1)[-1]==name];assert len(matches2)==1;(d,)=matches2;start=d['line']-1;end=next((i for i in range(start+1,len(rawlines)) if rawlines[i].startswith(('/--','namespace ','end ')) or pat.match(code_lines(text)[i])),len(rawlines));block='\n'.join(rawlines[start:end]).rstrip()+'\n';quotes.append('## '+path+':'+str(d['line'])+' '+name+'\n\n```lean\n'+block+'```\n');rows.append(dict(path=path,name=name,line=d['line'],private=d['private'],family_file_members=len(names),source_authored_denominator=len(decls),block_sha256=digest(block.encode())))
assert len(rows)==14
(OUT/'packet-crosscheck.json').write_text(json.dumps(dict(source=head,records=records,bundle_path=str(bundle),bundle_bytes=len(raw),bundle_sha256=digest(raw),sections=len(order),all640_rendered_blobs_exact=True,all184_JSON_parse=True,empty_sections=empty,changed_Lean_files=changed,API_to_base_complete_Lean_tree_equal=True,source_reference_to_head_complete_Lean_tree_equal=True,entries=entries),indent=2)+'\n')
(OUT/'first-entry-family.json').write_text(json.dumps(dict(status='Verified14 semantic declaration members/lower bound; not an exhaustive census or14 new debt charges',members=rows,total=14,denominators='all authored source declarations, not screen-eligible declarations or compiler constants'),indent=2)+'\n');(OUT/'first-entry-source-quotes.md').write_text('\n'.join(quotes));(OUT/'read-only-Git-commands.json').write_text(json.dumps(commands,indent=2)+'\n');(OUT/'check_packet_sources.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps(dict(bundle='640 exact mixed-pin segments',JSON_files=json_count,family_members=len(rows),source_denominators={p:next(r['source_authored_denominator'] for r in rows if r['path']==p) for p in family},source_changed=len(changed)),indent=2))
