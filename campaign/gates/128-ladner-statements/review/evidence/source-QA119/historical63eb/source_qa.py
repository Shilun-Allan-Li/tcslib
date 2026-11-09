from pathlib import Path
import json,re,hashlib,subprocess,difflib,shutil
O=Path(__file__).parent;pin=json.loads((O/'PIN.json').read_text());W=Path(pin['source_worktree']);R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');git=lambda t,*a:subprocess.check_output(['git','-C',str(t),*a]);ladner='TCSlib/Complexity/Diagonalization/Ladner.lean';facade='TCSlib/Complexity/Diagonalization.lean'
def strip_lean_comments(s):
 out=[];comments=[];i=0;length=0
 while i<len(s):
  if s.startswith('--',i):
   start=i;stop=s.find('\n',i);stop=len(s) if stop<0 else stop;comments.append({'kind':'line','code_offset':length,'text':s[start:stop]});i=stop;continue
  if s.startswith('/-',i):
   start=i;kind='declaration_doc' if s.startswith('/--',i) else 'module_doc' if s.startswith('/-!',i) else 'block';depth=1;i+=2
   while depth:
    assert i<len(s),'unterminated block comment'
    if s.startswith('/-',i):depth+=1;i+=2
    elif s.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   comments.append({'kind':kind,'code_offset':length,'text':s[start:i]});out.append(' ');length+=1;continue
  if s[i]=='"':
   start=i;i+=1
   while i<len(s):
    if s[i]=='\\':i+=2;continue
    if s[i]=='"':i+=1;break
    i+=1
   else:raise AssertionError('unterminated string')
   chunk=s[start:i];out.append(chunk);length+=len(chunk);continue
  if s[i]=='«':
   start=i;stop=s.find('»',i+1);assert stop>=0;chunk=s[start:stop+1];out.append(chunk);length+=len(chunk);i=stop+1;continue
  char=re.match(r"'(?:\\.|[^\\'\n])'",s[i:]) if s[i]=="'" else None
  if char:chunk=char.group();out.append(chunk);i+=len(chunk);length+=len(chunk);continue
  out.append(s[i]);length+=1;i+=1
 return ''.join(out),comments
prototype=(O/'source/PROTOTYPE56c.lean.txt').read_text();head=(O/'source/HEAD'/(ladner+'.txt')).read_text();pc,pm=strip_lean_comments(prototype);hc,hm=strip_lean_comments(head);(O/'PROTOTYPE-comment-stripped-full-code.txt').write_text(pc);(O/'HEAD-comment-stripped-full-code.txt').write_text(hc);(O/'PROTOTYPE-code-token-string.txt').write_text(' '.join(pc.split())+'\n');(O/'HEAD-code-token-string.txt').write_text(' '.join(hc.split())+'\n');assert pc==hc,'literal full non-comment code strings differ';nondoc=lambda rows:[r for r in rows if r['kind'] not in {'declaration_doc','module_doc'}];assert nondoc(pm)==nondoc(hm),'ordinary comments differ';(O/'PROTOTYPE-comments.json').write_text(json.dumps(pm,indent=2)+'\n');(O/'HEAD-comments.json').write_text(json.dumps(hm,indent=2)+'\n');(O/'prototype-to-HEAD.diff').write_text(''.join(difflib.unified_diff(prototype.splitlines(keepends=True),head.splitlines(keepends=True),fromfile='PROTOTYPE56c',tofile='HEAD63eb')))
basefacade=(O/'source/BASE'/(facade+'.txt')).read_text();headfacade=(O/'source/HEAD'/(facade+'.txt')).read_text();bc,bm=strip_lean_comments(basefacade);fc,fm=strip_lean_comments(headfacade);added='import TCSlib.Complexity.Diagonalization.Ladner\n';assert fc.count(added)==1 and added not in bc;assert fc.replace(added,'',1)==bc;oldimports=re.findall(r'^import\s+[^\n]+$',bc,re.M);newimports=re.findall(r'^import\s+[^\n]+$',fc,re.M);assert [r for r in newimports if r!=added.rstrip()]==oldimports;(O/'facade-BASE-full-code.txt').write_text(bc);(O/'facade-HEAD-full-code.txt').write_text(fc);(O/'facade-HEAD-with-authorized-import-removed-full-code.txt').write_text(fc.replace(added,'',1));(O/'facade-BASE-to-HEAD.diff').write_text(''.join(difflib.unified_diff(basefacade.splitlines(keepends=True),headfacade.splitlines(keepends=True),fromfile='BASE-facade',tofile='HEAD-facade')))
pattern=re.compile(r'(?m)^(?:noncomputable\s+)?(def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque)\s+([^\s(:{\[]+)');matches=list(pattern.finditer(hc));decls=[]
for i,m in enumerate(matches):
 block=hc[m.start():matches[i+1].start() if i+1<len(matches) else len(hc)];sorries=len(re.findall(r'\bsorry\b',block));name=m.group(2);kind=m.group(1);role='definition' if kind=='def' else 'mathematical statement with explicit sorry' if sorries else 'packaging using admitted intermediate statement' if name=='ladner' else 'proved interface reading';decls.append({'name':'Complexity.'+name,'kind':kind,'role':role,'direct_sorry_tokens':sorries,'source_line':next(j for j,line in enumerate(head.splitlines(),1) if re.match(r'^(?:noncomputable\s+)?'+kind+r'\s+'+re.escape(name)+r'(?=\s|:|\()',line))})
assert len(decls)==17 and sum(r['kind']=='def' for r in decls)==4 and sum(r['role']=='proved interface reading' for r in decls)==6 and sum(r['direct_sorry_tokens'] for r in decls)==6 and sum(r['role'].startswith('packaging') for r in decls)==1;(O/'SOURCE-DECLARATIONS17.json').write_text(json.dumps(decls,indent=2)+'\n')
maps=[]
for side in ['BASE','HEAD']:
 data={}
 for line in git(W,'ls-tree','-r',pin[side]).decode().splitlines():
  field,path=line.split('\t',1)
  if path.endswith('.lean'):data[path]=field.split()[2]
 maps.append(data);(O/(side+'-ALL-LEAN-BLOBS.json')).write_text(json.dumps(data,indent=2)+'\n')
assert set(maps[1])-set(maps[0])=={ladner} and not set(maps[0])-set(maps[1]);changed=[p for p in maps[0] if maps[0][p]!=maps[1][p]];assert changed==[facade];root=git(W,'show',pin['HEAD']+':TCSlib.lean');assert root==git(W,'show',pin['BASE']+':TCSlib.lean');assert root.decode().splitlines()[39]=='import TCSlib.Complexity.Diagonalization'
context=O/'context';context.mkdir();planpath='campaign/items/roadmap3/PLAN.md';(context/'roadmap3-PLAN.md').write_bytes((R/planpath).read_bytes());shutil.copyfile('/private/tmp/ab34-ladner-statement-source/ADOPTION.json',context/'root-source-adoption.json');(context/'prototype-MANIFEST.json').write_bytes((R/'campaign/items/dedup/overnight-2026-11-08/review/ladner-v2/MANIFEST.json').read_bytes());result={'HEAD':pin['HEAD'],'BASE':pin['BASE'],'only_two_source_paths_changed':True,'new_Ladner_BASE_absent':True,'BASE_absence_is_not_a_fake_zero_length_file_or_blob':True,'all_preexisting_Lean_blob_paths':len(maps[0]),'HEAD_Lean_blob_paths':len(maps[1]),'only_modified_old_source':facade,'all_other_old_Lean_blobs_exact':True,'facade_code_recovers_BASE_after_only_authorized_import_removed':True,'all_existing_facade_imports_exact_order':True,'facade_old_declaration_surface_empty':not bool(pattern.search(bc)),'root_TCSlib_lean_byte_exact_BASE_HEAD':True,'root_export_line40_exact':True,'prototype_kind':'local frozen source file SHA256, not Git revision','prototype_sha256':pin['prototype_sha256'],'literal_full_comment_stripped_code_strings_equal':True,'non_doc_comments_exact':True,'prototype_change_scope':'declaration/module doc comments only','new_public_source_declarations':17,'new_definitions':4,'proved_interface_readings':6,'explicit_mathematical_sorries':6,'packaging_results':1,'mathematical_holes_filled':False,'no_Lean_AX_seal_or_screen_execution_claim':True,'authorization':'PLAN(f), accepted LD1-7 and parent explicit planned home/import/facade authorization; no new choice inferred.'};(O/'SOURCE-QA.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
