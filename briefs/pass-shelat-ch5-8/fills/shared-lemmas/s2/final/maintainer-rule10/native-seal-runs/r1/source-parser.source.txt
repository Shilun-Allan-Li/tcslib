#!/usr/bin/env python3
"""Own static Gate06 declaration comparator. No Lean or repository writes."""
from pathlib import Path
import argparse, subprocess, json, re, hashlib, collections, csv, io
BASE='c7d8753a548ced71c1e1ea70e012c365af5c2171'
HEAD='e9d64158461bfe24ddc88ab885bc4017899b4c16'
G06=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
MAIN=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
R2=MAIN/'briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2'
HIST=MAIN/'briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r2/r6c'
def sha(x):return hashlib.sha256(x if isinstance(x,bytes) else x.encode()).hexdigest()
def git(rev,path):
 p=subprocess.run(['git','show',f'{rev}:{path}'],cwd=G06,capture_output=True)
 return p.stdout.decode() if p.returncode==0 else None
# Keep every non-comment byte, including strings and quoted identifiers, so code hashes
# cannot hide changes in formulas or literal values.
def no_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i] in ['"','«']:
   close='"' if s[i]=='"' else '»';j=i+1
   while j<len(s):
    if close=='"' and s[j]=='\\':j+=2;continue
    if s[j]==close:j+=1;break
    j+=1
   out.append(s[i:j]);i=j
  else:out.append(s[i]);i+=1
 return ''.join(out)
# Mask comments without shifting line/column positions; declaration command detection
# therefore ignores theorem-looking words inside comments.
def mask_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):out.append('  ');depth+=1;i+=2
   elif s.startswith('-/',i):out.append('  ');depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):out.append('  ');depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.append(' '*(j-i));i=j
  elif s[i] in ['"','«']:
   close='"' if s[i]=='"' else '»';j=i+1
   while j<len(s):
    if close=='"' and s[j]=='\\':j+=2;continue
    if s[j]==close:j+=1;break
    j+=1
   out.append(s[i:j]);i=j
  else:out.append(s[i]);i+=1
 return ''.join(out)
DECL=re.compile(r'^(?P<indent>\s*)(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*(?P<kind>theorem|lemma|def|instance|structure|inductive|abbrev|class|example)\b\s*(?P<name>[^\s(:{\[]*)')
BOUND=re.compile(r'^(?:namespace|section|end|variable|variables|include|omit|open|attribute|set_option|export|local|scoped|syntax|macro|elab|initialize|builtin_initialize|mutual)\b|^@\[')
def parse(s):
 raw=s.splitlines(keepends=True);masked=mask_comments(s).splitlines(keepends=True);decls=[];stack=[];contexts=[]
 for i,l in enumerate(masked):
  # Only column-zero scope commands. Indented tactic "end"s are not scopes.
  if l.startswith('namespace '):
   name=l.split()[1];stack.append(('namespace',name));contexts.append(l.strip())
  elif re.match(r'^(?:noncomputable\s+)?section(?:\s|$)',l):
   xs=l.split();stack.append(('section',xs[-1] if len(xs)>1 else ''));contexts.append(l.strip())
  elif re.match(r'^end(?:\s|$)',l):
   if stack:stack.pop()
   contexts.append(l.strip())
  elif re.match(r'^(variable|variables|include|omit|open|attribute|set_option)\b',l):
   contexts.append(l.strip())
  m=DECL.match(l)
  if not m:continue
  indent=len(m['indent']);name=m['name'];ns='.'.join(v for k,v in stack if k=='namespace')
  canonical=name[len('_root_.'):] if name.startswith('_root_.') else (ns+'.'+name if ns else name)
  decls.append({'name':name,'canonical':canonical,'kind':m['kind'],'start':i+1,'indent':indent,
                'scope_stack':list(stack),'context_commands':list(contexts)})
 for d in decls:
  i=d['start'];end=len(raw)
  for j in range(i,len(raw)):
   line=masked[j];r=raw[j]
   nonblank=line.strip()
   # A top-level docstring/section-doc or command/attribute starts the next declaration's envelope.
   same_or_less=(len(r)-len(r.lstrip()))<=d['indent']
   mm=DECL.match(line)
   if same_or_less and ((mm and len(mm['indent'])<=d['indent']) or
                        (nonblank and BOUND.match(line.lstrip())) or
                        r.lstrip().startswith(('/--','/-!'))):
    end=j;break
  while end>d['start'] and not raw[end-1].strip():end-=1
  d['end']=end;d['raw']=''.join(raw[d['start']-1:end]);d['code']=no_comments(d['raw'])
  # Preserve whitespace-bearing code separately from a token fallback.
  d['tokens']=re.findall(r'«[^»]*»|"(?:\\.|[^"\\])*"|[^\s]+',d['code'])
 return decls
def split_tsv(line):return re.split(r'\t|\\t',line.rstrip('\n'))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 pins=json.loads((R2/'pins.json').read_text());assert pins['base']==BASE and pins['head']==HEAD
 progress_path=R2/'runs-v3/survey-progress.json';progress_bytes=progress_path.read_bytes();progress=json.loads(progress_bytes)
 prior=[]
 for l in (R2/'inherited-observations/observations.tsv').read_text().splitlines()[1:]:
  xs=split_tsv(l);prior.append((xs[0],xs[1]))
 prior=set(prior)
 histdecl=[]
 for i,l in enumerate((HIST/'cleanup-b-decls.tsv').read_text().splitlines(),1):
  xs=split_tsv(l)
  if len(xs)>=2:histdecl.append((i,xs[0],xs[1]))
 histrows=[]
 for i,l in enumerate((HIST/'cleanup-b.tsv').read_text().splitlines(),1):
  xs=split_tsv(l)
  if len(xs)>=4:histrows.append((i,xs[2],re.sub(r'^(?:theorem|lemma|def|instance|structure|inductive|abbrev|class)\s+','',xs[3])))
 rows=[];excluded_prior=[];unmapped=[]
 for module in progress:
  path=module['module'].replace('.','/')+'.lean'
  if not module.get('valid_harness'):continue
  errs=module.get('errors',[])
  if not errs:continue
  logs=Path(module['attempt_log']).read_text().splitlines()
  bydecl=collections.defaultdict(list)
  for e in errs:bydecl[(e.get('declaration_start'),e.get('source_name'))].append(e)
  old=git(BASE,path);new=git(HEAD,path);assert new is not None
  hd=parse(new);bd=parse(old) if old is not None else []
  oldmap=collections.defaultdict(list)
  for d in bd:oldmap[(d['kind'],d['canonical'])].append(d)
  for (start,name),es in bydecl.items():
   if (path,name) in prior:
    excluded_prior.append({'file':path,'name':name,'diagnostics':len(es),'link':'inherited-observations/observations.tsv'})
    continue
   hs=[d for d in hd if d['start']==start and d['name']==name]
   if len(hs)!=1:
    unmapped.append({'file':path,'name':name,'start':start,'errors':es,'candidates':[(d['start'],d['name']) for d in hd if d['name']==name]});continue
   h=hs[0];bs=oldmap[(h['kind'],h['canonical'])]
   # Fall back only for investigation; classification remains ambiguous if the namespace changed.
   fallback=False
   if not bs:
    bs=[d for d in bd if d['name']==name and d['kind']==h['kind']];fallback=bool(bs)
   b=bs[0] if len(bs)==1 else None
   entry={'module':module['module'],'file':path,'name':name,'canonical':h['canonical'],'kind':h['kind'],
          'head_range':[h['start'],h['end']],'head_file_sha256':sha(new),'head_raw_sha256':sha(h['raw']),
          'head_code_sha256':sha(h['code']),'base_file_sha256':sha(old) if old is not None else None,
          'base_range':[b['start'],b['end']] if b else None,'base_raw_sha256':sha(b['raw']) if b else None,
          'base_code_sha256':sha(b['code']) if b else None,
          'preliminary_touched':any(e.get('touched_by_source_name') for e in es),
          'diagnostics':len(es),'probe_lines':[e['probe_line'] for e in es],
          'source_lines':[e.get('source_line') for e in es],'log':module['attempt_log'],'log_sha256':sha(Path(module['attempt_log']).read_bytes()),
          'valid_harness':module['valid_harness'],'source_base_seal_rerun':False,
          'namespace_fallback':fallback,'head_scope_stack':h['scope_stack'],'base_scope_stack':b['scope_stack'] if b else None}
   entry['log_line_numbers']=[i+1 for i,l in enumerate(logs) if any(re.search(r'\.lean:'+str(e['probe_line'])+':'+str(e['probe_column'])+r': error',l) for e in es)]
   if old is None:status='NEW_FILE'
   elif b is None:status='AMBIGUOUS_MISSING_OR_DUPLICATE_BASE_DECL'
   elif fallback or h['scope_stack']!=b['scope_stack']:status='AMBIGUOUS_SCOPE'
   elif h['raw']==b['raw']:status='RAW_IDENTICAL_CANDIDATE'
   elif h['code']==b['code']:status='COMMENT_STRIPPED_CODE_IDENTICAL_CANDIDATE'
   elif h['tokens']==b['tokens']:status='AMBIGUOUS_WHITESPACE_ONLY'
   else:status='CHANGED_CODE'
   entry['classification']=status
   variants={name,h['canonical'],re.sub(r'^_root_\.','',name)}
   # Historical inventories mix fully qualified and source-spelled declarations.
   entry['historical_decl_exact_rows']=[i for i,p,n in histdecl if p==path and n in variants]
   entry['historical_seal_exact_rows']=[i for i,p,n in histrows if p==path and n in variants]
   entry['historical_decl_suffix_candidates']=[(i,n) for i,p,n in histdecl if p==path and n not in variants and any(n.endswith('.'+v) or v.endswith('.'+n) for v in variants)]
   entry['historical_seal_suffix_candidates']=[(i,n) for i,p,n in histrows if p==path and n not in variants and any(n.endswith('.'+v) or v.endswith('.'+n) for v in variants)]
   if b:
    import difflib
    entry['raw_diff']=''.join(difflib.unified_diff(b['raw'].splitlines(keepends=True),h['raw'].splitlines(keepends=True),n=2))
   rows.append(entry)
 result={'schema':'inherited-full-survey-review/preliminary-v1','base':BASE,'head':HEAD,
         'progress_file':str(progress_path),'progress_sha256':sha(progress_bytes),'modules_completed':len(progress),
         'valid_modules':sum(bool(r.get('valid_harness')) for r in progress),
         'snapshot_labels':[r['label'] for r in progress],'linked_prior':excluded_prior,'unmapped':unmapped,'declarations':rows,
         'counts':dict(collections.Counter(r['classification'] for r in rows))}
 args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
 print('MODULES',len(progress),'CLASSIFICATIONS',result['counts'],'prior decl/diag',len(excluded_prior),sum(x['diagnostics'] for x in excluded_prior),'unmapped',unmapped)
 for r in rows:
  print(r['classification'],str(r['preliminary_touched'])[0],r['file'].split('TCSlib/')[-1],r['name'],r['base_range'],r['head_range'],'diag',r['diagnostics'],'hist',r['historical_decl_exact_rows'],r['historical_seal_exact_rows'])
if __name__=='__main__':main()
