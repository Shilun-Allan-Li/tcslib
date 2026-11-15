from pathlib import Path
import json,re,collections
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/seq-zk-proof/tcslib-exchange')
d=json.loads((OUT/'proposed-resolutions.json').read_text())
touched=json.loads((ROOT/'evidence/rule10/final-repair/explicit/touched.json').read_text())
manual=[]
for r in d['review']:
 if r['review_classification']=='NEEDS_MANUAL_BINDING_LOCATION':
  assert r['head']=='this' and r['file'].endswith('ZeroKnowledge/Defs.lean') and r['line'] in [474,496]
  n=472 if r['line']==474 else 494
  source=(ROOT/r['file']).read_text().splitlines()[n-1]
  r.update(review_classification='LOCAL_ANONYMOUS_HAVE_PROOF',review_basis='Lean names an anonymous have proof this; exact nearest binder is retained.',binding_candidates=[{'line':n,'source':source}],manual_resolution=True)
 if r['review_classification']!='LOCAL_BINDER_PROOF_OR_LET':continue
 f=r['file'];ls=(ROOT/f).read_text().splitlines();decl=next(x for x in touched['files'][f]['declarations'] if x['start']<=r['line']<=x['end'])
 head=re.escape(r['head']);tok=re.compile(r'(?<![\w\u0027])'+head+r'(?![\w\u0027])');evidence=[]
 for i in range(decl['decl_line']-1,r['line']):
  s=ls[i];typ=None
  if re.search(r'\b(?:have|let|letI|set|by_cases)\s+'+head+r'(?![\w\u0027])',s):typ='named have/let/set/case binder'
  elif r['head']=='this' and re.search(r'\bhave\s*:=',s):typ='anonymous have binder'
  elif re.search(r'\b(?:intro|rintro|rename_i)\s+[^:]*',s) and tok.search(s.split(':=',1)[0]):typ='intro/pattern binder'
  elif re.match(r'^\s*\|',s) and '=>' in s and tok.search(s.split('=>',1)[0]):typ='induction/case branch binder'
  elif re.search(r'\b(?:obtain|rcases)\b',s) and ':=' in s and tok.search(s.split(':=',1)[0]):typ='obtained/destructured pattern binder'
  elif re.search(r'\b(?:obtain|rcases|cases|split_ifs)\b',s) and 'with' in s and tok.search(s.split('with',1)[1]):typ='case/destructure with binder'
  elif re.search(r'\bset\b',s) and 'with' in s and tok.search(s.split('with',1)[1]):typ='set equation binder'
  elif re.search(r'\bfun\b',s) and '=>' in s and tok.search(s.split('=>',1)[0].split('fun',1)[1]):typ='lambda binder'
  elif (i<decl['decl_line']+15 and re.search(head+r'\s*:',s)):typ='declaration hypothesis binder'
  if typ:evidence.append({'line':i+1,'source':s,'binding_kind':typ})
 if evidence:r['direct_binding_evidence']=evidence
 else:manual.append(r)
d['by_class']=dict(collections.Counter(r['review_classification'] for r in d['review']))
d['unlocated_items']=0
d['direct_binding_search_without_match']=len(manual)
(OUT/'resolved-review.json').write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
(OUT/'direct-binding-manual-review.json').write_text(json.dumps(manual,indent=2,ensure_ascii=False)+'\n')
print('Final classes',json.dumps(d['by_class'],ensure_ascii=False))
print('Direct binding evidence absent',len(manual))
for r in manual:print(r['file'],r['line'],r['head'],r['source_context'])
