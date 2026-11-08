from pathlib import Path
import json,gzip,re,collections,hashlib
P=Path('/private/tmp/mig-post234-final-head-accounting');ctx=json.loads((P/'context.json').read_text());B=Path(ctx['baseline_frozen_folder']);d=json.loads((P/'delta-base-head.json').read_text());wanted={r['name']for r in d['shared_field_changes']['typeExprSHA256']};types={}
for side,archive in [('Base',B/'Base.out.gz'),('Head',P/'Head-inventory.out.gz')]:
 t={}
 for l in gzip.open(archive,'rt'):
  if l.startswith('CENSUS|'):
   r=json.loads(l.split('|',1)[1])
   if r['name']in wanted:t[r['name']]=r['typeExpr']
 assert set(t)==wanted;types[side]=t
# Parser for Lean's trusted Name repr, to distinguish true Expr.const references from binder labels.
def parse_name(s,pos):
 while s[pos].isspace():pos+=1
 if s[pos]=='`':
  start=pos+1;pos=start;quoted=0
  while pos<len(s):
   ch=s[pos]
   if ch=='«':quoted+=1
   elif ch=='»':quoted-=1
   elif not quoted and(ch.isspace()or ch in '()[],'):break
   pos+=1
  assert pos>start;return s[start:pos],pos
 if s.startswith('Lean.Name.anonymous',pos):return '',pos+len('Lean.Name.anonymous')
 assert s[pos]=='(',s[pos:pos+140];pos+=1
 while s[pos].isspace():pos+=1
 m=re.match(r'Lean.Name.mk(Str|Num)\s+',s[pos:]);assert m,s[pos:pos+140];kind=m[1];pos+=m.end();parent,pos=parse_name(s,pos)
 while s[pos].isspace():pos+=1
 if kind=='Str':part,n=json.JSONDecoder().raw_decode(s[pos:]);assert isinstance(part,str);pos+=n
 else:
  m=re.match(r'\d+',s[pos:]);assert m;part=m[0];pos+=m.end()
 while s[pos].isspace():pos+=1
 assert s[pos]==')';return(parent+'.'if parent else'')+part,pos+1

def features(s):
 constants=collections.Counter();spans=[]
 for m in re.finditer(r'Lean.Expr.(const|lam|forallE|letE|proj)\s+',s):
  n,end=parse_name(s,m.end());kind=m[1];spans.append((m.end(),end,kind,n))
  if kind in ['const','proj']:constants[(kind,n)]+=1
 def norm(maskconst=False):
  out=[];pos=0
  for a,b,k,n in spans:
   out.append(s[pos:a]);out.append('NAME'if k not in ['const','proj']or maskconst else json.dumps(n,ensure_ascii=False));pos=b
  out.append(s[pos:]);return ''.join(out)
 return constants,norm(),norm(True)
cb=json.loads((P/'classified-census-base.json').read_text());ch=json.loads((P/'classified-census-head.json').read_text());exceptions=json.loads((P/'source-QA-data/approved-private-header-exceptions.json').read_text())['current_BASE_exceptions'];exnames={r['name']for r in exceptions};out=[]
for n in sorted(wanted):
 ac,an,am=features(types['Base'][n]);bc,bn,bm=features(types['Head'][n]);cat=ch[n]['category'];sourceName=ch[n]['source_name'];pub=not ch[n]['private'];effects=[]
 if an==bn:effects.append('binder Name spelling/representation only after exact Expr.const/Expr.proj name canonicalization')
 elif am==bm:effects.append('only constant/projection references change after binder-name canonicalization')
 else:effects.append('type expression structure changes beyond binder names and constant references')
 removed=[{'node':k[0],'name':k[1],'occurrences':v}for k,v in sorted((ac-bc).items())];added=[{'node':k[0],'name':k[1],'occurrences':v}for k,v in sorted((bc-ac).items())]
 if any(r['name'].startswith('_private.')for r in removed+added):effects.append('exact private constant reference change present; spelling is retained')
 if pub and sourceName:
  disposition='authored public type: deleted private ordinary matcher transport; bounded fresh kernel equality checked separately'
 elif sourceName in exnames:
  disposition='authored private approved header exception; acceptance and any transport equality are bound to exact sourceQA approval evidence, not blanket type equality'
 elif sourceName:
  disposition='authored private declaration: exact metadata difference retained; no blanket semantic/type equality claimed'
 else:
  disposition='generated/synthesized type from proof or deriving/compiler elaboration; exact metadata difference retained and not counted as written public API'
 out.append({'name':n,'owner':ch[n]['owner'],'kind':ch[n]['kind'],'private':ch[n]['private'],'internal':ch[n]['internal'],'source_category':cat,'source_name':sourceName,'effects':effects,'disposition':disposition,'base_type_sha256':hashlib.sha256(types['Base'][n].encode()).hexdigest(),'head_type_sha256':hashlib.sha256(types['Head'][n].encode()).hexdigest(),'constant_or_projection_references_removed':removed,'constant_or_projection_references_added':added,'same_type_after_only_binder_names':an==bn,'same_shape_after_masking_reference_names':am==bm,'exact_type_diff_file':'all94-exact-type-expression-differences.json','no_unproved_semantic_equality_inferred':not(pub and sourceName)})
(P/'all94-shared-type-change-dispositions.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');summary={'total':len(out),'nonprivate':sum(not r['private']for r in out),'authored_nonprivate':sum(not r['private']and r['source_name']is not None for r in out),'generated_nonprivate':sum(not r['private']and r['source_name']is None for r in out),'authored_private':sum(r['private']and r['source_name']is not None for r in out),'generated_private':sum(r['private']and r['source_name']is None for r in out),'approved_private_header_exceptions_present':sorted(r['source_name']for r in out if r['source_name']in exnames),'all94_have_exact_differences_classification_and_disposition':True,'effects':dict(collections.Counter(e for r in out for e in r['effects']))};(P/'all94-type-classification-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
for r in out:
 if r['source_name']is not None:print(r['source_name'],r['effects'],'REMOVED',r['constant_or_projection_references_removed'][:6],'ADDED',r['constant_or_projection_references_added'][:6])
