from pathlib import Path
import json,gzip,hashlib,re,collections,datetime
P=Path('/private/tmp/g106-r4-compiled-and-seals');ctx=json.loads((P/'context.json').read_text());std={'propext','Classical.choice','Quot.sound'}
def save(n,d):(P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def raw(name):
 b=gzip.decompress((P/(name+'.out.gz')).read_bytes());r=json.loads((P/(name+'-run.json')).read_text());assert r['exit']==r['errors']==r['warnings']==r['sorry_warnings']==0 and len(b)==r['raw_bytes']and hashlib.sha256(b).hexdigest()==r['raw_sha256'];return b
maps={};stats={};simps={}
for side in ['Base','Head']:
 b=raw(side+'-census');text=b.decode();c={};ax={};pub={}
 for mm in re.finditer(r'(?m)^CONSTANT (\S+) module=(\S+) kind=(\S+) private=(true|false) internal=(true|false)$',text):
  n,owner,kind,pr,inter=mm.groups();assert n not in c;c[n]={'owner':owner,'kind':kind,'private':pr=='true','internal':inter=='true'}
 for mm in re.finditer(r'(?m)^(ALLAX|PUBLICAX)\|([^|\n]+)\|(\[[\s\S]*?\])',text):
  tag,n,a=mm.groups();a=a[1:-1].strip();v=[]if not a else re.split(r',\s*',a);dest=ax if tag=='ALLAX'else pub;assert n not in dest;dest[n]=v
 assert set(c)==set(ax)and set(pub)=={n for n,d in c.items()if not d['private']}and all(pub[n]==ax[n]for n in pub)
 count=re.findall(r'(?m)^COMPLETE\|constants=(\d+)\|roots=(\d+)$',text);assert count==[(str(len(c)),'16')];assert len(re.findall(r'(?m)^CONTEXT_PRESENT\|',text))==5
 for n in c:c[n]['axioms']=ax[n]
 typ=raw(side+'-types');markers=list(re.finditer(rb'(?m)^TYPE_REPR\|([^|\n]+)\||^TYPECOMPLETE\|[^\n]*',typ));seen=set();totalbytes=0
 for i,mm in enumerate(markers):
  if mm.group(1)is None:continue
  n=mm.group(1).decode();assert n not in seen;seen.add(n);end=markers[i+1].start()if i+1<len(markers)else len(typ);payload=typ[mm.end():end].rstrip(b'\n');c[n]['type_repr']={'raw_archive':side+'-types.out.gz.base64.txt','block':len(seen)-1,'utf8_bytes':len(payload),'sha256':hashlib.sha256(payload).hexdigest()};totalbytes+=len(payload)
 assert seen==set(c)
 ci={};at={};sr=collections.defaultdict(list)
 for line in raw(side+'-ciattrs').decode().splitlines():
  if line.startswith(('CI|','ATTR|','SIMP_RULE|')):
   tag,n,j=line.split('|',2);d=json.loads(j)
   if tag=='SIMP_RULE':sr[n].append(d)
   else:
    dest=ci if tag=='CI'else at;assert n not in dest;dest[n]=d
 assert set(c)==set(ci)==set(at)
 for n in c:c[n]['ci']=ci[n];c[n]['attributes']=at[n]
 bad={n:r['axioms']for n,r in c.items()if not set(r['axioms'])<=std};owners={m:{'total':sum(r['owner']==m for r in c.values()),'private':sum(r['owner']==m and r['private']for r in c.values()),'nonprivate':sum(r['owner']==m and not r['private']for r in c.values())}for m in ctx['owners']}
 stats[side]={'all':len(c),'private':sum(r['private']for r in c.values()),'nonprivate':len(pub),'nonprivate_noninternal':sum(not r['private']and not r['internal']for r in c.values()),'kinds':dict(collections.Counter(r['kind']for r in c.values())),'owners':owners,'ALLAX':len(ax),'PUBLICAX':len(pub),'nonstandard_axiom_constants':len(bad),'nonstandard':bad,'full_type_payload_utf8_bytes':totalbytes,'owned_effective_simp_rules':sum(map(len,sr.values()))}
 maps[side]=c;simps[side]=dict(sr);save('map-'+side.lower()+'.json',{'source':ctx['base']if side=='Base'else ctx['source'],'census':c,'counts':stats[side],'no_theorem_values_rendered':True,'complete_raw_types_in_archives':True});save('effective-simp-'+side.lower()+'.json',dict(sr))
b,h=maps['Base'],maps['Head'];added=set(h)-set(b);removed=set(b)-set(h);shared=set(b)&set(h);fields=['owner','kind','private','internal','ci','attributes','axioms'];changes={k:[n for n in sorted(shared)if b[n][k]!=h[n][k]]for k in fields};types=[n for n in sorted(shared)if(b[n]['type_repr']['sha256'],b[n]['type_repr']['utf8_bytes'])!=(h[n]['type_repr']['sha256'],h[n]['type_repr']['utf8_bytes'])];publicB={n for n,r in b.items()if not r['private']};publicH={n for n,r in h.items()if not r['private']};publicchanges={k:[n for n in changes[k]if n in publicB or n in publicH]for k in fields};publicchanges['types']=[n for n in types if n in publicB or n in publicH]
assert publicB==publicH and all(not ns for ns in publicchanges.values()),publicchanges
assert stats['Base']['nonstandard']==stats['Head']['nonstandard']and all(h[n]['owner']=='TCSlib.Complexity.TuringMachine.Build.Primitives'for n in stats['Head']['nonstandard'])
assert all(h[n]['private']for n in added)and all(b[n]['private']for n in removed)
assert simps['Base']==simps['Head']
# Complete records retain exact names/fields. Compare types by complete raw byte hash/length,
# excluding side-specific archive/block addresses, never normalizing private names or expressions.
delta={'added':{n:h[n]for n in sorted(added)},'removed':{n:b[n]for n in sorted(removed)},'shared_field_changes':{k:[{'name':n,'base':b[n][k],'head':h[n][k]}for n in names]for k,names in changes.items()},'shared_type_changes':[{'name':n,'base':b[n]['type_repr'],'head':h[n]['type_repr']}for n in types],'no_public_name_or_field_or_type_change':True,'all_added_removed_private':True}
save('delta-base-head.json',delta)
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base':ctx['base'],'head':ctx['source'],'both_endpoints_fresh':True,'counts':stats,'added':len(added),'removed':len(removed),'shared':len(shared),'shared_field_change_counts':{k:len(v)for k,v in changes.items()},'shared_type_change_count':len(types),'public_field_change_counts':{k:len(v)for k,v in publicchanges.items()},'all_nonprivate_names_and_types_CI_attrs_AXIOMS_exact':True,'owned_simp_rules_exact':True,'simp_proofs_are_only_exact_declaration_references_not_theorem_values':True,'inherited_nonstandard_exact':True,'no_new_nonstandard_axiom_dependency':True,'current45_root_coverage_pending_separate_probe':True,'no_proof_value_equality_claim':True}
save('metadata-summary.json',result);print(json.dumps({k:v for k,v in result.items()if k!='counts'}|{'counts':{k:{a:v[a]for a in ['all','private','nonprivate','ALLAX','PUBLICAX','nonstandard_axiom_constants','owned_effective_simp_rules','full_type_payload_utf8_bytes']}for k,v in stats.items()}},indent=2))
