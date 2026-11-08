from pathlib import Path
import ast, re, sys, json, hashlib, collections, datetime
root=Path(__file__).resolve().parents[1]
helper=root/'reproduction-tools/copy-text-screen-v3.py'
tree=ast.parse(helper.read_text())
selected=[]
for node in tree.body:
 if isinstance(node,ast.FunctionDef) and node.name in {'strip','scopes','qualify','body'}: selected.append(node)
 elif isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id in {'DECL','SCOPE'} for t in node.targets): selected.append(node)
namespace={'re':re,'sys':sys}
exec(compile(ast.Module(body=selected,type_ignores=[]),str(helper)+'<span-functions-only>','exec'),namespace)
# This reproduces strip exactly while retaining original source coordinates.
def strip_mapping(src):
 out=[]; offsets=[]; i=0; depth=0; n=len(src)
 while i<n:
  if src.startswith('/-',i): depth+=1; i+=2; continue
  if depth and src.startswith('-/',i): depth-=1; i+=2; continue
  if depth: i+=1; continue
  if src.startswith('--',i):
   j=src.find('\n',i); i=n if j<0 else j; continue
  out.append(src[i]); offsets.append(i); i+=1
 return ''.join(out),offsets
binding=json.loads((root/'bindings/FULL-SCREEN-SOURCE-CAPTURES.json').read_text())
all_phases={}; parser_decl_rows={}
for phase in ['BASE','LADNER']:
 inputs=[row for row in binding['rows'] if row['phase']==phase]
 nbase=collections.Counter(Path(row['path']).name for row in inputs)
 output=[]; all_decl=[]
 for item in inputs:
  source=root/item['capture']; original=source.read_text(); stripped,offsets=strip_mapping(original)
  assert stripped==namespace['strip'](original)
  matches=list(namespace['DECL'].finditer(stripped)); events=namespace['scopes'](item['path'],stripped); found=[]
  for index,match in enumerate(matches):
   end=matches[index+1].start() if index+1<len(matches) else len(stripped)
   full=stripped[match.start():end]; normalized=re.sub(r'\s+','',namespace['body'](full)); ns=[n for o,n in events if o<=match.start()][-1]
   start_original=offsets[match.start()]; end_original=offsets[end] if end<len(offsets) else len(original)
   row={'path':item['path'],'source_capture':item['capture'],'source_sha256':item['sha256'],'parser_kind':'proof' if match.group(2) in ('theorem','lemma') else 'term','syntax_kind':match.group(2),'short_name':match.group(3),'namespace_qualified_name':namespace['qualify'](ns,match.group(3)),'stripped_start_offset':match.start(),'stripped_end_offset':end,'source_start_character':start_original,'source_end_character_exclusive':end_original,'source_start_line':original.count('\n',0,start_original)+1,'source_end_line':original.count('\n',0,max(start_original,end_original-1))+1,'normalized_body':normalized,'normalized_body_chars':len(normalized),'normalized_body_sha256':hashlib.sha256(normalized.encode()).hexdigest(),'meets_60_character_capture_threshold':len(normalized)>=60,'source_span_note':'The parser slice ends at next regex declaration or file end and may retain namespace/section/end/render tails. It is not asserted to be a Lean declaration boundary.'}
   all_decl.append(row)
   if len(normalized)>=60: found.append(row)
  shorts=collections.Counter(row['short_name'] for row in found);quals=collections.Counter(row['namespace_qualified_name'] for row in found); seen=collections.Counter()
  for row in found:
   if shorts[row['short_name']]==1: label_name=row['short_name']
   elif quals[row['namespace_qualified_name']]==1: label_name=row['namespace_qualified_name']
   else:
    seen[row['namespace_qualified_name']]+=1;label_name=row['namespace_qualified_name']+'#'+str(seen[row['namespace_qualified_name']])
   row['screen_label']=(Path(item['path']).name if nbase[Path(item['path']).name]==1 else item['path'])+'::'+label_name
   output.append(row)
 assert len({row['screen_label'] for row in output})==len(output)
 all_phases[phase]=output;parser_decl_rows[phase]=all_decl
 destination=root/'screen'/('mapped-'+phase+'-captures.json')
 destination.write_text(json.dumps({'operation':'Source-coordinate mapping only, no pair scoring, grams, lcs or tiled execution. Uses four exact parsing functions and two regexes extracted from the captured actual tool AST.','tool_sha256':hashlib.sha256(helper.read_bytes()).hexdigest(),'source_population':len(inputs),'screened_parser_captures':len(output),'all_parser_declaration_matches':len(all_decl),'full_rows':[{k:v for k,v in row.items() if k!='normalized_body'} for row in output],'normalized_body_materialization':{'all_rows_retained_uncapped':True,'literal_source':'Each source_capture contains the entire literal source. Character/stripped offsets, exact captured strip/body functions, full normalized-body length and SHA256 reconstruct every capture losslessly. No copied body-string duplication is needed in this index.','expression':'re.sub(r\"\\s+\", \"\", body(strip(full_source)[stripped_start_offset:stripped_end_offset]))','delta_pair_endpoint_bodies':'Full normalized bodies and literal source spans for all actual NEW/GONE/changed-score endpoint captures will additionally be supplied with dispositions.'},'not_interface_declaration_count':True},ensure_ascii=False,indent=2)+'\n')
base={r['screen_label']:r for r in all_phases['BASE']};head={r['screen_label']:r for r in all_phases['LADNER']}
old_delta=[]
for label,row in base.items():
 other=head.get(label)
 if other is None or any(row[k]!=other[k] for k in ['path','parser_kind','normalized_body','namespace_qualified_name']): old_delta.append(label)
new=[head[label] for label in sorted(set(head)-set(base))]
assert not old_delta
assert all(r['path']=='TCSlib/Complexity/Diagonalization/Ladner.lean' for r in new)
summary={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'operation':'Pure source parser/capture mapping; no new copy-screen pair computation, Lean or helper jobs.','tool_sha256':hashlib.sha256(helper.read_bytes()).hexdigest(),'BASE_population':48,'LADNER_population':49,'BASE_parser_captures':len(base),'LADNER_parser_captures':len(head),'all_old_parser_label_kind_body_rows_exact':not old_delta,'changed_or_missing_old_capture_labels':old_delta,'new_screened_parser_captures':[{k:r[k] for k in ['screen_label','path','source_start_line','source_end_line','namespace_qualified_name','normalized_body_chars','normalized_body_sha256']} for r in new],'all17_new_owner_parser_matches':[{k:r[k] for k in ['short_name','namespace_qualified_name','source_start_line','source_end_line','normalized_body_chars','meets_60_character_capture_threshold']} for r in parser_decl_rows['LADNER'] if r['path']=='TCSlib/Complexity/Diagonalization/Ladner.lean'],'limits':['Actual root screen output is still required for every pair/score/disposition. This does not report pair results.','Parser spans may include structural tails and do not identify trusted-interface declarations by themselves.','Full literal sources and character coordinates reconstruct every mapped capture without truncation.']}
(root/'screen/CAPTURE-MAPPING-SUMMARY.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['BASE_population','LADNER_population','BASE_parser_captures','LADNER_parser_captures','all_old_parser_label_kind_body_rows_exact','new_screened_parser_captures']}))
