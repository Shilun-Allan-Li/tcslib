from pathlib import Path
import json,subprocess,hashlib,re,ast
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);H=lambda b:hashlib.sha256(b).hexdigest();base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';owner='TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean';head={123:'7c4b1a3e15b800cc4a98624f71a3b27458a41340',124:'cfa6a3ee327b03e601b25fd5f0535e85fd18f897'};raw={0:g('show',base+':'+owner).decode()}
for n,h in head.items():
 assert g('diff','--name-only',base,h,'--','*.lean').decode().splitlines()==[owner];raw[n]=g('show',h+':'+owner).decode();(O/str(n)/'OWNER-HEAD.lean.txt').write_text(raw[n]);(O/str(n)/'OWNER-BASE.lean.txt').write_text(raw[0])
helper=R/'devtools/seyoon/declfreeze.py';tree=ast.parse(helper.read_text());allowed={'KW','DECL','ANON','STOP','SCOPE'};nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(t,ast.Name) and t.id in allowed for t in n.targets)];ns={'re':re};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper),'exec'),ns);C={n:{name:(priv,t) for name,priv,t in ns['chunks'](s)} for n,s in raw.items()};five=['Turing.step_output_prefix','Turing.runFrom_output_prefix','Turing.runFrom_output_extends','Turing.runFrom_of_halted','Turing.state_isSome_of_runFrom'];three=['Turing.SafeRun.zero','Turing.SafeRun.cons','Turing.SafeRun.trans'];new='Turing.safeRun_iff_segment';results=[]
for n,names in [(123,five),(124,three)]:
 A=C[0];B=C[n];assert set(B)-set(A)==({new} if n==124 else set());assert not set(A)-set(B);assert sorted(k for k in A if A[k]!=B[k])==sorted(names);rev=raw[n];checks=[]
 for name in names:
  a=A[name][1];b=B[name][1];assert a[:a.index(':=')]==b[:b.index(':=')];assert rev.count(b)==1;rev=rev.replace(b,a,1);checks.append({'name':name,'literal_doc_header_before_outer_assignment_exact':True,'BASE_chunk_sha256':H(a.encode()),'HEAD_chunk_sha256':H(b.encode())})
 if n==124:
  helpertext=B[new][1];assert B[new][0] and rev.count(helpertext+'\n\n')==1;rev=rev.replace(helpertext+'\n\n','',1)
 assert rev==raw[0];pub=lambda d:sum(not x[0] for x in d.values());priv=lambda d:sum(x[0] for x in d.values());result={'gate':n,'BASE':base,'HEAD':head[n],'owner':owner,'BASE_Git_blob':g('rev-parse',base+':'+owner).decode().strip(),'HEAD_Git_blob':g('rev-parse',head[n]+':'+owner).decode().strip(),'BASE_sha256':H(raw[0].encode()),'HEAD_sha256':H(raw[n].encode()),'public':[pub(A),pub(B)],'private':[priv(A),priv(B)],'all_existing_names_headers_docs_definitions_imports_attributes_and_other_bytes_exact':True,'exact_reversal_recovers_BASE':True,'changed_roots':checks,'new_private_only':new if n==124 else None};(O/str(n)/'SOURCE-VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');results.append(result)
# Pure text only: the independent source transformations commute, no Git merge object or Lean run.
combined1=raw[124]
for name in five:assert combined1.count(C[0][name][1])==1;combined1=combined1.replace(C[0][name][1],C[123][name][1],1)
combined2=raw[123]
for name in three:
 b=C[124][name][1]
 if name=='Turing.SafeRun.zero':b=C[124][new][1]+'\n\n'+b
 assert combined2.count(C[0][name][1])==1;combined2=combined2.replace(C[0][name][1],b,1)
assert combined1==combined2;(O/'COMBINED-TEXT-HYPOTHESIS.lean.txt').write_text(combined1)
matched=[]
for rev in ['50998b88fda9f5c9ae949735b70bc4c14b3a19fe','b9e76f4c9db3049e6e56b838715aedc945abd258']:
 g('cat-file','-e',rev+'^{commit}');b=g('show',rev+':'+owner);matched.append({'local_validation_commit':rev,'owner_blob':g('rev-parse',rev+':'+owner).decode().strip(),'owner_sha256':H(b),'owner_equals_combined_text':b==combined1.encode(),'not_a_campaign_merge_or_standalone_execution_claim':True})
(O/'SHARED-OWNER-COMMUTATIVITY.json').write_text(json.dumps({'owner':owner,'source_transformations_disjoint_and_commute_exactly':True,'combined_text_sha256':H(combined1.encode()),'combined_source_is_private_hypothesis_not_a_new_Git_commit':True,'local_validation_owner_comparisons':matched,'standalone_replay_snapshots_must_not_be_spliced':True,'after_first_merge_second_requires_actual_merged_owner_and_current_context_validation':'Use an exact passed whole-tree match or an actual merged-owner/downstream replay; pure text commutativity is not an execution certificate.'},indent=2)+'\n');print(json.dumps({'source_checks':[{k:r[k] for k in ['gate','public','private','HEAD_sha256','exact_reversal_recovers_BASE']} for r in results],'combined_owner_sha256':H(combined1.encode()),'local_validation_comparisons':matched},indent=2))
