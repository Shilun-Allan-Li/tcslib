from pathlib import Path
import subprocess,json,hashlib,re,ast
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);H=lambda b:hashlib.sha256(b).hexdigest()
helper=R/'devtools/seyoon/declfreeze.py';tree=ast.parse(helper.read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};ns={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),str(helper),'exec'),ns)
old=json.loads(Path('/private/tmp/ab34-gate129-preflight/CURRENT-ALIGNMENT-BINDING.json').read_text());heads={}
for ref in ['origin/pr/251','origin/pr/248']:
 heads[ref]=g('rev-parse',ref+'^{commit}').decode().strip();g('cat-file','-e',heads[ref]+'^{commit}')
rows=[];(O/'gate129-alignment').mkdir(exist_ok=True)
for name,path in [('Turing.FinTM.controlAction_def','TCSlib/Complexity/TuringMachine/Simulation.lean'),('Turing.inputMoveAction_eq','TCSlib/Complexity/TuringMachine/Build/Catalog.lean'),('Turing.inputFoldTM_tr_bwd','TCSlib/Complexity/TuringMachine/Build/Scan.lean')]:
 src=g('show',heads['origin/pr/251']+':'+path);s=src.decode();cs={n:(private,c) for n,private,c in ns['chunks'](s)};assert name in cs;priv,chunk=cs[name];q=O/'gate129-alignment'/(name+'.lean.txt');q.write_text(chunk+'\n');blob=g('rev-parse',heads['origin/pr/251']+':'+path).decode().strip();g('cat-file','-e',blob)
 r={'name':name,'ref':'refs/remotes/origin/pr/251','source':heads['origin/pr/251'],'path':path,'owner_Git_blob':blob,'owner_SHA256':H(src),'source_line':s[:s.find(chunk)].count('\n')+1,'chunk_SHA256_without_capture_LF':H(chunk.encode()),'capture':str(q.relative_to(O)),'private':priv,'owner_Lean_exact_old_approved_alignment_source':src==g('show',old['approved_aligned_source']+':'+path),'reader_chunk_exact_old_approved_alignment_source':chunk=={n:c for n,p,c in ns['chunks'](g('show',old['approved_aligned_source']+':'+path).decode())}[name]}
 if name=='Turing.FinTM.controlAction_def':
  peer=g('show',heads['origin/pr/248']+':'+path);ps=peer.decode();pcs={n:(p,c) for n,p,c in ns['chunks'](ps)};ppriv,pchunk=pcs[name];pq=O/'gate129-alignment'/'peer-controlAction_def.lean.txt';pq.write_text(pchunk+'\n');pb=g('rev-parse',heads['origin/pr/248']+':'+path).decode().strip();g('cat-file','-e',pb)
  r['known_peer']={'ref':'refs/remotes/origin/pr/248','source':heads['origin/pr/248'],'path':path,'owner_Git_blob':pb,'owner_SHA256':H(peer),'source_line':ps[:ps.find(pchunk)].count('\n')+1,'chunk_SHA256_without_capture_LF':H(pchunk.encode()),'capture':str(pq.relative_to(O)),'complete_doc_name_statement_proof_byte_equal':chunk==pchunk,'same_original_peer_as_preflight':heads['origin/pr/248']==json.loads(Path('/private/tmp/ab34-gate129-preflight/STATEMENT-TWIN.json').read_text())['other_source']}
 rows.append(r)
assert all(r['reader_chunk_exact_old_approved_alignment_source'] for r in rows)
assert rows[0]['known_peer']['complete_doc_name_statement_proof_byte_equal']
result={'heads':heads,'original_aligned_source_from_prior_evidence':old['approved_aligned_source'],'three_readers':rows,'interpretation':'Current #251 three reader chunks equal the previously approved aligned source. Their owner files have later mechanical proof repairs, so full-owner equality is separately reported false. Its full controlAction_def doc/name/statement/proof chunk exactly equals the established #248 peer. This is a source-byte alignment check only; no Lean/metadata/replay execution, mergeability claim, peer merge assumption or naming decision.'}
(O/'GATE129-ALIGNMENT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
