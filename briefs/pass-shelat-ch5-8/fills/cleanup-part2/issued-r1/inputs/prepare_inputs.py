#!/usr/bin/env python3
"""Own static cleanup-input preparation. No native/processes except read-only Git."""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib
import heapq
import importlib.util
import json
import re
import subprocess

OUT = Path(__file__).resolve().parent
PREP = OUT.parent
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
ANCESTOR = '1aa5506f58f77c215e56d24311ec33bd931cacf1'
OWN_PARSER = PREP/'review-inventory/source_inventory.py'
OWN_PARSER_SHA = 'ab2da32ecf903305a60bcde844f81d58c19370daaa068c83bddd217845bc7019'
INPUTS = {}
OUTPUTS = []


def sha(data): return hashlib.sha256(data).hexdigest()


def git(*args):
    return subprocess.run(['git','-C',str(MAIN),*args],check=True,
                          stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout


def read(path):
    path=Path(path); data=path.read_bytes()
    INPUTS[str(path)]={'bytes':len(data),'sha256':sha(data)}
    return data


def save(path,data):
    path=OUT/path
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('xb') as f:f.write(data)
    OUTPUTS.append({'path':str(path.relative_to(OUT)),'bytes':len(data),'sha256':sha(data)})


def jsave(path,data): save(path,(json.dumps(data,indent=2)+'\n').encode())


def linesave(path,items): save(path,(''.join(x+'\n' for x in items)).encode())


def main():
    assert sha(read(OWN_PARSER))==OWN_PARSER_SHA
    spec=importlib.util.spec_from_file_location('own_frozen_parser',OWN_PARSER)
    parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
    # A Finset cardinality line such as #G.edgeFinset is part of a statement,
    # not a Lean #command. Restrict this inherited lexical boundary accordingly.
    parser.CMD=re.compile(parser.CMD.pattern.replace(
        '|#|', '|#(?:check|check_failure|print|eval|reduce|synth|guard|guard_msgs|exit|help|where|lint|find|min_imports|adaptation_note)\\b|'))
    scope=json.loads(read(PREP/'review-scope/scope-review.json'))
    read(PREP/'review-scope/scope-review.md')
    assert scope['post_S2_source_commit']==ANCESTOR
    n=json.loads(read(PREP/'review-inventory/N-deferred-groups.json'))
    owner_rows=json.loads(read(PREP/'review-inventory/final-ownership-files.json'))
    assert n['post_s2_head']==ANCESTOR
    records_head=git('rev-parse','HEAD').decode().strip()
    tree=git('rev-parse',ANCESTOR+':TCSlib').decode().strip()
    assert git('rev-parse','HEAD:TCSlib').decode().strip()==tree
    entries=git('ls-tree','-rz',ANCESTOR,'--','TCSlib','TCSlib.lean','audits/pass-shelat/Checks.lean').split(b'\0')
    source={}
    for entry in entries:
        if not entry:continue
        metadata,path_b=entry.split(b'\t',1);path=path_b.decode()
        if not path.endswith('.lean'):continue
        data=(MAIN/path).read_bytes();blob=metadata.split()[2].decode()
        assert hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()==blob,('live source drift',path)
        module=path.removesuffix('.lean').replace('/','.')
        assert module not in source
        source[module]={'path':path,'data':data,'blob':blob,'sha256':sha(data),
                        'clean':parser.mask(data.decode()),'imports':[]}
    path_module={v['path']:k for k,v in source.items()}
    # Plain source imports are the complete import form at this pinned source.
    graph={m:set() for m in source};external=defaultdict(list)
    import_re=re.compile(r'^\s*import\s+(.+?)\s*$')
    for module,v in source.items():
        for line_no,line in enumerate(v['clean'].splitlines(),1):
            match=import_re.match(line)
            if not match:
                if re.match(r'^\s*(?:public|private|meta)\s+import\b',line):
                    raise ValueError('unsupported import form at '+v['path']+':'+str(line_no))
                continue
            for name in match.group(1).split():
                assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',name),(module,line_no,name)
                v['imports'].append({'line':line_no,'module':name,'local':name in source})
                if name in source:graph[module].add(name)
                else:
                    assert not name.startswith(('TCSlib.','audits.')),('missing local import',module,name)
                    external[name].append({'module':module,'path':v['path'],'line':line_no})
    reverse={m:set() for m in graph}
    for m,ds in graph.items():
        for d in ds:reverse[d].add(m)
    def closure(seeds,edges):
        seen=set(seeds);stack=list(seeds)
        while stack:
            for nxt in edges[stack.pop()]:
                if nxt not in seen:seen.add(nxt);stack.append(nxt)
        return seen
    def topo(selected):
        degrees={m:len(graph[m]&selected) for m in selected}
        queue=[m for m,n in degrees.items() if n==0];heapq.heapify(queue);order=[]
        while queue:
            m=heapq.heappop(queue);order.append(m)
            for child in sorted(reverse[m]&selected):
                degrees[child]-=1
                if degrees[child]==0:heapq.heappush(queue,child)
        if len(order)!=len(selected):raise ValueError('local import cycle: '+repr(sorted(m for m,n in degrees.items() if n)))
        positions={m:i for i,m in enumerate(order)}
        assert all(positions[d]<positions[m] for m in selected for d in graph[m]&selected)
        return order
    topo(set(graph)) # Detect cycles even outside the selected replay scopes.
    # Validate every directly imported external module against installed primary sources.
    toolchain=read(MAIN/'lean-toolchain').decode().strip()
    lake_manifest=json.loads(read(MAIN/'lake-manifest.json'))
    assert toolchain=='leanprover/lean4:v4.25.0'
    core=Path('/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean')
    package_roots=sorted(p for p in (MAIN/'.lake/packages').iterdir() if p.is_dir())
    external_rows=[]
    for name,sites in sorted(external.items()):
        rel=Path(name.replace('.','/')+'.lean')
        candidates=[r/rel for r in [core,*package_roots] if (r/rel).is_file()]
        assert len(candidates)==1,('missing/ambiguous external source',name,[str(p) for p in candidates])
        p=candidates[0];data=p.read_bytes()
        external_rows.append({'module':name,'path':str(p),'bytes':len(data),'sha256':sha(data),'sites':sites})
    reasons=defaultdict(set)
    def consume(path,reason):
        assert path in path_module,('unknown consumer',path)
        assert path!='TCSlib.lean' and not path.startswith('audits/')
        reasons[path].add(reason)
    for row in owner_rows:consume(row['path'],'J_N_OBSERVATION_OWNER')
    for group,rows in scope['A_remaining_source_keys'].items():
        for row in rows:consume(row[0],'A_'+group)
    for row in scope['B_owner_and_26_consumer_files']:consume(row['path'],'B_DL17')
    for row in scope['F_remaining']:consume(row['path'],'F_ORBIT_ZERO')
    for row in scope['M_recommended_closed_scope']:consume(row[0],'M_CLOSED_MATHLIB_SCOPE')
    for group in ['G7','G10','G13','G18','G22','G23','G25']:
        for row in n['groups'][group]['members']:
            if row['role']=='consumer':consume(row['path'],'N_'+group)
    # E/K/L are stated in scope-review.md; the JSON records source hashes but no E/K/L key arrays.
    for path,reason in [
        ('TCSlib/Cryptography/Asymptotic/PRF.lean','D_TOTAL_DECODER_COVERAGE'),
        ('TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine.lean','E_DIRECT_NONUNIFORM_IMPORT'),
        ('TCSlib/Cryptography/ZeroKnowledge/Defs.lean','K_DEVIATION_DOCSTRING'),
        ('TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean','L_ENVELOPE_DOCSTRING'),
        ('TCSlib/Cryptography/ZeroKnowledge/Interaction.lean','L_FORMULA_DOCSTRINGS'),
        ('TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean','SEPARATE_SOURCED_DISTADV_SUNGLASSRED_READER_REPAIR'),
        ('TCSlib/Complexity/Randomized/NonUniform.lean','THREE_PUBLIC_DEFINITION_FREEZE_EXCEPTION_SOURCE'),
        ('TCSlib/Complexity/Randomized/PPT.lean','THREE_PUBLIC_DEFINITION_FREEZE_EXCEPTION_HOME')]:consume(path,reason)
    provider_paths=[
        'TCSlib/Complexity/ClassNP/PolyTime.lean','TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean',
        'TCSlib/Complexity/ClassP/BinaryArith/Basic.lean','TCSlib/Complexity/Randomized/Build/StateLoop.lean',
        'TCSlib/Complexity/Randomized/Repetition.lean','TCSlib/Cryptography/Asymptotic/Adversary.lean',
        'TCSlib/Cryptography/Asymptotic/CollectionsHelpers.lean','TCSlib/Cryptography/Asymptotic/Sampling.lean',
        'TCSlib/Cryptography/HardcoreBit/Basic.lean','TCSlib/Programs/Util/List.lean',
        'TCSlib/Cryptography/NumberTheory/Units.lean','TCSlib/Cryptography/NumberTheory/QuadraticResidues.lean',
        'TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean']
    assert all(p in path_module for p in provider_paths)
    consumers={path_module[p] for p in reasons}
    explicit_providers={path_module[p] for p in provider_paths}
    planned=consumers|explicit_providers
    permitted=closure(planned,graph)
    root=path_module['TCSlib.lean'];checks=path_module['audits/pass-shelat/Checks.lean']
    check_only={root,checks}
    assert not permitted&check_only,('aggregates in editable closure',permitted&check_only)
    roles=[]
    for module in topo(permitted|check_only):
        v=source[module]
        role='CHECK_ONLY' if module in check_only else 'CONSUMER' if module in consumers else 'PROVIDER_ONLY'
        roles.append({'module':module,'path':v['path'],'role':role,
                      'explicit_shared_provider':module in explicit_providers,
                      'scope_reasons':sorted(reasons.get(v['path'],[])),
                      'allowed':('No worker patch; immutable aggregate/audit.' if role=='CHECK_ONLY' else
                         'Only scoped proof/dedup/documentation tasks and the enumerated public freeze exceptions; add owner readers as needed.' if role=='CONSUMER' else
                         'Solely add public equation/iff/field/run reader lemmas beside existing owned definitions, with formula docstrings; no existing definition, theorem statement, proof or algorithm changes.'),
                      'source_sha256':v['sha256'],'source_bytes':len(v['data'])})
    # The primary order covers planned consumer/provider homes. The conservative order
    # also covers any new reader placed in a finite provider-only closure path.
    planned_affected=closure(planned,reverse)
    affected=closure(permitted,reverse)
    root_prereqs=closure({root},graph)-{root}
    checks_prereqs=closure({checks},graph)-{checks}
    affected_prereqs=closure(affected,graph)-affected
    orders={'consumer-owner-order':consumers,'primary-owner-order':planned,
       'provider-upstream-order':permitted-consumers,'editable-union-order':permitted,
       'planned-affected-downstream-order':planned_affected,
       'affected-downstream-order':affected,'affected-prerequisites-order':affected_prereqs,
       'root-prerequisites-order':root_prereqs,'checks-prerequisites-order':checks_prereqs}
    assert root not in root_prereqs and checks not in checks_prereqs
    order_meta={}
    for label,selected in orders.items():
        ordered=topo(selected)
        linesave('orders/'+label+'.txt',[source[m]['path'].removesuffix('.lean') for m in ordered])
        order_meta[label]={'modules':len(ordered),'source_paths':[source[m]['path'] for m in ordered],
                           'local_prerequisites_outside_order':sorted({d for m in selected for d in graph[m]-selected})}
    # Direct narrowed roots, never a cache command. Include all separate replay scopes.
    root_scopes={'primary-union':planned,'editable-union':permitted,
                 'affected-downstream':affected,'root-prerequisites':root_prereqs|{root},
                 'checks-prerequisites':checks_prereqs|{checks}}
    mathlib_lists={}
    for label,selected in root_scopes.items():
        roots=sorted({i['module'] for m in selected for i in source[m]['imports'] if i['module']=='Mathlib' or i['module'].startswith('Mathlib.')})
        linesave('mathlib/'+label+'-roots.txt',roots);mathlib_lists[label]=roots
    all_roots=sorted({r for roots in mathlib_lists.values() for r in roots})
    linesave('mathlib/all-needed-union-roots.txt',all_roots)
    bare=[label for label,roots in mathlib_lists.items() if 'Mathlib' in roots]
    # Per-source and per-declaration lexical census, retaining anonymous/unassigned sites.
    lexical=[];declaration_rows=[];occurrences=[];parsed={}
    token_re=re.compile(r'(?<![\w\'])\b(sorryAx|sorry|admit|axiom)\b(?![\w\'])')
    for module,v in sorted(source.items()):
        ds=parser.parse(v['data'].decode(),v['path']);parsed[v['path']]=ds
        source_tokens=[]
        for line_no,line in enumerate(v['clean'].splitlines(),1):
            for match in token_re.finditer(line):
                candidates=[d for d in ds if d['start']<=line_no<=d['end']]
                assert len(candidates)<=1
                d=candidates[0] if candidates else None
                item={'path':v['path'],'module':module,'line':line_no,'column':match.start()+1,
                    'token':match.group(1),'source_declaration':d['canonical'] if d else None,
                    'source_declaration_start':d['start'] if d else None,
                    'owner_limit':'Source lexical declaration; not an elaborated generated/private Name.' if d else 'Anonymous command or outside recognized named declaration; retained, not dropped.'}
                source_tokens.append(item);occurrences.append(item)
        counts=Counter(x['token'] for x in source_tokens)
        lexical.append({'module':module,'path':v['path'],'counts':dict(counts),
                        'unassigned_occurrences':sum(x['source_declaration'] is None for x in source_tokens)})
        for d in ds:
            count=Counter(x['token'] for x in source_tokens if x['source_declaration_start']==d['start'])
            declaration_rows.append({**parser.public(d),'lexical_counts':dict(count),
                                     'role':next((r['role'] for r in roles if r['path']==v['path']),'CHECK_REPLAY_ONLY')})
    freezes=[]
    for path,key,target,allowance in [
      ('TCSlib/Complexity/Randomized/NonUniform.lean','Complexity.PPT.toNUPPT','TCSlib/Complexity/Randomized/PPT.lean','May relocate with identical canonical name, visibility, header and body; no algorithm or subtype-data change.'),
      ('TCSlib/Complexity/Randomized/NonUniform.lean','Complexity.PPT.ofPolyTime','TCSlib/Complexity/Randomized/PPT.lean','May relocate with identical canonical name, visibility, header and body; preserve the exact chosen NUPPT witness and uniform proof contract.'),
      ('TCSlib/Complexity/Randomized/PPT.lean','Complexity.NUPPT.ofPolyTime','TCSlib/Complexity/Randomized/PPT.lean','Proof/reader reexpression only, preserving header, chosen M/Ct/ct witnesses, coins, adv, advice, advice bound and every-input behavior. No new choice witness, algorithm or cost bound.')]:
        d,how=parser.exact_decl(parsed[path],key);assert d and d['kind']=='def' and not d['private']
        raw=d['raw'];masked=parser.mask(raw)
        delimiters=[x for x in [masked.find(':='),masked.find('where')] if x>=0]
        point=min(delimiters);width=2 if masked[point:point+2]==':=' else 5
        header=raw[:point];body=raw[point+width:]
        freezes.append({**parser.public(d),'raw_source':raw,'header':header,'body':body,
            'header_sha256':sha(header.encode()),'body_sha256':sha(body.encode()),
            'permitted_destination':target,'allowed_exception':allowance,
            'field_rhs_baseline':{line.split(':=',1)[0].strip():line.split(':=',1)[1].strip()
                for line in body.splitlines() if ':=' in line} if key=='Complexity.NUPPT.ofPolyTime' else None})
    # Verbatim copies preserve the original observation units; preparation never rewrites them.
    copies={
      'historical/cleanup-b.tsv':MAIN/'briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r2/r6c/cleanup-b.tsv',
      'historical/cleanup-b-decls.tsv':MAIN/'briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence-r2/r6c/cleanup-b-decls.tsv',
      'historical/row-dispositions.json':PREP/'review-inventory/final-historical-row-dispositions.json',
      'observations/canonical-work-units.json':PREP/'review-inventory/final-canonical-work-units.json',
      'observations/ownership-union.tsv':PREP/'review-inventory/ownership-union.tsv',
      'observations/bounded-summary.json':PREP/'review-inventory/final-bounded-summary.json',
      'observations/separate-source-gap-observations.json':PREP/'review-inventory/source-gap-observations.json',
      'scope/scope-review.json':PREP/'review-scope/scope-review.json',
      'scope/scope-review.md':PREP/'review-scope/scope-review.md',
      'scope/N-deferred-groups.json':PREP/'review-inventory/N-deferred-groups.json'}
    for destination,original in copies.items():save(destination,read(original))
    for path,h in scope['source_sha256'].items():assert source[path_module[path]]['sha256']==h
    fingerprints=[{'module':m,'path':v['path'],'bytes':len(v['data']),'sha256':v['sha256'],'git_blob':v['blob'],
                   'imports':v['imports'],'imports_sha256':sha((json.dumps(v['imports'],separators=(',',':'))+'\n').encode())}
                  for m,v in sorted(source.items())]
    jsave('source-import-fingerprints.json',fingerprints)
    jsave('local-import-graph.json',{'ancestor':ANCESTOR,'edges':{m:sorted(ds) for m,ds in sorted(graph.items())},
          'external_direct_source_imports':external_rows,'cycles':[],'missing_local_imports':[],
          'external_limit':'Direct source existence/fingerprints only; no external dependency replay or installed-object validation.'})
    jsave('role-manifest.json',{'ancestor':ANCESTOR,'roles':roles,'immutable_path_prefixes':['audits/'],
        'immutable_exact_paths':['TCSlib.lean'],'new_modules_permitted':False,
        'optional_exclusions':scope['optional_groups_recommended_excluded'],
        'provider_only_limit':'Finite existing local upstream-closure paths only; new public readers, never existing definition/statement/proof changes.'})
    jsave('public-definition-freeze.json',freezes)
    jsave('lexical-admissions-by-source.json',lexical)
    jsave('lexical-admissions-by-declaration.json',declaration_rows)
    jsave('lexical-admission-occurrences.json',occurrences)
    jsave('order-manifest.json',order_meta)
    counts={'consumer_owner_files':len(consumers),'explicit_shared_provider_files':len(explicit_providers),
      'explicit_providers_not_consumers':len(explicit_providers-consumers),'primary_owner_union':len(planned),
      'provider_only_files':len(permitted-consumers),'editable_union_files':len(permitted),
      'check_only_aggregates':len(check_only),'all_local_source_modules':len(source),
      'orders':{k:v['modules'] for k,v in order_meta.items()},
      'mathlib_direct_roots':{k:len(v) for k,v in mathlib_lists.items()},'all_needed_mathlib_union_roots':len(all_roots),
      'bare_mathlib_roots_scopes':bare,'direct_external_source_modules':len(external_rows),
      'library_lexical_admissions':dict(Counter(x['token'] for x in occurrences if x['path'].startswith('TCSlib/'))),
      'aggregate_lexical_admissions':dict(Counter(x['token'] for x in occurrences if not x['path'].startswith('TCSlib/'))),
      'unassigned_lexical_occurrences':sum(x['source_declaration'] is None for x in occurrences)}
    jsave('SUMMARY.json',{'status':'STATIC_ISSUE_INPUTS_ONLY_NO_NATIVE_NO_DISPATCH','ancestor':ANCESTOR,
       'records_head_at_start':records_head,'library_git_tree':tree,'counts':counts,
       'coverage_limits':['Baseline source graph only; recompute after imports, public-home relocation or actual changed-file scope moves.',
         'Provider-only permission is not permission to alter existing proofs/data/statements.',
         'Affected order includes all downstream local modules, including facades and check-only aggregates; root/Checks prerequisites exclude their own aggregate.',
         'Lexical counts are not kernel axiom dependency results; anonymous/unassigned occurrences are retained.',
         'No Lean/cache/native/apps/received worker code, main/exchange mutation, or Git writes occurred.']})
    assert git('rev-parse','HEAD:TCSlib').decode().strip()==tree
    for v in source.values():assert sha((MAIN/v['path']).read_bytes())==v['sha256']
    jsave('INPUTS-MANIFEST.json',{'ancestor':ANCESTOR,'records_head_at_start':records_head,
         'records_head_at_end':git('rev-parse','HEAD').decode().strip(),'library_git_tree':tree,
         'tool_sha256':sha(Path(__file__).read_bytes()),'own_parser_sha256':OWN_PARSER_SHA,
         'input_files':INPUTS,'outputs':OUTPUTS.copy(),'counts':counts,'all_live_source_bytes_stable':True,
         'native_commands_run':False,'git_writes':False,'source_or_main_or_exchange_writes':False})
    print(json.dumps(counts,indent=2))


if __name__=='__main__':main()
