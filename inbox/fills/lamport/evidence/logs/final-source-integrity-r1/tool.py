"""Audit a concrete final commit using Git blobs only; never runs Lean.

Run as python3 -I final_source_integrity.py --root REPO --commit FULL_SHA
--output FRESH_DIRECTORY. The issue base and authorized source ownership are
fixed below. Raw source, diff, removed lines and check results are retained.

This is a source-text/lexical audit, NOT a full Lean parser or semantic theorem
equivalence proof. It proves exact textual preservation where indicated and
separately lists allowed-region/context changes for review. Compiled theorem
types, axioms, Rule-10 seals and campaign lint remain independent requirements.
"""
import argparse
import datetime
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

BASE = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
MAIN = 'TCSlib/Cryptography/Authentication/Signatures/Lamport.lean'
AUTH = 'TCSlib/Cryptography/Authentication.lean'
HELPERS = 'TCSlib/Cryptography/Authentication/Signatures/Lamport/'
HELPER_MODULE = 'TCSlib.Cryptography.Authentication.Signatures.Lamport.'
TARGET = 'lamport_oneTimeSecure'
DECL = re.compile(r'^(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom|instance)'
                  r'\s+([^\s(:{]+)', re.M)
COMMAND = re.compile(r'^(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*'
                     r'(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom|instance|'
                     r'namespace|section|end|open|variable|variables|include|omit|attribute|set_option|'
                     r'universe|universes|local|scoped|notation|macro|syntax|elab|run_cmd|initialize)\b', re.M)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(root, *args, check=True):
    p = subprocess.run(['git', '--no-optional-locks', '-C', str(root), *args], capture_output=True)
    if check and p.returncode:
        raise RuntimeError(p.stderr.decode(errors='replace'))
    return p


def blob(root, revision, path):
    p = git(root, 'show', revision + ':' + path, check=False)
    return None if p.returncode else p.stdout


def lexical(text):
    """Mask nested comments and strings, retaining offsets/newlines; collect comments."""
    out, comments, strings = list(text), [], []
    i = 0
    while i < len(text):
        start = i
        if text.startswith('--', i):
            stop = text.find('\n', i)
            stop = len(text) if stop < 0 else stop
            comments.append(dict(start=i, end=stop, kind='line'))
        elif text.startswith('/-', i):
            kind = 'module' if text.startswith('/-!', i) else 'doc' if text.startswith('/--', i) else 'block'
            depth, stop = 1, i + 2
            while depth and stop < len(text):
                if text.startswith('/-', stop): depth, stop = depth + 1, stop + 2
                elif text.startswith('-/', stop): depth, stop = depth - 1, stop + 2
                else: stop += 1
            if depth: raise RuntimeError('unclosed Lean block comment')
            comments.append(dict(start=i, end=stop, kind=kind))
        elif text[i] == '"':
            stop = i + 1
            while stop < len(text):
                if text[stop] == '\\': stop += 2
                elif text[stop] == '"': stop += 1; break
                else: stop += 1
            else: raise RuntimeError('unclosed Lean string')
            strings.append(dict(start=i, end=stop))
        else:
            i += 1
            continue
        for index in range(start, stop):
            if out[index] != '\n': out[index] = ' '
        i = stop
    return ''.join(out), comments, strings


def line_number(text, offset):
    return text.count('\n', 0, offset) + 1


def declarations(text):
    code, comments, _ = lexical(text)
    boundaries = {m.start() for m in COMMAND.finditer(code)}
    boundaries.update(c['start'] for c in comments
                      if c['kind'] != 'line' and (c['start'] == 0 or text[c['start']-1] == '\n'))
    boundaries.update(m.start() for m in re.finditer(r'^@\[', code, re.M))
    boundaries.add(len(text))
    result = []
    for match in DECL.finditer(code):
        end = min(pos for pos in boundaries if pos > match.start())
        raw = text[match.start():end].rstrip()
        docs = [c for c in comments if c['kind'] == 'doc' and c['end'] <= match.start()
                and not text[c['end']:match.start()].strip()]
        doc = docs[-1] if docs else None
        result.append(dict(kind=match.group(1), name=match.group(2), start=match.start(),
                           end=match.start()+len(raw), line=line_number(text,match.start()), raw=raw,
                           doc=doc, doc_raw=text[doc['start']:doc['end']] if doc else None))
    return result


def target_info(text):
    ds = [d for d in declarations(text) if d['name'] == TARGET]
    if len(ds) != 1: raise RuntimeError('target declaration not unique')
    d = ds[0]
    code, _, _ = lexical(text)
    assignment = code.find(':=', d['start'], d['end'])
    if assignment < 0: raise RuntimeError('target assignment delimiter missing')
    return dict(declaration=d, header=text[d['start']:assignment].rstrip(),
                proof_start=assignment+2, proof_end=d['end'])


def module_regions(text):
    _, comments, _ = lexical(text)
    doc = next(c for c in comments if c['kind'] == 'module')
    lines = text[doc['start']:doc['end']].splitlines(keepends=True)
    offsets, pos = [], doc['start']
    for line in lines: offsets.append((pos,pos+len(line)));pos += len(line)
    title = [i for i,line in enumerate(lines) if line.startswith('# ')]
    if len(title) != 1: raise RuntimeError('module title not unique')
    result = [dict(start=offsets[title[0]][0],end=offsets[title[0]][1],kind='module_title')]
    in_results, status = False, []
    for i,line in enumerate(lines):
        if line.startswith('## '): in_results = line.strip() == '## Main results'
        if in_results and TARGET in line:
            stop=i+1
            while stop<len(lines) and lines[stop].strip() and not re.match(r'^(?:## |\* |- )',lines[stop]):stop+=1
            status.append((i,stop))
    if len(status)!=1:raise RuntimeError('main-results target status item not unique')
    a,b=status[0]
    result.append(dict(start=offsets[a][0],end=offsets[b-1][1],kind='main_results_target_status'))
    for i,line in enumerate(lines):
        if line.strip()=='## Contents':
            stop=i+1
            while stop<len(lines) and not lines[stop].startswith('## '):stop+=1
            result.append(dict(start=offsets[i][0],end=offsets[stop-1][1],kind='contents'))
    return doc,result


def allowed_regions(text):
    target=target_info(text)
    _, regions=module_regions(text)
    d=target['declaration']
    if not d['doc']:raise RuntimeError('target docstring is not directly attached')
    regions += [dict(start=d['doc']['start'],end=d['doc']['end'],kind='target_docstring'),
                dict(start=target['proof_start'],end=target['proof_end'],kind='target_proof')]
    return target,regions


def simp_attributes(text):
    code,_,_=lexical(text)
    found=[]
    for m in re.finditer(r'@\[|\battribute\s*\[',code):
        begin=code.find('[',m.start(),m.end());depth=1;end=begin+1
        while depth and end<len(code):
            if code[end]=='[':depth+=1
            elif code[end]==']':depth-=1
            end+=1
        body=code[begin+1:end-1]
        direct=bool(re.search(r'(?<![\w])[-+]?simp(?![\w])',body))
        generated=bool(re.search(r'(?<![\w])simps!?(?![\w])',body))
        if direct or generated:
            local=bool(re.search(r'\blocal\b',body))
            false_config=bool(re.search(r'\bisSimp\s*:=\s*false\b',body))
            found.append(dict(line=line_number(text,m.start()),raw=text[m.start():end],
                              local=local,direct_simp=direct,simps=generated,
                              explicit_isSimp_false=false_config,
                              global_mutation=(direct and not local) or (generated and not false_config)))
    return found


def imports(text):
    code,_,_=lexical(text)
    rows=[]
    for m in re.finditer(r'^import\s+([^\n]+)',code,re.M):
        end=text.find('\n',m.start());end=len(text) if end<0 else end+1
        rows.append(dict(start=m.start(),end=end,modules=m.group(1).split(),raw=text[m.start():end]))
    return rows


def auth_import_only(old,new):
    def strip(text):
        out=text
        for row in reversed(imports(text)):out=out[:row['start']]+out[row['end']:]
        return out
    a=[module for row in imports(old) for module in row['modules']]
    b=[module for row in imports(new) for module in row['modules']]
    iterator=iter(b);preserved=all(any(value==wanted for value in iterator) for wanted in a)
    extra=[value for value in b if value not in a]
    return dict(non_import_bytes_equal=strip(old)==strip(new),original_imports_preserved=preserved,
                added_imports=extra,only_owned_helper_imports_added=all(x.startswith(HELPER_MODULE) for x in extra),
                pass_=strip(old)==strip(new) and preserved and all(x.startswith(HELPER_MODULE) for x in extra))


def prohibited(text):
    code,_,_=lexical(text)
    pattern=re.compile(r'(?<![\w\'])\b(?:sorry|admit|axiom|unsafe|sorryAx|mkSorry|axiomDecl)\b')
    rows=[dict(line=line_number(text,m.start()),token=m.group()) for m in pattern.finditer(code)]
    for m in re.finditer(r'\bset_option\s+allowUnsafeReducibility\s+true\b',code):
        rows.append(dict(line=line_number(text,m.start()),token=m.group()))
    return rows


def main_preservation(old,new):
    old_target,regions=allowed_regions(old);new_target,new_regions=allowed_regions(new)
    old_ds=declarations(old);new_ds=declarations(new)
    comparisons=[]
    for d in old_ds:
        same=[v for v in new_ds if v['name']==d['name']]
        row=dict(name=d['name'],kind=d['kind'],base_line=d['line'],unique_final=len(same)==1)
        if len(same)==1:
            f=same[0];row.update(final_line=f['line'],kind_equal=d['kind']==f['kind'])
            if d['name']==TARGET:
                row.update(header_exact=old_target['header']==new_target['header'],
                           doc_and_proof_authorized_to_change=True)
            else:
                row.update(declaration_bytes_exact=d['raw']==f['raw'],
                           attached_docstring_bytes_exact=d['doc_raw']==f['doc_raw'])
        comparisons.append(row)
    old_lines=old.splitlines(keepends=True);new_lines=new.splitlines(keepends=True)
    offsets=[];pos=0
    for line in old_lines:offsets.append((pos,pos+len(line)));pos+=len(line)
    removed=[]
    for op,a,b,c,d in difflib.SequenceMatcher(a=old_lines,b=new_lines,autojunk=False).get_opcodes():
        if op not in ('delete','replace'):continue
        for index in range(a,b):
            lo,hi=offsets[index]
            reasons=[r['kind'] for r in regions if r['start']<hi and r['end']>lo]
            removed.append(dict(base_line=index+1,text=old_lines[index],allowed_overlap=reasons,
                                whitespace_only=not old_lines[index].strip(),opcode=op,
                                replacement_final_lines=[c+1,d]))
    bad=[r for r in removed if not r['allowed_overlap'] and not r['whitespace_only']]
    old_doc,old_mod=module_regions(old);new_doc,new_mod=module_regions(new)
    def protected_doc(text,doc,spans):
        out=text[doc['start']:doc['end']]
        for region in sorted(spans,key=lambda r:r['start'],reverse=True):
            out=out[:region['start']-doc['start']]+out[region['end']-doc['start']:]
        return out
    a=protected_doc(old,old_doc,old_mod);b=protected_doc(new,new_doc,new_mod)
    it=iter(b.splitlines());prose_preserved=all(any(v==wanted for v in it) for wanted in a.splitlines())
    old_title=next(old[r['start']:r['end']].strip() for r in old_mod if r['kind']=='module_title')
    new_title=next(new[r['start']:r['end']].strip() for r in new_mod if r['kind']=='module_title')
    status=next(new[r['start']:r['end']] for r in new_mod if r['kind']=='main_results_target_status')
    allowed_diffs=[]
    for kind in ['module_title','main_results_target_status','target_docstring','target_proof','contents']:
        before=''.join(old[r['start']:r['end']] for r in regions if r['kind']==kind)
        after=''.join(new[r['start']:r['end']] for r in new_regions if r['kind']==kind)
        allowed_diffs.append(dict(region=kind,base=before,final=after))
    # Extra context commands are surfaced for human review, not silently declared semantic no-ops.
    code,_,_=lexical(new)
    base_code,_,_=lexical(old)
    context_pattern=re.compile(r'^(?:namespace|section|end|open|variable|variables|include|omit|'
                               r'set_option|universe|universes|local|scoped|notation|macro|syntax|elab|run_cmd)\b[^\n]*',re.M)
    base_context=[m.group() for m in context_pattern.finditer(base_code)]
    final_context=[m.group() for m in context_pattern.finditer(code)]
    new_context=[dict(line=line_number(new,m.start()),text=m.group())
                 for m in context_pattern.finditer(code) if m.group() not in base_context]
    good_declarations=all(r['unique_final'] and r.get('kind_equal') and
        (r.get('header_exact') if r['name']==TARGET else
         r.get('declaration_bytes_exact') and r.get('attached_docstring_bytes_exact')) for r in comparisons)
    return dict(target_statement_raw_equal=old_target['header']==new_target['header'],
                target_statement_base=old_target['header'],target_statement_final=new_target['header'],
                original_declarations=comparisons,original_non_target_declarations_exact=good_declarations,
                removed_lines=removed,forbidden_removed_lines=bad,
                protected_module_prose_preserved_in_order=prose_preserved,
                module_title_expected=new_title==old_title.replace(' (statement phase)',''),
                target_main_results_status_updated=not re.search(r'\bsorry\b|\bstated\b',status),
                contents_present=any(r['kind']=='contents' for r in new_regions),
                allowed_region_review=allowed_diffs,new_context_commands_for_review=new_context,
                original_context_stream=base_context,final_context_stream=final_context,
                pass_=good_declarations and not bad and prose_preserved and
                      new_title==old_title.replace(' (statement phase)','') and
                      not re.search(r'\bsorry\b|\bstated\b',status))


def main(args):
    root=Path(args.root).resolve();out=Path(args.output).resolve()
    if out.exists():raise RuntimeError('refusing to overwrite output directory')
    if not re.fullmatch(r'[0-9a-f]{40}',args.commit):raise RuntimeError('use immutable full commit SHA')
    git(root,'merge-base','--is-ancestor',BASE,args.commit)
    out.mkdir(parents=True)
    (out/'tool.py').write_bytes(Path(__file__).read_bytes())
    raw=git(root,'diff','--no-ext-diff','--no-renames','--name-status','-z',BASE,args.commit).stdout
    (out/'name-status.raw').write_bytes(raw)
    (out/'diff.raw.patch').write_bytes(git(root,'diff','--no-ext-diff','--binary','--full-index',
                                         '--no-renames',BASE,args.commit).stdout)
    pieces=raw.decode().split('\0');changes=[]
    for i in range(0,len(pieces)-1,2):
        status,path=pieces[i:i+2]
        changes.append(dict(status=status,path=path,allowed=(path in (MAIN,AUTH) or
                            (path.startswith(HELPERS) and path.endswith('.lean'))) and status in ('A','M')))
    history=[]
    commits=git(root,'rev-list','--reverse',BASE+'..'+args.commit).stdout.decode().splitlines()
    for commit in commits:
        row=git(root,'diff-tree','--no-commit-id','--name-status','-r','--no-renames',commit).stdout
        (out/('commit-'+commit+'.name-status.raw')).write_bytes(row)
        paths=[line.split('\t')[-1] for line in row.decode().splitlines()]
        history.append(dict(commit=commit,paths=paths,scope_valid=all(p in(MAIN,AUTH)or
                        (p.startswith(HELPERS)and p.endswith('.lean')) for p in paths)))
    sources={};file_checks=[]
    for change in changes:
        path=change['path'];before=blob(root,BASE,path);after=blob(root,args.commit,path)
        for label,data in [('base',before),('final',after)]:
            if data is not None:
                target=out/'sources'/label/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        if after is None:continue
        text=after.decode();sources[path]=text
        attributes=simp_attributes(text)
        row=dict(path=path,base_source_absent=before is None,base_sha256=sha(before) if before else None,
                 final_sha256=sha(after),lines=len(text.splitlines()),strictly_below_1000=len(text.splitlines())<1000,
                 prohibited_code_tokens=prohibited(text),simp_attributes=attributes,
                 bare_Mathlib_import=any('Mathlib' in r['modules'] for r in imports(text)))
        if path.startswith(HELPERS):row['no_new_global_simp']=not any(a['global_mutation'] for a in attributes)
        elif before is not None:
            oldattrs=[a['raw'] for a in simp_attributes(before.decode()) if a['global_mutation']]
            newattrs=[a['raw'] for a in attributes if a['global_mutation']]
            row['global_simp_source_directives_preserved']=oldattrs==newattrs
        file_checks.append(row)
    preservation=main_preservation(blob(root,BASE,MAIN).decode(),sources[MAIN])
    auth=auth_import_only(blob(root,BASE,AUTH).decode(),sources[AUTH])
    passed=all(c['allowed'] for c in changes) and all(r['scope_valid'] for r in history) and auth['pass_'] and preservation['pass_']
    passed=passed and all(r['strictly_below_1000'] and not r['prohibited_code_tokens'] and
                          not r['bare_Mathlib_import'] and r.get('no_new_global_simp',True) and
                          r.get('global_simp_source_directives_preserved',True) for r in file_checks)
    result=dict(base=BASE,commit=args.commit,created_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                source='Git blobs only; working-tree/untracked Lean files were not read',
                mechanical_pass=bool(passed),scope=changes,per_commit_scope=history,files=file_checks,
                authentication_import_only=auth,main_preservation=preservation,
                manual_review_required=['Review allowed title/status/Contents/target-doc/target-proof regions',
                    'Review new top-level context/metaprogram commands for name/typeclass/context effects',
                    'This lexical check does not establish Lean semantic equivalence or the effective imported simp environment; use compiled theorem-type/axiom/seal/lint evidence'],
                tool_sha256=sha(Path(__file__).read_bytes()))
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'allowed-region-review.json').write_text(json.dumps(preservation['allowed_region_review'],indent=2)+'\n')
    (out/'removed-lines.json').write_text(json.dumps(preservation['removed_lines'],indent=2)+'\n')
    print(json.dumps(dict(mechanical_pass=passed,commit=args.commit,changed_files=len(changes),
         original_declarations=len(preservation['original_declarations']),
         forbidden_removed_lines=len(preservation['forbidden_removed_lines']),
         output=str(out)),indent=2))
    return 0 if passed else 1


parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root',required=True);parser.add_argument('--commit',required=True)
parser.add_argument('--output',required=True)
if __name__=='__main__':sys.exit(main(parser.parse_args()))
