"""hygiene.py <file>... (gsw-6a-fills, new; check 9): (a) every private declaration has a docstring that contains
"Glue." and a backticked formula (a backtick span with `=`, `≤`, `<`, `↔`, `→` or `∀`); (b) every declaration
whose proof body (after its first `:=`) has 20 or more lines has `**Proof sketch.**` in its docstring.
Lists every violation; RESULT counts."""
import sys, re
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|instance)\s+(\S+)')
CONT = re.compile(r'^(termination_by|decreasing_by)\b')
na = nb = 0; nh = np_ = 0
for f in sys.argv[1:]:
    L = open(f, encoding='utf-8').read().split('\n')
    for i, l in enumerate(L):
        m = DECL.match(l)
        if not m: continue
        doc = ''
        if i > 0 and L[i - 1].rstrip().endswith('-/'):
            k = i - 1
            while k >= 0 and not L[k].startswith('/--'): k -= 1
            doc = '\n'.join(L[k:i])
        j = i + 1
        while j < len(L) and (not L[j] or L[j][0].isspace() or CONT.match(L[j])): j += 1
        while j > i + 1 and not L[j - 1].strip(): j -= 1
        blk = '\n'.join(L[i:j]); p = blk.find(':=')
        body = blk[p:].count('\n') + 1 if p >= 0 else 0
        priv = (m.group(1) or '').strip().startswith('private')
        if priv:
            nh += 1
            ok = 'Glue.' in doc and re.search(r'`[^`]*(=|≤|<|↔|→|∀)[^`]*`', doc)
            if not ok: na += 1; print(f'HELPER-DOC\t{f}:{i + 1}\t{m.group(3)}\tglue={"Glue." in doc}')
        if body >= 20:
            np_ += 1
            if '**Proof sketch.**' not in doc: nb += 1; print(f'NO-SKETCH\t{f}:{i + 1}\t{m.group(3)}\tbody_lines={body}')
print(f'RESULT private_helpers={nh} helper_doc_violations={na} long_proofs={np_} missing_sketches={nb}')
