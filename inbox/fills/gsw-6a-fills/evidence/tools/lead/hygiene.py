"""hygiene.py [--base <repo> <rev>] <file>... (gsw-6a-fills, new; check 9): (a) every private declaration that is
new against <rev> (private declarations already in the base file, e.g. CarrySave's csaLevelsAux, are frozen and
skipped; listed as BASE-PRIVATE) has a docstring that contains
"Glue." and a backticked formula (a backtick span with `=`, `≤`, `<`, `↔`, `→` or `∀`); (b) every declaration
of 20 or more lines (statement through proof, as style_lint counts) has `**Proof sketch.**` in its docstring.
Lists every violation; RESULT counts."""
import sys, re
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|instance)\s+(\S+)')
CONT = re.compile(r'^(termination_by|decreasing_by)\b')
import subprocess
args = sys.argv[1:]; brepo = brev = None
if args and args[0] == '--base': brepo, brev = args[1], args[2]; args = args[3:]
na = nb = 0; nh = np_ = 0
for f in args:
    L = open(f, encoding='utf-8').read().split('\n')
    basepriv = set()
    if brepo:
        bt = subprocess.run(['git', '-C', brepo, 'show', f'{brev}:{f}'], capture_output=True).stdout.decode()
        basepriv = {m.group(3) for l in bt.split('\n') if (m := DECL.match(l)) and (m.group(1) or '').strip().startswith('private')}
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
        body = j - i  # lines of the declaration, statement through proof (style_lint's measure)
        priv = (m.group(1) or '').strip().startswith('private')
        if priv and m.group(3) in basepriv:
            print(f'BASE-PRIVATE\t{f}:{i + 1}\t{m.group(3)}\t(frozen, not a helper of this job)')
        elif priv:
            nh += 1
            ok = 'Glue.' in doc and re.search(r'`[^`]*(=|≤|<|↔|→|∀)[^`]*`', doc)
            if not ok: na += 1; print(f'HELPER-DOC\t{f}:{i + 1}\t{m.group(3)}\tglue={"Glue." in doc}')
        if body >= 20:
            np_ += 1
            if '**Proof sketch.**' not in doc: nb += 1; print(f'NO-SKETCH\t{f}:{i + 1}\t{m.group(3)}\tbody_lines={body}')
print(f'RESULT private_helpers={nh} helper_doc_violations={na} long_proofs={np_} missing_sketches={nb}')
