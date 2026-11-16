"""controls.py <worktree> <spec.json> <outdir>: paired Rule 10 controls, one pair per owner.
spec: list of {owner, def, stmt, neg, pos}: `example <stmt> := <neg>` reads the owner's definition
`def` through its body (rfl/Iff.rfl), `example <stmt> := <pos>` through its published reader.
Writes, per owner O, three files under <worktree>/evidence/rule10/controls/:
  Control_<O>_neg_unsealed.lean (no seal; must pass), Control_<O>_neg_sealed.lean (`attribute [local
  irreducible] def`; must fail with exactly one error), Control_<O>_pos_sealed.lean (sealed, reader;
  must pass); runs each with check.py (host lock) and writes <outdir>/summary.txt."""
import sys, json, os, re, subprocess
wt, specf, outdir = sys.argv[1:4]
spec = json.load(open(specf))
cd = os.path.join(wt, 'evidence/rule10/controls'); os.makedirs(cd, exist_ok=True); os.makedirs(outdir, exist_ok=True)
summ = open(os.path.join(outdir, 'summary.txt'), 'w')
for s in spec:
    tag = s['owner'].split('.', 1)[1].replace('.', '_')
    for kind, seal, term, expect in [('neg_unsealed', False, s['neg'], 0), ('neg_sealed', True, s['neg'], 1),
                                     ('pos_sealed', True, s['pos'], 0)]:
        name = f'Control_{tag}_{kind}'
        src = f'import {s["owner"]}\nset_option autoImplicit false\n'
        if seal: src += f'attribute [local irreducible] {s["def"]}\n'
        src += f'-- {kind}: reads `{s["def"]}` ' + ('through its body' if kind.startswith('neg') else 'through its reader') + '\n'
        src += f'example {s["stmt"]} :=\n  {term}\n'
        open(os.path.join(cd, name + '.lean'), 'w').write(src)
        open(os.path.join(outdir, name + '.lean'), 'w').write(src)
        log = os.path.join(outdir, name + '.log')
        if os.path.exists(log): os.remove(log)
        r = subprocess.run(['python3', '-I', '/home/user/work/tools/check.py', wt, f'evidence/rule10/controls/{name}', log],
                           capture_output=True, text=True)
        txt = open(log, encoding='utf8').read()
        errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M))
        ok = (errs == expect)
        line = f'{name}\tdef={s["def"]}\terrors={errs}\texpected={expect}\t{"OK" if ok else "UNEXPECTED"}'
        print(line); summ.write(line + '\n'); summ.flush()
