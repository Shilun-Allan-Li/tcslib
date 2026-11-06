"""gen_collect.py <mods.txt> <outdir> <out.lean>: write the candidate-collector Lean file, importing
every target module and writing its results to <outdir>."""
import sys, os
mods_file, outdir, out = sys.argv[1:4]
mods = [l.strip() for l in open(mods_file) if l.strip()]
body = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'collect_body.lean')).read()
head = ''.join(f'import {m}\n' for m in mods)
defs = ('\nopen Lean in\ndef targetMods : Array Name := #[' +
        ', '.join('`' + m for m in mods) + ']\n' +
        f'def outDir : System.FilePath := "{outdir}"\n\n')
with open(out, 'w', encoding='utf-8') as o:
    o.write(head + defs + body)
print(len(mods), 'modules ->', out)
