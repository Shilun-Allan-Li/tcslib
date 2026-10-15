"""Append the axiom prints of the prescribed and suggested home declarations and of rows
17-18, and `#check`s of the inherited privates the brief cites, to the overlay (before its
final `end Turing`). Usage: python3 -I mkchecks.py <overlay.lean> <out.lean>"""
import sys
src = open(sys.argv[1], encoding='utf-8').read()
tail = '\nend Turing\n'
assert src.endswith(tail) and src.count('\nend Turing') == 1
ax = ['rt_exists_scratchTemplateTM', 'rt_binDigits_one', 'rt_initRecord_fields',
      'rt_tailTM', 'rt_tail_run', 'exists_recordTemplateTM', 'exists_recordInitTM']
ck = ['rt_copy_seam', 'rt_embed_matches', 'rt_embed_radius', 'rt_moveWordTM',
      'rt_moveWord_run', 'rt_bufferMask', 'rt_template_fields', 'rt_centeredWord',
      'rt_copyState', 'rt_copyMachine', 'rt_copy_run']
add = ''.join(f'#print axioms {n}\n' for n in ax) + ''.join(f'#check @{n}\n' for n in ck)
open(sys.argv[2], 'w', encoding='utf-8').write(src[:-len(tail)] + '\n' + add + tail)
print('appended', len(ax), 'axiom prints and', len(ck), 'checks')
