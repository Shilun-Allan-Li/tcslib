r"""(bb1-sim, lead: copied unchanged from bb1-sim-statements.) insert_blocks.py <file> <spec>... (bb1-sim-statements, lead): pure insertions. Each spec is
AFTER_LINE:BLOCK_FILE (1-based line number of the base file after which the block's lines go).
Specs are applied bottom-up so the base line numbers stay valid. The block file's text is inserted
verbatim (a trailing newline of the block file ends its last line)."""
import sys
path, specs = sys.argv[1], sys.argv[2:]
lines = open(path, encoding='utf-8').read().split('\n')
assert lines[-1] == '', 'file must end with a newline'
for spec in sorted(specs, key=lambda s: -int(s.split(':', 1)[0])):
    n, blk = spec.split(':', 1)
    b = open(blk, encoding='utf-8').read()
    assert b.endswith('\n')
    lines[int(n):int(n)] = b[:-1].split('\n')
open(path, 'w', encoding='utf-8').write('\n'.join(lines))
