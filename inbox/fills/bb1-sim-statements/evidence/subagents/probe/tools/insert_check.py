"""insert_check.py <worktree> <outdir>: extract the two reader blocks from PlProbe/BB1SimReaders.lean,
insert each (one blank line, then the block) after its anchor in copies of Defs.lean (after line
430) and BonehBoyen.lean (after line 412) at T4's head, write the copies to PlProbe/Scratch/InsDefs.lean
and InsBonehBoyen.lean, and check that removing the blocks restores the originals byte for byte."""
import sys, hashlib, os
wt, out = sys.argv[1:3]
r = open(os.path.join(wt, 'PlProbe/BB1SimReaders.lean'), encoding='utf-8').read()
a = r.index("/-- **Oracle `0` of the game on the game's query type**"); b = r.index('end IBEScheme')
c = r.index("/-- **`Setup` at the scheme's types**"); d = r.index('end TCSlib.Cryptography.AdvancedEncryption.IdentityBased')
blocks = {'Defs': (r[a:b].rstrip('\n'), 430, '  (OracleComp.bind_pure _).symm', '/-- The codec of the adversary'),
          'BonehBoyen': (r[c:d].rstrip('\n'), 412, '  exists_congr fun _ => List.ofFn_inj.symm', '/-- **BB1 is perfectly correct**')}
base = os.path.join(wt, 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/')
for name, (blk, line, last, nxt) in blocks.items():
    src = open(base + name + '.lean', encoding='utf-8').read()
    L = src.split('\n')
    assert L[line - 1] == last and L[line] == '' and L[line + 1].startswith(nxt), name
    bl = blk.split('\n')
    N = L[:line] + [''] + bl + L[line:]
    new = '\n'.join(N)
    open(os.path.join(wt, 'PlProbe/Scratch/Ins' + name + '.lean'), 'w', encoding='utf-8').write(new)
    open(os.path.join(out, name + '-block.lean.txt'), 'w', encoding='utf-8').write(blk + '\n')
    back = '\n'.join(N[:line] + N[line + 1 + len(bl):])
    print(f"{name}: base {hashlib.sha256(src.encode()).hexdigest()} lines {src.count(chr(10))}; "
          f"block {len(bl)} lines, max width {max(len(x) for x in bl)}; after insertion "
          f"{new.count(chr(10))} lines {hashlib.sha256(new.encode()).hexdigest()}; "
          f"removal restores base: {back == src}")
