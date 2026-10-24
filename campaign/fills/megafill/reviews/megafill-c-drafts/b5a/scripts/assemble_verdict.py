import hashlib, sys, itertools
ov = open(sys.argv[1], encoding='utf-8').read()
blk = open(sys.argv[2], encoding='utf-8').read()
target = sys.argv[3]
tail = "end MachineFormat\n\nend Turing\n"
assert ov.endswith(tail), "overlay tail"
head = ov[:-len(tail)]
pr = "#print axioms Turing.MachineFormat.b5a_window_verdict\n"
found = None
blocks = {'full': blk}
lines = blk.split('\n')
# variant without the 3 header comment lines (+ following blank)
blocks['nohdr'] = '\n'.join(lines[4:])
blocks['nohdr3'] = '\n'.join(lines[3:])
for (bn, b), sep_after, sep_before_pr in itertools.product(blocks.items(), ['', '\n'], ['', '\n']):
    for strip in [False, True]:
        bb = b.rstrip('\n') + '\n' if strip else b
        s = head + bb + sep_after + tail + sep_before_pr + pr
        h = hashlib.sha256(s.encode('utf-8')).hexdigest()
        if h == target:
            found = (bn, repr(sep_after), repr(sep_before_pr), strip)
            open(sys.argv[4], 'w', encoding='utf-8').write(s)
print('MATCH' if found else 'NO MATCH', found)
