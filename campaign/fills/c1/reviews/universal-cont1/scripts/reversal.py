import sys
ov = open(sys.argv[1], encoding='utf-8').read().split('\n')
hd = open(sys.argv[2], encoding='utf-8').read().split('\n')
# head = ov[0:226] + home(1420 lines) + ov[226:281] + [body] + ov[282:]
a, n = 226, 1420
home = hd[a:a+n]
rest = hd[:a] + hd[a+n:]
print('home head lines %d-%d (%d lines); first: %r; last: %r' % (a+1, a+n, n, home[0], home[-1]))
print('line after home (head %d): %r' % (a+n+1, hd[a+n]))
assert ov[281] == '  sorry', ov[281]
body = rest[281]
print('overlay line 282:', repr(ov[281]), '-> head line %d:' % (a+n+282-226), repr(body))
rest[281] = '  sorry'
print('reversal == overlay byte for byte:', '\n'.join(rest) == '\n'.join(ov))
