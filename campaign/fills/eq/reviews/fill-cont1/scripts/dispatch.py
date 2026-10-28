"""Compare the dispatched attachments with their repository copies at a revision, after replacing
@ANCESTOR@ by the base (python3 -I; reads files given as arguments).
usage: python3 -I dispatch.py <dispatched> <repo copy> <base>"""
import hashlib, sys
d, r, base = sys.argv[1:4]
D = open(d, 'rb').read(); Rr = open(r, 'rb').read()
n = Rr.count(b'@ANCESTOR@')
sub = Rr.replace(b'@ANCESTOR@', base.encode())
print(f'{d.split("/")[-1]}: sha256 {hashlib.sha256(D).hexdigest()}; repo copy has {n} @ANCESTOR@; '
      f'equal after substitution: {sub == D}; equal unsubstituted: {Rr == D}')
