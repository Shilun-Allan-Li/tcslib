"""alt_ns.py (no arguments; run as `python3 -I alt_ns.py`)

Checks the planned glue names (and the probe's `abs_inner_le`, and unprimed `sidSpec_rng_one/two`)
at three candidate namespaces (IdentityBased, IdentityBased.BB1Machine, IdentityBased.IBEScheme)
against the declaration index of TCSlib/ and audits/ at 633dcf99, built by
../clash/clash_scan.py; prints CLASH/free and same-short-name declarations.

written by tools-agent (sub-agent), fill bb1-machine
"""
import importlib.util, sys
sys.dont_write_bytecode = True
sp = importlib.util.spec_from_file_location(
    'cs', '/home/user/exch/x/inbox/fills/bb1-machine/evidence/clash/clash_scan.py')
cs = importlib.util.module_from_spec(sp); sp.loader.exec_module(cs)
idx = cs.base_index('/home/user/fill/wt-sub', '633dcf99')
N = 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased'
names = ['cast_eq_padFin', 'ofFn_padFin_ofFn', 'ofFn_decAnswer_some', "sidSpec_rng_one'",
         "sidSpec_rng_two'", 'expect_bb1SimImpl', 'abs_expect_bb1Sim_sub_distinguisherL_le',
         'abs_inner_le', 'sidSpec_rng_one', 'sidSpec_rng_two']
for n in names:
    for ns in (N, N + '.BB1Machine', N + '.IBEScheme'):
        f = ns + '.' + n
        print(f, 'CLASH' if f in idx['full'] else 'free',
              [x['path'] + ':' + str(x['line']) for x in idx['full'].get(f, [])],
              'short:', [x['full'] for x in idx['short'].get(n, [])][:5])
