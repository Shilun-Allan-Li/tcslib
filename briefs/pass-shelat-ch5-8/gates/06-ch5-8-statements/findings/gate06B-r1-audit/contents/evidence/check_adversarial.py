#!/usr/bin/env python3
"""Finite audit models, not Lean elaboration or cryptographic security tests.

The schedule comparison constructs the expected transcript by running the
subprotocols separately.  The tested side follows the published composer.
No repository code is imported or changed.
"""
import hashlib
import itertools
import json


def words(n):
    return list(itertools.product((0, 1), repeat=n))


def pair(a, b):
    return tuple(v for bit in a for v in (bit, bit)) + (0, 1) + tuple(b)


def unpair(w):
    left = []
    for i in range(0, len(w) - 1, 2):
        a, b = w[i:i + 2]
        if (a, b) == (0, 1):
            return tuple(left), tuple(w[i + 2:])
        if a != b:
            return None
        left.append(a)
    return None


def projections(w):
    return unpair(w) or ((), ())


def xor(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


def pad(w, n):
    return (tuple(w) + (0,) * n)[:n]


def special_enc(evaluator, key, message, nonce):
    p = evaluator(key, nonce)
    return pair(nonce, p[:len(nonce)] + xor(message, p[len(nonce):]))


def special_dec(evaluator, n, ell, key, ciphertext):
    nonce, body = projections(ciphertext)
    if (len(key), len(nonce), len(body)) != (n, n, n + ell):
        return None
    p = evaluator(key, nonce)
    if body[:n] != p[:n]:
        return None
    return xor(body[n:], p[n:])


def hash_bits(tag, obj, width=5):
    digest = hashlib.sha256(json.dumps([tag, obj], sort_keys=True).encode()).digest()
    return tuple((digest[i // 8] >> (i % 8)) & 1 for i in range(width))


def run(p, v, verifier_first, moves):
    """The D8 execution rule: returns the two received-message lists."""
    hp, hv = [], []
    for t in range(moves):
        if (t % 2 == 0) == verifier_first:
            hp.append(v(hv))
        else:
            hv.append(p(hp))
    return hp, hv


def composition_case(calls, submoves, mainmoves, subfirst, mainfirst, salt):
    main_p_coins, main_v_coins = 2, 3
    sub_p_coins, sub_v_coins = 3, 2
    ra = hash_bits('ra', salt, main_p_coins + calls * sub_p_coins)
    rb = hash_bits('rb', salt, main_v_coins + calls * sub_v_coins)
    za, zb = (1, 0), (0, 1, 1)
    lead = int(mainfirst)

    def run_input_a(j):
        return hash_bits('input-a', [za, ra[:main_p_coins], j], 2) if j < calls else ()

    def run_input_b(j):
        return hash_bits('input-b', [zb, rb[:main_v_coins], j], 3) if j < calls else ()

    def sub_p(j, hist):
        c = ra[main_p_coins + j * sub_p_coins:main_p_coins + (j + 1) * sub_p_coins]
        return hash_bits('sub-p', [run_input_a(j), c, hist, salt])

    def sub_v(j, hist):
        c = rb[main_v_coins + j * sub_v_coins:main_v_coins + (j + 1) * sub_v_coins]
        return hash_bits('sub-v', [run_input_b(j), c, hist, salt])

    def select(hist, j, p, verifier):
        return [hist[submoves * j + q] if submoves * j + q < len(hist) else ()
                for q in range(p) if ((q % 2 == 0) == subfirst) == verifier]

    def answers_a(hist):
        return sum((pad(sub_p(j, select(hist, j, submoves, True)), 2)
                    for j in range(calls)), ())

    def answers_b(hist):
        return sum((pad(sub_v(j, select(hist, j, submoves, False)), 3)
                    for j in range(calls)), ())

    def main_p(answer, hist):
        return hash_bits('main-p', [za, answer, ra[:main_p_coins], hist, salt])

    def main_v(answer, hist):
        return hash_bits('main-v', [zb, answer, rb[:main_v_coins], hist, salt])

    def composed_p(hist):
        k = len(hist)
        if k < calls * submoves:
            j, p = divmod(k, submoves)
            return () if ((p % 2 == 0) == subfirst) else sub_p(j, select(hist, j, p, True))
        if mainfirst and k == calls * submoves:
            return ()
        return main_p(answers_a(hist), hist[calls * submoves:])

    def composed_v(hist):
        q = max(0, len(hist) - 1)
        if q < calls * submoves:
            j, p = divmod(q, submoves)
            return sub_v(j, select(hist, j, p, False)) if ((p % 2 == 0) == subfirst) else ()
        return main_v(answers_b(hist), hist[calls * submoves + lead:])

    # Independent expected layout: run each subprotocol in isolation, then main.
    expected_p, expected_v = [], []
    honest_a, honest_b = (), ()
    for j in range(calls):
        p = lambda h, j=j: sub_p(j, h)
        v = lambda h, j=j: sub_v(j, h)
        hp, hv = run(p, v, subfirst, submoves)
        honest_a += pad(p(hp), 2)
        honest_b += pad(v(hv), 3)
        hp, hv = [], []
        for t in range(submoves):
            if (t % 2 == 0) == subfirst:
                m = v(hv)
                expected_p.append(m)
                expected_v.append(())
                hp.append(m)
            else:
                m = p(hp)
                expected_p.append(())
                expected_v.append(m)
                hv.append(m)
    expected_v += [()] * lead
    mp = lambda h: main_p(honest_a, h)
    mv = lambda h: main_v(honest_b, h)
    main_hp, main_hv = run(mp, mv, mainfirst, mainmoves)
    expected_p += main_hp
    expected_v += main_hv
    actual = run(composed_p, composed_v, False, calls * 2 * submoves + lead + mainmoves)
    assert actual == (expected_p, expected_v)
    if mainmoves > 0:
        assert composed_p(actual[0]) == mp(main_hp)
        assert composed_v(actual[1]) == mv(main_hv)


def main():
    counts = {'special_encryption_cases': 0, 'ot_cases': 0, 'composition_cases': 0}
    for n in range(4):
        for ell in range(4):
            e = lambda k, r, n=n, ell=ell: hash_bits('pad', [k, r], n + ell)
            for k, r, m in itertools.product(words(n), words(n), words(ell)):
                c = special_enc(e, k, m, r)
                assert len(c) == 3 * n + ell + 2
                assert special_dec(e, n, ell, k, c) == m
                counts['special_encryption_cases'] += 1
    # The empty string is not a pair but passes the raw zero-length checks.
    assert unpair(()) is None
    assert special_dec(lambda k, r: (), 0, 0, (), ()) == ()
    # All finite permutations and predicates on a two-element domain; domain
    # encodings are abstract canonical elements, and the tape chooses one.
    for perm in itertools.permutations(range(2)):
        inv = {p: x for x, p in enumerate(perm)}
        for predicate in words(2):
            for a0, a1, b, known, raw in itertools.product(range(2), repeat=5):
                aa = (a0, a1)
                yy = [raw, raw]
                yy[b] = perm[known]
                zz = tuple(predicate[inv[y]] ^ a for y, a in zip(yy, aa))
                received_a, received_b = [], []
                sender = lambda h: ('index',) if not h else zz if len(h) == 1 else ()
                receiver = lambda h: tuple(yy) if len(h) == 1 else () if len(h) == 2 else (
                    predicate[known] ^ h[1][b],)
                received_a, received_b = run(sender, receiver, False, 5)
                assert sender(received_a) == ()
                assert receiver(received_b) == (aa[b],)
                counts['ot_cases'] += 1
    for c, r, m, sf, mf, salt in itertools.product(range(4), range(6), range(1, 7),
                                                (False, True), (False, True), range(3)):
        composition_case(c, r, m, sf, mf, salt)
        counts['composition_cases'] += 1
    # Reproduce the documented zero-main counterexample with rho = swap.
    x, y = (1,), (0,)
    p = lambda h: x if not h else h[0]
    v = lambda h: y if len(h) == 1 else h[0] if h else ()
    hp, hv = run(p, v, False, 3)
    assert (p(hp), v(hv)) == (y, x)
    def sub_history(hist, before, alice_receives):
        return [hist[q] if q < len(hist) else () for q in range(before)
                if (q % 2 == 1) == alice_receives]

    def swap_composed_p(hist):
        q = len(hist)
        if q < 3:
            return p(sub_history(hist, q, True)) if q % 2 == 0 else ()
        return p(sub_history(hist, 3, True))  # zero-move main's local answer

    def swap_composed_v(hist):
        q = max(0, len(hist) - 1)
        if q < 3:
            return v(sub_history(hist, q, False)) if q % 2 == 1 else ()
        return v(sub_history(hist, 3, False))

    chp, chv = run(swap_composed_p, swap_composed_v, False, 6)
    assert swap_composed_p(chp) == y
    assert swap_composed_v(chv) == () != x
    # Correct first opening need not mean unique opening: with all Boolean
    # labels equal, a constant label encryption opens every row correctly.
    enc = lambda ks, o: (tuple(ks), o)
    dec = lambda ks, c: c[1] if tuple(ks) == c[0] else None
    table = [enc((0, 0), 0) for _ in words(2)]
    for assignment in words(2):
        openings = [dec((0, 0), c) for c in table]
        assert openings[0] == 0 and sum(o is not None for o in openings) == 4
    # Without sink outputs, output decoding pairs reveal the other input.
    ka, kb, kg = ('a0', 'a1'), ('b0', 'b1'), ('g0', 'g1')
    gate = [enc((ka[a], kb[b]), kg[a & b]) for a, b in words(2)]
    for secret in (0, 1):
        real_output = (0, 0 & secret)
        assert real_output == (0, 0)
        opened = [dec((ka[1], kb[secret]), c) for c in gate]
        recovered = next(o for o in opened if o is not None)
        assert kg.index(recovered) == secret
    # If output labels coincide, decodeOut chooses false even for true.
    decode_out = lambda k, k0, k1: 0 if k == k0 else int(k == k1)
    assert decode_out((), (), ()) == 0
    print(json.dumps({'status': 'PASS', **counts,
                      'zero_length_malformed_ciphertext': 'accepted, as documented finding',
                      'zero_main_counterexample': 'Bob outputs empty instead of x',
                      'good_does_not_imply_unique': 'four successful rows',
                      'non_sink_output_attack': 'same ideal output, other input recovered',
                      'coincident_output_keys': 'decodeOut returns false'}, indent=2))


if __name__ == '__main__':
    main()
