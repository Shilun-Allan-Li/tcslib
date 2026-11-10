"""Independent finite checks of the combined mathematical and raw-word statements.

This is supporting evidence, not Lean execution or a proof of general statements.
Run with python3 -I, serially after native checks. No external packages are used.
"""

from fractions import Fraction
from functools import lru_cache
from itertools import product
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def words(length):
    return list(product((False, True), repeat=length))


def pair(a, b):
    return tuple(v for bit in a for v in (bit, bit)) + (False, True) + tuple(b)


@lru_cache(maxsize=50000)
def parse(z):
    first = []
    for i in range(0, len(z) - 1, 2):
        a, b = z[i:i + 2]
        if a == b:
            first.append(a)
        elif not a and b:
            return tuple(first), z[i + 2:]
        else:
            return (), ()
    return (), ()


def fst(z):
    return parse(tuple(z))[0]


def snd(z):
    return parse(tuple(z))[1]


def value(z):
    result = 0
    for bit in z:
        result = 2 * result + int(bit)
    return result


def write(n, width):
    return tuple(bool((n >> i) & 1) for i in range(width - 1, -1, -1))


def normalize(z, width):
    return write(value(z), width)


def scalar(op, c, a, b):
    return write(op(value(a), value(b)), len(c))


def dot_step(z):
    c, xs, ys, acc = fst(z), fst(snd(z)), fst(snd(snd(z))), snd(snd(snd(z)))
    width = len(c)
    mul = scalar(lambda a, b: a * b, c, xs[:width], ys[:width])
    return pair(c, pair(xs[width:], pair(ys[width:],
        scalar(lambda a, b: a + b, c, acc, mul))))


def repeat(step, n, z):
    for _ in range(n):
        z = step(z)
    return z


def dot(c, n, x, y):
    done = repeat(dot_step, len(n), pair(c, pair(x, pair(y, (False,) * len(c)))))
    return snd(snd(snd(done)))


def matrix_step(z):
    ctx = fst(z)
    c, n, v = fst(ctx), fst(snd(ctx)), snd(snd(ctx))
    rows, out = fst(snd(z)), snd(snd(z))
    length = len(n) * len(c)
    return pair(ctx, pair(rows[length:], out + dot(c, n, rows[:length], v)))


def matrix(width, rows, columns, a, v):
    c, n = (False,) * width, (True,) * columns
    ctx = pair(c, pair(n, v))
    return snd(snd(repeat(matrix_step, rows, pair(ctx, pair(a, ())))))


def collision_step(z):
    c, xs, ys, out = fst(z), fst(snd(z)), fst(snd(snd(z))), snd(snd(snd(z)))
    x, y = (xs or (False,))[0], (ys or (False,))[0]
    block = (not x and y,) + normalize((x != y,), len(c))
    return pair(c, pair(xs[1:], pair(ys[1:], out + block)))


def collision(width, count, raw):
    init = pair((False,) * width, pair(raw[:count], pair(raw[count:], ())))
    return snd(snd(snd(repeat(collision_step, count, init))))


def expand_step(z):
    c, bits, out = fst(z), fst(snd(z)), snd(snd(z))
    return pair(c, pair(bits[1:], out + normalize(((bits or (False,))[0],), len(c))))


def expand(width, count, raw):
    return snd(snd(repeat(expand_step, count, pair((False,) * width, pair(raw, ())))))


def determinant(a):
    rows = [[Fraction(v) for v in row] for row in a]
    result = Fraction(1)
    for j in range(len(rows)):
        pivot = next((i for i in range(j, len(rows)) if rows[i][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            rows[j], rows[pivot] = rows[pivot], rows[j]
            result = -result
        p = rows[j][j]
        result *= p
        for i in range(j + 1, len(rows)):
            scale = rows[i][j] / p
            for k in range(j + 1, len(rows)):
                rows[i][k] -= scale * rows[j][k]
    return result


def anti(v):
    n = len(v)
    return [[v[(j - i) % n] * (1 if i <= j else -1)
        for j in range(n)] for i in range(n)]


def main():
    counts = {}
    # Model the actual aligned pair parser and total projections, not merely valid pairs.
    raw_words = [w for n in range(9) for w in words(n)]
    growth_states = list(raw_words)
    small = [w for n in range(4) for w in words(n)]
    for width in range(5):
        c = (False,) * width
        for x in small:
            for y in small:
                growth_states.append(pair(c, pair(x, pair(y, x))))
                growth_states.append(pair(pair(c, pair(x, y)), pair(x, y)))
    for z in growth_states:
        for step in [dot_step, matrix_step, collision_step, expand_step]:
            output = step(z)
            assert fst(output) == fst(z)
            assert len(output) <= len(z) + 8 * (len(fst(z)) + 1)
    counts['raw_and_framed_growth_states'] = len(growth_states)
    counts['growth_comparisons'] = 4 * len(growth_states)
    comparisons = 0
    for width in range(5):
        for n in range(5):
            for x in small:
                for y in small:
                    actual = dot((True,) * width, (False,) * n, x, y)
                    expected = sum(value(x[i * width:(i + 1) * width]) *
                        value(y[i * width:(i + 1) * width]) for i in range(n))
                    assert actual == write(expected, width)
                    comparisons += 1
    counts['raw_dot_comparisons'] = comparisons
    comparisons = 0
    for width in range(4):
        for n in range(4):
            for raw in raw_words:
                bits = (raw + (False,) * (2 * n))[:2 * n]
                assert expand(width, n, raw) == tuple(v for bit in bits[:n]
                    for v in write(int(bit) % (1 << width), width))
                expected = tuple(v for x, y in zip(bits[:n], bits[n:])
                    for v in ((x < y,) + write(abs(int(x) - int(y)), width)))
                assert collision(width, n, raw) == expected
                comparisons += 2
    counts['raw_expansion_and_signed_comparisons'] = comparisons
    comparisons = 0
    for width in range(4):
        for n in range(4):
            for m in range(4):
                for a, v in zip(raw_words[::7], raw_words[::11]):
                    expected = tuple(bit for i in range(m) for bit in write(sum(
                        value(a[(i * n + j) * width:(i * n + j + 1) * width]) *
                        value(v[j * width:(j + 1) * width]) for j in range(n)), width))
                    assert matrix(width, m, n, a, v) == expected
                    comparisons += 1
    counts['raw_matrix_comparisons'] = comparisons
    comparisons = 0
    for b in range(6):
        for a in range(1, 6):
            p, delta, q = 1 << b, 1 << a, 1 << (b + a)
            for m in range(p):
                for e in range(-delta // 2 + 1, delta // 2):
                    z = (delta * m + e) % q
                    assert ((z + delta // 2) // delta) % p == m
                    comparisons += 1
    counts['strict_scalar_rounding_comparisons'] = comparisons
    # Independently count images of small bounded-noise LTF keys.
    inversions = images = 0
    for b in range(4):
        for w in range(3):
            n = b * w
            for d in range(3):
                for bound in range(2):
                    a = max(1, (2 * n * bound).bit_length())
                    delta, q = 1 << a, 1 << (b + a)
                    for pattern in range(3):
                        amat = [[(i + 2 * j + pattern) % q for j in range(d)] for i in range(n)]
                        tmat = [[(2 * i + j + pattern) % q for j in range(d)] for i in range(w)]
                        errors = [[bound * (((i + j + pattern) % 3) - 1)
                            for j in range(w)] for i in range(n)]
                        lossy_images = set()
                        for x in words(n):
                            first = tuple(sum(amat[i][j] * x[i] for i in range(n)) % q for j in range(d))
                            err = tuple(sum(errors[i][j] * x[i] for i in range(n)) for j in range(w))
                            message = tuple(sum(int(x[j * b + k]) << k for k in range(b)) for j in range(w))
                            second = tuple((sum(tmat[j][k] * first[k] for k in range(d)) + err[j] +
                                delta * message[j]) % q for j in range(w))
                            recovered = tuple(((second[j] - sum(tmat[j][k] * first[k]
                                for k in range(d))) % q + delta // 2) // delta % (1 << b) for j in range(w))
                            assert recovered == message
                            inversions += 1
                            lossy_second = tuple((sum(tmat[j][k] * first[k] for k in range(d)) + err[j]) % q
                                for j in range(w))
                            lossy_images.add((first, lossy_second))
                        assert len(lossy_images) <= q ** d * (2 * n * bound + 1) ** w
                        images += 1
    counts['gadget_inversion_inputs'] = inversions
    counts['lossy_image_budgets'] = images
    rank_checks = 0
    for u in range(4):
        w = 1 << u
        vectors = list(product((-1, 0, 1), repeat=w)) if w <= 4 else [
            tuple(((j * j + k * j + k) % 5) - 2 for j in range(w)) for k in range(31)]
        for v in vectors:
            if any(v):
                assert determinant(anti(v)) != 0
                rank_checks += 1
    counts['anti_cyclic_rational_rank_checks'] = rank_checks
    # Explicit full public matrices, not only the already-cancelled residual formula.
    branch_inputs = 0
    for u in range(3):
        w = 1 << u
        for b in range(3):
            n = w * b
            a = max(1, (2 * n).bit_length())
            delta, p0, q = 1 << a, 1 << (b + u + 1), 1 << (b + u + 1 + a)
            amat = [(i + 1) % q for i in range(n)]
            tmat = [(j + 2) % q for j in range(w)]
            errors = [[((i + j) % 3) - 1 for j in range(w)] for i in range(n)]
            branches = words(w)
            for star in branches:
                for v in branches:
                    if w == 4 and (sum(v) + 2 * sum(star)) % 4:
                        continue
                    diff = anti([int(x) - int(y) for x, y in zip(v, star)])
                    image = set()
                    for x in words(n):
                        first = sum(amat[i] * x[i] for i in range(n)) % q
                        second = tuple(sum((amat[i] * tmat[j] + errors[i][j] +
                            delta * sum(((1 << (i % b)) if b and i // b == k else 0) *
                                diff[k][j] for k in range(w))) * x[i] for i in range(n)) % q
                            for j in range(w))
                        image.add((first, second))
                        branch_inputs += 1
                    if v != star:
                        assert len(image) == (1 << n)
                    else:
                        assert len(image) <= q * (2 * n + 1) ** w
    counts['all_but_one_input_evaluations'] = branch_inputs
    result = dict(counts=counts, all_passed=True, lean_executed=False,
        general_mathematics_proved=False, polynomial_time_proved=False,
        malformed_pair_parser_modeled=True, strict_bounds_and_degenerate_dimensions=True,
        no_hardness_or_completed_primitive_claim=True)
    (HERE / 'evidence/finite-semantics.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
