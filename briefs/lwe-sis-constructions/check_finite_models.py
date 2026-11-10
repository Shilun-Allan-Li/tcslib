#!/usr/bin/env python3
"""Exact small-instance checks of the planned LWE/SIS constructions.

Run with python3 -I. These checks use independent elementary definitions, not Lean
evaluation. Passing is corroboration of the mathematical conventions and boundary
conditions; it does not establish Lean elaboration or asymptotic security.
"""

import itertools
import json
from fractions import Fraction


def vectors(modulus, length):
    return itertools.product(range(modulus), repeat=length)


def dot(left, right):
    return sum(x * y for x, y in zip(left, right, strict=True))


def distance(value, center, modulus):
    residue = (value - center) % modulus
    return min(residue, modulus - residue)


def decrypt_bit(secret, a, value, modulus):
    residual = (value - dot(a, secret)) % modulus
    return int(distance(residual, modulus // 2, modulus) < distance(residual, 0, modulus))


def shared_secret_check():
    # Condition on a public matrix with both entries 1, and take zero noise.
    # Real samples always agree; fresh-secret-per-row samples agree only 1/q of the time.
    modulus = 3
    common = [(secret, secret) for secret in range(modulus)]
    fresh = list(vectors(modulus, 2))
    common_agreement = Fraction(sum(x == y for x, y in common), len(common))
    fresh_agreement = Fraction(sum(x == y for x, y in fresh), len(fresh))
    assert common_agreement == 1
    assert fresh_agreement == Fraction(1, modulus)
    return {"modulus": modulus, "common_agreement": str(common_agreement),
            "fresh_agreement": str(fresh_agreement)}


def symmetric_correctness():
    count = 0
    for modulus in (4, 8, 12):
        bound = modulus // 4 - 1
        for secret in vectors(modulus, 1):
            for a in vectors(modulus, 1):
                for error in range(-bound, bound + 1):
                    for bit in (0, 1):
                        value = (dot(a, secret) + error + bit * (modulus // 2)) % modulus
                        assert decrypt_bit(secret, a, value, modulus) == bit
                        count += 1
    # Strictness matters: q/4 is a tie, not an admissible error for perfect correctness.
    assert decrypt_bit((0,), (0,), 2 + 4, 8) == 0
    return {"cases": count, "tie_boundary_rejected": True}


def public_key_correctness():
    modulus, samples, bound = 12, 2, 1
    assert 4 * samples * bound < modulus
    count = 0
    selectors = list(vectors(2, samples))
    for a in vectors(modulus, samples):
        for secret in range(modulus):
            for errors in itertools.product(range(-bound, bound + 1), repeat=samples):
                values = tuple((ai * secret + ei) % modulus
                               for ai, ei in zip(a, errors, strict=True))
                for selector in selectors:
                    cipher_a = dot(selector, a) % modulus
                    for bit in (0, 1):
                        cipher_b = (dot(selector, values) + bit * (modulus // 2)) % modulus
                        assert decrypt_bit((secret,), (cipher_a,), cipher_b, modulus) == bit
                        count += 1
    return {"modulus": modulus, "samples": samples, "error_bound": bound, "cases": count}


def sis_collisions():
    collisions = 0
    for modulus, columns in ((2, 2), (3, 2), (5, 3)):
        inputs = list(vectors(2, columns))
        assert len(inputs) > modulus
        for row in vectors(modulus, columns):
            saw_collision = False
            for left, right in itertools.combinations(inputs, 2):
                if dot(row, left) % modulus != dot(row, right) % modulus:
                    continue
                difference = tuple(x - y for x, y in zip(left, right, strict=True))
                assert any(difference)
                assert dot(row, difference) % modulus == 0
                assert sum(x * x for x in difference) <= columns
                saw_collision = True
                collisions += 1
            assert saw_collision
    # The SIS relation uses nonzero integers, even when their residue vector is zero.
    modulus = 5
    trivial_integer_vector = (modulus, 0)
    assert any(trivial_integer_vector)
    assert all(x % modulus == 0 for x in trivial_integer_vector)
    assert sum(x * x for x in trivial_integer_vector) == modulus**2
    return {"collisions_checked": collisions, "integer_nonzero_boundary_checked": True}


def subset_hash_universality():
    pairs = 0
    for modulus, rows, outputs in ((2, 3, 2), (4, 2, 2)):
        inputs = list(vectors(2, rows))
        matrices = list(vectors(modulus, rows * outputs))

        def image(matrix, selector):
            return tuple(sum(selector[i] * matrix[i * outputs + j] for i in range(rows))
                         % modulus for j in range(outputs))

        for left, right in itertools.combinations(inputs, 2):
            collision_count = sum(image(matrix, left) == image(matrix, right)
                                  for matrix in matrices)
            assert Fraction(collision_count, len(matrices)) == Fraction(1, modulus**outputs)
            pairs += 1
    return {"distinct_input_pairs_checked": pairs, "composite_modulus_included": True}


def main():
    results = {
        "kind": "independent finite mathematical sanity checks",
        "native_lean_elaboration": False,
        "asymptotic_security_proved": False,
        "common_secret": shared_secret_check(),
        "symmetric_correctness": symmetric_correctness(),
        "public_key_correctness": public_key_correctness(),
        "sis_collision_reduction": sis_collisions(),
        "subset_hash_universality": subset_hash_universality(),
    }
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
