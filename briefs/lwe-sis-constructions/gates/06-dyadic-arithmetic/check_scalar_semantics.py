"""Compare finite bit-list operation models with independent integer residues.

This is a supporting mathematical check, not Lean execution, parser verification
or a complexity proof. Run serially after native jobs, with python3 -I.
"""

from itertools import product
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def read_msb(word):
    value = 0
    for bit in word:
        value = 2 * value + int(bit)
    return value


def read_le(word):
    return sum(int(bit) << index for index, bit in enumerate(word))


def le_bits(value):
    return tuple(bool((value >> index) & 1) for index in range(value.bit_length()))


def to_le(word):
    return le_bits(read_le(word[::-1]))


def normalize(word, width):
    return ((False,) * width + word)[len(word):]


def from_le(word, width):
    return normalize(word[::-1], width)


def reference_word(value, width):
    return tuple(bool((value >> index) & 1) for index in range(width - 1, -1, -1))


def check_pair(left, right, width):
    left_value, right_value = read_msb(left), read_msb(right)
    left_le, right_le = to_le(left), to_le(right)
    modulus_word = (True,) + (False,) * width
    prepared_left = le_bits(read_le(left_le) + read_le(to_le(modulus_word)))
    prepared_right = to_le(normalize(right, width))
    assert read_le(prepared_right) <= read_le(prepared_left)
    arithmetic_words = [
        le_bits(read_le(left_le) + read_le(right_le)),
        le_bits(read_le(left_le) * read_le(right_le)),
        le_bits(max(read_le(prepared_left) - read_le(prepared_right), 0)),
    ]
    reference_values = [left_value + right_value, left_value * right_value,
                        left_value - right_value]
    modulus = 1 << width
    for word, value in zip(arithmetic_words, reference_values):
        output = from_le(word, width)
        assert len(output) == width
        assert output == reference_word(value % modulus, width)


def main():
    words = [word for length in range(7) for word in product((False, True), repeat=length)]
    ordinary, boundary = 0, 0
    for width in range(13):
        for left in words:
            for right in words:
                check_pair(left, right, width)
                ordinary += 1
        modulus = 1 << width
        values = sorted({0, 1, modulus - 1, modulus, modulus + 1,
                         2 * modulus + 3, (1 << (width + 3)) - 1})
        for left in values:
            for right in values:
                check_pair(reference_word(left, max(1, left.bit_length())),
                           reference_word(right, max(1, right.bit_length())), width)
                boundary += 1
    result = dict(widths=list(range(13)), words_through_length=6, words=len(words),
                  word_pair_width_scenarios=ordinary, boundary_scenarios=boundary,
                  scalar_operation_comparisons=3 * (ordinary + boundary),
                  leading_zeros_empty_words_and_zero_width_included=True,
                  overlong_operand_values_included=True,
                  malformed_pair_parser_modeled=False,
                  lean_executed=False, complexity_proved=False,
                  underflow_counterexample=dict(width=2, left=0, right=5,
                      plain_natural_subtraction=0,
                      add_modulus_without_right_normalization=0,
                      correct_residue=3))
    (HERE / "evidence/finite-semantics.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
