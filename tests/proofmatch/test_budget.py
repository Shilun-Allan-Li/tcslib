import unittest
from decimal import Decimal

from proofmatch.budget import (
    Budget,
    BudgetExceeded,
    StageEstimate,
    estimate_cleanup,
    token_cost,
)


class BudgetTests(unittest.TestCase):
    def test_rejects_stage_that_exceeds_remaining_fixture_cap(self):
        budget = Budget(Decimal("1.00"), Decimal("0.82"))

        with self.assertRaisesRegex(BudgetExceeded, r"remaining \$0\.18"):
            budget.require(
                StageEstimate(
                    "compare",
                    input_tokens=80_000,
                    output_tokens=8_000,
                    usd=Decimal("0.25"),
                )
            )

    def test_accepting_stage_reserves_its_estimated_cost(self):
        budget = Budget(Decimal("1.00"), Decimal("0.10"))

        budget.require(StageEstimate("cleanup", 10_000, 5_000, Decimal("0.04")))

        self.assertEqual(budget.spent_usd, Decimal("0.14"))

    def test_cleanup_estimate_rounds_characters_up_conservatively(self):
        estimate = estimate_cleanup(raw_characters=20_001)

        self.assertEqual(estimate.input_tokens, 5_001)
        self.assertEqual(estimate.output_tokens, 5_001)
        self.assertEqual(estimate.usd, Decimal("0.15003"))

    def test_token_cost_uses_separate_input_and_output_rates(self):
        self.assertEqual(
            token_cost("claude-opus-4-8", input_tokens=1_000_000, output_tokens=100_000),
            Decimal("7.50"),
        )

    def test_unknown_model_is_estimated_at_fallback_rates(self):
        # A model with no price row (a new release, a dated id) is estimated at the
        # opus-class fallback rate instead of failing the pre-flight.
        from proofmatch.budget import ESTIMATE_FALLBACK_MODEL
        self.assertEqual(
            token_cost("imaginary", 1_000_000, 1_000_000),
            token_cost(ESTIMATE_FALLBACK_MODEL, 1_000_000, 1_000_000),
        )

    def test_versioned_model_ids_use_their_family_row(self):
        self.assertEqual(token_cost("gpt-5-2026-01-01", 1_000_000, 0), Decimal("1.25"))
        self.assertEqual(token_cost("claude-opus-4-8-20260101", 1_000_000, 0), Decimal("5.00"))


if __name__ == "__main__":
    unittest.main()
