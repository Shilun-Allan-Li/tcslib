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

    def test_unknown_model_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "unknown model"):
            token_cost("imaginary", 100, 100)


if __name__ == "__main__":
    unittest.main()
