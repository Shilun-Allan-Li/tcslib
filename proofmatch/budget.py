from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal

from proofmatch.agents import DEFAULT_MODEL


# Anthropic list prices in USD per million input/output tokens.
MODEL_PRICES: dict[str, tuple[Decimal, Decimal]] = {
    "claude-opus-4-8": (Decimal("5.00"), Decimal("25.00")),
    "claude-sonnet-5": (Decimal("3.00"), Decimal("15.00")),
    "claude-haiku-4-5": (Decimal("1.00"), Decimal("5.00")),
}


class BudgetExceeded(RuntimeError):
    pass


@dataclass(frozen=True)
class StageEstimate:
    name: str
    input_tokens: int
    output_tokens: int
    usd: Decimal


@dataclass
class Budget:
    cap_usd: Decimal | None = None
    spent_usd: Decimal = Decimal("0")

    @property
    def remaining_usd(self) -> Decimal | None:
        if self.cap_usd is None:
            return None
        return max(Decimal("0"), self.cap_usd - self.spent_usd)

    def require(self, estimate: StageEstimate) -> None:
        remaining = self.remaining_usd
        if remaining is not None and estimate.usd > remaining:
            raise BudgetExceeded(
                f"{estimate.name} is estimated at ${estimate.usd:.2f}, "
                f"but the run has only remaining ${remaining:.2f}"
            )
        self.spent_usd += estimate.usd


def token_cost(
    model: str,
    input_tokens: int,
    output_tokens: int,
) -> Decimal:
    try:
        input_rate, output_rate = MODEL_PRICES[model]
    except KeyError as error:
        raise ValueError(f"unknown model: {model}") from error
    if input_tokens < 0 or output_tokens < 0:
        raise ValueError("token counts cannot be negative")
    return (
        Decimal(input_tokens) * input_rate
        + Decimal(output_tokens) * output_rate
    ) / Decimal(1_000_000)


def estimate_cleanup(
    raw_characters: int,
    model: str = DEFAULT_MODEL,
) -> StageEstimate:
    if raw_characters < 0:
        raise ValueError("raw_characters cannot be negative")
    estimated_tokens = (raw_characters + 3) // 4
    return StageEstimate(
        name="cleanup",
        input_tokens=estimated_tokens,
        output_tokens=estimated_tokens,
        usd=token_cost(model, estimated_tokens, estimated_tokens),
    )
