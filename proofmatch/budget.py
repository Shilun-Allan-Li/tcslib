from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal

from proofmatch.model_policy import DEFAULT_MODEL


# List prices in USD per million input/output tokens, both vendors. These only
# feed the pre-flight ESTIMATES and the Codex spend (whose CLI reports tokens,
# not dollars); the Claude CLI reports `total_cost_usd` itself, so a missing or
# stale row here never misreports what a Claude run cost.
MODEL_PRICES: dict[str, tuple[Decimal, Decimal]] = {
    # Anthropic
    "claude-opus-4-8": (Decimal("5.00"), Decimal("25.00")),
    "claude-sonnet-5": (Decimal("3.00"), Decimal("15.00")),
    "claude-haiku-4-5": (Decimal("1.00"), Decimal("5.00")),
    # OpenAI (via the Codex CLI)
    "gpt-5": (Decimal("1.25"), Decimal("10.00")),
    "gpt-5-codex": (Decimal("1.25"), Decimal("10.00")),
    "gpt-5-mini": (Decimal("0.25"), Decimal("2.00")),
    "gpt-5-nano": (Decimal("0.05"), Decimal("0.40")),
    "o3": (Decimal("2.00"), Decimal("8.00")),
    "o4-mini": (Decimal("1.10"), Decimal("4.40")),
    "gpt-4.1": (Decimal("2.00"), Decimal("8.00")),
}

#: A model with no price row is estimated at this row's rate (opus-class, the
#: pipeline's floor), and the estimate is flagged as approximate.
ESTIMATE_FALLBACK_MODEL = "claude-opus-4-8"
_warned_models: set[str] = set()


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


def price_row(model: str) -> tuple[Decimal, Decimal] | None:
    """The price row for `model`, or for its family when the id carries a date or
    version suffix (`gpt-5-2026-01-01`, `claude-opus-4-8-20260101`)."""
    if model in MODEL_PRICES:
        return MODEL_PRICES[model]
    for known in sorted(MODEL_PRICES, key=len, reverse=True):
        if model.startswith(known + "-") or model.startswith(known + "."):
            return MODEL_PRICES[known]
    return None


def token_cost(
    model: str,
    input_tokens: int,
    output_tokens: int,
) -> Decimal:
    row = price_row(model)
    if row is None:
        if model not in _warned_models:
            _warned_models.add(model)
            print(f"  note: no price table entry for {model}; estimating at "
                  f"{ESTIMATE_FALLBACK_MODEL} rates (Claude spend is still tracked exactly)")
        row = MODEL_PRICES[ESTIMATE_FALLBACK_MODEL]
    input_rate, output_rate = row
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
