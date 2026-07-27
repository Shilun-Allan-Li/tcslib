from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from proofmatch.artifacts import sha256_file


Runner = Callable[..., subprocess.CompletedProcess[str]]


@dataclass(frozen=True)
class PageDiagnostic:
    page_number: int
    confidence: float
    reasons: tuple[str, ...]


@dataclass(frozen=True)
class ExtractionReport:
    source_pdf: str
    source_fingerprint: str
    extractor: str
    page_count: int
    diagnostics: tuple[PageDiagnostic, ...]


def split_pages(extracted_text: str) -> list[str]:
    pages = extracted_text.split("\f")
    if pages and pages[-1] == "":
        pages.pop()
    return pages


def diagnose_page(page_number: int, text: str) -> PageDiagnostic:
    reasons: list[str] = []
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    if not lines:
        reasons.append("empty-page")
    else:
        short_lines = sum(len(line) <= 3 for line in lines)
        if len(lines) >= 5 and short_lines / len(lines) >= 0.35:
            reasons.append("fragmented-lines")
        detached_symbols = {"→", "←", "≤", "≥", "=", "∧", "∨", "−", "+", "/"}
        if any(line in detached_symbols for line in lines):
            reasons.append("detached-math-symbols")
        replacement_count = text.count("\ufffd") + text.count("(cid:")
        if replacement_count:
            reasons.append("encoding-artifacts")
    confidence = max(0.0, 1.0 - 0.2 * len(reasons))
    return PageDiagnostic(page_number, confidence, tuple(reasons))


def format_raw_markdown(
    source_fingerprint: str,
    extractor: str,
    pages: list[str],
) -> str:
    header = (
        "<!-- generated-by: proofmatch local extraction -->\n"
        f"<!-- source-pdf-sha256: {source_fingerprint} -->\n"
        f"<!-- extractor: {extractor} -->\n\n"
    )
    sections = []
    for page_number, page in enumerate(pages, start=1):
        sections.append(f"<!-- pdf-page: {page_number} -->\n{page}")
    return header + "\n\n".join(sections) + "\n"


def _run(
    runner: Runner,
    command: list[str],
) -> subprocess.CompletedProcess[str]:
    try:
        result = runner(
            command,
            check=True,
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise RuntimeError(f"local PDF command failed: {' '.join(command)}") from error
    return result


def extract_pdf(
    pdf: Path,
    raw_markdown: Path,
    runner: Runner = subprocess.run,
) -> ExtractionReport:
    if not pdf.is_file():
        raise FileNotFoundError(pdf)
    version = _run(runner, ["pdf2txt.py", "--version"]).stdout.strip()
    extracted = _run(runner, ["pdf2txt.py", "-o", "-", str(pdf)]).stdout
    pages = split_pages(extracted)
    fingerprint = sha256_file(pdf)
    raw_markdown.parent.mkdir(parents=True, exist_ok=True)
    raw_markdown.write_text(
        format_raw_markdown(fingerprint, version, pages),
        encoding="utf-8",
    )
    diagnostics = tuple(
        diagnose_page(page_number, page)
        for page_number, page in enumerate(pages, start=1)
    )
    return ExtractionReport(
        source_pdf=str(pdf),
        source_fingerprint=fingerprint,
        extractor=version,
        page_count=len(pages),
        diagnostics=diagnostics,
    )


def render_page(pdf: Path, page_number: int, output_png: Path) -> Path:
    if page_number < 1:
        raise ValueError("page_number must be positive")
    output_png.parent.mkdir(parents=True, exist_ok=True)
    command = [
        "gs",
        "-q",
        "-dSAFER",
        "-dBATCH",
        "-dNOPAUSE",
        "-sDEVICE=png16m",
        "-r180",
        f"-dFirstPage={page_number}",
        f"-dLastPage={page_number}",
        f"-sOutputFile={output_png}",
        str(pdf),
    ]
    try:
        subprocess.run(command, check=True, capture_output=True)
    except (OSError, subprocess.CalledProcessError) as error:
        raise RuntimeError(f"could not render PDF page {page_number}") from error
    return output_png
