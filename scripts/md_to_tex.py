r"""Markdown-flavoured Lean docstring prose -> blueprint LaTeX.

The GraphTheory chapters were originally produced from Lean docstrings by a
`blueprint_from_docstring.py` that is no longer in the repo.  This module
re-implements just the prose conversion it performed, so that
`blueprint_restate.py` can rebuild the *statement* half of those entries.

Conversion is deliberately conservative: anything it does not recognise is
passed through with the LaTeX-special characters escaped, so a surprising
docstring degrades to plain text rather than to broken LaTeX.
"""

from __future__ import annotations

import re

#: Unicode -> LaTeX math body (no surrounding `$`).  Everything here is rendered
#: inside math mode; `math_wrap` decides whether a `$...$` pair is needed.
MATH: dict[str, str] = {
    "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta", "ε": r"\varepsilon",
    "ζ": r"\zeta", "η": r"\eta", "θ": r"\theta", "ι": r"\iota", "κ": r"\kappa",
    "λ": r"\lambda", "μ": r"\mu", "ν": r"\nu", "ξ": r"\xi", "π": r"\pi",
    "ρ": r"\rho", "σ": r"\sigma", "τ": r"\tau", "υ": r"\upsilon", "φ": r"\varphi",
    "χ": r"\chi", "ψ": r"\psi", "ω": r"\omega",
    "Γ": r"\Gamma", "Δ": r"\Delta", "Θ": r"\Theta", "Λ": r"\Lambda", "Ξ": r"\Xi",
    "Π": r"\Pi", "Σ": r"\Sigma", "Φ": r"\Phi", "Ψ": r"\Psi", "Ω": r"\Omega",
    "ℕ": r"\mathbb{N}", "ℤ": r"\mathbb{Z}", "ℚ": r"\mathbb{Q}", "ℝ": r"\mathbb{R}",
    "ℂ": r"\mathbb{C}", "𝔽": r"\mathbb{F}", "𝓑": r"\mathcal{B}", "𝓒": r"\mathcal{C}",
    "𝓟": r"\mathcal{P}", "𝓝": r"\mathcal{N}",
    "≤": r"\le", "≥": r"\ge", "≠": r"\ne", "≡": r"\equiv", "≅": r"\cong",
    "∼": r"\sim", "≈": r"\approx", "≪": r"\ll", "≫": r"\gg", "⊑": r"\sqsubseteq",
    "∈": r"\in", "∉": r"\notin", "∋": r"\ni", "⊂": r"\subset", "⊄": r"\not\subset",
    "⊆": r"\subseteq", "⊈": r"\nsubseteq", "⊃": r"\supset", "⊇": r"\supseteq",
    "∩": r"\cap", "∪": r"\cup", "∅": r"\emptyset", "∖": r"\setminus",
    "→": r"\to", "↦": r"\mapsto", "←": r"\leftarrow", "↔": r"\leftrightarrow",
    "⇒": r"\Rightarrow", "⇐": r"\Leftarrow", "⇔": r"\Leftrightarrow",
    "⟹": r"\Longrightarrow", "⟸": r"\Longleftarrow", "⟺": r"\Longleftrightarrow",
    "∀": r"\forall", "∃": r"\exists", "¬": r"\neg", "∧": r"\land", "∨": r"\lor",
    "∑": r"\sum", "∏": r"\prod", "∫": r"\int", "√": r"\sqrt{}", "∂": r"\partial",
    "±": r"\pm", "∓": r"\mp", "×": r"\times", "÷": r"\div", "·": r"\cdot",
    "∘": r"\circ", "⊕": r"\oplus", "⊗": r"\otimes", "⊔": r"\sqcup", "⊓": r"\sqcap",
    "⊤": r"\top", "⊥": r"\bot", "∣": r"\mid", "∤": r"\nmid", "∞": r"\infty",
    "⌊": r"\lfloor", "⌋": r"\rfloor", "⌈": r"\lceil", "⌉": r"\rceil",
    "‖": r"\|", "⟨": r"\langle", "⟩": r"\rangle", "□": r"\square", "⋯": r"\cdots",
    "½": r"\tfrac{1}{2}", "⅓": r"\tfrac{1}{3}", "¼": r"\tfrac{1}{4}",
    "ᗮ": r"^{\perp}", "⃗": "",
}

#: Sub/superscript characters -> the plain character plus the script it carries.
SUBSCRIPT = {
    "₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4", "₅": "5", "₆": "6",
    "₇": "7", "₈": "8", "₉": "9", "ᵢ": "i", "ⱼ": "j", "ₖ": "k", "ₘ": "m",
    "ₙ": "n", "ₚ": "p", "ᵥ": "v", "ₓ": "x", "₊": "+", "₋": "-",
}
SUPERSCRIPT = {
    "⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4", "⁵": "5", "⁶": "6",
    "⁷": "7", "⁸": "8", "⁹": "9", "⁺": "+", "⁻": "-", "ⁿ": "n", "ᵏ": "k",
    "ᵀ": "T", "ᶜ": "c", "ⁱ": "i",
}

#: Latin letters carrying a combining accent, plus precomposed forms.
ACCENTED = {
    "á": r"\'a", "é": r"\'e", "í": r"\'i", "ó": r"\'o", "ú": r"\'u",
    "à": r"\`a", "è": r"\`e", "ì": r"\`i", "ò": r"\`o", "ù": r"\`u",
    "â": r"\^a", "ê": r"\^e", "î": r"\^i", "ô": r"\^o", "û": r"\^u",
    "ä": r'\"a', "ë": r'\"e', "ï": r'\"i', "ö": r'\"o', "ü": r'\"u',
    "ő": r"\H{o}", "ű": r"\H{u}", "ç": r"\c{c}", "ñ": r"\~n", "å": r"\aa{}",
    "ø": r"\o{}", "š": r"\v{s}", "č": r"\v{c}", "ž": r"\v{z}", "ř": r"\v{r}",
    "Á": r"\'A", "É": r"\'E", "Ö": r'\"O', "Ő": r"\H{O}",
}

#: Combining marks that follow the letter they decorate.
COMBINING = {
    "̄": "bar",      # macron, e.g. S̄
    "̂": "hat",      # circumflex
    "̆": "breve",    # e.g. Erdős's Ő is precomposed; breve shows up on ŭ
    "̃": "tilde",
}
COMBINING_TEX = {"bar": r"\bar", "hat": r"\hat", "breve": r"\breve", "tilde": r"\tilde"}

_ESCAPE = {
    "\\": r"\textbackslash{}",
    "&": r"\&",
    "%": r"\%",
    "$": r"\$",
    "#": r"\#",
    "_": r"\_",
    "{": r"\{",
    "}": r"\}",
    "~": r"\textasciitilde{}",
    "^": r"\textasciicircum{}",
}


def _apply_combining(s: str) -> str:
    """`S̄` -> `$\\bar{S}$`; must run before the per-character passes."""
    out = []
    i = 0
    while i < len(s):
        ch = s[i]
        nxt = s[i + 1] if i + 1 < len(s) else ""
        kind = COMBINING.get(nxt)
        if kind and (ch.isalnum() or ch in MATH):
            base = MATH.get(ch, ch)
            out.append(f"${COMBINING_TEX[kind]}{{{base}}}$")
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def math_wrap(body: str, in_math: bool) -> str:
    return body if in_math else f"${body}$"


def _translate_chars(s: str, in_math: bool) -> str:
    """Unicode -> LaTeX, one character at a time, honouring sub/superscript runs."""
    out: list[str] = []
    i = 0
    while i < len(s):
        ch = s[i]
        if ch in SUBSCRIPT or ch in SUPERSCRIPT:
            table = SUBSCRIPT if ch in SUBSCRIPT else SUPERSCRIPT
            mark = "_" if ch in SUBSCRIPT else "^"
            run = ""
            while i < len(s) and s[i] in table:
                run += table[s[i]]
                i += 1
            out.append(math_wrap(f"{mark}{{{run}}}", in_math))
            continue
        if ch in MATH:
            #: A combining mark such as U+20D7 maps to nothing; emitting `$$` for it
            #: would open display math and derail the rest of the paragraph.
            if MATH[ch]:
                out.append(math_wrap(MATH[ch], in_math))
            i += 1
            continue
        if ch in ACCENTED:
            out.append(ACCENTED[ch])
            i += 1
            continue
        if ch == "—":
            out.append("---")
            i += 1
            continue
        if ch in ("–", "−"):
            out.append("--" if ch == "–" else ("-" if in_math else "$-$"))
            i += 1
            continue
        if ch == "…":
            out.append(r"\dots{}" if not in_math else r"\dots")
            i += 1
            continue
        if ch == "′":
            out.append(math_wrap("'", in_math))
            i += 1
            continue
        if ch == "§":
            out.append(r"\S{}")
            i += 1
            continue
        if ch in ("“", "”"):
            out.append('"')
            i += 1
            continue
        if ch in ("‘", "’"):
            out.append("'")
            i += 1
            continue
        if ord(ch) > 127:
            # Unknown non-ASCII: drop rather than emit an un-typesettable byte.
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def texttt(code: str) -> str:
    r"""Lean code span -> `\texttt{...}`, unicode lifted into inline math.

    A code span may itself carry LaTeX math (`` `a ∈ $\bar{T}$` `` is how the
    docstrings write a set complement), so `$...$` runs pass through as math
    instead of being escaped into `\textbackslash{}bar\{T\}`.
    """
    out = []
    #: `_apply_combining` itself emits `$\bar{S}$`, so it must run before the split.
    for k, part in enumerate(re.split(r"(\$[^$]*\$)", _apply_combining(code))):
        if k % 2:
            out.append("$" + math(part[1:-1]) + "$")
            continue
        for ch in part:
            if ch in _ESCAPE:
                out.append(_ESCAPE[ch])
            elif ord(ch) > 127:
                out.append(_translate_chars(ch, in_math=False))
            else:
                out.append(ch)
    return r"\texttt{" + "".join(out) + "}"


def math(body: str) -> str:
    r"""Existing LaTeX math -> LaTeX math: translate unicode, escape nothing.

    The body of a `$...$` or `$$...$$` span in a docstring is already LaTeX, so
    the escaping `prose` applies to backslashes and braces would destroy it.
    """
    #: `\tag` is only legal inside an amsmath equation environment; blueprint
    #: displays are plain `\[...\]`, so render the book's equation number inline.
    body = re.sub(r"\\tag\{([^}]*)\}", r"\\qquad (\1)", body)
    return _translate_chars(_apply_combining(body), in_math=True)


def prose(text: str) -> str:
    r"""Plain docstring prose -> LaTeX, leaving `$...$` spans untouched."""
    text = _apply_combining(text)
    parts = re.split(r"(\$[^$]*\$)", text)
    out = []
    for k, part in enumerate(parts):
        if k % 2:                                  # an existing $...$ span
            out.append("$" + math(part[1:-1]) + "$")
            continue
        buf = []
        for ch in part:
            if ch in ("&", "%", "#", "_", "{", "}", "^", "~", "\\"):
                buf.append(_ESCAPE[ch])
            else:
                buf.append(ch)
        out.append(_translate_chars("".join(buf), in_math=False))
    return "".join(out)
