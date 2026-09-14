r"""Quality checks for an informal statement.

`dataset_hygiene.py` asks whether a statement leaks the *proof*.  This module
asks the harder question: does it state the *theorem*, well enough to stand in a
handout on its own?

The bar, in the order the checks fire:

unbound-variable  a single-letter symbol is used without ever being introduced
                  ("$C.\mathrm{depth} = ...$" with no "Let $C$ be ...")
anaphora          it points outside itself -- "the embedding", "as above",
                  "the same hypotheses as", "restated", "this lemma"
lean-notation     a Lean identifier is used as if it were mathematical notation
                  (`\texttt{toFeedForward}`, snake_case, dot-notation)
title-in-body     the prose opens by repeating its own title verbatim
no-claim          too short, or no verb that states something
formalisation     Mathlib/instance/repo talk (shared with dataset_hygiene)

Every check is deliberately conservative: it fires on shapes that are nearly
always wrong, so that a clean report means something.  Used both to measure the
existing dataset and to gate regenerated statements before they are cached.
"""

from __future__ import annotations

import functools
import re
from pathlib import Path

# --------------------------------------------------------------------------- #
# Anaphora: the statement leans on a neighbour the reader does not have.
# --------------------------------------------------------------------------- #
#: A noun phrase pointing at a neighbour is only anaphoric when it is *not*
#: immediately pinned down: "the reduction graph associated to $f$" defines
#: itself, "The embedding uses one extra layer" does not.
_PINS_ITSELF = r"(?!\s+(?:associated|attached|of|for|on|with|given|defined|"     \
              r"induced|obtained|from|into|above\s+is|that|which|\$))"

ANAPHORA = re.compile(
    r"(?ix)\b("
    r"(?:the|this|that|these|those)\s+(?:same\s+)?"
    #: `result` and `claim` are left out: they are ordinary nouns far more often
    #: than pointers ("the resulting state", "the claim information of $p$").
    r"(?:embedding|lemma|theorem|statement|construction|definition|"
    r"proposition|corollary|above|below|"
    r"preceding|previous|foregoing|latter|former)\b" + _PINS_ITSELF +
    r"|under\s+the\s+same\s+hypotheses"
    r"|same\s+(?:hypotheses|assumptions|setting|notation|conditions)\s+as"
    r"|\bas\s+(?:above|below|before|in\s+the\s+(?:previous|preceding|last))"
    r"|\b(?:restated|restatement|re-stated)\b"
    #: "the real-valued version of the Radon-Nikodym derivative" is a definition,
    #: not a pointer, so `version of` is not on this list.
    r"|\b(?:the\s+)?(?:mirror|analogue|counterpart)\s+of\s+(?:the\s+)?"
    r"(?:previous|preceding|above|foregoing|last)\b"
    r"|\bauxiliary\s+(?:form|restatement|version)\b"
    r"|\bsee\s+(?:above|below)\b"
    r")"
)

# --------------------------------------------------------------------------- #
# Lean identifiers masquerading as notation.
# --------------------------------------------------------------------------- #
#: `\texttt{...}` holding something that is plainly a Lean name: an escaped
#: underscore, a dotted path, or interior camelCase.
TEXTTT_LEAN = re.compile(r"\\texttt\{[^}]*(?:\\_|\.[A-Za-z]|[a-z][A-Z])[^}]*\}")
#: Bare dot-notation outside `\texttt{}`: `C.toFeedForward`, `f.eval`.
DOT_NOTATION = re.compile(r"(?<![\\A-Za-z0-9])[A-Za-z][A-Za-z0-9']*\.[a-z][A-Za-z0-9]*")
#: `\mathrm{Nat.card}`, `\mathtt{getLitAt}` -- a Lean path inside a math font.
#: camelCase alone is not enough here: `\mathrm{TimeM}` is the object's real
#: name.  A dot or an underscore in a math font is what marks a Lean path.
MATHFONT_LEAN = re.compile(
    r"\\(?:mathrm|mathtt|mathsf|operatorname)\{[^}]*(?:\.[A-Za-z]|\\?_[A-Za-z]{2,})[^}]*\}"
)
#: `\mathrm{composedDelta}` -- a lowercase-initial name with an interior capital
#: is a Lean function, not notation.  `\mathrm{TimeM}` (capital-initial) is a type
#: name and stays; `\mathrm{val}`, `\mathrm{depth}` are ordinary operator names.
MATHFONT_CAMEL = re.compile(
    r"\\(?:mathrm|mathtt|mathsf|operatorname)\{\s*[a-z][A-Za-z0-9]*[a-z][A-Z][A-Za-z0-9]*\s*\}"
)

# --------------------------------------------------------------------------- #
# Bound variables.
# --------------------------------------------------------------------------- #
#: A phrase that introduces objects.  Any of these anywhere in the statement is
#: taken as evidence that its variables are quantified.
BINDER = re.compile(
    r"(?ix)\b("
    r"let|for\s+(?:every|all|any|each|a|an)|for\s+\d|if|given|suppose|assume|fix|"
    r"consider|there\s+(?:is|are|exists?)|every|each|any\s+\w|whenever|"
    r"denote|write|\bset\b"
    r")"
)
#: Statements that need no binder because they quantify over nothing.
NULLARY = re.compile(r"(?ix)\b(is|are|equals?|denotes?|holds?|means?)\b")

_CLAIM_VERB = re.compile(
    r"(?i)\b(is|are|has|have|holds?|equals?|satisfies|contains?|admits?|exists?|"
    r"then|denotes?|means?|assigns?|sends?|yields?|gives?|returns?|maps?|"
    r"coincides?|agrees?|bounds?|lies?|belongs?|follows?)\b"
)
#: A relation inside math mode: the statement's claim may be the formula itself.
_RELATION = re.compile(
    r"(?:\\\[|\$)[^$]*?"
    r"(?:=|\\le\b|\\ge\b|\\leq\b|\\geq\b|\\ne\b|\\neq\b|<|>|"
    r"\\subseteq\b|\\subset\b|\\in\b|\\notin\b|\\equiv\b|\\cong\b|"
    r"\\iff\b|\\Rightarrow\b|\\Leftrightarrow\b|\\to\b|\\mid\b)",
    re.S,
)

MIN_CHARS = 45
#: Single-letter math variables, the ones a statement must introduce.
VARIABLE = re.compile(r"(?<![A-Za-z\\])([A-Za-z])(?![A-Za-z])")


_MATH_SPAN_RE = re.compile(r"\$([^$]+)\$|\\\[(.+?)\\\]", re.S)


def _math_spans(text: str) -> list[str]:
    return [inline or display for inline, display in _MATH_SPAN_RE.findall(text)]


def uses_variables(text: str) -> bool:
    """True when the prose actually manipulates named objects."""
    for span in _math_spans(text):
        letters = {m.group(1) for m in VARIABLE.finditer(span)}
        letters -= set("edioal")            # e, d(i), o, a, l read as words/constants
        if letters:
            return True
    return False


#: "If P, then P" -- a faithful rendering of a Lean statement that assumes its
#: own conclusion.  The prose is not at fault, but the pair is worthless, so it
#: is surfaced rather than shipped silently.
_IF_THEN = re.compile(r"(?is)\bif\b(.{12,400}?)[,.]?\s*\bthen\b(.{12,400}?)(?:\.\s|\.$|$)")
#: LaTeX spacing and delimiter noise, so `\;\le\;` and `\le` compare equal.
_NOISE = re.compile(r"\\[,;:!]|\\quad|\\qquad|\\left|\\right|\\[\[\]]|[\s${}]+")


def _bare(text: str) -> str:
    return _NOISE.sub("", text).strip(".,;:")


def is_tautology(text: str) -> bool:
    """True for "if P, then P" -- a Lean statement that assumes its conclusion."""
    for match in _IF_THEN.finditer(text):
        head, tail = _bare(match.group(1)), _bare(match.group(2))
        if len(head) >= 10 and head == tail:
            return True
    return False

#: LaTeX that will not typeset: an unclosed `$`, `{`, or `\[`.  The blueprint is
#: a compiled document, so a single unbalanced delimiter from a generated
#: statement derails every entry after it.
_ESCAPED = re.compile(r"\\[\$&%#_{}]")


def latex_unsafe(text: str) -> bool:
    body = _ESCAPED.sub("", text)
    body = re.sub(r"\\\\\[", "", body)          # `\\[4pt]` is a line break
    return (
        body.count("$") % 2 != 0
        or body.count("{") != body.count("}")
        or body.count(r"\[") != body.count(r"\]")
    )


# --------------------------------------------------------------------------- #
# Macros the blueprint can actually typeset.
# --------------------------------------------------------------------------- #
#: Control words from the LaTeX kernel, amsmath, amssymb and mathtools, which the
#: blueprint preamble loads.  Project macros are read from the preamble itself,
#: so this list only has to cover the standard ones.
_STANDARD = set("""
alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota kappa
lambda mu nu xi pi varpi rho varrho sigma varsigma tau upsilon phi varphi chi
psi omega Gamma Delta Theta Lambda Xi Pi Sigma Upsilon Phi Psi Omega
le ge ne neq leq geq ll gg equiv sim simeq approx cong propto asymp doteq
in notin ni subset supset subseteq supseteq subsetneq nsubseteq sqsubseteq
cap cup sqcap sqcup setminus emptyset varnothing complement
to gets mapsto longmapsto rightarrow leftarrow leftrightarrow hookrightarrow
Rightarrow Leftarrow Leftrightarrow longrightarrow longleftarrow
Longrightarrow Longleftarrow Longleftrightarrow implies iff xrightarrow
forall exists nexists neg lnot land lor wedge vee bigwedge bigvee
sum prod int oint bigcap bigcup bigoplus bigotimes coprod
pm mp times div cdot ast star circ bullet oplus ominus otimes odot
top bot mid nmid parallel perp angle triangle square diamond frown smile
infty partial nabla surd sqrt prime dagger
lfloor rfloor lceil rceil langle rangle lvert rvert lVert rVert vert Vert
left right big Big bigg Bigg bigl bigr Bigl Bigr biggl biggr Biggl Biggr
bigm Bigm biggm Biggm middle
frac tfrac dfrac binom tbinom dbinom over atop choose
hat widehat bar overline underline tilde widetilde vec dot ddot check breve acute grave
mathrm mathit mathbf mathsf mathtt mathcal mathbb mathfrak mathscr boldsymbol
operatorname text textrm textit textbf texttt textsf emph
log ln exp sin cos tan sec csc cot arcsin arccos arctan sinh cosh tanh
min max sup inf lim limsup liminf det dim ker deg gcd Pr arg hom
quad qquad hspace vspace smallskip medskip bigskip
dots ldots cdots vdots ddots dotsb dotsc dotsm
substack stackrel overset underset displaystyle textstyle scriptstyle
begin end label ref eqref nonumber notag tag pmod bmod mod
colon semicolon nobreakspace space thinspace negthinspace enspace
lesssim gtrsim preceq succeq prec succ vartriangleleft leadsto rightsquigarrow
ell hbar imath jmath aleph wp Re Im
restriction upharpoonright downharpoonright
mathbin mathrel mathop mathpunct mathopen mathclose limits nolimits
cdotp ldotp bmod pmod underbrace overbrace
sqsubset sqsupset trianglelefteq trianglerighteq unlhd unrhd
nmid ncong nsim nleq ngeq nless ngtr nleqslant ngeqslant
leqslant geqslant eqslantless eqslantgtr
bigsqcup biguplus uplus amalg wr dagger ddagger
varDelta varGamma varLambda varOmega varPhi varPi varSigma varTheta
""".split())

_DEF_RE = re.compile(
    r"\\(?:new|renew|provide)command\*?\s*\{?\\([a-zA-Z]+)"
    r"|\\DeclareMathOperator\*?\s*\{\\([a-zA-Z]+)"
    r"|\\let\s*\\([a-zA-Z]+)"
)
_PREAMBLE = (Path(__file__).resolve().parent.parent / "blueprint" / "src",)


@functools.lru_cache(maxsize=1)
def known_macros() -> frozenset[str]:
    """Every control word the blueprint can typeset: standard plus project."""
    names = set(_STANDARD)
    for root in _PREAMBLE:
        for path in list(root.glob("*.sty")) + list(root.glob("preamble/*.tex")):
            try:
                text = path.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            for match in _DEF_RE.finditer(text):
                names.add(next(g for g in match.groups() if g))
    return frozenset(names)


_USED_RE = re.compile(r"\\([a-zA-Z]+)")


def unknown_macros(text: str) -> list[str]:
    """Control words the blueprint preamble does not provide.

    `\\bbp` looks plausible next to the project's `\\bbr` and `\\bbz`, but only
    `\\bbP` exists -- and an undefined control sequence stops the LaTeX run, so a
    single invented macro would take the whole document down.
    """
    allowed = known_macros()
    return sorted({m.group(1) for m in _USED_RE.finditer(text)} - allowed)


@functools.lru_cache(maxsize=1)
def _multitoken_macros() -> frozenset[str]:
    """Project macros that expand to more than one token.

    `\\bbr` is `\\mathbb{R}`, so `$x_\\bbr$` hands the subscript a group rather
    than a single symbol and the run stops.  `$x_\\alpha$` is fine -- `\\alpha`
    is one symbol -- so only the project's own macros are at issue.
    """
    names = set()
    for root in _PREAMBLE:
        for path in list(root.glob("*.sty")) + list(root.glob("preamble/*.tex")):
            try:
                text = path.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            for match in re.finditer(
                r"\\(?:new|renew|provide)command\*?\s*\{?\\([a-zA-Z]+)\}?"
                r"(?:\[\d\])*\s*\{(.*)",
                text,
            ):
                body = match.group(2)
                if "{" in body or "\\" in body:
                    names.add(match.group(1))
    return frozenset(names)


def unbraced_script(text: str) -> list[str]:
    """`_\\bbr` / `^\\bbr` -- a script applied to a multi-token macro."""
    risky = _multitoken_macros()
    return sorted({
        m.group(1) for m in re.finditer(r"[_^]\\([a-zA-Z]+)", text)
        if m.group(1) in risky
    })


def typesets(text: str) -> bool:
    """True when the blueprint can compile this statement.

    The single predicate both `check` and `blueprint_restate.py` use, so a
    statement can never be rejected by one and accepted by the other.
    """
    return (not latex_unsafe(text) and not unknown_macros(text)
            and not unbraced_script(text))


#: Exercise phrasing: an instruction to the reader, not a statement of fact.
IMPERATIVE = re.compile(
    r"(?ix)(^|[.;]\s+)(show|prove|deduce|verify|find|construct|determine|"
    r"conclude|establish)\s+(that|whether|a|an|the|all|every)\b"
)
#: `\texttt{}` is for code.  A regenerated statement that reaches for it is
#: spelling a mathematical object the way Lean does.
TYPEWRITER = re.compile(r"\\texttt\{")


def check(statement: str, title: str = "", strict: bool = False) -> list[str]:
    """Rubric violations in one informal statement, worst first.

    `strict` adds the checks that only make sense for freshly generated prose:
    no `\\texttt{}` at all, and no exercise phrasing.  Measuring the legacy
    dataset leaves them off, since much of it quotes textbook exercises verbatim.
    """
    found: list[str] = []
    flat = re.sub(r"\s+", " ", statement).strip()

    if len(flat) < MIN_CHARS:
        found.append("no-claim")
    elif not (_CLAIM_VERB.search(flat) or _RELATION.search(statement)):
        # A statement may carry its claim entirely in a display --
        # "For every subset $S$, \[ \sum_{x \in S} a(x) \le \sum_x \max(a(x),0) \]"
        # has no claim verb at all, so a relation in math mode counts too.
        found.append("no-claim")

    if ANAPHORA.search(flat):
        found.append("anaphora")

    if (TEXTTT_LEAN.search(flat) or MATHFONT_LEAN.search(flat)
            or MATHFONT_CAMEL.search(flat)):
        found.append("lean-notation")
    else:
        #: Strip math-mode subscripted names (`$T_{m,\nu}$`) before looking for
        #: dot-notation, so "i.e." and "Fig. 2" style prose does not trip it.
        probe = re.sub(r"(?i)\b(?:i\.e|e\.g|a\.e|a\.s|w\.r\.t|cf|etc|vs|resp|fig|no|eq)\.", " ", flat)
        if DOT_NOTATION.search(probe):
            found.append("lean-notation")

    if uses_variables(flat) and not BINDER.search(flat) and not NULLARY.search(flat):
        found.append("unbound-variable")

    if title:
        head = re.sub(r"\s+", " ", title).strip().rstrip(".:")
        if head and flat.lower().startswith(head.lower()):
            found.append("title-in-body")

    if not typesets(statement):
        found.append("latex-unsafe")

    if is_tautology(flat):
        found.append("tautology")

    if strict:
        if TYPEWRITER.search(flat):
            found.append("typewriter")
        if IMPERATIVE.search(flat):
            found.append("imperative")

    return found


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def _main() -> int:
    """Grade a built dataset or the regenerated-statement cache.

        python3 scripts/statement_quality.py                     # the cache
        python3 scripts/statement_quality.py --dataset           # the .jsonl
        python3 scripts/statement_quality.py --show 20           # print offenders
    """
    import argparse
    import collections
    import json

    base = Path(__file__).resolve().parent.parent
    ap = argparse.ArgumentParser(description=_main.__doc__)
    ap.add_argument("--dataset", nargs="?", const=str(base / "dataset" / "tcslib_theorems.jsonl"),
                    help="grade statement_informal in a built dataset instead")
    ap.add_argument("--show", type=int, default=0)
    ap.add_argument("--strict", action="store_true",
                    help="apply the checks meant for freshly generated prose")
    args = ap.parse_args()

    rows: list[tuple[str, str, str]] = []
    if args.dataset:
        for line in Path(args.dataset).open():
            if line.strip():
                d = json.loads(line)
                rows.append((d["id"], d.get("statement_informal", ""), ""))
    else:
        for path in sorted((base / "blueprint" / "src" / "references" / "statements").glob("*.json")):
            d = json.loads(path.read_text(encoding="utf-8"))
            rows.append((d.get("lean_name", path.stem), d.get("statement", ""), d.get("title", "")))

    tally: collections.Counter[str] = collections.Counter()
    hits = []
    for name, statement, title in rows:
        problems = check(statement, title, strict=args.strict or not args.dataset)
        tally.update(problems)
        if problems:
            hits.append((name, problems, statement))

    print(f"{len(rows)} statements, {len(hits)} flagged")
    for kind, count in tally.most_common():
        print(f"  {count:5d}  {kind}")
    for name, problems, statement in hits[: args.show]:
        print(f"\n=== {name}  [{','.join(problems)}]")
        print(re.sub(r"\s+", " ", statement)[:400])
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
