"""Turn paper/paper.md into paper/paper.tex.

paper.md is the only source: edit it, then run

    python paper/tools/md2tex.py          # writes paper/paper.tex
    python paper/tools/md2tex.py --check  # fails if paper.tex is out of date

and build the PDF with LuaLaTeX (twice, for the bookmarks):

    cd paper && lualatex paper.tex && lualatex paper.tex

The workflow "Build the paper" does both on GitHub's machines and keeps the PDF.

Only the Markdown that paper.md uses is understood: one title, an author line, short italic
notes before the abstract, "##" and "###" headings, paragraphs, bullet and numbered lists
(nested by indentation), fenced code blocks, pipe tables, **bold**, *italic*, `code`,
x^{...} and x^y as superscripts, and x_y as subscripts. Standard library only.
"""

import re
import sys
from pathlib import Path

PAPER = Path(__file__).resolve().parent.parent
SOURCE = PAPER / "paper.md"
TARGET = PAPER / "paper.tex"

PREAMBLE = r"""% Generated from paper.md by tools/md2tex.py. Do not edit by hand: edit paper.md and rerun.
% Build with LuaLaTeX: lualatex paper.tex (twice).
\documentclass[11pt,a4paper]{article}
\usepackage[margin=2.5cm]{geometry}
\usepackage{fontspec}
% Latin Modern has no Greek letters or logic symbols; LuaLaTeX takes those from the fonts below.
\directlua{
  luaotfload.add_fallback("textfallback", {
    "Latin Modern Math:mode=node;",
    "DejaVu Serif:mode=node;",
    "DejaVu Sans:mode=node;",
  })
  luaotfload.add_fallback("codefallback", {
    "DejaVu Sans Mono:mode=node;",
    "Latin Modern Math:mode=node;",
    "DejaVu Sans:mode=node;",
  })
}
\setmainfont{Latin Modern Roman}[RawFeature={fallback=textfallback}]
\setmonofont{DejaVu Sans Mono}[Scale=MatchLowercase, RawFeature={fallback=codefallback}]
\usepackage{microtype}
\usepackage{enumitem}
\setlist{itemsep=2pt, topsep=4pt, parsep=0pt}
\usepackage{booktabs}
\usepackage{array}
\usepackage{xltabular}
\usepackage{xcolor}
\usepackage{fvextra}
\fvset{fontsize=\footnotesize, breaklines=true, breakautoindent=true, frame=lines,
  framesep=2mm, rulecolor=\color{black!40}}
\usepackage[hidelinks, bookmarksnumbered]{hyperref}
\tracinglostchars=2
\emergencystretch=3em
\setlength{\abovetopsep}{4pt}
"""


def escape(s):
    """Escape LaTeX's special characters in plain text."""
    out = []
    for ch in s:
        if ch in "&%$#_{}":
            out.append("\\" + ch)
        elif ch == "~":
            out.append(r"\textasciitilde{}")
        elif ch == "^":
            out.append(r"\textasciicircum{}")
        elif ch == "\\":
            out.append(r"\textbackslash{}")
        else:
            out.append(ch)
    return "".join(out)


def quotes(s):
    """Straight double quotes to curly ones, by what stands before and after them."""
    out = []
    for i, ch in enumerate(s):
        if ch != '"':
            out.append(ch)
            continue
        before = s[i - 1] if i > 0 else None
        after = s[i + 1] if i + 1 < len(s) else None
        opening = (before is None or before in " ([{\u2013\u2014/") and after not in (None, " ", ",", ".", ";", ":", ")")
        out.append("\u201c" if opening else "\u201d")
    return "".join(out)


def text(s):
    """Plain text: curly quotes, sub- and superscripts, escaping."""
    s = quotes(s)
    out, pos = [], 0
    for m in re.finditer(r"\^\{([^}]*)\}|\^(\S)|(?<=\w)_([A-Za-z0-9]+)", s):
        out.append(escape(s[pos:m.start()]))
        if m.group(1) is not None:
            out.append(r"\textsuperscript{" + escape(m.group(1)) + "}")
        elif m.group(2) is not None:
            out.append(r"\textsuperscript{" + escape(m.group(2)) + "}")
        else:
            out.append(r"\textsubscript{" + escape(m.group(3)) + "}")
        pos = m.end()
    out.append(escape(s[pos:]))
    return "".join(out)


def code(s):
    """Inline code: typewriter font, with places where a long name may break."""
    out = []
    for i, ch in enumerate(s):
        out.append(escape(ch))
        if ch in "./_" and i + 1 < len(s):
            out.append(r"\allowbreak{}")
        elif ch.islower() and i + 1 < len(s) and s[i + 1].isupper():
            out.append(r"\penalty300{}")
    return r"\texttt{" + "".join(out) + "}"


INLINE = re.compile(r"`([^`]+)`|\*\*(.+?)\*\*|\*(.+?)\*")


def inline(s):
    """Inline Markdown: `code`, **bold**, *italic*, then plain text."""
    out, pos = [], 0
    for m in INLINE.finditer(s):
        out.append(text(s[pos:m.start()]))
        if m.group(1) is not None:
            out.append(code(m.group(1)))
        elif m.group(2) is not None:
            out.append(r"\textbf{" + inline(m.group(2)) + "}")
        else:
            out.append(r"\emph{" + inline(m.group(3)) + "}")
        pos = m.end()
    out.append(text(s[pos:]))
    return "".join(out)


def table(rows):
    """A pipe table as a booktabs table that may break across pages."""
    cells = [[c.strip() for c in re.split(r"(?<!\\)\|", r.strip().strip("|"))] for r in rows]
    head, body = cells[0], cells[2:]
    n = len(head)
    lengths = [max(len(r[j]) if j < len(r) else 0 for r in [head] + body) for j in range(n)]
    widths = [sum(len(r[j]) for r in body if j < len(r)) / max(len(body), 1) for j in range(n)]
    wide = [j for j in range(n) if lengths[j] > 18]
    total = sum(widths[j] for j in wide) or 1
    factors = {j: min(max(widths[j] * len(wide) / total, 0.5), 2.0) for j in wide}
    scale = len(wide) / (sum(factors.values()) or 1)
    spec = []
    for j in range(n):
        if j in factors:
            spec.append(r">{\raggedright\arraybackslash\hsize=%.2f\hsize}X" % (factors[j] * scale))
        elif all(re.fullmatch(r"[\d,.]+", r[j]) for r in body if j < len(r) and r[j]):
            spec.append("r")
        else:
            spec.append("l")
    size = r"\small" if n <= 3 else r"\footnotesize"
    lines = [
        r"\begingroup" + size + r"\setlength{\tabcolsep}{4pt}",
        r"\begin{xltabular}{\linewidth}{@{}" + "".join(spec) + "@{}}",
        r"\toprule",
        " & ".join(r"\textbf{" + inline(c) + "}" if c else "" for c in head) + r" \\",
        r"\midrule",
        r"\endhead",
    ]
    for r in body:
        r = r + [""] * (n - len(r))
        lines.append(" & ".join(inline(c) for c in r) + r" \\")
    lines += [r"\bottomrule", r"\end{xltabular}", r"\endgroup"]
    return "\n".join(lines)


def heading(level, title):
    if level == 2:
        cmd, depth = "section", 1
    else:
        cmd, depth = "subsection", 2
    return (
        "\\" + cmd + "*{" + inline(title) + "}\n"
        r"\phantomsection\addcontentsline{toc}{" + cmd + "}{" + inline(title) + "}"
    )


LIST = re.compile(r"^( *)([-*]|\d+\.) (.*)$")


def convert(md):
    lines = md.split("\n")
    out = []
    buf = []  # words of the paragraph or list item being read
    stack = []  # open lists: (marker indent, "itemize" or "enumerate")
    in_abstract = False

    def flush():
        if buf:
            out.append(inline(" ".join(buf)))
            buf.clear()

    def close_lists(to_indent=-1):
        flush()
        while stack and stack[-1][0] > to_indent:
            out.append(r"\end{" + stack.pop()[1] + "}")

    # Title, author line and the notes before the first section.
    i = 0
    while not lines[i].startswith("# "):
        i += 1
    title = lines[i][2:].strip()
    i += 1
    front = []
    while not lines[i].startswith("## "):
        if lines[i].strip():
            para = [lines[i].strip()]
            i += 1
            while lines[i].strip() and not lines[i].startswith("## "):
                para.append(lines[i].strip())
                i += 1
            front.append(" ".join(para))
        else:
            i += 1
    authors = front[0].strip("*")
    names = re.split(r",\s*|\s+and\s+", authors)
    notes = [p.strip("*") for p in front[1:]]
    out.append(PREAMBLE)
    out.append(r"\hypersetup{pdftitle={" + text(title) + "}, pdfauthor={" + text(", ".join(names)) + "}}")
    out.append(r"\title{" + inline(title) + "}")
    out.append(r"\author{" + r" \and ".join(text(n) for n in names) + "}")
    out.append(r"\date{\small\itshape" + r"\\[0.5ex]".join(inline(n) for n in notes) + "}")
    out.append(r"\begin{document}")
    out.append(r"\maketitle")

    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        if stripped.startswith("```"):
            close_lists()
            body = []
            i += 1
            while not lines[i].strip().startswith("```"):
                body.append(lines[i])
                i += 1
            out.append("\\begin{Verbatim}\n" + "\n".join(body) + "\n\\end{Verbatim}")
            i += 1
            continue

        if stripped.startswith("|"):
            close_lists()
            rows = []
            while i < len(lines) and lines[i].strip().startswith("|"):
                rows.append(lines[i])
                i += 1
            out.append(table(rows))
            continue

        m = re.match(r"^(#{2,3}) (.*)$", line)
        if m:
            close_lists()
            if in_abstract:
                out.append(r"\end{abstract}")
                in_abstract = False
            if m.group(2).strip() == "Abstract":
                out.append(r"\begin{abstract}")
                in_abstract = True
            else:
                out.append(heading(len(m.group(1)), m.group(2).strip()))
            i += 1
            continue

        if not stripped:
            # A blank line ends a paragraph; it ends the lists unless an item or an indented
            # line follows.
            j = i + 1
            while j < len(lines) and not lines[j].strip():
                j += 1
            nxt = lines[j] if j < len(lines) else ""
            if stack and (LIST.match(nxt) or nxt.startswith(" ")):
                flush()
            else:
                close_lists()
                out.append("")
            i += 1
            continue

        m = LIST.match(line)
        if m:
            indent, marker, rest = len(m.group(1)), m.group(2), m.group(3)
            kind = "itemize" if marker in "-*" else "enumerate"
            close_lists(indent) if stack and stack[-1][0] > indent else flush()
            if not stack or stack[-1][0] < indent:
                start = "" if kind == "itemize" or marker == "1." else "[start=%s]" % marker[:-1]
                out.append(r"\begin{" + kind + "}" + start)
                stack.append((indent, kind))
            out.append(r"\item")
            buf.append(rest)
            i += 1
            continue

        if stack and not line.startswith(" "):
            close_lists()
        buf.append(stripped)
        i += 1

    close_lists()
    if in_abstract:
        out.append(r"\end{abstract}")
    out.append(r"\end{document}")
    tex = "\n".join(out) + "\n"
    return re.sub(r"\n{3,}", "\n\n", tex)


def main():
    tex = convert(SOURCE.read_text(encoding="utf-8"))
    if "--check" in sys.argv[1:]:
        current = TARGET.read_text(encoding="utf-8") if TARGET.exists() else ""
        if current != tex:
            sys.exit("paper.tex is out of date: run python paper/tools/md2tex.py")
        print("paper.tex matches paper.md")
        return
    TARGET.write_text(tex, encoding="utf-8", newline="\n")
    print("wrote", TARGET.relative_to(PAPER.parent))


if __name__ == "__main__":
    main()
