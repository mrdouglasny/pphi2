#!/usr/bin/env python3
"""Generate blueprint/src/content.tex from the extracted dependency graph
(scripts/blueprint_graph.tsv) plus per-declaration informal statements found in
summary/**/*.md across pphi2 and its upstream deps. Edges come from the real
Lean dependency data; statements are reused where lean-summarize produced them.
"""
import re, glob, os, collections

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SUMMARY_DIRS = [
    os.path.join(ROOT, "summary"),
    os.path.join(ROOT, ".lake/packages/GaussianField/summary"),
    os.path.join(ROOT, ".lake/packages/bochner/summary"),
]

# ---- parse the dependency graph -------------------------------------------
nodes = []
for line in open(os.path.join(ROOT, "scripts/blueprint_graph.tsv")):
    parts = line.rstrip("\n").split("\t")
    while len(parts) < 4:
        parts.append("")
    kind, fq, module, deps = parts[0], parts[1], parts[2], parts[3]
    nodes.append((kind, fq, module, deps.split() if deps else []))
nodeset = {fq for _, fq, _, _ in nodes}

# ---- parse informal statements from summaries -----------------------------
stmt = {}      # shortname -> markdown statement
flagged = {}   # shortname -> "axiom"/"deprecated"
hdr = re.compile(r"^###\s+`([^`]+)`\s*(\(axiom\)|\(deprecated\))?")
for d in SUMMARY_DIRS:
    for md in glob.glob(os.path.join(d, "**/*.md"), recursive=True):
        cur, buf = None, []
        for line in open(md):
            m = hdr.match(line)
            if m or line.startswith("---") or line.startswith("## "):
                if cur and cur not in stmt:
                    stmt[cur] = " ".join(buf).strip()
                cur, buf = (m.group(1) if m else None), []
                if m and m.group(2):
                    flagged[m.group(1)] = m.group(2).strip("()")
            elif cur is not None:
                buf.append(line.strip())
        if cur and cur not in stmt:
            stmt[cur] = " ".join(buf).strip()

# ---- helpers --------------------------------------------------------------
def label(fq):
    return re.sub(r"[^A-Za-z0-9]", "-", fq)

def esc_text(s):  # escape LaTeX specials in non-math text
    for a, b in [("\\", r"\textbackslash "), ("&", r"\&"), ("%", r"\%"),
                 ("#", r"\#"), ("_", r"\_"), ("{", r"\{"), ("}", r"\}"),
                 ("^", r"\^{}"), ("~", r"\~{}")]:
        s = s.replace(a, b)
    return s

def md2tex(s):  # convert a summary md statement to LaTeX, preserving $math$
    out = []
    for j, span in enumerate(re.split(r"(\$[^$]*\$)", s)):
        if j % 2 == 1:
            out.append(span)                       # math: keep verbatim
        else:
            t = span.replace("**", "")             # drop bold markers
            for k, p in enumerate(re.split(r"(`[^`]+`)", t)):
                if k % 2 == 1:
                    out.append(r"\texttt{%s}" % esc_text(p[1:-1]))
                else:
                    out.append(esc_text(p))
    return "".join(out)

def shortname(fq):
    return fq.split(".")[-1]

def stmt_for(fq):
    sn = shortname(fq)
    if sn in stmt and stmt[sn]:
        return md2tex(stmt[sn])
    return r"\texttt{%s}" % esc_text(fq)  # fallback: the Lean name

ENVOF = {"thm": "theorem", "def": "definition", "axiom": "theorem", "struct": "definition"}

# ---- group by top namespace, then module ----------------------------------
def topns(fq): return fq.split(".")[0]
chapters = collections.OrderedDict()
for kind, fq, module, deps in nodes:
    chapters.setdefault(topns(fq), collections.OrderedDict()).setdefault(module, []).append((kind, fq, deps))

CHAP_TITLE = {
    "Pphi2": "pphi2: P(Φ)₂ construction",
    "Common": "pphi2: common QFT framework",
    "GaussianField": "gaussian-field (upstream)",
    "GaussianHilbert": "gaussian-hilbert (upstream)",
    "Nuclear": "gaussian-field: nuclear spaces (upstream)",
    "SchwartzNuclear": "gaussian-field: Schwartz/nuclear (upstream)",
    "SmoothCircle": "gaussian-field: smooth circle (upstream)",
    "Lattice": "gaussian-field: lattice (upstream)",
    "HeatKernel": "gaussian-field: heat kernel (upstream)",
    "Torus": "gaussian-field: torus (upstream)",
}

out = []
out.append(r"""\chapter{Overview}
This is the \emph{full} declaration-level dependency graph of \texttt{pphi2}
together with its upstream dependencies in our own libraries
(\texttt{gaussian-field}, \texttt{gaussian-hilbert}, \dots), covering %d
declarations and their real dependency edges. Edges are \emph{extracted} from
the compiled Lean environment (\texttt{scripts/BlueprintGraph.lean}), not
hand-drawn. Informal statements are reused from \texttt{summary/**/*.md} where
available (otherwise the node shows its Lean name). Declarations flagged
\textbf{(axiom)} are assumed, not proved.
""" % len(nodes))

for chap, mods in chapters.items():
    out.append("\\chapter{%s}" % esc_text(CHAP_TITLE.get(chap, chap)))
    for module, decls in mods.items():
        out.append("\\section{\\texttt{%s}}" % esc_text(module))
        for kind, fq, deps in decls:
            env = ENVOF.get(kind, "definition")
            lbl = label(fq)
            ax = " (axiom)" if kind == "axiom" or flagged.get(shortname(fq)) == "axiom" else ""
            uses = ", ".join(label(d) for d in deps if d in nodeset)
            out.append("\\begin{%s}[\\texttt{%s}%s]\\label{%s}" %
                        (env, esc_text(shortname(fq)), ax, lbl))
            out.append("  \\lean{%s}\\leanok" % fq)
            if uses:
                out.append("  \\uses{%s}" % uses)
            out.append("  " + stmt_for(fq))
            out.append("\\end{%s}" % env)

open(os.path.join(ROOT, "blueprint/src/content.tex"), "w").write("\n".join(out) + "\n")
print("nodes:", len(nodes), " with-summary:",
      sum(1 for _, fq, _, _ in nodes if shortname(fq) in stmt),
      " chapters:", len(chapters))
