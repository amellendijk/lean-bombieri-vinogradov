#!/usr/bin/env python3
r"""Consistency check between the Lean blueprint annotations and the LaTeX chapters.

Run after `lake build :blueprint`. Reports
  * `\inputleannode{label}` in blueprint/src/chapters/*.tex without a generated node,
  * generated nodes that no chapter includes,
  * `\uses{}` targets (generated or hand-written) that are not labels of the document
    (typically a PrimeNumberTheoremAnd constant that needs a `-Const` exclude in `uses`/`proofUses`),
  * nodes that are not `\leanok` (i.e. some declaration still has a `sorry`).
Exit status 1 if anything is reported.
"""
import glob, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
lib = os.path.join(ROOT, '.lake/build/blueprint/library/BV.tex')
if not os.path.exists(lib):
    sys.exit('missing ' + lib + ' (run `lake build :blueprint` first)')
mods = re.findall(r'\\input\{([^}]*)\}', open(lib).read())
artifacts = {}
for m in mods:
    m = m if os.path.exists(m) else m + '.tex'
    for lbl, path in re.findall(r'\\newleannode\{([^}]*)\}\{\\input\{([^}]*)\}\}', open(m).read()):
        artifacts[lbl] = path if os.path.exists(path) else path + '.tex'   # later modules win, as in LaTeX

chapters = '\n'.join(open(f).read() for f in sorted(glob.glob(os.path.join(ROOT, 'blueprint/src/chapters/*.tex'))))
included = set(re.findall(r'\\inputleannode\{([^}]*)\}', chapters))
hand_labels = set(re.findall(r'\\label\{([^}]*)\}', chapters))
labels = hand_labels | set(artifacts)

problems = []
for lbl in sorted(included - set(artifacts)):
    problems.append(f'\\inputleannode{{{lbl}}} has no generated node')
for lbl in sorted(set(artifacts) - included):
    problems.append(f'generated node {lbl} is not included by any chapter')
texts = {lbl: open(p).read() for lbl, p in artifacts.items()}
texts['<chapters>'] = chapters
for lbl, t in texts.items():
    for u in re.findall(r'\\uses\{([^}]*)\}', t):
        for x in {x.strip() for x in u.split(',') if x.strip()} - labels:
            problems.append(f'{lbl}: \\uses{{{x}}} is not a label of the document')
for lbl, t in texts.items():
    if lbl != '<chapters>' and '\\leanok' not in t.split('\\begin{proof}')[0]:
        problems.append(f'{lbl}: statement not \\leanok')
print('\n'.join(problems) if problems else f'ok: {len(artifacts)} generated nodes, {len(hand_labels - set(artifacts))} hand-written labels')
sys.exit(1 if problems else 0)
