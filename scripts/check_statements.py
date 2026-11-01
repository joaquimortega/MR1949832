#!/usr/bin/env python3
"""Check that no declaration statement changed between a reference commit and a target tree.

Usage: python3 scripts/check_statements.py [REF] [TARGET_DIR]
  REF         git ref of the reviewed scaffold (default: scaffold-reviewed)
  TARGET_DIR  working tree to compare (default: repository root)

For every `theorem`/`lemma`/`def`/`abbrev`/`structure`/`instance` in `OrtegaCerdaMultipliers/**`
present at REF, the statement (text from the keyword to the first top-level `:=`, `where` or
`|`, whitespace-normalised, comments removed) must be identical in TARGET_DIR.  New declarations
are allowed; removed or changed ones are reported.  Exit code 1 if anything changed.
"""
import pathlib, re, subprocess, sys

root = pathlib.Path(__file__).resolve().parent.parent
ref = sys.argv[1] if len(sys.argv) > 1 else "scaffold-reviewed"
target = pathlib.Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else root

KW = r"(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*(theorem|lemma|def|abbrev|structure|instance|class)\s+"
decl_re = re.compile(r"^" + KW + r"([^\s:(\[{]+)", re.M)


def strip_comments(s: str) -> str:
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)  # block and doc comments (non-nested is enough here)
    return re.sub(r"--[^\n]*", " ", s)


def statements(text: str) -> dict:
    text = strip_comments(text)
    out = {}
    ms = list(decl_re.finditer(text))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        chunk = text[m.start():end]
        # cut at the first top-level ':=' / ' where' / leading '|' (pattern-matching defs)
        cut = len(chunk)
        for pat in (":=", "\nwhere", " where\n", "\n  |"):
            j = chunk.find(pat)
            if j != -1:
                cut = min(cut, j)
        key = m.group(2)
        out[key] = " ".join(chunk[:cut].split())
    return out


def files_at_ref():
    ls = subprocess.run(["git", "-C", str(root), "ls-tree", "-r", "--name-only", ref,
                         "OrtegaCerdaMultipliers"], capture_output=True, text=True, check=True)
    for path in ls.stdout.split():
        if path.endswith(".lean"):
            txt = subprocess.run(["git", "-C", str(root), "show", f"{ref}:{path}"],
                                 capture_output=True, text=True, check=True).stdout
            yield path, txt


# Coordinator-approved removals/changes of non-main helper statements found false during
# implementation (each recorded in NOTEBOOK.md, implementation log).
APPROVED = {
    "integral_bumpPot_mul_laplacian": "false as parsed (∫ z, a - b), unused; intended statement is the primed lemma (NOTEBOOK I-03)",
    "lintegral_FR_near": "false for s > 1, unused; replaced by lintegral_FR_near_of_le_one (NOTEBOOK I-01)",
}

bad = 0
for path, old in files_at_ref():
    new_path = target / path
    if not new_path.exists():
        print(f"REMOVED FILE {path}")
        bad += 1
        continue
    olds, news = statements(old), statements(new_path.read_text())
    for name, st in olds.items():
        if name in APPROVED:
            if name not in news or news[name] != st:
                print(f"approved change {path}: {name} ({APPROVED[name]})")
            continue
        if name not in news:
            print(f"REMOVED {path}: {name}")
            bad += 1
        elif news[name] != st:
            print(f"CHANGED {path}: {name}\n  old: {st}\n  new: {news[name]}")
            bad += 1
print("OK: no statement changed" if bad == 0 else f"{bad} problem(s)")
sys.exit(1 if bad else 0)
