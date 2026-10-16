#!/usr/bin/env python3
"""Extract the claims of the paper from its LaTeX source.

Writes three JSON files into the output directory:
  claims.json        one record per numbered environment, with its paper number, label and text
  prose_claims.json  one record per theorem-like phrase or asymptotic-rate statement that occurs
                     OUTSIDE any numbered environment
  claims_sources.json  the files read, the SHA-256 of their flattened text, and every LaTeX label

A missing `\\input`/`\\include` target fails the extraction rather than dropping its claims. Only
literal file arguments are followed; numbered environments sit in the files that are.

Numbering follows the paper's own `\\newtheorem{theorem}{Theorem}[section]` with every other
environment sharing that counter, so the numbers printed here are the numbers the paper prints.
Usage:  extract_paper_claims.py <dir-holding-the-WP-tree> <output-dir>
"""
import hashlib
import re, os, json, sys

NUMBERED = ["theorem", "proposition", "lemma", "corollary", "definition", "assumption",
            "example", "remark", "convention", "hypothesis"]
MASTERS = {"WP": ("WP/paper/wellposedness.tex", "WP/paper")}
CLAIM = re.compile(r"\b(we\s+(prove|show|establish|obtain|derive|verify|construct)|"
                   r"is\s+of\s+order|of\s+order|converges?\s+(to|at)|rate\s+of\s+convergence|"
                   r"first[- ]order|second[- ]order|\bunique(ly)?\b|there\s+exists?|"
                   r"is\s+bounded\s+by|bounded\s+above\s+by)\b", re.I)
RATE = re.compile(r"(O\s*\\?left?\(|\\mathcal\{O\}|\bO\(\\tau|\bO\(\\delta|\bO\(h)")


def strip_comments(s):
    out = []
    for line in s.split("\n"):
        r = ""
        for i, ch in enumerate(line):
            if ch == "%" and (i == 0 or line[i - 1] != "\\"):
                break
            r += ch
        out.append(r)
    return "\n".join(out)


MISSING = []


def expand(path, depth=0):
    """Flatten \\input/\\include into (source-file, chunk) pairs in document order. A missing
    file is recorded in `MISSING`, and `main` fails on it."""
    if depth > 12:
        MISSING.append(path + " (include depth exceeded)")
        return []
    if not os.path.exists(path):
        MISSING.append(path)
        return []
    base = os.path.dirname(path)
    txt = strip_comments(open(path, encoding="utf-8", errors="replace").read())
    parts, pos = [], 0
    for m in re.finditer(r"\\(?:input|include)\{([^}]+)\}", txt):
        if "#" in m.group(1):
            continue  # a macro parameter inside a \newcommand body, not a file
        parts.append((path, txt[pos:m.start()]))
        sub = m.group(1) if m.group(1).endswith(".tex") else m.group(1) + ".tex"
        parts.extend(expand(os.path.normpath(os.path.join(base, sub)), depth + 1))
        pos = m.end()
    parts.append((path, txt[pos:]))
    return parts


def matching_end(txt, start, env):
    depth, i = 1, start
    pat = re.compile(r"\\(begin|end)\{" + re.escape(env) + r"\}")
    while True:
        m = pat.search(txt, i)
        if not m:
            return len(txt)
        depth += 1 if m.group(1) == "begin" else -1
        if depth == 0:
            return m.start()
        i = m.end()


def numbered(name, master, root):
    section, appendix, counter, claims = 0, False, 0, []
    envpat = re.compile(r"\\begin\{(" + "|".join(NUMBERED) + r")\}(\[[^\]]*\])?")
    for src, txt in expand(master):
        rel, i = os.path.relpath(src, root), 0
        while i < len(txt):
            msec = re.compile(r"\\(section|appendix)\b").search(txt, i)
            menv = envpat.search(txt, i)
            if menv is None and msec is None:
                break
            if msec is not None and (menv is None or msec.start() < menv.start()):
                if msec.group(1) == "appendix":
                    appendix, section = True, 0
                else:
                    section, counter = section + 1, 0
                i = msec.end()
                continue
            env, opt = menv.group(1), (menv.group(2) or "").strip("[]")
            bs = menv.end()
            be = matching_end(txt, bs, env)
            body = txt[bs:be].strip()
            counter += 1
            sec = chr(64 + section) if appendix and section > 0 else str(section)
            lab = re.search(r"\\label\{([^}]+)\}", body)
            claims.append({"paper": name, "env": env, "number": f"{sec}.{counter}",
                           "title": opt, "label": lab.group(1) if lab else None, "file": rel,
                           "statement": re.sub(r"\s+", " ", body)})
            i = be
    return claims


def prose(name, root):
    rows = []
    for dp, _, fs in os.walk(root):
        for fn in sorted(fs):
            if not fn.endswith(".tex") or "/figs" in dp or fn.startswith("fig"):
                continue
            p = os.path.join(dp, fn)
            raw = strip_comments(open(p, encoding="utf-8", errors="replace").read())
            free = raw
            for env in NUMBERED:
                free = re.sub(r"\\begin\{" + env + r"\}.*?\\end\{" + env + r"\}", " ", free,
                              flags=re.S)
            for kind, pat in (("phrase", CLAIM), ("rate", RATE)):
                for m in pat.finditer(free):
                    a, b = max(0, m.start() - 120), min(len(free), m.end() + 160)
                    rows.append({"paper": name, "file": os.path.relpath(p, root), "kind": kind,
                                 "hit": m.group(0)[:30],
                                 "ctx": re.sub(r"\s+", " ", free[a:b]).strip()})
    return rows


def main(src, out):
    allc, allp = [], []
    for k, (m, r) in MASTERS.items():
        allc += numbered(k, os.path.join(src, m), os.path.join(src, r))
        allp += prose(k, os.path.join(src, r))
    if MISSING:
        print("FAIL: included sources not found:\n  " + "\n  ".join(sorted(set(MISSING))))
        sys.exit(1)
    sources = {}
    for k, (m, r) in MASTERS.items():
        h = hashlib.sha256()
        files, labels = [], set()
        for f, chunk in expand(os.path.join(src, m)):
            files.append(os.path.relpath(f, src))
            h.update(chunk.encode("utf-8"))
            labels.update(re.findall(r"\\label\{([^}]+)\}", chunk))
        sources[k] = {"master": m, "files": sorted(set(files)), "sha256": h.hexdigest(),
                      "labels": sorted(labels)}
    os.makedirs(out, exist_ok=True)
    json.dump(allc, open(os.path.join(out, "claims.json"), "w"), indent=1)
    json.dump(allp, open(os.path.join(out, "prose_claims.json"), "w"), indent=1)
    json.dump(sources, open(os.path.join(out, "claims_sources.json"), "w"), indent=1)
    print(f"numbered claims {len(allc)}, prose claims {len(allp)}")
    for k, v in sources.items():
        print(f"  {k}: {len(v['files'])} source files, sha256 {v['sha256'][:16]}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
