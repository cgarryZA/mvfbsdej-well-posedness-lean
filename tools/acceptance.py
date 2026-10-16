#!/usr/bin/env python3
"""The acceptance check of the manuscript.

Every claim of the paper, at the revision formalised against, has a stable identifier in
`acceptance/claims.json` (the frozen inventory) and a scope: `formal` (a statement to be proved),
`definition` (a definition or assumption, reviewed but not proved), or one of the out-of-scope
reasons `expository`, `literature`, `empirical`, `proof-step` (a step inside a printed proof,
superseded by the proof of the enclosing result), `part-of` (a clause of another claim) and
`duplicate`. A formal claim has one or more clauses; a clause names

* `spec`: a closed proposition `Dissertation.PaperSpec.*` (a definition of type `Prop` with no
  parameters), written from the manuscript;
* `accept`: a theorem `Dissertation.Acceptance.*` whose type is exactly that proposition, or
* `refute`: a theorem whose type is its negation, with the corrected statement as a separate
  clause (`corrects`);
* `witness` (optional): a theorem `Dissertation.Acceptance.*` stating that the proposition's
  hypotheses hold at an instance the manuscript intends. Its statement is compared with the
  proposition's hypotheses by the review; the check verifies that it is a theorem of the
  acceptance layer over the three standard axioms.

The check is mechanical. It reads the manuscript at the pinned version (`PAPER_SOURCE`, whose
source is vendored in `manuscript/paper/`; `--paper` names another such `paper/` directory, or a
git checkout read with `git archive` at the pin) and compares the hash of every claim's source
text with the inventory; it asks Lean
(`tools/acceptance_probe.lean`) whether each proposition is a closed `Prop` of the specification
layer, whether each proof has exactly the proposition (or its negation) as type, which axioms each
proof depends on (only `propext`, `Classical.choice`, `Quot.sound` pass), and whether a module of
the specification layer imports the acceptance layer; and it hashes every proposition and every
declaration of `Dissertation` or `LevyStochCalc` its meaning depends on (proofs erased). A
proposition or definition counts as reviewed only when `acceptance/review/*.md` records a review
of it at its current hash, so a change of meaning reopens its review.

A claim is *accepted* when every clause is proved and reviewed. The report says, per claim, which
of these holds; it does not grade coverage.

    acceptance.py check [--paper PATH] [--write]     check; with --write regenerate the report
    acceptance.py hashes NAME...                     print current hashes, for review markers
    acceptance.py comparator-inputs --out CFG        challenge module and config for comparator
    acceptance.py comparator-bind --evidence DIR (--stage start | --exit-code N)
                                                     bind a comparator run to its inputs
    acceptance.py release-gate [--paper PATH] [--comparator-result FILE]
                                                     strict whole-paper gate

`check` is the development consistency check. It fails on a probe error, a source-hash mismatch,
a numbered environment of the manuscript at its pin that the inventory does not list, a layering
violation, a malformed inventory (clause graph included), or (without --write) a report that
differs from the committed one. Open, unspecified and unreviewed claims are statuses,
not failures, so its PASS is not a statement about any paper as a whole.

`release-gate` is the strict check of the paper. It fails unless the manuscript sources are
present and current, the consistency check is clean, every scope decision is reviewed, every
formal claim is accepted (every clause proved, every review current and by a reviewer other than
the author of the statements), every definition claim is reviewed likewise, no printed clause is
refuted, and a comparator result certifies a successful kernel replay of every proof of the
paper in the current environment: the process exited with status 0, its log reports the replay,
and the digests it recorded (toolchain, the Lean sources and package files of this repository and
of LevyStochCalc, the inventory, the comparator configuration and challenge) are the current ones
and did not change during the run. A log alone is not evidence: it names declarations, not their
content.
"""
import argparse
import collections
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CLAIMS = os.path.join(ROOT, "acceptance", "claims.json")
REVIEW_DIR = os.path.join(ROOT, "acceptance", "review")
REPORT = os.path.join(ROOT, "ACCEPTANCE.md")
STATUS = os.path.join(ROOT, "acceptance", "status.json")
PROBE = os.path.join(ROOT, "tools", "acceptance_probe.lean")
PAPERS = {"A": ("WP", "2608.23203v1", "well-posedness")}
PAPER_SOURCE = "https://arxiv.org/abs/2608.23203v1"
PAPER_DIR = os.path.join(ROOT, "manuscript", "paper")
SCOPES = {"formal", "definition", "expository", "literature", "empirical", "proof-step",
          "part-of", "duplicate"}
OUT_OF_SCOPE = SCOPES - {"formal", "definition"}
FORMAL_ENVS = {"theorem", "proposition", "lemma", "corollary", "example", "remark"}
DEFINITION_ENVS = {"definition", "assumption", "convention", "hypothesis"}


def sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def norm(text):
    return re.sub(r"\s+", " ", text).strip()


# ---------------------------------------------------------------------------------------------
# The manuscripts at the pinned commits

def extract(path, tmp):
    """Extract the manuscript into `tmp`; return (envs, sources dir). `path` is a git repository
    holding the pinned revision (its `paper/` tree is read at the pin) or a directory holding the
    `paper/` tree itself."""
    import shutil
    src = os.path.join(tmp, "papers")
    for key, pin, _ in PAPERS.values():
        dest = os.path.join(src, key)
        os.makedirs(dest, exist_ok=True)
        if os.path.exists(os.path.join(path, ".git")):
            arch = subprocess.run(["git", "-C", path, "archive", pin, "paper"],
                                  capture_output=True, check=True)
            subprocess.run(["tar", "-x", "-C", dest], input=arch.stdout, check=True)
        else:
            shutil.copytree(path, os.path.join(dest, "paper"))
    out = os.path.join(tmp, "extract")
    run = subprocess.run([sys.executable, os.path.join(ROOT, "tools", "extract_paper_claims.py"),
                          src, out], capture_output=True, text=True)
    if run.returncode != 0:
        sys.exit("claim extraction failed:\n" + run.stdout + run.stderr)
    return json.loads(pathlib.Path(os.path.join(out, "claims.json")).read_text()), src


def paper_of(key):
    return next(p for p, v in PAPERS.items() if v[0] == key)


def env_id(env):
    """`<paper>:<label>` for an environment that carries its own label, else
    `<paper>:<environment>-<number>` (a label met later in the body belongs to an equation)."""
    paper = paper_of(env["paper"])
    own = re.match(r"\s*\\label\{([^}]*)\}", env["statement"])
    label = own.group(1) if own else None
    if label:
        return label if label.startswith(paper + ":") else f"{paper}:{label}"
    return f"{paper}:{env['env']}-{env['number']}"


def line_text(src, paper, location):
    """The source line at `location` (`paper/<file>:<line>`) of a paper's pinned tree."""
    path, _, line = location.rpartition(":")
    full = os.path.join(src, PAPERS[paper][0], path)
    lines = pathlib.Path(full).read_text(encoding="utf-8").split("\n")
    return lines[int(line) - 1]


# ---------------------------------------------------------------------------------------------
# The Lean probe

def run_probe(queries, tmp):
    qpath = os.path.join(tmp, "query.txt")
    with open(qpath, "w") as _f:
        _f.write("\n".join(queries) + "\n")
    env = dict(os.environ, ACCEPTANCE_QUERY=qpath)
    run = subprocess.run(["lake", "env", "lean", PROBE], capture_output=True, text=True, env=env,
                         cwd=ROOT)
    out = run.stdout + run.stderr
    if run.returncode != 0 or "DONE" not in out:
        sys.exit("acceptance probe failed:\n" + out[-4000:])
    res = {"spec": {}, "def": {}, "proof": {}, "closure": collections.defaultdict(dict),
           "layer": [], "spec_modules": []}
    for line in out.splitlines():
        parts = line.split(" ")
        tag = parts[0]
        if tag == "SPEC" or tag == "DEF":
            res["spec" if tag == "SPEC" else "def"][parts[1]] = {
                "verdict": parts[2], "hash": parts[3] if len(parts) > 3 else None,
                "module": parts[4] if len(parts) > 4 else None}
        elif tag == "CLOS":
            res["closure"][parts[1]][parts[2]] = {"kind": parts[3], "hash": parts[4],
                                                  "module": parts[5],
                                                  "line": int(parts[6]) if len(parts) > 6 else 0}
        elif tag in ("ACC", "REF", "WIT"):
            res["proof"][parts[1]] = {"kind": tag, "spec": parts[2], "verdict": parts[3],
                                      "axioms": parts[4],
                                      "levels": [] if parts[5] == "-" else parts[5].split(",")}
        elif tag == "LAYER":
            res["layer"].append(line)
        elif tag == "SPECMODULE":
            res["spec_modules"].append(parts[1])
    return res


# ---------------------------------------------------------------------------------------------
# Review records

MARK = re.compile(r"<!--\s*(spec|def)-review:\s*(\S+)\s+([0-9a-f]{32})\s+by=(\S+)\s*-->")


def read_reviews():
    spec, defs = {}, {}
    if not os.path.isdir(REVIEW_DIR):
        return spec, defs
    for name in sorted(os.listdir(REVIEW_DIR)):
        if not name.endswith(".md"):
            continue
        text = pathlib.Path(REVIEW_DIR, name).read_text()
        for kind, decl, h, who in MARK.findall(text):
            (spec if kind == "spec" else defs)[decl] = (h, name, who)
    return spec, defs


# ---------------------------------------------------------------------------------------------
# check

def validate(data):
    errs, ids = [], set()
    for e in data["claims"]:
        if e["id"] in ids:
            errs.append(f"duplicate id {e['id']}")
        ids.add(e["id"])
        if e["scope"] not in SCOPES:
            errs.append(f"{e['id']}: unknown scope {e['scope']}")
        if e["scope"] in ("part-of", "duplicate") and not e.get("scope_note"):
            errs.append(f"{e['id']}: scope {e['scope']} must name its host claim")
        if e["scope"] in OUT_OF_SCOPE and e["clauses"]:
            errs.append(f"{e['id']}: an out-of-scope claim has clauses")
        for c in e["clauses"]:
            for key, pre in (("spec", "Dissertation.PaperSpec."),
                             ("accept", "Dissertation.Acceptance."),
                             ("refute", "Dissertation.Acceptance."),
                             ("witness", "Dissertation.Acceptance.")):
                v = c.get(key)
                if v and not v.startswith(pre):
                    errs.append(f"{e['id']}: {key} {v} is not under {pre}")
            if c.get("accept") and c.get("refute"):
                errs.append(f"{e['id']}: clause {c.get('name')} is both proved and refuted")
            if (c.get("accept") or c.get("refute") or c.get("witness")) and not c.get("spec"):
                errs.append(f"{e['id']}: clause {c.get('name')} has a proof but no proposition")
        errs += validate_clauses(e)
    hosts = {e["id"]: e["scope_note"] for e in data["claims"]
             if e["scope"] in ("part-of", "duplicate")}
    for e in data["claims"]:
        if e["scope"] in ("part-of", "duplicate") and e["scope_note"] not in ids:
            errs.append(f"{e['id']}: host {e['scope_note']} is not a claim id")
    for start in hosts:
        seen, cur = [start], hosts[start]
        while cur in hosts and cur not in seen:
            seen.append(cur)
            cur = hosts[cur]
        if cur in seen:
            errs.append(f"{start}: part-of/duplicate hosts form a cycle through {cur}")
    return errs


def validate_clauses(e):
    """The clause graph of one claim: names are unique, every `corrects` names an original clause
    of the same claim (never itself, never another correction, so no chain or cycle), and a
    formal claim with clauses has at least one original clause."""
    errs = []
    names = [c.get("name", "main") for c in e["clauses"]]
    for n in sorted({n for n in names if names.count(n) > 1}):
        errs.append(f"{e['id']}: duplicate clause name {n!r}")
    originals = {c.get("name", "main") for c in e["clauses"] if not c.get("corrects")}
    for c in e["clauses"]:
        t = c.get("corrects")
        if not t:
            continue
        if t == c.get("name", "main"):
            errs.append(f"{e['id']}: clause {t!r} corrects itself")
        elif t not in names:
            errs.append(f"{e['id']}: clause {c.get('name')!r} corrects a missing clause {t!r}")
        elif t not in originals:
            errs.append(f"{e['id']}: clause {c.get('name')!r} corrects a correction {t!r}")
    if e["scope"] == "formal" and e["clauses"] and not originals:
        errs.append(f"{e['id']}: a formal claim has corrections but no original clause")
    return errs


def check(args):
    data, failures, status, source_checked = evaluate(args.paper or PAPER_DIR)
    report = render(data, status, source_checked)
    if args.write:
        with open(REPORT, "w") as _f:
            _f.write(report)
        with open(STATUS, "w") as _f:
            json.dump(status, _f, indent=1, ensure_ascii=False, sort_keys=True)
        with open(STATUS, "a") as _f:
            _f.write("\n")
    else:
        old = pathlib.Path(REPORT).read_text() if os.path.exists(REPORT) else ""
        if old != report:
            failures.append("ACCEPTANCE.md differs from the generated report (run with --write)")
    for f in failures:
        print("FAIL", f)
    s = status["summary"]
    for p in PAPERS:
        print(f"paper {p}: " + ", ".join(f"{k} {v}" for k, v in s[p].items()))
    if not source_checked:
        print("note: manuscript not found; source hashes not checked")
    if failures:
        sys.exit(1)
    print("PASS (development consistency check: not a release gate; see release-gate)")


def source_failures(claims, envs, line_of):
    """The inventory against the numbered environments `envs` extracted at the pins, in both
    directions (`line_of(entry)` reads the anchor line of an entry): an environment whose text
    changed, an anchor line that changed or is missing, an environment extracted twice, and an
    extracted environment that the inventory does not list."""
    out = []
    ids = collections.Counter(env_id(env) for env in envs)
    by_id = {env_id(env): sha(norm(env["statement"])) for env in envs}
    out += [f"{i}: extracted twice from the manuscripts" for i in sorted(ids) if ids[i] > 1]
    for e in claims:
        if e["id"] in by_id:
            if by_id[e["id"]] != e["source_sha256"]:
                out.append(f"{e['id']}: source text changed at the pin")
        elif e["source_sha256"]:
            try:
                if sha(norm(line_of(e))) != e["source_sha256"]:
                    out.append(f"{e['id']}: source line changed at the pin")
            except (OSError, IndexError, ValueError):
                out.append(f"{e['id']}: source location {e['location']} missing")
    listed = {e["id"] for e in claims}
    out += [f"{i}: in the manuscript at the pin, not in the inventory"
            for i in sorted(set(by_id) - listed)]
    return out


def evaluate(papers):
    """The inventory, the consistency failures, the status and whether the manuscript sources
    were checked."""
    data = json.loads(pathlib.Path(CLAIMS).read_text())
    failures = validate(data)
    with tempfile.TemporaryDirectory() as tmp:
        source_checked = False
        if papers and os.path.isdir(papers):
            envs, src = extract(papers, tmp)
            failures += source_failures(data["claims"], envs,
                                        lambda e: line_text(src, e["paper"], e["location"]))
            source_checked = True
        queries = []
        for e in data["claims"]:
            for c in e["clauses"]:
                if c.get("spec"):
                    queries.append(f"SPEC {c['spec']}")
                if c.get("accept"):
                    queries.append(f"ACC {c['accept']} {c['spec']}")
                if c.get("refute"):
                    queries.append(f"REF {c['refute']} {c['spec']}")
                if c.get("witness"):
                    queries.append(f"WIT {c['witness']} {c['spec']}")
                for d in c.get("defs", []):
                    queries.append(f"DEF {d}")
        probe = run_probe(sorted(set(queries)), tmp)
    failures += [f"layering: {l}" for l in probe["layer"]]
    for n, r in {**probe["spec"], **probe["def"]}.items():
        if r["verdict"] != "ok":
            failures.append(f"{n}: {r['verdict']}")
    for n, r in probe["proof"].items():
        if r["verdict"] != "ok":
            failures.append(f"{n}: {r['verdict']}")
    spec_rev, def_rev = read_reviews()
    status = build_status(data, probe, spec_rev, def_rev)
    return data, failures, status, source_checked


# ---------------------------------------------------------------------------------------------
# The release gate

COMPARATOR_OK = ("Lean default kernel accepts", "Your solution is okay!")
COMPARATOR_RESULT = "comparator_result.json"
PACKAGE_FILES = ("lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json")
BOUND_FILES = ("acceptance/claims.json", "tools/acceptance.py", "tools/acceptance_probe.lean",
               "tools/extract_paper_claims.py", "tools/comparator_check.sh")


def file_sha256(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def tree_digest(root, files):
    """A digest of the files `files` (paths relative to `root`): their paths and contents."""
    h = hashlib.sha256()
    for rel in sorted(files):
        h.update(rel.encode() + b"\0" + bytes.fromhex(file_sha256(os.path.join(root, rel))))
    return h.hexdigest()


def lean_tree(root, top):
    """The Lean sources of the library `top` under `root`: `top.lean` and every `.lean` file below
    `top/`."""
    out = [f"{top}.lean"] if os.path.exists(os.path.join(root, f"{top}.lean")) else []
    for dp, dn, fn in os.walk(os.path.join(root, top)):
        dn[:] = sorted(d for d in dn if not d.startswith("."))
        out += [os.path.relpath(os.path.join(dp, f), root) for f in fn if f.endswith(".lean")]
    return out


def dependency_root():
    """The source directory of the requirement `LevyStochCalc`: its path, or for a git
    requirement its checkout in the package directory."""
    import tomllib
    with open(os.path.join(ROOT, "lakefile.toml"), "rb") as f:
        cfg = tomllib.load(f)
    for req in cfg.get("require", []):
        if req.get("name") == "LevyStochCalc":
            if req.get("path"):
                return os.path.normpath(os.path.join(ROOT, req["path"]))
            return os.path.join(ROOT, ".lake", "packages", "LevyStochCalc")
    return None


def environment_binding():
    """Digests of the inputs of the replayed environment: the toolchain; the Lean sources, the
    package files (the manifest pins every git dependency by revision), the inventory and the
    tools that generate the challenge of this repository; the Lean sources and package files of
    the dependency `LevyStochCalc`."""
    def package(root, top, extra=()):
        files = lean_tree(root, top) + [f for f in PACKAGE_FILES + tuple(extra)
                                        if os.path.exists(os.path.join(root, f))]
        return tree_digest(root, files)
    dep = dependency_root()
    return {"toolchain": pathlib.Path(os.path.join(ROOT, "lean-toolchain")).read_text().strip(),
            "Dissertation": package(ROOT, "Dissertation", BOUND_FILES),
            "LevyStochCalc": package(dep, "LevyStochCalc") if dep and os.path.isdir(dep)
            else None}


def comparator_bind(args):
    """Bind a comparator run in the evidence directory to its inputs. With `--stage start`, before
    the run, record the environment. After the run, write `comparator_result.json`: the exit
    status, whether the log reports a successful kernel replay, the theorems of the configuration,
    the digests of the configuration and the challenge, the environment, and whether it is the one
    recorded at the start."""
    ev = args.evidence
    start = os.path.join(ev, "environment_start.json")
    env = environment_binding()
    if args.stage == "start":
        with open(start, "w") as _f:
            json.dump(env, _f, indent=1)
        return

    def read(name):
        p = os.path.join(ev, name)
        return pathlib.Path(p).read_text() if os.path.exists(p) else None
    cfg, challenge, log = (os.path.join(ev, "comparator.json"),
                           os.path.join(ev, "AcceptanceChallenge.lean"), read("comparator.log"))
    result = {
        "exit_code": args.exit_code,
        "kernel_accepts": bool(log) and all(m in log for m in COMPARATOR_OK),
        "theorem_names": (json.loads(pathlib.Path(cfg).read_text())["theorem_names"]
                          if os.path.exists(cfg) else []),
        "config_sha256": file_sha256(cfg) if os.path.exists(cfg) else None,
        "challenge_sha256": file_sha256(challenge) if os.path.exists(challenge) else None,
        "environment": env,
        "environment_unchanged": (os.path.exists(start)
                                  and json.loads(pathlib.Path(start).read_text()) == env),
        "versions": read("comparator_versions.txt"),
    }
    with open(os.path.join(ev, COMPARATOR_RESULT), "w") as _f:
        json.dump(result, _f, indent=1)
    print(f"comparator result -> {os.path.join(ev, COMPARATOR_RESULT)}")


def comparator_failures(result, names, env, evidence=None):
    """Every reason a comparator result does not certify a replay of the environment `env` that
    covers the proofs `names`: no result, a failed process, a log without a successful replay, an
    environment that changed during the run or differs from `env`, a configuration or challenge
    in the evidence directory `evidence` other than the one recorded, or a proof not replayed."""
    if not result:
        return ["comparator: no result (tools/comparator_check.sh writes comparator_result.json)"]
    out = []
    if result.get("exit_code") != 0:
        out.append(f"comparator: exit status {result.get('exit_code')}")
    if not result.get("kernel_accepts"):
        out.append("comparator: the log records no successful kernel replay")
    if not result.get("environment_unchanged"):
        out.append("comparator: the environment changed during the run")
    recorded = result.get("environment") or {}
    for k in sorted(set(env) | set(recorded)):
        if recorded.get(k) != env.get(k):
            out.append(f"comparator: {k} is not the replayed one")
    if evidence is not None:
        for key, name in (("config_sha256", "comparator.json"),
                          ("challenge_sha256", "AcceptanceChallenge.lean")):
            p = os.path.join(evidence, name)
            if not result.get(key) or not os.path.exists(p) or file_sha256(p) != result[key]:
                out.append(f"comparator: {name} missing or not the one recorded")
    missing = sorted(set(names) - set(result.get("theorem_names") or []))
    if missing:
        out.append(f"comparator: {len(missing)} proofs not replayed, e.g. {missing[0]}")
    return out


def release_failures(data, status, consistency, source_checked, paper, comparator):
    """Every reason the paper is not releasable as a whole: the strict gate is the conjunction of
    current manuscript sources, a clean consistency check, reviewed scope decisions, every formal
    claim accepted (every clause proved and every review current and independent), every
    definition claim independently reviewed, no printed clause refuted (a refuted clause must be
    corrected in the released manuscript, not only beside it in the inventory), and a comparator
    replay of every proof of the paper (`comparator` lists the reasons there is none)."""
    out = []
    if not source_checked:
        out.append("sources: manuscript not available, source hashes unchecked")
    out += [f"consistency: {f}" for f in consistency]
    rows = [r for r in status["claims"] if r["paper"] == paper]
    if not rows:
        out.append(f"inventory: no claims for paper {paper}")
    for r in rows:
        if not r["scope_reviewed"]:
            out.append(f"{r['id']}: scope decision ({r['scope']}) not reviewed")
        if r["scope"] in OUT_OF_SCOPE:
            continue
        if r["scope"] == "definition":
            if r["status"] != "definition: reviewed":
                out.append(f"{r['id']}: {r['status']}")
            continue
        if r["status"] != "formal: accepted":
            out.append(f"{r['id']}: {r['status']}")
        for c in r["clauses"]:
            if c.get("refute_ok"):
                out.append(f"{r['id']}: printed clause refuted, unresolved in the manuscript: "
                           f"{c['name']}")
            if c.get("witness") and not c.get("witness_ok"):
                out.append(f"{r['id']}: witness fails: {c['name']}")
    return out + list(comparator)


def release_gate(args):
    data, consistency, status, source_checked = evaluate(args.paper or PAPER_DIR)
    names = sorted({c["accept"] for e in data["claims"] if e["paper"] == "A"
                    for c in e["clauses"] if c.get("accept")})
    path = args.comparator_result
    result = json.loads(pathlib.Path(path).read_text()) if path and os.path.exists(path) else None
    comparator = comparator_failures(result, names, environment_binding(),
                                     os.path.dirname(os.path.abspath(path)) if result else None)
    out = release_failures(data, status, consistency, source_checked, "A", comparator)
    for f in out:
        print("FAIL", f)
    if out:
        print(f"RELEASE GATE: FAIL ({len(out)} reasons)")
        sys.exit(1)
    print("RELEASE GATE: PASS")


AUTHOR = "claude-author"


def closure_review(names, probe, def_rev):
    """(pending, changed, author) project declarations in the closures of `names` without a
    current review, and those whose current review is by the author of the statements. A
    statement of a clause is reviewed by its own spec-review; every other declaration, auxiliary
    definitions of the statement layer included, needs a def-review."""
    pending, changed, author = set(), set(), set()
    for n in names:
        for d, info in probe["closure"].get(n, {}).items():
            if d in probe["spec"]:
                continue
            if d not in def_rev:
                pending.add(d)
            elif def_rev[d][0] != info["hash"]:
                changed.add(d)
            elif def_rev[d][2] == AUTHOR:
                author.add(d)
    return pending, changed, author


def build_status(data, probe, spec_rev, def_rev):
    rows, summary = [], {p: collections.Counter() for p in PAPERS}
    for e in data["claims"]:
        row = {"id": e["id"], "paper": e["paper"], "number": e["number"], "kind": e["kind"],
               "scope": e["scope"], "scope_note": e["scope_note"],
               "scope_reviewed": e["scope_reviewed"], "clauses": []}
        for c in e["clauses"]:
            spec = c.get("spec")
            cs = {"name": c.get("name", "main"), "spec": spec, "accept": c.get("accept"),
                  "refute": c.get("refute"), "corrects": c.get("corrects"),
                  "witness": c.get("witness"),
                  "defs": c.get("defs", [])}
            if spec:
                sp = probe["spec"].get(spec, {})
                cs["spec_ok"] = sp.get("verdict") == "ok"
                cs["spec_hash"] = sp.get("hash")
                rev = spec_rev.get(spec)
                cs["spec_review"] = (f"reviewed by {rev[2]}" if rev and rev[0] == sp.get("hash")
                                     else "changed since review" if rev else "not reviewed")
                pending, changed, author = closure_review([spec], probe, def_rev)
                if rev and rev[0] == sp.get("hash") and rev[2] == AUTHOR:
                    author.add(spec)
            else:
                pending, changed, author = closure_review(cs["defs"], probe, def_rev)
                for d in cs["defs"]:
                    dh = probe["def"].get(d, {}).get("hash")
                    rev = def_rev.get(d)
                    if not rev:
                        pending.add(d)
                    elif rev[0] != dh:
                        changed.add(d)
                    elif rev[2] == AUTHOR:
                        author.add(d)
                cs["spec_review"] = "n/a"
            cs["defs_pending"] = sorted(pending)
            cs["defs_changed"] = sorted(changed)
            cs["author_reviewed"] = sorted(author)
            for key in ("accept", "refute", "witness"):
                if c.get(key):
                    cs[key + "_ok"] = probe["proof"].get(c[key], {}).get("verdict") == "ok"
            row["clauses"].append(cs)
        row["status"] = claim_status(e, row["clauses"])
        summary[e["paper"]][row["status"]] += 1
        rows.append(row)
    return {"claims": rows, "summary": {p: dict(sorted(v.items())) for p, v in summary.items()}}


def reviewed(cs):
    return ((cs["spec_review"].startswith("reviewed") or cs["spec_review"] == "n/a")
            and not cs["defs_pending"] and not cs["defs_changed"])


def claim_status(e, clauses):
    """The status of a claim from the states of all its clauses. A refuted original clause never
    hides another original clause: the status says whether every refuted clause has a proved
    correction and whether the remaining original clauses are proved."""
    if e["scope"] in OUT_OF_SCOPE:
        return "out of scope: " + e["scope"]
    if e["scope"] == "definition":
        if not clauses:
            return "definition: not yet stated"
        if not all(reviewed(c) for c in clauses):
            return "definition: review pending"
        return ("definition: author-reviewed" if any(c["author_reviewed"] for c in clauses)
                else "definition: reviewed")
    if not clauses:
        return "formal: unspecified"
    originals = [c for c in clauses if not c.get("corrects")]
    if not originals:
        return "formal: malformed"
    refuted = [c for c in originals if c.get("refute_ok")]
    rest = [c for c in originals if not c.get("refute_ok")]
    rest_proved = all(c.get("accept_ok") for c in rest)
    if refuted:
        fixed = all(any(k.get("accept_ok") for k in clauses
                        if k.get("corrects") == c.get("name", "main")) for c in refuted)
        return ("refuted as printed" + ("; corrected statement proved" if fixed else "")
                + ("" if rest_proved else "; other clauses open"))
    if rest_proved:
        if not all(reviewed(c) for c in rest):
            return "formal: proved, review pending"
        return ("formal: proved, author-reviewed" if any(c["author_reviewed"] for c in rest)
                else "formal: accepted")
    return "formal: open"


# ---------------------------------------------------------------------------------------------
# The report

ORDER = ["formal: accepted", "formal: proved, author-reviewed", "formal: proved, review pending",
         "refuted as printed",
         "refuted as printed; corrected statement proved",
         "refuted as printed; other clauses open",
         "refuted as printed; corrected statement proved; other clauses open", "formal: open",
         "formal: unspecified", "formal: malformed", "definition: reviewed",
         "definition: author-reviewed", "definition: review pending",
         "definition: not yet stated"]


def short(n):
    return n.replace("Dissertation.PaperSpec.", "").replace("Dissertation.Acceptance.", "")


def render(data, status, source_checked):
    out = ["# Acceptance status of the manuscript", "",
           "Generated by `tools/acceptance.py` from `acceptance/claims.json`; do not edit by hand. "
           "The policy is `acceptance/README.md`.", "",
           "A claim is *accepted* when every clause has a proposition in `Dissertation.PaperSpec` "
           "written from the manuscript, a theorem in `Dissertation.Acceptance` whose type is "
           "exactly that proposition and whose axioms are among `propext`, `Classical.choice`, "
           "`Quot.sound`, and a review of the proposition and of every definition of "
           "`Dissertation` or `LevyStochCalc` its meaning depends on, recorded at the current "
           "hash, by a reviewer other than the author of the statements. *Proved, "
           "author-reviewed* has every review, but some only by the author of the statements "
           f"(`by={AUTHOR}`), which is not an independent check of their meaning. *Proved, "
           "review pending* has the proof but not every review. *Open* has the "
           "proposition but no proof. *Unspecified* has no proposition yet. The scope decisions "
           "of the frozen inventory are listed with their state of review.", ""]
    if not source_checked:
        out += ["The manuscript was not available: source hashes were not checked in this run.",
                ""]
    cols = ORDER + sorted({k for s in status["summary"].values() for k in s if k not in ORDER})
    out += ["## Summary", "", "| Status | " + " | ".join(PAPERS) + " |",
            "|---|" + "---|" * len(PAPERS)]
    for c in cols:
        out.append(f"| {c} | " + " | ".join(str(status["summary"][p].get(c, 0)) for p in PAPERS)
                   + " |")
    out.append("")
    by_paper = collections.defaultdict(list)
    for r in status["claims"]:
        by_paper[r["paper"]].append(r)
    for p, (_, pin, title) in PAPERS.items():
        out += [f"## Paper {p} ({title}, `{pin}`)", "",
                "| Claim | Number | Status | Proposition | Proof | Review |", "|---|---|---|---|---|---|"]
        for r in by_paper[p]:
            if r["scope"] in OUT_OF_SCOPE:
                continue
            props, proofs, revs = [], [], []
            for c in r["clauses"]:
                if c["spec"]:
                    props.append(f"`{short(c['spec'])}`")
                for d in c["defs"]:
                    props.append(f"`{d}`")
                if c.get("accept"):
                    proofs.append(f"`{short(c['accept'])}`" + ("" if c.get("accept_ok") else " (fails)"))
                if c.get("refute"):
                    proofs.append(f"¬ `{short(c['refute'])}`" + ("" if c.get("refute_ok") else " (fails)"))
                if c["spec"]:
                    rv = c["spec_review"]
                    if c.get("witness"):
                        rv += (f", hypotheses met: `{short(c['witness'])}`"
                               + ("" if c.get("witness_ok") else " (fails)"))
                elif c["defs"]:
                    rv = "definitions"
                else:
                    rv = "no proposition"
                k = len(c["defs_pending"]) + len(c["defs_changed"])
                tag = f"{c['name']}: " if len(r["clauses"]) > 1 else ""
                revs.append(tag + rv + (f", {k} definitions pending" if k else ""))
            out.append(f"| `{r['id']}` | {r['number']} | {r['status']} | {', '.join(props) or '—'}"
                       f" | {', '.join(proofs) or '—'} | {'; '.join(revs) or '—'} |")
        out.append("")
    out += ["## Out of scope", "",
            "| Claim | Number | Reason | Note | Scope reviewed |", "|---|---|---|---|---|"]
    for r in status["claims"]:
        if r["scope"] in OUT_OF_SCOPE:
            note = (r["scope_note"] or "").replace("|", "\\|").replace("\n", " ")
            if len(note) > 120:
                note = note[:117] + "..."
            out.append(f"| `{r['id']}` | {r['number']} | {r['scope']} | {note} | "
                       f"{'yes' if r['scope_reviewed'] else 'no'} |")
    out.append("")
    return "\n".join(out)


def hashes(args):
    with tempfile.TemporaryDirectory() as tmp:
        probe = run_probe([f"DEF {n}" for n in args.names], tmp)
    for n in args.names:
        r = probe["def"].get(n, {})
        print(f"<!-- def-review: {n} {r.get('hash')} by=REVIEWER -->  ({r.get('verdict')})")
        for d, info in sorted(probe["closure"].get(n, {}).items()):
            print(f"    closure {info['kind']:9} {d} {info['hash']} "
                  f"{info['module'].replace('.', '/')}.lean:{info['line']}")


def comparator_inputs(args):
    """Write `AcceptanceChallenge.lean` (each proved statement as a `sorry` theorem under the name of
    its proof, importing only the statements) and the comparator configuration."""
    data = json.loads(pathlib.Path(CLAIMS).read_text())
    pairs = sorted({(c["accept"], c["spec"]) for e in data["claims"] for c in e["clauses"]
                    if c.get("accept")})
    with tempfile.TemporaryDirectory() as tmp:
        probe = run_probe([f"ACC {a} {s}" for a, s in pairs], tmp)
    lines = ["import Dissertation.PaperSpec", ""]
    names = []
    for acc, spec in pairs:
        r = probe["proof"][acc]
        if r["verdict"] != "ok":
            continue
        lv = r["levels"]
        head = f"universe {' '.join(lv)} in\n" if lv else ""
        inst = f".{{{', '.join(lv)}}}" if lv else ""
        lines.append(f"{head}theorem {acc} : {spec}{inst} := sorry\n")
        names.append(acc)
    with open(os.path.join(ROOT, "AcceptanceChallenge.lean"), "w") as _f:
        _f.write("\n".join(lines))
    cfg = {"challenge_module": "AcceptanceChallenge", "solution_module": "Dissertation.Acceptance",
           "theorem_names": names,
           "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
           "enable_nanoda": args.nanoda}
    with open(args.out, "w") as _f:
        json.dump(cfg, _f, indent=1)
    print(f"{len(names)} theorems -> AcceptanceChallenge.lean, {args.out}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check")
    c.add_argument("--paper")
    c.add_argument("--write", action="store_true")
    h = sub.add_parser("hashes")
    h.add_argument("names", nargs="+")
    k = sub.add_parser("comparator-inputs")
    k.add_argument("--out", required=True)
    k.add_argument("--nanoda", action="store_true")
    b = sub.add_parser("comparator-bind")
    b.add_argument("--evidence", required=True)
    stage = b.add_mutually_exclusive_group(required=True)
    stage.add_argument("--stage", choices=["start"])
    stage.add_argument("--exit-code", type=int)
    g = sub.add_parser("release-gate")
    g.add_argument("--paper")
    g.add_argument("--comparator-result")
    args = ap.parse_args()
    {"check": check, "hashes": hashes,
     "comparator-inputs": comparator_inputs, "comparator-bind": comparator_bind,
     "release-gate": release_gate}[args.cmd](args)


if __name__ == "__main__":
    main()
