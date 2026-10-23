#!/usr/bin/env python3
"""Regression tests of the status logic, the inventory validation and the release gate of
`tools/acceptance.py`. They use synthetic inventories and need neither Lean nor the manuscripts.

    python3 tools/test_acceptance.py
"""
import argparse
import json
import os
import pathlib
import sys
import unittest
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import acceptance as A  # noqa: E402


def clause(name, spec=True, accept_ok=None, refute_ok=None, corrects=None, review="reviewed by x",
           pending=(), changed=(), author=()):
    c = {"name": name, "spec": f"MVFBSDEJ.PaperSpec.{name}" if spec else None,
         "corrects": corrects, "witness": None, "defs": [], "spec_review": review,
         "defs_pending": list(pending), "defs_changed": list(changed),
         "author_reviewed": list(author)}
    if accept_ok is not None:
        c["accept"] = f"MVFBSDEJ.Acceptance.{name}"
        c["accept_ok"] = accept_ok
    if refute_ok is not None:
        c["refute"] = f"MVFBSDEJ.Acceptance.{name}_false"
        c["refute_ok"] = refute_ok
    return c


FORMAL = {"scope": "formal"}


def claim(cid, clauses, scope="formal", paper="A", note="", scope_reviewed=True):
    return {"id": cid, "paper": paper, "scope": scope, "scope_note": note,
            "scope_reviewed": scope_reviewed, "clauses": clauses}


class Status(unittest.TestCase):
    def test_mixed_refutation_correction_open(self):
        cs = [clause("printed", refute_ok=True),
              clause("fixed", accept_ok=True, corrects="printed"),
              clause("other", spec=False)]
        self.assertEqual(A.claim_status(FORMAL, cs),
                         "refuted as printed; corrected statement proved; other clauses open")

    def test_refutation_without_correction_and_open(self):
        cs = [clause("printed", refute_ok=True), clause("other")]
        self.assertEqual(A.claim_status(FORMAL, cs), "refuted as printed; other clauses open")

    def test_refutation_all_resolved(self):
        cs = [clause("printed", refute_ok=True),
              clause("fixed", accept_ok=True, corrects="printed"),
              clause("other", accept_ok=True)]
        self.assertEqual(A.claim_status(FORMAL, cs),
                         "refuted as printed; corrected statement proved")

    def test_correction_of_another_clause_does_not_count(self):
        cs = [clause("p1", refute_ok=True), clause("p2", refute_ok=True),
              clause("fix1", accept_ok=True, corrects="p1")]
        self.assertEqual(A.claim_status(FORMAL, cs), "refuted as printed")

    def test_correction_only_claim_is_not_accepted(self):
        cs = [clause("fix", accept_ok=True, corrects="missing-clause")]
        self.assertEqual(A.claim_status(FORMAL, cs), "formal: malformed")

    def test_stale_definition_hash(self):
        cs = [clause("a", accept_ok=True, changed=["MVFBSDEJ.X"])]
        self.assertEqual(A.claim_status(FORMAL, cs), "formal: proved, review pending")

    def test_author_only_review(self):
        cs = [clause("a", accept_ok=True, author=["MVFBSDEJ.PaperSpec.a"])]
        self.assertEqual(A.claim_status(FORMAL, cs), "formal: proved, author-reviewed")

    def test_clean(self):
        self.assertEqual(A.claim_status(FORMAL, [clause("a", accept_ok=True)]),
                         "formal: accepted")

    def test_open(self):
        self.assertEqual(A.claim_status(FORMAL, [clause("a", accept_ok=True), clause("b")]),
                         "formal: open")


class Validate(unittest.TestCase):
    def raw(self, clauses):
        return claim("A:x", [{k: v for k, v in c.items()
                              if k in ("name", "spec", "accept", "refute", "corrects")}
                             for c in clauses])

    def test_dangling_correction(self):
        e = self.raw([clause("a", accept_ok=True), clause("fix", corrects="nope")])
        self.assertTrue(any("missing clause" in m for m in A.validate_clauses(e)))

    def test_self_correction(self):
        e = self.raw([clause("a", accept_ok=True), clause("fix", corrects="fix")])
        self.assertTrue(any("corrects itself" in m for m in A.validate_clauses(e)))

    def test_correction_cycle(self):
        e = self.raw([clause("o", accept_ok=True), clause("a", corrects="b"),
                      clause("b", corrects="a")])
        self.assertTrue(any("corrects a correction" in m for m in A.validate_clauses(e)))

    def test_correction_only(self):
        e = self.raw([clause("fix", corrects="gone")])
        self.assertTrue(any("no original clause" in m for m in A.validate_clauses(e)))

    def test_duplicate_names(self):
        e = self.raw([clause("a", accept_ok=True), clause("a", accept_ok=True)])
        self.assertTrue(any("duplicate clause name" in m for m in A.validate_clauses(e)))

    def test_clean_graph(self):
        e = self.raw([clause("p", refute_ok=True), clause("fix", accept_ok=True, corrects="p")])
        self.assertEqual(A.validate_clauses(e), [])

    def test_host_cycle(self):
        data = {"claims": [claim("A:a", [], scope="part-of", note="A:b"),
                           claim("A:b", [], scope="duplicate", note="A:a")]}
        self.assertTrue(any("cycle" in m for m in A.validate(data)))


def status_of(rows):
    return {"claims": [dict(r, number="1", kind="k", status=A.claim_status(r, r["clauses"]))
                       for r in rows], "summary": {}}


class Alignment(unittest.TestCase):
    def test_numbered_statements_in_target(self):
        data = {"claims": [
            dict(claim("A:thm", [clause("thm", accept_ok=True)]), number="Theorem 3.3"),
            dict(claim("A:lem", [clause("lem", refute_ok=True),
                                 clause("lem_fix", accept_ok=True, corrects="lem")]),
                 number="Lemma A.1"),
            dict(claim("A:def", [dict(clause("d", spec=False), defs=["MVFBSDEJ.D"])],
                       scope="definition"), number="Definition 2.1"),
            dict(claim("A:part", [], scope="part-of", note="A:thm"), number="Example 5.1"),
            dict(claim("A:eq", [clause("eq", accept_ok=True)]), number="(4.2)")]}
        status = {"claims": [{"id": c["id"], "status": "s"} for c in data["claims"]]}
        out = A.alignment(data, status)
        self.assertIn('source: "Theorem 3.3"', out)
        self.assertIn('source: "Lemma A.1"', out)
        self.assertIn('"MVFBSDEJ.Acceptance.lem_false"', out)
        self.assertIn('"MVFBSDEJ.Acceptance.lem_fix"', out)
        self.assertIn('"MVFBSDEJ.D"', out)
        self.assertNotIn("Example 5.1", out)
        self.assertNotIn("(4.2)", out)


class ReleaseGate(unittest.TestCase):
    def clean_rows(self):
        return [claim("A:a", [clause("a", accept_ok=True)]),
                claim("A:lit", [], scope="literature")]

    def test_clean_passes(self):
        st = status_of(self.clean_rows())
        self.assertEqual(A.release_failures({}, st, [], True, "A", []), [])

    def test_missing_manuscript(self):
        st = status_of(self.clean_rows())
        out = A.release_failures({}, st, [], False, "A", [])
        self.assertTrue(any(m.startswith("sources:") for m in out))

    def test_open_clause_behind_refutation(self):
        rows = [claim("A:a", [clause("printed", refute_ok=True),
                              clause("fixed", accept_ok=True, corrects="printed"),
                              clause("other", spec=False)])]
        out = A.release_failures({}, status_of(rows), [], True, "A", [])
        self.assertTrue(any("other clauses open" in m for m in out))
        self.assertTrue(any("printed clause refuted" in m for m in out))

    def test_author_only_review(self):
        rows = [claim("A:a", [clause("a", accept_ok=True, author=["x"])])]
        out = A.release_failures({}, status_of(rows), [], True, "A", [])
        self.assertTrue(any("author-reviewed" in m for m in out))

    def test_unreviewed_scope(self):
        rows = [claim("A:lit", [], scope="literature", scope_reviewed=False)]
        out = A.release_failures({}, status_of(rows), [], True, "A", [])
        self.assertTrue(any("scope decision" in m for m in out))

    def test_comparator_required(self):
        out = A.release_failures({}, status_of(self.clean_rows()), [], True, "A",
                                 A.comparator_failures(None, ["x"], {}))
        self.assertTrue(any(m.startswith("comparator:") for m in out))

    def test_consistency_failure(self):
        out = A.release_failures({}, status_of(self.clean_rows()), ["x"], True, "A", [])
        self.assertTrue(any(m.startswith("consistency:") for m in out))

    def run_gate(self, rows, consistency=(), source=True):
        data = {"claims": [dict(r, clauses=[{k: c.get(k) for k in ("name", "spec", "accept")}
                                            for c in r["clauses"]]) for r in rows]}
        args = argparse.Namespace(paper=None, comparator_result=None)
        with mock.patch.object(A, "evaluate",
                               return_value=(data, list(consistency), status_of(rows), source)), \
                mock.patch("builtins.print"):
            try:
                A.release_gate(args)
            except SystemExit as ex:
                return ex.code
        return 0

    def test_cli_exit_code(self):
        self.assertEqual(self.run_gate(self.clean_rows()), 1)  # no comparator result given
        rows = [claim("A:a", [clause("a", accept_ok=True), clause("b")])]
        self.assertEqual(self.run_gate(rows), 1)

    def test_cli_passes_with_replay(self):
        import tempfile
        with tempfile.TemporaryDirectory() as ev:
            write_evidence(ev, ENV, ["MVFBSDEJ.Acceptance.a"])
            rows = self.clean_rows()
            data = {"claims": [dict(r, clauses=[{k: c.get(k) for k in ("name", "spec", "accept")}
                                                for c in r["clauses"]]) for r in rows]}
            args = argparse.Namespace(paper=None,
                                      comparator_result=os.path.join(ev, A.COMPARATOR_RESULT))
            with mock.patch.object(A, "evaluate", return_value=(data, [], status_of(rows), True)), \
                    mock.patch.object(A, "environment_binding", return_value=dict(ENV)), \
                    mock.patch("builtins.print"):
                A.release_gate(args)

    def test_refutation_must_be_replayed(self):
        import tempfile
        rows = [claim("X:a", [clause("printed", refute_ok=True),
                              clause("fixed", accept_ok=True, corrects="printed")])]
        keys = ("name", "spec", "accept", "refute")
        data = {"claims": [dict(r, clauses=[{k: c.get(k) for k in keys} for c in r["clauses"]])
                           for r in rows]}
        printed = []
        with tempfile.TemporaryDirectory() as ev:
            write_evidence(ev, ENV, ["MVFBSDEJ.Acceptance.fixed"])
            args = argparse.Namespace(paper=None,
                                      comparator_result=os.path.join(ev, A.COMPARATOR_RESULT))
            with mock.patch.object(A, "evaluate", return_value=(data, [], status_of(rows), True)), \
                    mock.patch.object(A, "environment_binding", return_value=dict(ENV)), \
                    mock.patch("builtins.print",
                               side_effect=lambda *a: printed.append(" ".join(map(str, a)))):
                with self.assertRaises(SystemExit):
                    A.release_gate(args)
        self.assertTrue(any("not replayed, e.g. MVFBSDEJ.Acceptance.printed_false" in m
                            for m in printed))


class Challenge(unittest.TestCase):
    """The statements `comparator-inputs` writes for the replay."""

    def test_refutation_is_the_negation(self):
        self.assertEqual(A.challenge_line("R", "S", "REF", ["w"], "0, 0, w"),
                         "theorem R.{w} : ¬ S.{0, 0, w} := sorry\n")

    def test_universe_order_of_the_proof(self):
        self.assertEqual(A.challenge_line("T", "S", "ACC", ["u", "v"], "v, u"),
                         "theorem T.{u, v} : S.{v, u} := sorry\n")

    def test_no_universes(self):
        self.assertEqual(A.challenge_line("T", "S", "ACC", [], ""), "theorem T : S := sorry\n")


ENV = {"toolchain": "leanprover/lean4:v4.32.0", "MVFBSDEJ": "d1", "LevyStochCalc": "l1"}
NAME = "MVFBSDEJ.Acceptance.a"


def write_evidence(ev, env, names, exit_code=0, log="\n".join(A.COMPARATOR_OK), drift=False):
    """A comparator run in `ev` bound by `comparator_bind`, with the environment `env` (changing
    during the run when `drift`)."""
    with open(os.path.join(ev, "comparator.json"), "w") as _f:
        _f.write(json.dumps({"theorem_names": names}))
    with open(os.path.join(ev, "AcceptanceChallenge.lean"), "w") as _f:
        _f.write("theorem x : True := sorry\n")
    with open(os.path.join(ev, "comparator.log"), "w") as _f:
        _f.write(log)
    with mock.patch.object(A, "environment_binding", return_value=dict(env)), \
            mock.patch("builtins.print"):
        A.comparator_bind(argparse.Namespace(evidence=ev, stage="start", exit_code=None))
    after = dict(env, MVFBSDEJ="changed") if drift else dict(env)
    with mock.patch.object(A, "environment_binding", return_value=after), \
            mock.patch("builtins.print"):
        A.comparator_bind(argparse.Namespace(evidence=ev, stage=None, exit_code=exit_code))
    return json.loads(pathlib.Path(os.path.join(ev, A.COMPARATOR_RESULT)).read_text())


class Sources(unittest.TestCase):
    """The source checks in both directions."""

    def env(self, label, text):
        return {"paper": "WP", "env": "theorem", "number": "1",
                "statement": f"\\label{{A:{label}}} {text}"}

    def entry(self, label, text):
        return {"id": f"A:{label}", "paper": "A", "location": "paper/x.tex:1",
                "source_sha256": A.sha(A.norm(f"\\label{{A:{label}}} {text}"))}

    def test_clean(self):
        self.assertEqual(A.source_failures([self.entry("t", "x")], [self.env("t", "x")],
                                           lambda e: ""), [])

    def test_changed_text_under_unchanged_label(self):
        out = A.source_failures([self.entry("t", "x")], [self.env("t", "y")], lambda e: "")
        self.assertTrue(any("source text changed" in m for m in out))

    def test_inserted_theorem_rejected(self):
        out = A.source_failures([self.entry("t", "x")],
                                [self.env("t", "x"), self.env("new", "z")], lambda e: "")
        self.assertTrue(any("A:new: in the manuscript" in m for m in out))

    def test_duplicate_extraction_rejected(self):
        out = A.source_failures([self.entry("t", "x")], [self.env("t", "x"), self.env("t", "x")],
                                lambda e: "")
        self.assertTrue(any("extracted twice" in m for m in out))

    def test_changed_anchor_line(self):
        e = {"id": "A:p", "paper": "A", "location": "paper/x.tex:3",
             "source_sha256": A.sha(A.norm("old line"))}
        self.assertTrue(A.source_failures([e], [], lambda _: "new line"))
        self.assertEqual(A.source_failures([e], [], lambda _: "old line"), [])


    def test_region_line_pins(self):
        """An entry pinned by source region checks every line its passage spans and names the
        first one that changed."""
        lines = ["\\begin{align}", "a&=1\\\\", "b&=2", "\\end{align}"]
        e = {"id": "A:eq", "paper": "A", "location": "paper/x.tex:10",
             "source_hash_scheme": A.REGION_SCHEME, "source_sha256": "f" * 64,
             "source_line_sha256": [A.sha(l) for l in lines]}
        self.assertEqual(A.source_failures([e], [], lambda _, k=0: lines[k]), [])
        edited = lines[:2] + ["b&=3"] + lines[3:]
        out = A.source_failures([e], [], lambda _, k=0: edited[k])
        self.assertEqual(out, ["A:eq: line 3 of its source passage (line 12 of paper/x.tex) "
                               "changed at the pin"])
        self.assertTrue(A.source_failures([e], [], lambda _, k=0: lines[:2][k]))
        self.assertTrue(A.source_failures([dict(e, source_line_sha256=[])], [],
                                          lambda _, k=0: lines[k]))


class ComparatorEvidence(unittest.TestCase):
    """The binding of a comparator run to its inputs."""

    def failures(self, env_now=ENV, names=(NAME,), **kw):
        import tempfile
        with tempfile.TemporaryDirectory() as ev:
            result = write_evidence(ev, ENV, [NAME], **kw)
            return A.comparator_failures(result, list(names), dict(env_now), ev)

    def test_fresh_replay_accepted(self):
        self.assertEqual(self.failures(), [])

    def test_changed_sources_same_names_rejected(self):
        out = self.failures(env_now=dict(ENV, MVFBSDEJ="d2"))
        self.assertTrue(any("MVFBSDEJ is not the replayed one" in m for m in out))

    def test_changed_dependency_or_toolchain_rejected(self):
        self.assertTrue(self.failures(env_now=dict(ENV, LevyStochCalc="l2")))
        self.assertTrue(self.failures(env_now=dict(ENV, toolchain="leanprover/lean4:v4.33.0")))

    def test_success_text_from_failed_process_rejected(self):
        self.assertTrue(any("exit status 1" in m for m in self.failures(exit_code=1)))

    def test_log_without_replay_rejected(self):
        out = self.failures(log="Exporting #[" + NAME + "]")
        self.assertTrue(any("no successful kernel replay" in m for m in out))

    def test_environment_changed_during_run_rejected(self):
        out = self.failures(drift=True)
        self.assertTrue(any("changed during the run" in m for m in out))

    def test_missing_proof_rejected(self):
        out = self.failures(names=(NAME, "MVFBSDEJ.Acceptance.b"))
        self.assertTrue(any("not replayed" in m for m in out))

    def test_absent_result_rejected(self):
        self.assertTrue(A.comparator_failures(None, [NAME], dict(ENV)))

    def test_mismatched_challenge_rejected(self):
        import tempfile
        with tempfile.TemporaryDirectory() as ev:
            result = write_evidence(ev, ENV, [NAME])
            with open(os.path.join(ev, "AcceptanceChallenge.lean"), "a") as _f:
                _f.write("-- edited\n")
            out = A.comparator_failures(result, [NAME], dict(ENV), ev)
            self.assertTrue(any("AcceptanceChallenge.lean" in m for m in out))
            os.remove(os.path.join(ev, "comparator.json"))
            out = A.comparator_failures(result, [NAME], dict(ENV), ev)
            self.assertTrue(any("comparator.json" in m for m in out))

    def test_tree_digest_sees_content(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, "X"))
            with open(os.path.join(d, "X", "a.lean"), "w") as _f:
                _f.write("theorem a : True := trivial\n")
            h1 = A.tree_digest(d, A.lean_tree(d, "X"))
            with open(os.path.join(d, "X", "a.lean"), "w") as _f:
                _f.write("theorem a : 1 = 1 := rfl\n")
            self.assertNotEqual(h1, A.tree_digest(d, A.lean_tree(d, "X")))


H = "0123456789abcdef0123456789abcdef"
OLD, NEW = "a" * 64, "b" * 64
SPEC = "MVFBSDEJ.PaperSpec.a"
ACC = "MVFBSDEJ.Acceptance.a"
DEFN = "MVFBSDEJ.D"


def marker(kind, name, who, *sources, h=H):
    src = "".join(f" source={c}@{d}" for c, d in sources)
    return f"<!-- {kind}-review: {name} {h} by={who}{src} -->"


class ReviewMarkers(unittest.TestCase):
    """A review counts for a claim only while the passage digest it records is the claim's
    current one."""

    def inventory(self, digest=NEW):
        return {"claims": [
            dict(claim("A:t", [{"name": "main", "spec": SPEC, "accept": ACC}]),
                 number="Theorem 1", kind="theorem", source_sha256=digest),
            dict(claim("A:u", [{"name": "main", "spec": SPEC, "accept": ACC}]),
                 number="Remark 2", kind="remark", source_sha256=NEW),
            dict(claim("A:d", [{"name": "main", "spec": None, "defs": [DEFN]}],
                       scope="definition"), number="Definition 1", kind="definition",
                 source_sha256=digest)]}

    def probe(self, closure=None):
        return {"spec": {SPEC: {"verdict": "ok", "hash": H}},
                "def": {DEFN: {"verdict": "ok", "hash": H}},
                "proof": {ACC: {"verdict": "ok"}}, "closure": closure or {}}

    def status(self, text, digest=NEW, closure=None):
        spec, defs, bad = A.parse_reviews([("A.md", text)])
        self.assertEqual(bad, [])
        st = A.build_status(self.inventory(digest), self.probe(closure), spec, defs)
        return {r["id"]: r for r in st["claims"]}, st

    def test_parse(self):
        spec, defs, bad = A.parse_reviews([("A.md", marker("spec", SPEC, "r", ("A:t", NEW))
                                            + marker("def", DEFN, "r"))])
        self.assertEqual(spec[SPEC], [{"hash": H, "file": "A.md", "by": "r",
                                       "sources": {"A:t": NEW}}])
        self.assertEqual(defs[DEFN][0]["sources"], {})
        self.assertEqual(bad, [])

    def test_malformed_marker_reported(self):
        _, _, bad = A.parse_reviews([("A.md", f"<!-- spec-review: {SPEC} {H} by=r "
                                               "source=A:t@abc -->")])
        self.assertEqual(len(bad), 1)
        self.assertIn("malformed review marker", bad[0])

    def test_current_passage_reviewed(self):
        rows, _ = self.status(marker("spec", SPEC, "r", ("A:t", NEW)))
        self.assertEqual(rows["A:t"]["status"], "formal: accepted")
        self.assertEqual(rows["A:t"]["clauses"][0]["spec_review"], "reviewed by r")

    def test_changed_passage_reopens_and_is_named(self):
        rows, st = self.status(marker("spec", SPEC, "r", ("A:t", OLD), ("A:u", NEW)))
        self.assertEqual(rows["A:t"]["status"], "formal: proved, review pending")
        self.assertEqual(rows["A:t"]["clauses"][0]["spec_review"], "passage changed since review")
        self.assertEqual(rows["A:t"]["clauses"][0]["passage_changed"], {SPEC: ["r"]})
        # The same reading still counts for the claim whose passage is unchanged.
        self.assertEqual(rows["A:u"]["status"], "formal: accepted")
        notes = A.passage_notes(st)
        self.assertEqual(len(notes), 1)
        self.assertTrue(notes[0].startswith("A:t: its source passage changed since the reading "
                                            "of a by r"))

    def test_reading_without_passage_is_not_a_review(self):
        rows, _ = self.status(marker("spec", SPEC, "r"))
        self.assertEqual(rows["A:t"]["clauses"][0]["spec_review"], "not reviewed")
        self.assertEqual(rows["A:t"]["status"], "formal: proved, review pending")

    def test_reading_of_another_claim_does_not_count(self):
        rows, _ = self.status(marker("spec", SPEC, "r", ("A:u", NEW)))
        self.assertEqual(rows["A:t"]["status"], "formal: proved, review pending")
        self.assertEqual(rows["A:u"]["status"], "formal: accepted")

    def test_changed_proposition_still_reopens(self):
        rows, _ = self.status(marker("spec", SPEC, "r", ("A:t", NEW), h="f" * 32))
        self.assertEqual(rows["A:t"]["clauses"][0]["spec_review"], "changed since review")

    def test_later_marker_at_older_hash_reopens(self):
        """The last marker, in file order, is the current record: a reading at the current hash
        followed by one at an older hash does not count."""
        cur = marker("spec", SPEC, "r", ("A:t", NEW))
        old = marker("spec", SPEC, "r", ("A:t", NEW), h="f" * 32)
        spec, defs, _ = A.parse_reviews([("A.md", cur), ("rereads.md", old)])
        st = A.build_status(self.inventory(NEW), self.probe(), spec, defs)
        row = {r["id"]: r for r in st["claims"]}["A:t"]
        self.assertEqual(row["clauses"][0]["spec_review"], "changed since review")
        self.assertEqual(row["status"], "formal: proved, review pending")
        rows, _ = self.status(old + cur)
        self.assertEqual(rows["A:t"]["status"], "formal: accepted")

    def test_fresh_reading_beside_stale_one(self):
        text = (marker("spec", SPEC, "claude-author", ("A:t", NEW))
                + marker("spec", SPEC, "r", ("A:t", OLD)))
        rows, _ = self.status(text)
        self.assertEqual(rows["A:t"]["status"], "formal: proved, author-reviewed")
        text += marker("spec", SPEC, "s", ("A:t", NEW))
        rows, _ = self.status(text)
        self.assertEqual(rows["A:t"]["status"], "formal: accepted")

    def test_definition_claim_passage(self):
        rows, _ = self.status(marker("def", DEFN, "r", ("A:d", NEW)))
        self.assertEqual(rows["A:d"]["status"], "definition: reviewed")
        rows, _ = self.status(marker("def", DEFN, "r", ("A:d", OLD)))
        self.assertEqual(rows["A:d"]["status"], "definition: review pending")
        self.assertEqual(rows["A:d"]["clauses"][0]["passage_changed"], {DEFN: ["r"]})

    def test_closure_definitions_are_reviewed_at_their_hash(self):
        closure = {SPEC: {"MVFBSDEJ.X": {"kind": "def", "hash": H, "module": "M",
                                             "line": 1}}}
        text = marker("spec", SPEC, "r", ("A:t", NEW)) + marker("def", "MVFBSDEJ.X", "r")
        rows, _ = self.status(text, closure=closure)
        self.assertEqual(rows["A:t"]["status"], "formal: accepted")

    def test_marker_sources_validated(self):
        spec, defs, _ = A.parse_reviews([("A.md", marker("spec", SPEC, "r", ("A:nope", NEW))
                                          + marker("def", DEFN, "r", ("A:t", NEW)))])
        out = A.marker_failures(self.inventory(), spec, defs)
        self.assertTrue(any("A:nope, which is not a claim" in m for m in out))
        self.assertTrue(any("def-review of MVFBSDEJ.D by r records a reading of A:t, which "
                            "does not use it" in m for m in out))

if __name__ == "__main__":
    unittest.main()
