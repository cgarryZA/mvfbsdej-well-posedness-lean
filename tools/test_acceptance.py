#!/usr/bin/env python3
"""Regression tests of the status logic, the inventory validation and the release gate of
`tools/acceptance.py`. They use synthetic inventories and need neither Lean nor the manuscripts.

    python3 tools/test_acceptance.py
"""
import argparse
import json
import os
import sys
import unittest
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import acceptance as A  # noqa: E402


def clause(name, spec=True, accept_ok=None, refute_ok=None, corrects=None, review="reviewed by x",
           pending=(), changed=(), author=()):
    c = {"name": name, "spec": f"Dissertation.PaperSpec.A.{name}" if spec else None,
         "corrects": corrects, "witness": None, "defs": [], "spec_review": review,
         "defs_pending": list(pending), "defs_changed": list(changed),
         "author_reviewed": list(author)}
    if accept_ok is not None:
        c["accept"] = f"Dissertation.Acceptance.A.{name}"
        c["accept_ok"] = accept_ok
    if refute_ok is not None:
        c["refute"] = f"Dissertation.Acceptance.A.{name}_false"
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
        cs = [clause("a", accept_ok=True, changed=["Dissertation.X"])]
        self.assertEqual(A.claim_status(FORMAL, cs), "formal: proved, review pending")

    def test_author_only_review(self):
        cs = [clause("a", accept_ok=True, author=["Dissertation.PaperSpec.A.a"])]
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
            write_evidence(ev, ENV, ["Dissertation.Acceptance.A.a"])
            rows = self.clean_rows()
            data = {"claims": [dict(r, clauses=[{k: c.get(k) for k in ("name", "spec", "accept")}
                                                for c in r["clauses"]]) for r in rows]}
            args = argparse.Namespace(paper=None,
                                      comparator_result=os.path.join(ev, A.COMPARATOR_RESULT))
            with mock.patch.object(A, "evaluate", return_value=(data, [], status_of(rows), True)), \
                    mock.patch.object(A, "environment_binding", return_value=dict(ENV)), \
                    mock.patch("builtins.print"):
                A.release_gate(args)


ENV = {"toolchain": "leanprover/lean4:v4.32.0", "Dissertation": "d1", "LevyStochCalc": "l1"}
NAME = "Dissertation.Acceptance.A.a"


def write_evidence(ev, env, names, exit_code=0, log="\n".join(A.COMPARATOR_OK), drift=False):
    """A comparator run in `ev` bound by `comparator_bind`, with the environment `env` (changing
    during the run when `drift`)."""
    open(os.path.join(ev, "comparator.json"), "w").write(json.dumps({"theorem_names": names}))
    open(os.path.join(ev, "AcceptanceChallenge.lean"), "w").write("theorem x : True := sorry\n")
    open(os.path.join(ev, "comparator.log"), "w").write(log)
    with mock.patch.object(A, "environment_binding", return_value=dict(env)), \
            mock.patch("builtins.print"):
        A.comparator_bind(argparse.Namespace(evidence=ev, stage="start", exit_code=None))
    after = dict(env, Dissertation="changed") if drift else dict(env)
    with mock.patch.object(A, "environment_binding", return_value=after), \
            mock.patch("builtins.print"):
        A.comparator_bind(argparse.Namespace(evidence=ev, stage=None, exit_code=exit_code))
    return json.load(open(os.path.join(ev, A.COMPARATOR_RESULT)))


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
        out = self.failures(env_now=dict(ENV, Dissertation="d2"))
        self.assertTrue(any("Dissertation is not the replayed one" in m for m in out))

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
        out = self.failures(names=(NAME, "Dissertation.Acceptance.A.b"))
        self.assertTrue(any("not replayed" in m for m in out))

    def test_absent_result_rejected(self):
        self.assertTrue(A.comparator_failures(None, [NAME], dict(ENV)))

    def test_mismatched_challenge_rejected(self):
        import tempfile
        with tempfile.TemporaryDirectory() as ev:
            result = write_evidence(ev, ENV, [NAME])
            open(os.path.join(ev, "AcceptanceChallenge.lean"), "a").write("-- edited\n")
            out = A.comparator_failures(result, [NAME], dict(ENV), ev)
            self.assertTrue(any("AcceptanceChallenge.lean" in m for m in out))
            os.remove(os.path.join(ev, "comparator.json"))
            out = A.comparator_failures(result, [NAME], dict(ENV), ev)
            self.assertTrue(any("comparator.json" in m for m in out))

    def test_tree_digest_sees_content(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, "X"))
            open(os.path.join(d, "X", "a.lean"), "w").write("theorem a : True := trivial\n")
            h1 = A.tree_digest(d, A.lean_tree(d, "X"))
            open(os.path.join(d, "X", "a.lean"), "w").write("theorem a : 1 = 1 := rfl\n")
            self.assertNotEqual(h1, A.tree_digest(d, A.lean_tree(d, "X")))

if __name__ == "__main__":
    unittest.main()
