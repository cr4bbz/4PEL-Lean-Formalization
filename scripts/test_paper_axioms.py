import unittest

from check_paper_axioms import audit_output


class AuditTests(unittest.TestCase):
    def test_standard_multiline(self):
        rows = audit_output("'a' depends on axioms: [propext,\nQuot.sound]", ["a"])
        self.assertEqual(rows[0]["trust"], "standard-lean")

    def test_no_axioms(self):
        self.assertEqual(audit_output("'a' does not depend on any axioms", ["a"])[0]["axioms"], [])

    def test_native_rejected(self):
        for dep in ["a._native.native_decide.ax_1_1", "Lean.ofReduceBool", "Lean.trustCompiler"]:
            with self.subTest(dep=dep), self.assertRaises(ValueError):
                audit_output(f"'a' depends on axioms: [{dep}]", ["a"])

    def test_reject_unproved(self):
        for dep in ["sorryAx", "PEL4.unproved", "x_native.native_decide.ax", "a._native.native_decide.ax_extra"]:
            with self.subTest(dep=dep), self.assertRaises(ValueError):
                audit_output(f"'a' depends on axioms: [{dep}]", ["a"])

    def test_incomplete_and_duplicate(self):
        for output, expected in [("", []), ("", ["a"]),
                                 ("'a' does not depend on any axioms", ["a", "a"]),
                                 ("'a' does not depend on any axioms\n'a' does not depend on any axioms", ["a"])]:
            with self.subTest(output=output), self.assertRaises(ValueError):
                audit_output(output, expected)

    def test_review_lemmas_strict(self):
        name = "PEL4.PaperReview.boundary"
        with self.assertRaises(ValueError):
            audit_output(f"'{name}' depends on axioms: [Lean.ofReduceBool]", [name])


if __name__ == "__main__":
    unittest.main()
