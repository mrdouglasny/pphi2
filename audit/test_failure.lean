/-
DELIBERATE TEST FAILURE — to be reverted before merge.

This file contains a `sorry` and is NOT in audit/sorry-allowlist.txt.
It's also not imported by Pphi2.lean, so `lake build` is unaffected.

Purpose: exercise the sorry-confinement gate from the
math-commons/formalization-assurance reusable workflow.
-/

theorem audit_test_failure : True := by sorry
