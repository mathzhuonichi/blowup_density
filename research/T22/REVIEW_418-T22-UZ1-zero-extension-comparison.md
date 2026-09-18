ACCEPT-WITH-NOTES

## what the lane claims

The report claims the canonical U-Z1 theorem with required quantifier order, positive constant, two inequalities, type-match probe, nonzero bump, and standard axiom audit.

## what is in Lean

The theorem at formalization/NSFormalization/Section3/T22/ZeroExtensionComparison.lean:28 exactly matches the field at formalization/NSFormalization/Section3/T22/Domain.lean:70; conjuncts are lines 32-35 and 74-77. Cutoff and constant selection are lines 37-39, the left bound line 42, and cutoff datum application lines 47-50. Empty and nonempty datum cases are lines 51-61. Probe matches are research/T22/probes/zero_extension_comparison_closes.lean:23-35; the nonzero bump is proved through line 108.

No vacuous or silently strengthened hypothesis was found. Positivity is used in line 60, and support/smoothness are passed at line 49. Whole-tree grep found no missing lemma relevant to any claimed gap.

## gaps

No proof gap remains. No sorry/admit/axiom/native_decide or maxHeartbeats appears in the reviewed files. CutoffDatum.lean is a new prerequisite file; no existing tracked module is modified relative to origin/erenup/integration-section3.

A substantive negative probe reversing the left inequality failed with the expected Lean type mismatch.

## commands and results

- lake build module: exit 0, Build completed successfully (9886 jobs).
- lake env lean module and closing probe: exit 0, 0 output.
- lake env lean axioms_uz1.lean: exit 0; [propext, Classical.choice, Quot.sound].
- make check: exit 0; 13 policy tests OK and 45 work items consistent.
- scripts/gates.sh: completed with no lane errors. Verification was untouched, so base-ref contract checking was not required.
- Negative probe research/T22/probes/rev418_negative.lean: failed with expected type mismatch.
