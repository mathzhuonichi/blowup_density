# Lane 162: ordinary enstrophy

## Theorem and scope

The target is the original C01 ordinary Frobenius gradient energy, tested
against the actual Laplacian. The candidate exports the identity, differential
bound, and integrated bound with the explicit constant `CRH1 = 2`. It does not
add an assumed smooth Sobolev path, energy identity, or pressure orthogonality.
The H2 Fourier estimate and the remaining full C01 API are outside this batch.

## Existing APIs and proof route

`EnstrophyIdentity.lean` applies `ordinaryWord_hasDerivWithinAt` separately to
the three words of length one and differentiates their squared physical L2
norms. Summation and `field_directional_inner` give the derivative pairing
with minus twice the Laplacian. This avoids subtracting word energies of
orders one and zero while proving the same ordinary gradient energy.

The length-one pressure and velocity words remain in the gradient and
solenoidal closed subspaces. Their orthogonality, summed and integrated by
parts, proves the pressure/Laplacian pairing vanishes. The classical solution
supplies both subspace hypotheses, and `momentum_split_toLp` then gives the
identity with the exact nonlinear and forcing signs.

Time derivatives are first obtained on a translated compact interior window
using the existing velocity and temporal-slice jet paths. The clamp is removed
locally and the translation undone. No claim of an endpoint derivative is used.

`EnstrophyBounds.lean` converts the already proved extended-real trilinear
bound under the original smallness threshold to a real work estimate. A
weighted square proves Young's inequality for forcing. Each spends one
quarter of the viscosity, leaving the coefficient ν in the doubled identity
and giving `CRH1 = 2`.

The true gradient and Laplacian energies are continuous on every compact
solution slab, including zero, through their physical L2 paths. The Laplacian
is therefore interval integrable. The integrated estimate uses Mathlib's
`sub_le_integral_of_hasDeriv_right_of_le`: it requires the derivative only on
the open interval and an integrable upper bound, supplied by the force square
and Laplacian square. Thus the original `Ico 0 t` smallness is sufficient,
including the degenerate endpoint t=0. The initial term is identified by the
actual classical initial equality.

## Remaining scope and original-vocabulary consumers

`axioms_enstrophy162.lean` contains all three complete original Spec consumers.
Its gradient uses the actual contract gradient tensor and the existing
non-definitional V2 PiLp/Frobenius bridge. The other quantities and the
registered `C₁` are definitionally the implementation's quantities. This
probe does not edit or extend a frozen contract.

The H2/Fourier comparison (`sobolevTwoFourier`) and the two H2 time-integral
consequences remain open after this batch. The three new outputs are not yet
registered in a new contract/API version. They must not be described as a
complete C01 API or a completed Section 4 theorem.

## Verification log

Compilation is delegated exclusively to `/root/wave2_compile` (Luna high).
The first identity build failed on an ambiguous `Space` caused by two open
namespaces; the unused `EulerSmoothLimit` open was removed. No mathematical
hypothesis or conclusion was weakened to address the error. The r3 build
(`tmp/compile_EnstrophyBounds_r3_20260915.log`) compiled the complete identity
successfully. Bounds reached four API/rewriting errors (ordered multiplication
names, pointwise word-path rewriting, and pointwise function subtraction);
these were corrected for r4. Final verification by the assigned Luna compiler:

- `lake build NSFormalization.Section4.C01.EnstrophyBounds` rebuilt both new
  modules successfully; `tmp/compile_EnstrophyBounds_r4_20260915.log` records
  `BUILD_EXIT_CODE=0`. There are no warnings in either new module.
- `lake env lean ../research/C01/axioms_enstrophy162.lean` compiled all three
  complete original-Spec consumers; `tmp/probe_axioms_enstrophy162_r4_20260915.log`
  records `PROBE_EXIT_CODE=0`.
- All three consumers and the five additional analytic exports audited there
  depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The independent source review's compilation condition is now satisfied; see
`REVIEW_ENSTROPHY_162.md`. These checks establish the three new original-field
proofs, not registration of a new contract or completion of the remaining H2
and Section 4 obligations. No Lean command was run by the proof author.
