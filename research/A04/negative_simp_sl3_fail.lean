import NSFormalization.Section4.A04.LaplacianAssembly
import NSFormalization.Section4.D01.SmoothDatum

/-!
# Lane 115 (SIMP-A04, SL3 cluster) — signature/drift checks + controls — THIS FILE MUST FAIL

`lake env lean` on this file **exits 1** with one elaboration error per block.  It has two kinds
of must-fail blocks, neither of which is load-bearing evidence on its own:

## Signature/drift checks (N1–N7)  — NOT load-bearing evidence
Each drops one hypothesis (or weakens the conclusion) and tries to discharge the weakened
statement by *applying the original theorem with the dropped argument*.  Every such application is
ill-typed: N1–N4 error with `Unknown identifier` (a name that is no longer assumed), N5–N7 with a
`Type mismatch` (the real theorem's conclusion still carries the `^2` / the leading minus).  **This
only witnesses that the exported signature still lists the argument / still has that conclusion —
it says nothing about whether the weaker statement is provable by other means** (`REVIEW_SIMP_SL3.md`
Findings 3–4).  Blocks are `set_option autoImplicit false in` so a block that *did* elaborate would
be a real finding (a removable hypothesis on a frozen statement) rather than an `autoImplicit`
re-binding (the 077 trap).

## Controls (C1–C2) — must NOT be provable
The two reviewer controls (`/tmp/rev115/p3_control.lean`): the collapse *conclusions* of
`negative_simp_sl3.lean` (`datum = 0`, `angularDirectionalDerivative s a f = 0`), stated WITHOUT the
weakened hypothesis `H`.  `simp` / `aesop` cannot prove them (`simp made no progress`; `aesop failed
after exhaustive search`) — which is exactly why the collapse proofs in `negative_simp_sl3.lean`
genuinely *use* `H`.  (Run at the default heartbeat budget; they fail cleanly, no `maxHeartbeats`.)

## The real evidence is elsewhere
The genuine load-bearing evidence lives in the companion file `research/A04/negative_simp_sl3.lean`
(which must compile SILENTLY): refutation-by-collapse theorems proving each weakened statement
entails something manifestly false, plus fidelity examples and non-degenerate non-vacuity witnesses.

RUN: `lake env lean` this file; expect exit 1, one elaboration error per N-block and per control.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A04
open NSFormalization.Paper3
open NSFormalization.Section4.D01 (IsSobolevDatum smoothAngularDatum)
open NSFormalization.Section4.A03 (lift gradientSobolevENorm)
open NSFormalization.Section4.A05 (SmoothL2)
open NSFormalization.Section4.A02 (SpaceTimeField)
open EulerLpTranslation (SmoothL2Field)
open scoped InnerProductSpace

/-! ## Signature/drift checks (N1–N7) -/

-- N1: `gradientSobolevENorm_toReal_sq_eq_datum_sum` with `hA` dropped.
set_option autoImplicit false in
example {Z : SmoothL2Field Space} (m : ℕ) {A : RealVectorSobolev ((m : ℝ) + 1)} :
    (gradientSobolevENorm (m : ℝ) Z.field).toReal ^ 2 =
      ∑ j : Fin 3, ‖((WithLp.toLp 2 fun i =>
          angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j) (A i)) :
          RealVectorSobolev (m : ℝ))‖ ^ 2 :=
  gradientSobolevENorm_toReal_sq_eq_datum_sum m hA

-- N2: `inner_datum_laplacian` (the pairing identity) with `hA` dropped.
set_option autoImplicit false in
example (m : ℕ) {Z : SmoothL2Field Space}
    {G : RealVectorSobolev (m : ℝ)} {A' : RealVectorSobolev ((m : ℝ) + 1)}
    {A : RealVectorSobolev ((m : ℝ) + 2)}
    (hG : IsSobolevDatum (m : ℝ) Z.field G) (hA' : IsSobolevDatum ((m : ℝ) + 1) Z.field A') :
    (inner ℝ G (laplacianDatum m A) : ℝ) = - ∑ j : Fin 3, ‖derivDatumStep m j A'‖ ^ 2 :=
  inner_datum_laplacian m hG hA' hA

-- N3: `inner_datum_laplacian_le'` (the consumer-shaped `hlap`) with `hL` dropped.
set_option autoImplicit false in
example (m : ℕ) {u : SpaceTimeField} {t : ℝ}
    (hsl : SmoothL2 (fun x => u (t, x)))
    {G : RealVectorSobolev (m : ℝ)} {A' : RealVectorSobolev ((m : ℝ) + 1)}
    {A : RealVectorSobolev ((m : ℝ) + 2)} {L : RealVectorSobolev (m : ℝ)}
    (hG : IsSobolevDatum (m : ℝ) (fun x => u (t, x)) G)
    (hA' : IsSobolevDatum ((m : ℝ) + 1) (fun x => u (t, x)) A')
    (hA : IsSobolevDatum ((m : ℝ) + 2) (fun x => u (t, x)) A) :
    (inner ℝ G L : ℝ) ≤ - gradientSobolevNormAt (m : ℝ) u t ^ 2 :=
  inner_datum_laplacian_le' m hsl hG hA' hA hL

-- N4: `isSobolevDatum_laplacian` (Part 1) with `hA` dropped.
set_option autoImplicit false in
example {Z : SmoothL2Field Space} (m : ℕ) {A : RealVectorSobolev ((m : ℝ) + 2)} :
    IsSobolevDatum (m : ℝ) (fun x => spatialLaplacian (lift Z.field) 0 x) (laplacianDatum m A) :=
  isSobolevDatum_laplacian m hA

-- N5: `real_inner_lowering_pairing` with the conclusion weakened (the `^ 2` dropped).
set_option autoImplicit false in
example (s r t : ℝ) (hrs : r ≤ s) (hts : t ≤ s)
    (hms : (r + t) / 2 ≤ s) (w : Lp ℂ 2 (volume : Measure Space)) :
    (inner ℝ (angularOrderLowering s r hrs w) (angularOrderLowering s t hts w) : ℝ) =
      ‖angularOrderLowering s ((r + t) / 2) hms w‖ :=
  real_inner_lowering_pairing s r t hrs hts hms w

-- N6: `real_inner_angularDirectionalDerivative` with the leading minus dropped.
set_option autoImplicit false in
example (s : ℝ) (a : Space) (f g : Lp ℂ 2 (volume : Measure Space)) :
    (inner ℝ f (angularDirectionalDerivative s a g) : ℝ) =
      (inner ℝ (angularDirectionalDerivative s a f) g : ℝ) :=
  real_inner_angularDirectionalDerivative s a f g

-- N7: `inner_angularDirectionalDerivative_right` (ℂ) with the leading minus dropped.
set_option autoImplicit false in
example (s : ℝ) (a : Space) (f g : Lp ℂ 2 (volume : Measure Space)) :
    ⟪f, angularDirectionalDerivative s a g⟫_ℂ = ⟪angularDirectionalDerivative s a f, g⟫_ℂ :=
  inner_angularDirectionalDerivative_right s a f g

/-! ## Controls (C1–C2): the collapse conclusions are NOT provable without the weakened hypothesis -/

-- C1: `datum_zero_of_weakenedNoHL`'s conclusion without `H : WeakenedNoHL` — `simp` cannot do it.
set_option autoImplicit false in
example (Z : SmoothL2Field Space) (m : ℕ) :
    smoothAngularDatum (m + 2) (m : ℝ) (by push_cast; linarith) Z = 0 := by
  simp

-- C2: `deriv_eq_zero_of_weakenedPairing`'s conclusion without `H : WeakenedPairing` — `aesop` fails.
set_option autoImplicit false in
example (s : ℝ) (a : Space) (f : Lp ℂ 2 (volume : Measure Space)) :
    angularDirectionalDerivative s a f = 0 := by
  aesop

end
