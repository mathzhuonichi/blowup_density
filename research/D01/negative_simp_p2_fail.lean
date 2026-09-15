/-
  Lane 129 (SIMP-D01-orderzero) — NEGATIVE tester file (must FAIL to compile).

  Each block restates one of the six main P2-chain exports with a single load-bearing hypothesis
  DROPPED, under `set_option autoImplicit false in` (so a hypothesis that appears in the statement
  type cannot be silently re-bound as an implicit — `logs/LESSONS.md` 2026-09-14, entry on
  autoImplicit false negatives), and offers the original proof route.  Every block MUST error.

  Two kinds of dependency are exhibited (labelled per block):
   • STRUCTURAL — the dropped hypothesis (or its data) appears in the *conclusion*, so the statement
     is not even well-formed without it (`unknown identifier`).  This is a genuine necessity, not a
     signature artefact.  (`add_drop_hw`, `pressureGradient_eq_drop_hf`.)
   • ROUTE — the hypothesis is consumed inside the proof; without it the established proof does not
     typecheck (`type mismatch`, missing argument).  A *full* falsification of these (a field whose
     order-0 datum is provably not transverse / not longitudinal; or the smooth solution with
     `∇p ∈ L² \ H¹` of `D01/Pressure.lean:62-66` for P2) needs a Fourier-transform computation or a
     non-`L²`/out-of-`F_R` field and is NOT formalized here — see `ATTEMPTS_SIMP.md`, honestly
     labelled "could only show: not provable without".  Non-vacuity that the dropped hypothesis is a
     genuine restriction is in `negative_simp_p2.lean` (the nonzero curl-free `∇bump`).

  Check:  cd verification && lake env lean ../research/D01/negative_simp_p2_fail.lean
  Expect: NONZERO exit, one error per block.
-/
import NSFormalization.Section4.D01.PressureJets

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (ClassicalSolutionR)
open NSFormalization.Section4.A03 (partialDeriv)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source.RealSobolev (FourierData)
open scoped ContDiff

namespace Lane129NegFail

set_option autoImplicit false in
/-- ROUTE. `orderZeroDatum_transverse_of_divergence_free` minus `hdiv`.  The general claim (every
smooth `L²` field is order-0 transverse) is false, but the proof-route dependency is what errors. -/
theorem transverse_drop_hdiv {z : Space → Space} (hz : MemLp z 2 volume)
    (hsmooth : ContDiff ℝ ∞ z) :
    ∀ᵐ ξ : Space ∂volume,
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * ((orderZeroDatum hz j : FourierData) ξ) = 0 :=
  by exact orderZeroDatum_transverse_of_divergence_free hz hsmooth

set_option autoImplicit false in
/-- ROUTE. `orderZeroDatum_longitudinal_of_curl_free` minus `hcurl`. -/
theorem longitudinal_drop_hcurl {z : Space → Space} (hz : MemLp z 2 volume)
    (hsmooth : ContDiff ℝ ∞ z) :
    ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * ((orderZeroDatum hz j : FourierData) ξ)
        = ((ξ j : ℝ) : ℂ) * ((orderZeroDatum hz i : FourierData) ξ) :=
  by exact orderZeroDatum_longitudinal_of_curl_free hz hsmooth

set_option autoImplicit false in
/-- ROUTE. `lerayComplement_zero_orderZeroDatum_eq_self` minus `hcurl`. -/
theorem leray_drop_hcurl {z : Space → Space} (hz : MemLp z 2 volume)
    (hsmooth : ContDiff ℝ ∞ z) :
    Leray.lerayComplement 0 (orderZeroDatum hz) = orderZeroDatum hz :=
  by exact Leray.lerayComplement_zero_orderZeroDatum_eq_self hz hsmooth

set_option autoImplicit false in
/-- STRUCTURAL. `orderZeroDatum_add` minus `hw`: the conclusion `orderZeroDatum (hz.add hw) = …
+ orderZeroDatum hw` names `hw`, so it is ill-formed without it. -/
theorem add_drop_hw {z w : Space → Space} (hz : MemLp z 2 volume) :
    orderZeroDatum (hz.add hw) = orderZeroDatum hz + orderZeroDatum hw :=
  by exact orderZeroDatum_add hz hw

set_option autoImplicit false in
/-- STRUCTURAL. `orderZeroDatum_pressureGradient_eq` minus `hf`: the RHS names
`smoothL2_momentumResidual_slice u hf ht`, so the statement itself needs `hf`. -/
theorem pressureGradient_eq_drop_hf {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    orderZeroDatum (memLp_pressureGradient_slice u ht)
      = Leray.lerayComplement 0
          (orderZeroDatum (smoothL2_momentumResidual_slice u hf ht).memLp) :=
  by exact orderZeroDatum_pressureGradient_eq u hf ht

-- `P2_drop_hf` (dropping `hf` from `pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`)
-- was DELETED after the lane-129 review (REVIEW_SIMP_P2.md finding 3).  Dropping `hf` leaves a
-- *complete, well-formed* statement (`hf` occurs nowhere in the conclusion), so the only error a
-- drop-one-arg check produced was `Unknown identifier 'hf'` inside the PROOF TERM — an empty check
-- (any undefined name yields it), the anti-pattern of LESSONS 2026-09-14.  `hf`'s necessity for P2
-- is genuine but is known only from the paper-level counterexample `D01/Pressure.lean:62-66` (a
-- smooth divergence-free `u` with `∇p ∈ L² \ H¹`, whose `f` is defined by the momentum equation and
-- is NOT in `F_R`), which is not formalized in a SIMP lane.  The STRUCTURAL block
-- `pressureGradient_eq_drop_hf` above already exhibits a genuine (statement-level) `hf`-dependence of
-- the order-0 identity `orderZeroDatum_pressureGradient_eq`.

end Lane129NegFail
