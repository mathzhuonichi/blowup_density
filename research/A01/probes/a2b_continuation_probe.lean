import NSFormalization.Source.OrdinaryForcedLocal
import Euler.BoundedMildContinuation

/-!
Probe for A01 unit A2b-a′ (lane 122 review, reviewer finding F5, verbatim from
`research/A01/REVIEW_A3.md` §3 with the elided `hF`/`_` filled in).

It confirms that the OpenAI/local forced Picard layer DOES have a
continuation-from-an-a-priori-bound theorem on exactly `exists_local`'s carrier
and `Coefficients` bundle: `EulerBoundedMildContinuation.exists_global_mild_of_bound`
composes with `ForcedCylinderLocal.coefficients 1 hq (sobolevPath F hF q)` — the
same bundle `Source/OrdinaryForcedLocal.exists_local` feeds to `quadraticDuhamel`
— by a one-line proof term.  So A2b-a is S–M on this spine, not L, and needs no
HeliCorgi/`FormalPatched` continuation.

Author of the statement + proof: the lane-122 reviewer (`REVIEW_A3.md`).
Check: `cd verification && lake env lean ../research/A01/probes/a2b_continuation_probe.lean`.
-/

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem probe_forced_global_mild_of_bound {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
        (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R) :
    ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
      ‖u‖ ≤ R ∧
      u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
      ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t :=
  EulerBoundedMildContinuation.exists_global_mild_of_bound 1 q ν hν S hS R hR _ hu₀
    (coefficients 1 hq (sobolevPath F hF q)) hbound

#print axioms probe_forced_global_mild_of_bound
