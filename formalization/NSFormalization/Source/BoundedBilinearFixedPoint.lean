import Mathlib

/-!
# Generic bounded-bilinear contraction estimates

This file isolates the norm estimates used by quadratic Picard maps.  A
continuous bilinear map is represented as a continuous linear map into the
space of continuous linear maps.  No PDE-specific estimate is hidden here.
-/

noncomputable section

namespace NSFormalization.Source.BoundedBilinearFixedPoint

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The value of a bounded bilinear map, with its operator norm bound exposed. -/
theorem norm_bilinear_apply_le (B : E →L[𝕜] E →L[𝕜] F) (u v : E) :
    ‖B u v‖ ≤ ‖B‖ * ‖u‖ * ‖v‖ := by
  calc
    ‖B u v‖ ≤ ‖B u‖ * ‖v‖ := (B u).le_opNorm v
    _ ≤ (‖B‖ * ‖u‖) * ‖v‖ := by
      gcongr
      exact B.le_opNorm u
    _ = ‖B‖ * ‖u‖ * ‖v‖ := by ring

/-- Quadratic self-interaction is controlled by the bilinear operator norm. -/
theorem norm_bilinear_self_le (B : E →L[𝕜] E →L[𝕜] F) (u : E) :
    ‖B u u‖ ≤ ‖B‖ * ‖u‖ ^ 2 := by
  simpa [pow_two, mul_assoc] using norm_bilinear_apply_le B u u

/-- Polarization estimate for the difference of two quadratic values. -/
theorem norm_bilinear_self_sub_self_le (B : E →L[𝕜] E →L[𝕜] F)
    (u v : E) :
    ‖B u u - B v v‖ ≤ ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rw [show B u u - B v v = B (u - v) u + B v (u - v) by
    simp only [sub_eq_add_neg, map_add, map_neg, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply]
    module]
  calc
    ‖B (u - v) u + B v (u - v)‖ ≤
        ‖B (u - v) u‖ + ‖B v (u - v)‖ := norm_add_le _ _
    _ ≤ (‖B‖ * ‖u - v‖ * ‖u‖) +
        (‖B‖ * ‖v‖ * ‖u - v‖) := by
      gcongr
      · exact norm_bilinear_apply_le B (u - v) u
      · exact norm_bilinear_apply_le B v (u - v)
    _ = ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

/-- On a radius-`R` ball, the quadratic map is `2 ‖B‖ R`-Lipschitz. -/
theorem norm_bilinear_self_sub_self_le_of_norm_le
    (B : E →L[𝕜] E →L[𝕜] F) {R : ℝ} (hR : 0 ≤ R)
    {u v : E} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖B u u - B v v‖ ≤ 2 * ‖B‖ * R * ‖u - v‖ := by
  have h := norm_bilinear_self_sub_self_le B u v
  have hsum : ‖u‖ + ‖v‖ ≤ 2 * R := by linarith
  have hB : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg _
  have hd : 0 ≤ ‖u - v‖ := norm_nonneg _
  calc
    ‖B u u - B v v‖ ≤ ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := h
    _ ≤ ‖B‖ * (2 * R) * ‖u - v‖ := by gcongr
    _ = 2 * ‖B‖ * R * ‖u - v‖ := by ring

end NSFormalization.Source.BoundedBilinearFixedPoint
