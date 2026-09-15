import NSFormalization.Section4.R43.CriticalPairing

open Set NavierStokes.ProblemStatement

namespace NSFormalization.Section4.R43

open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField ClassicalSolutionR MemForceR)

/- The second conjunct of `rcritical1_of_trilinear` feeds the R43 wrapper with
no adapter: the four scalar functions are instantiated definitionally. -/
example {T ν C₀ c : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {w : ClassicalSolutionR ν a f T} (hf : MemForceR f)
    (hcrit : CriticalDatumPath w hf)
    (htri : CriticalTrilinearEstimate (C₀ := C₀) hcrit)
    (hC₀ : 0 < C₀) (hν : 0 < ν) (hc0 : 0 ≤ c) (hclt : c < 1 / (2 * C₀))
    (hy : Continuous (criticalNormAt w.velocity))
    (hy0 : criticalNormAt w.velocity 0 = 0)
    (hynonneg : ∀ t ∈ Icc 0 T, 0 ≤ criticalNormAt w.velocity t)
    {N : ℝ → ℝ} (hN : ContinuousOn N (Icc 0 T)) (hN0 : N 0 = 0)
    (hNbound : ∀ t ∈ Icc 0 T, N t ≤ c * ν)
    (hb : ∀ t ∈ Ioo 0 T, 0 ≤ criticalForceAt f t)
    (hdN : ∀ t ∈ Ioo 0 T, HasDerivAt N (criticalForceAt f t) t) :
    ∀ t ∈ Icc 0 T, criticalNormAt w.velocity t ≤ c * ν := by
  have hR := rcritical1_of_trilinear hf hcrit htri
  exact criticalNormBound_radius hC₀ hν hc0 hclt hy hy0 hynonneg hN hN0 hNbound hb
    hR.1 hdN hR.2

/- The same conjunct feeds the underlying domain-agnostic consumer verbatim. -/
example {T ν C K ρ : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {w : ClassicalSolutionR ν a f T} (hf : MemForceR f)
    (hcrit : CriticalDatumPath w hf)
    (htri : CriticalTrilinearEstimate (C₀ := C) hcrit)
    (hν : 0 ≤ ν) (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρK : ρ < K)
    (hK : C * K ≤ ν / 2)
    (hy : Continuous (criticalNormAt w.velocity))
    (hy0 : criticalNormAt w.velocity 0 = 0)
    (hynonneg : ∀ t ∈ Icc 0 T, 0 ≤ criticalNormAt w.velocity t)
    {N : ℝ → ℝ} (hN : ContinuousOn N (Icc 0 T)) (hN0 : N 0 = 0)
    (hNbound : ∀ t ∈ Icc 0 T, N t ≤ ρ)
    (hb : ∀ t ∈ Ioo 0 T, 0 ≤ criticalForceAt f t)
    (hdN : ∀ t ∈ Ioo 0 T, HasDerivAt N (criticalForceAt f t) t) :
    ∀ t ∈ Icc 0 T, criticalNormAt w.velocity t ≤ ρ := by
  have hR := rcritical1_of_trilinear hf hcrit htri
  exact NSFormalization.Paper1.critical_norm_bound hν hC hρ0 hρK hK hy hy0 hynonneg
    hN hN0 hNbound hb hR.1 hdN hR.2

end NSFormalization.Section4.R43
