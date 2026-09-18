import NSFormalization.Section3.T15.Placement

namespace NSFormalization.Section3.T15

open Set NavierStokes.ProblemStatement

-- Reviewer mutation (lane 376): double the spatial scale in the conclusion.
-- Fed the genuine raw packet clauses, the honest U2 lemma
-- `scaledVelocity_tsupp_subset` produces the `x₀ + ε • K_*` image, never the
-- `x₀ + (2ε) • K_*` one, so this must FAIL to typecheck (`lake env lean`
-- exits 1 with a set/image type mismatch). It is kept as a guard that the
-- lemma does not overreach on the scale.
example {u : VelocityField} {x₀ : Space} {T ε : ℝ} {carrier Kstar : Set Space}
    (hε : 0 < ε) (hcarrier_compact : IsCompact carrier)
    (hvel : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar) {t : ℝ} (ht : t < T) :
    tsupport (fun x => scaledVelocity u x₀ T ε (t, x)) ⊆
      (fun y => x₀ + (2 * ε) • y) '' Kstar :=
  scaledVelocity_tsupp_subset hε hcarrier_compact hvel hcarrier_subset ht

end NSFormalization.Section3.T15
