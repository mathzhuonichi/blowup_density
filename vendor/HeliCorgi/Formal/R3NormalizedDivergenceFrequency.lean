import Formal.R3NormalizedDivergenceTerm
import Formal.R3DivergencePointwise

namespace MNS2

open MeasureTheory Filter

noncomputable section

def r3NormalizedDivergenceFrequencyAux :
    R3L2Velocity →L[ℂ] R3L2ScalarAux :=
  r3NormalizedDivergenceTermAux 0 +
    r3NormalizedDivergenceTermAux 1 + r3NormalizedDivergenceTermAux 2

theorem r3NormalizedDivergenceFrequencyAux_ae (f : R3L2Velocity) :
    r3NormalizedDivergenceFrequencyAux f =ᵐ[volume]
      fun ξ => r3NormalizedDivergencePointwise ξ (f ξ) := by
  change
    ((r3NormalizedDivergenceTermAux 0 f + r3NormalizedDivergenceTermAux 1 f +
      r3NormalizedDivergenceTermAux 2 f : R3L2ScalarAux) : R3 → ℂ) =ᵐ[volume]
      fun ξ => r3NormalizedDivergencePointwise ξ (f ξ)
  filter_upwards
    [Lp.coeFn_add
      (r3NormalizedDivergenceTermAux 0 f + r3NormalizedDivergenceTermAux 1 f)
      (r3NormalizedDivergenceTermAux 2 f),
     Lp.coeFn_add (r3NormalizedDivergenceTermAux 0 f) (r3NormalizedDivergenceTermAux 1 f),
     r3NormalizedDivergenceTermAux_ae 0 f,
     r3NormalizedDivergenceTermAux_ae 1 f,
     r3NormalizedDivergenceTermAux_ae 2 f]
    with ξ hsum hsum01 h0 h1 h2
  simp only [hsum, hsum01, Pi.add_apply, h0, h1, h2]
  rfl

end

end MNS2
