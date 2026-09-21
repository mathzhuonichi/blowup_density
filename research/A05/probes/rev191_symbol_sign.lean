import NSFormalization.Section4.A05.RieszShift

/-!
Reviewer mutation probe for lane 191.

The main U8 symbol identity is deliberately mutated by flipping its sign.
The original proof must not establish this statement.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.A05

example (j i : Fin 3) (Z : RealVectorSobolev (3 / 2)) :
    ((((derivativeHalfDatum j Z) i : RealSobolevHilbert (1 / 2)) : FourierData) :
        Space → ℂ) =ᵐ[volume]
      fun ξ => -(NSFormalization.Section4.R43.rieszCoordinateSymbol j ξ) *
        (Z i : FourierData) ξ := by
  exact derivativeHalfDatum_symbol j i Z
