import NSFormalization.Section4.D01.OrderZeroDatum
import NSFormalization.Section4.D01.ForceClass
import NSFormalization.Section4.D01.LerayDatum

/-!
# Order-0 datum algebra (unit D01 / P2 sub-lemma SL8 preparation)

`research/D01/P2_SPLIT.md` sub-lemma **SL7b/SL8**, and `research/D01/REVIEW_ORDER_ZERO.md` §6.2–6.3.
`Section4/D01/OrderZeroDatum.lean` exposes `orderZeroDatum hz : RealVectorSobolev 0`, the order-0
angular Sobolev datum of a bare square-integrable field (`isSobolevDatum_orderZeroDatum`), but says
nothing about how it interacts with the vector-space operations on the field.  The eq:Rpressure
assembly needs exactly that: the momentum identity `∂ₜu = h − ∇p` (with `h = f − (u·∇)u + νΔu`)
manifests at order 0 as a *subtraction* of order-0 data, and the Leray complement `(I−P)` acting on
those data must respect the subtraction.

This module supplies the missing algebra:

* `isSobolevDatum_sub` — the datum of a difference is the difference of the data, the exact
  subtraction partner of `ForceClass.isSobolevDatum_add` (identical proof, `map_sub` /
  `integral_sub` / `PiLp.sub_apply` for `map_add` / `integral_add` / `PiLp.add_apply`), gated by
  the same `SchwartzPairable` side condition.
* `orderZeroDatum_add`, `orderZeroDatum_sub` — additivity and subtractivity of `orderZeroDatum`
  itself.  Both go through datum **uniqueness** (`ForceClass.isSobolevDatum_unique`,
  `angularRealization_injective`): each side is an order-0 datum of the same physical field, so they
  coincide.  The `SchwartzPairable` hypotheses `isSobolevDatum_add`/`_sub` demand are free from the
  bare `MemLp` hypothesis via `schwartzPairable_of_memLp` fed with `OrderZeroDatum.memLp_component`
  — no continuity assumption is needed (recorded route, `research/D01/ATTEMPTS_SL8_PREP.md`).
* `lerayComplement_orderZeroDatum_add`, `lerayComplement_orderZeroDatum_sub` — the datum-carrier
  Leray complement `Leray.lerayComplement 0` is a `→L[ℝ]` (`Section4/D01/LerayDatum.lean`), so it is
  additive/subtractive by `map_add` / `map_sub`; combined with the two facts above this is the
  order-0 shadow of `(I−P)(datum⁰ h) = datum⁰(∂ₜu) + (I−P)(datum⁰ ∇p)` that SL8 consumes.

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_sl8_prep.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev

variable {s : ℝ} {z w : Space → Space}

/-- **The datum of a difference is the difference of the data.**  The subtraction partner of
`ForceClass.isSobolevDatum_add`: `angularRealization` is a continuous linear map, so the
distributional side is subtractive outright, and the physical side is a Bochner integral that
splits over a difference exactly when both pairings are integrable — the `SchwartzPairable`
hypothesis. -/
theorem isSobolevDatum_sub {A B : RealVectorSobolev s}
    (hz : SchwartzPairable z) (hw : SchwartzPairable w)
    (hA : IsSobolevDatum s z A) (hB : IsSobolevDatum s w B) :
    IsSobolevDatum s (z - w) (A - B) := by
  intro i ψ
  have hcoe : ((((A - B) i : RealSobolevHilbert s)) : FourierData)
      = ((A i : RealSobolevHilbert s) : FourierData)
        - ((B i : RealSobolevHilbert s) : FourierData) := rfl
  rw [hcoe, map_sub]
  show angularRealization s ((A i : FourierData)) ψ
      - angularRealization s ((B i : FourierData)) ψ = _
  rw [hA i ψ, hB i ψ]
  have hsplit : (fun x : Space => ψ x * (((z - w) x i : ℝ) : ℂ))
      = fun x : Space => ψ x * ((z x i : ℝ) : ℂ) - ψ x * ((w x i : ℝ) : ℂ) := by
    funext x
    show ψ x * (((z x - w x) i : ℝ) : ℂ) = _
    rw [PiLp.sub_apply]
    push_cast
    ring
  rw [hsplit, integral_sub (hz i ψ) (hw i ψ)]

/-- **`orderZeroDatum` is additive.**  Both `orderZeroDatum (hz.add hw)` and
`orderZeroDatum hz + orderZeroDatum hw` are order-0 data of the same field `z + w`
(`isSobolevDatum_orderZeroDatum`, `isSobolevDatum_add`), hence equal by uniqueness. -/
theorem orderZeroDatum_add (hz : MemLp z 2 volume) (hw : MemLp w 2 volume) :
    orderZeroDatum (hz.add hw) = orderZeroDatum hz + orderZeroDatum hw :=
  isSobolevDatum_unique (isSobolevDatum_orderZeroDatum (hz.add hw))
    (isSobolevDatum_add
      (schwartzPairable_of_memLp (fun i => memLp_component hz i))
      (schwartzPairable_of_memLp (fun i => memLp_component hw i))
      (isSobolevDatum_orderZeroDatum hz) (isSobolevDatum_orderZeroDatum hw))

/-- **`orderZeroDatum` is subtractive.**  Both `orderZeroDatum (hz.sub hw)` and
`orderZeroDatum hz - orderZeroDatum hw` are order-0 data of the same field `z - w`
(`isSobolevDatum_orderZeroDatum`, `isSobolevDatum_sub`), hence equal by uniqueness.  This is the
`∂ₜu = h − ∇p` shape at order 0. -/
theorem orderZeroDatum_sub (hz : MemLp z 2 volume) (hw : MemLp w 2 volume) :
    orderZeroDatum (hz.sub hw) = orderZeroDatum hz - orderZeroDatum hw :=
  isSobolevDatum_unique (isSobolevDatum_orderZeroDatum (hz.sub hw))
    (isSobolevDatum_sub
      (schwartzPairable_of_memLp (fun i => memLp_component hz i))
      (schwartzPairable_of_memLp (fun i => memLp_component hw i))
      (isSobolevDatum_orderZeroDatum hz) (isSobolevDatum_orderZeroDatum hw))

/-- The datum-carrier Leray complement at order 0 commutes with the sum of order-0 data
(`Leray.lerayComplement 0` is a `→L[ℝ]`, so `map_add`; then `orderZeroDatum_add`). -/
theorem lerayComplement_orderZeroDatum_add (hz : MemLp z 2 volume) (hw : MemLp w 2 volume) :
    Leray.lerayComplement 0 (orderZeroDatum (hz.add hw))
      = Leray.lerayComplement 0 (orderZeroDatum hz)
        + Leray.lerayComplement 0 (orderZeroDatum hw) := by
  rw [orderZeroDatum_add, map_add]

/-- The datum-carrier Leray complement at order 0 commutes with the difference of order-0 data
(`Leray.lerayComplement 0` is a `→L[ℝ]`, so `map_sub`; then `orderZeroDatum_sub`).  This is the
order-0 linearity SL8 uses to split `(I−P)(datum⁰ h)` along `h = ∂ₜu + ∇p`. -/
theorem lerayComplement_orderZeroDatum_sub (hz : MemLp z 2 volume) (hw : MemLp w 2 volume) :
    Leray.lerayComplement 0 (orderZeroDatum (hz.sub hw))
      = Leray.lerayComplement 0 (orderZeroDatum hz)
        - Leray.lerayComplement 0 (orderZeroDatum hw) := by
  rw [orderZeroDatum_sub, map_sub]

end NSFormalization.Section4.D01
