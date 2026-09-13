import NSFormalization.Paper1.FiniteWeightedPairing

/-!
Zero-frequency invariance for the finite homogeneous Fourier pairing.

The multiplier `|2*pi*k|` vanishes at `k = 0`, so removing the zero mode
from a finite spectral cutoff does not change this pairing.  This is the
finite-cutoff form of the standard homogeneous Sobolev convention that
constants have zero seminorm (e.g. Bahouri--Chemin--Danchin,
*Fourier Analysis and Nonlinear Partial Differential Equations*, Def. 1.1).
-/
noncomputable section
namespace NSFormalization.Paper1
open scoped BigOperators ComplexConjugate

/-- The homogeneous weighted pairing is unchanged after deleting frequency 0. -/
theorem finiteWeightedPairing_erase_zero (c d : TorusFreq → ℂ) (S : Finset TorusFreq) :
    finiteWeightedPairing c d (S.erase 0) = finiteWeightedPairing c d S := by
  classical
  by_cases h0 : 0 ∈ S
  · unfold finiteWeightedPairing
    apply Finset.sum_subset (Finset.erase_subset 0 S)
    intro k hkS hkErase
    have hk0 : k = 0 := by
      by_contra hne
      exact hkErase (Finset.mem_erase.mpr ⟨hne, hkS⟩)
    subst k
    simp
  · simp [finiteWeightedPairing, h0]

/-- In particular, the zero singleton contributes nothing to the pairing. -/
theorem finiteWeightedPairing_singleton_zero (c d : TorusFreq → ℂ) :
    finiteWeightedPairing c d ({0} : Finset TorusFreq) = 0 := by
  simp [finiteWeightedPairing]

end NSFormalization.Paper1
