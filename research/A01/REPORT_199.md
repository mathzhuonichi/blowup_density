# Lane 199 report — partial result, general-data closure still open

## 1. Theorems, exact statements, constants

Branch: `erenup/199-A01-envelope`. Before the fix, the lane commit was rebased
onto `origin/erenup/integration` at
`86d5bf867d5a33a002a1a9ab9140fced8306cde7`. No push was performed.

The module proves the exact signed regularized energy identity and the scalar
ODE envelope construction. It does **not** prove the requested general-data
`forcingFamilyBound_of_cylinder`, `envelopeConversion_of_cylinder`,
`finiteMildEnergy`, or unconditional `mildGronwall'` / `hb_of_base''`.
The exported downstream theorems explicitly carry the comparison hypothesis
and are named `_of_rootComparison`.

For a genuine second-order cylinder jet J,

    inner(f, jetLaplacian J) = -∑ i : Fin 4, ‖J.word(i)‖².

`identity_jetLaplacian_pairing` proves this using the vendor second-derivative
identity. `full_word_energy_hasDerivAt` and
`regularized_full_energy_hasDerivAt` consequently give, for the actual full
regularized word family e and actual regularized mild source f,

    (∑ W, ‖e_W‖²)′ = 2∑ W, inner(e_W,f_W)
                       - 2ν∑ W,∑ i, ‖∂ᵢe_W‖².

The exact specialization to the given mild competitor is:

```lean
theorem regularized_full_energy_hasDerivAt {q : ℕ} (n : ℕ)
    {ν S T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (u₀ : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS D u₀ u t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    let v := fun (W : SobolevWord (q+1)) r => extendPath T hT
      (EulerRegularizedWordEquation.regularizedWordPath 1
        (Nat.le_of_lt_succ W.1.isLt) n W.2 T u) r
    let f := fun W : SobolevWord (q+1) => extendPath T hT
      (EulerRegularizedWordTime.sourceWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T
        (sourcePath (D.comp (timeInclusion hTS)) u)) t
    HasDerivAt (fun s => familyEnergy (ContinuousLinearMap.id ℝ (LiftL2 1))
      (fun W => value 1 (v W s)))
      (2 * ∑ W, ⟪value 1 (v W t), f W⟫_ℝ -
        2 * ν * ∑ W, ∑ i : Fin 4, ‖(toJet 1 (v W t)).word (fun _ : Fin 1 => i)‖^2) t
```

The scalar function is explicit:

```lean
def energyComparison (α : ℝ → ℝ) (b c t : ℝ) : ℝ :=
  Real.exp (∫ s in (0 : ℝ)..t, α s) *
    (c + b * ∫ s in (0 : ℝ)..t, Real.exp (-(∫ r in (0 : ℝ)..s, α r)))
```

`energyComparison_hasDerivAt` proves y′=αy+b for continuous α at every real
time, `energyComparison_zero` proves y(0)=c, and
`energyComparison_unique` proves that any global pointwise `HasDerivAt`
solution with y(0)=c equals this explicit function. Its integrating-factor
proof shows `exp(-∫₀ᵗ α) * (y-energyComparison)` has derivative zero.
Thus the envelope is characterized, not merely exhibited.
`energyComparison_nonneg` proves y≥0 for t,b,c≥0. With

    k(t) = A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) u(t)‖),
    α(t) = k(t)²/(4ν),
    b = E * ‖sobolevPath F hF (q+1)‖,
    c = E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖,

`comparison_envelope` constructs x=y², d=2yy′, g=ky/(2ν). It proves
½d+νg²=k√x g+b√x **as equality**, together with continuity, nonnegativity,
the initial bound and every interior derivative. Thus the coefficient in
the downstream Grönwall conclusion is exactly A²/(4ν), with 16²=256.

No general-data A is provided. E and A remain parameters; the pre-existing
explicit norm constant is E(q)=sqrt(card(SobolevWord(q+1))). The zero-data
checks use that E and A=1; they do not assert this A works for general data.

The exact conditional exports include:

```lean
theorem finiteMildEnergy_of_rootComparison {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ} (hE : 0 ≤ E)
    (hcomparison : CylinderRootComparison hq hν a F hF E A) :
    FiniteMildEnergy hq hν a ha F hF E A

theorem envelopeConversion_of_rootComparison {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ} (hE : 0 ≤ E)
    (hcomparison : CylinderRootComparison hq hν a F hF E A) :
    EnvelopeConversion hq hν a F hF E A

theorem mildGronwall_of_rootComparison {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ} (hE : 0 ≤ E)
    (hcomparison : CylinderRootComparison hq hν a F hF E A) :
    MildGronwall hq hν a ha F hF E (A^2/(4*ν))

theorem hb_of_base_of_rootComparison {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E A : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    (hcomparison : ∀ q (hq : 6 ≤ q), CylinderRootComparison hq hν a F hF (E q) (A q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF
      (aprioriRadius a F hF R₆ E (fun q => A q^2/(4*ν)) q)
```

## 2. Files and conformance

- New `formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean`:
  18 declarations, no heartbeat overrides, existing Lean modules untouched.
- New `research/A01/axioms_envelope.lean`: all 18 module declarations and
  four helper proofs print exactly `[propext, Classical.choice, Quot.sound]`.
  Zero data is checked for every competitor by uniqueness, and both new
  conditional finite-energy/conversion theorems are actually applied.
  Nonstationary scalar examples and two negative arithmetic checks compile.
- New `research/A01/ATTEMPTS_ENVELOPE.md`: analytic limits, negative routes,
  satisfiability and resolved compiler diagnostics.
- Updated the explicitly requested A3-M2 sub-rows in `research/A01/A3_SPLIT.md`.
- This new `research/A01/REPORT_199.md` is the handoff record. Other existing
  records and modules were left unchanged under the new-files restriction.

## 3. Gaps, exact residual, and error text

ONE named analytic predicate is used by the delivered finite-energy chain:

```lean
def CylinderRootComparison {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ t, energyRootPath u t ≤
      energyComparison (fun s => (cylinderEnvelopeDriver hq hT A u s)^2/(4*ν))
        (E * ‖sobolevPath F hF (q+1)‖)
        (E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖) t
```

This fixes the scalar function explicitly and asks only for root domination.
It is not proved for general nonzero mild solutions. In particular, the
physical/cylinder word and tensor pairing bridges, the finite tame estimate
on the actual carrier, and the passage of the signed regularized inequality
to its comparison limit remain unfinished. The module does not disguise
these as merely scalar algebra. No all-order constructor or
ClassicalSolutionR-level energy result is applied on the mild path.

The original `ForcingFamilyBound` independently remains open, with its
statement unchanged in MildEnergyPremises.lean. It controls root times a
nonnegative forcing FAMILY NORM, not just a signed nonlinear pairing.
Its source/pressure cancellation and quantitative commutator family estimate
are not established here. `ForcingFamilyBound` is not a premise of the new
conditional chain: `CylinderRootComparison` implies `FiniteMildEnergy`
directly. It is nevertheless the internal estimate needed in a proof of
`CylinderRootComparison`, where the signed regularized identity must be
passed to the root comparison. This lane proves neither general-data target;
lanes 200 and 201 now own those obligations.

There is no unresolved Lean error. Observed and resolved diagnostics include:

```
Invalid field `exp`: The environment does not contain `Continuous.exp`
Type mismatch: After simplification, term HasDerivAt.pow (hyd t ht) 2 ...
Application type mismatch: The argument J has type
SpatialJet 1 standardDirection 2 f
but is expected to have type
SpatialJet 1 EulerCylinderSobolev.standardDirection 2 ...
linarith failed to find a contradiction
```

Resolutions: explicit Real.continuous_exp composition; conversion between real
module presentations; opening the genuine cylinder-direction namespace;
and multiplying exp(P)exp(-P)=1 by b with linear_combination. Details are in
ATTEMPTS_ENVELOPE.md.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`, ran lake from
`verification/`, and set `LEAN_NUM_THREADS=6`.

```
lake build NSFormalization.Section4.A01.MildEnergyEnvelope
lake env lean ../formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean
lake env lean ../research/A01/axioms_envelope.lean
# reviewer probes (positive probes pass; mutation/target probes fail as intended)
make check
make test
git diff --check
```

All positive gates exited 0. The direct module check produced **0 bytes**:
the module itself is silent. `lake build` replays pre-existing dependency
warnings, but the new module emits none. The conformance run reports 22
declarations with exactly the three required axioms and no errors/warnings.
`make check` and the registered test closure passed. The reviewer algebra
probe passes, while the coefficient mutation and missing-target probes fail
as intended. These infrastructure checks are not a proof of the still-open
cylinder comparison or forcing-family estimate.

The attributed change report is `git diff --stat
origin/erenup/integration...HEAD`, i.e. the three-dot lane diff: nine files,
one formalization module plus eight lane/review records, with 1570 insertions
and two deletions. A two-dot diff is not used because integration-side branch
movement would contaminate lane attribution.

Local gate logs are in gitignored `tmp/envelope-{build,direct,axioms,check,test}.log`.
