# Fourier calculus attempts, lane 305

## Source search and selected route

Read CLAUDE.md, NEXT_SESSION.md, PLAN.md, the first forty LESSONS lines,
T10/T12/T13 comparison records, canonical DatumBasics/Parseval/PhysicalBridge,
and Paper1 TorusCube. Explicit grep searches covered AddCircleMulti,
AddCircle, IntervalIntegral FTC/integration by parts, Constructions/Pi,
Paper1 Periodic*.lean and LocalizationBoundary. No missing-library claim
was needed: PeriodicFourierDerivative already proves cube integration by
parts and the derivative symbol. PeriodicHigherSobolev supplies all integer
energies; PeriodicSmoothSobolev supplies all real weighted orders;
PeriodicH2Embedding proves inverse-weight lattice summability using ZLattice;
PeriodicH2Uniform supplies actual C² absolute summability. These are reused.

## Resolved errors (verbatim excerpts)

1. Direct rewriting through the wrapper:
   `Tactic rewrite failed: Did not find an occurrence of the pattern
   periodicFourierCoeff (fun x => (fderiv ℝ (spatialPartial i f) x)
   (coordinateVector ?j)) ?k`.
   Fix: use the Paper1 spatialPartial theorem before rewriting the wrappers.
2. Integral measure inference:
   `'change' tactic failed, pattern ... is not definitionally equal to target`.
   Fix: specify `∂periodicTorusMeasure` and the integral inequality's `μ`.
3. Assuming the two weight spellings were definitional:
   `(deterministic) timeout at whnf, maximum number of heartbeats (200000)
   has been reached`.
   Fix: prove periodicFrequencyWeight_eq_paper1 explicitly by norm algebra.
   No heartbeat increase was used.
4. Character norm simplification left
   `⊢ ∏ x, ‖↑(k x • y x).toCircle‖ = 1`.
   Fix: use the exact Circle.norm_coe simplification, not unrestricted simp.
5. Premature cast simplification left real rather than natural exponent:
   `has type Summable fun k => periodicFrequencyWeight k ^ ((2 : ℝ) * ↑N)
   * ‖periodicFourierCoeff f k‖ ^ 2`.
   Fix: simplify only Real.rpow_natCast before distributing casts.
6. Component continuity inference:
   `Application type mismatch ... ContDiff ℝ ∞ (⇑?m.63 ∘ v)`.
   Fix: explicitly set `(𝕜 := ℝ)` on EuclideanSpace.proj.
7. Real partial coercions:
   `f has type Space → ℝ but is expected to have type Space → ℂ`.
   Fix: annotate the inner partial value as ℝ before coercing to ℂ.
8. Component periodicity rewriting:
   `Tactic rewrite failed: Did not find an occurrence of the pattern
   v (x + coordinateVector j)`.
   Fix: dsimp the composed function before rewriting periodicity.
9. Single-mode probe: `Type mismatch: After simplification` between
   UnitPeriods and IsPeriodicSpatial conjunctions.
   Fix: prove the exponential function equals periodicCharacter by function extensionality, then rewrite the whole function. Unfolding predicates alone did not rewrite the unapplied function under ContDiff.

## Residual scope

No incomplete proof declarations are retained. Scalar conclusions compile.
The alternative all-order-energy decay route is documented in REPORT_305.
Vector consumers still need packaging beyond the exported component
corollaries (e.g. a vector physical Laplacian Parseval equality); this lane
does not claim those downstream T12 theorems. See REPORT_305 for precise scope.
