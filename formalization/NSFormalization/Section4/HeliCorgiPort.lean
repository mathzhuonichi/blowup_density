import Formal.R3EndpointSafeProjectedLocalExistence
import Formal.R3NavierStokesEquation
import Formal.R3HelmholtzPressure

/-!
# Smoke module for the in-place HeliCorgi port (task U05, step 1)

`formalization/lakefile.toml` declares a `Formal` library whose `srcDir` is
`../vendor/HeliCorgi`, so the 84 vendored modules that compile unchanged under this
repository's pin (Lean 4.34.0-rc2, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`)
are built in place, with `vendor/HeliCorgi` left byte-identical.

This module exists so that the port is actually exercised by CI: a lakefile-only change
compiles nothing, whereas `experiments/build_changed_lean.py` compiles this file — and
therefore the whole 84-module closure — whenever it changes.

It adds no mathematics.  Each `example` below is a type-checked reference to an upstream
declaration; nothing here is a contract, a binding or an acceptance test, and none of it
certifies a manuscript theorem.  See `research/U05/REPORT.md` (probe),
`research/U05/REVIEW.md` (review) and `research/U05/PORT.md` (port record).

The four modules of the continuation branch do **not** compile at this pin; they live as
patched copies in the `FormalPatched` library (`formalization/FormalPatched/`).
-/

namespace NSFormalization.Section4.HeliCorgiPort

/-- Local existence with closed-ball uniqueness for the R³ endpoint-safe projected mild
equation (`Formal.R3EndpointSafeProjectedLocalExistence`). -/
example := @MNS2.r3EndpointSafeProjected_exists_localMildSolution

/-- The certified local trajectory satisfies the concrete mild equation. -/
example := @MNS2.r3EndpointSafeProjected_localMildSolution_equation

/-- The Helmholtz pressure witness (`Formal.R3HelmholtzPressure`).  `noncomputable`
because the upstream definition is. -/
noncomputable example := @MNS2.r3HelmholtzPressure

/-- `∇p = −(I−P)F` componentwise in `𝓢'`. -/
example := @MNS2.r3HelmholtzPressure_gradient

/-- The Navier–Stokes equation along a mild solution
(`Formal.R3NavierStokesEquation`). -/
example := @MNS2.r3EndpointSafeProjectedMild_navierStokes

/-- The existence composition of the same. -/
example := @MNS2.exists_r3EndpointSafeProjectedMild_navierStokes

end NSFormalization.Section4.HeliCorgiPort
