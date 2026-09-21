# Selected OpenAI Navier–Stokes and Euler source dependencies

This directory retains the upstream modules required by the current article
proof/test closure, together with LICENSE and the pinned Lake configuration.
It is not a complete upstream checkout. Unused umbrella modules and comparator
challenge templates are excluded. The full downloaded source archive remains
in `reference/`.

Use `lake -d verification build` from the repository root. The selected library
modules use Lean 4.34.0-rc2 and the Mathlib revision fixed by the checked-in
manifest. Upstream project:
https://github.com/openai/NavierStokesAndEuler.
