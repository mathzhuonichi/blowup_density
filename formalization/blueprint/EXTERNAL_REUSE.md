# Current upstream reuse

The project fixes Lean 4.34.0-rc2 and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The checked-in Lake manifests retain
the required external dependency revisions. Only local and vendored modules
reachable from current proof/test entry points remain.

The OpenAI source snapshot was recorded with reference revision
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`; the full downloaded source archive is
retained in `reference/`. The selected source tree is not represented as an
unmodified complete upstream checkout. OpenAI Navier–Stokes and Euler modules
are both actual dependencies. Comparator challenge templates are not inputs
and have been removed.

The HeliCorgi source snapshot was recorded as revision
`de518485776d1d8de60f0c51151121df71e3ab6d` of
[ns-mns2-flowmap-bridge](https://github.com/HeliCorgi/ns-mns2-flowmap-bridge).
Its retained `Formal` modules compile in place under the main project's pin.
Unused standalone 4.32.1 package metadata and patched compatibility modules
are not build targets. Both upstream licenses remain in `vendor/`.

Cited literature remains in [reference/](../../reference/README.md). Citations
are mathematical sources, not Lean axioms. The article-declaration audit
checks actual kernel dependencies, including the selected upstream construction
and nonexistence comparison; see [the graph](DEPENDENCY_GRAPH.md).
