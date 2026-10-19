# Metrization

A Lean library for the Nagata–Smirnov metrization theorem and a locally finite
closed metrizable neighbourhood-cover criterion. The results use Mathlib's
notions of topological basis, local finiteness and metrizability, and concern the
given topology rather than a replacement topology.

## Headline results

- **Sigma-locally-finite basis criterion**
  ([`TopologicalSpace.metrizableSpace_of_sigmaLocallyFinite_isTopologicalBasis`](Metrization/LocallyFinite.lean)).
  A T₃ space is metrizable if it has an open basis in countably many locally finite
  indexed levels. Each level may have an arbitrary index type; local finiteness
  counts the original indices, including repetitions.
- **Metric converse**
  ([`TopologicalSpace.exists_sigmaLocallyFinite_isTopologicalBasis`](Metrization/LocallyFinite.lean)).
  Every metrizable space has an open basis in countably many locally finite
  levels, each indexed by the points of the space.
- **Closed metrizable neighbourhood-cover criterion**
  ([`TopologicalSpace.metrizableSpace_of_locallyFinite_isClosed_interior_cover`](Metrization/LocallyFinite.lean)).
  A space is metrizable if it has a locally finite family of closed subsets whose
  interiors cover the space and each of which is metrizable in its original
  subtype topology. No ambient separation assumption is required.

## Using the library

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "metrization"
git = "https://github.com/FormalFrontier/metrization.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake records the resolved commit in
`lake-manifest.json`; to select a particular release, replace `main` with its full
commit hash. The library uses Lean `v4.34.0-rc2` and Mathlib
[`83abb3e776bdefcbc447a1e44d0debe4010039e5`](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5).

Import the complete library:

```lean
import Metrization
```

For just the metrization criteria, use `import Metrization.LocallyFinite`.
The declarations remain in the `TopologicalSpace` namespace; the finite-support
continuity lemma is in `LocallyFinite`.

The [coproduct clients](MetrizationTest/LocallyFinite.lean) instantiate all three
headline results. The basis examples use the discrete coproduct `Σ r : ℝ, PUnit`
with uncountable singleton levels. The cover example uses `Σ r : ℝ, ℝ` and its
clopen components, whose metrizability is obtained independently from their
homeomorphisms to `ℝ`.

## Building

The toolchain and the complete dependency graph are pinned in `lean-toolchain`
and `lake-manifest.json`. With Lean installed, run:

```sh
lake exe cache get && lake build
```

Both `Metrization` and `MetrizationTest` are default build targets. The only direct
dependency is Mathlib.

## Contents

| Module | Contents |
| --- | --- |
| `Metrization` | Public imports of all three library modules |
| `Metrization.Finsupp` | Continuity of locally finite finite-support coordinate maps into `WithLp 1` |
| `Metrization.RegularBasis` | Normality and countable closed exhaustion of open sets from a regular sigma-locally-finite basis |
| `Metrization.LocallyFinite` | The three metrization criteria |
| `MetrizationTest.LocallyFinite` | The three coproduct clients |
| `MetrizationTest` | Public import of the client module |

## Conventions and limitations

`IsTopologicalBasis` includes openness of every basis member. The basis criterion
requires T₃, while the normality and closed-exhaustion lemmas require only
`RegularSpace`. The latter exhaustion need not be increasing.

The index types of the basis levels and the closed cover need not be countable;
empty levels and repeated members are allowed subject to the stated local
finiteness. No second-countability, separability, finite-dimensionality, local
compactness or completeness hypothesis is imposed. Closedness and coverage by
interiors are essential hypotheses of the closed-cover criterion; an arbitrary
open metrizable cover is not the statement proved here.

The finite-support continuity lemma uses arbitrary coordinate spaces with `Zero`
and `PseudoMetricSpace`, and the canonical `WithLp 1` finite-support pseudometric.
It does not identify that topology with an unspecified topology on finitely
supported functions.

## References

- J. Nagata, *On a necessary and sufficient condition of metrizability* (1950).
- Yu. M. Smirnov, *A necessary and sufficient condition for metrizability of a
  topological space* (1951).
- [Mathlib](https://github.com/leanprover-community/mathlib4): topological bases,
  locally finite families, separation and Urysohn's lemma, metric paracompactness,
  countable products, finite-support ℓᵖ metrics and coproduct homeomorphisms.

## Credits and license

Authors: Formal Frontier Agents. The mathematical arguments follow the classical
Nagata–Smirnov criterion and its metric converse and closed-neighbourhood
corollary. The Lean modules and coproduct clients reuse the earlier generic
metrization formalizations by Formal Frontier Agents. Mathlib and its contributors
provide the underlying topological, metric, finite-support and homeomorphism APIs;
specific references are retained in the module documentation. AI agents
contributed to the formalization and documentation. Licensed under Apache-2.0;
see [LICENSE](LICENSE).
