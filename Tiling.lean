import Tiling.Polarity
import Tiling.FP
import Tiling.Combinatorics.Paths

/-!
# Surface tilings and incidence master theorems

Import Tiling for the full library, or Tiling.Polarity / Tiling.FP for a single application.
The library lives under proof/tiling and shares the parent project's Mathlib and Lean toolchain.
Run lake build Tiling from proof to compile all library modules, including the examples.

The layers separate geometry from the combinatorics and algebra of cancellation:

* Combinatorics.Quadrangulation: square-side gluings, endpoint occurrences, surface links,
  and orientation twisting. Loops, parallel edges and repeated boundary vertices are retained.
* Combinatorics.Coloring: local orientability, global vertex colorings, and the implication
  from orientability plus coloring to orientation twisting.
* Combinatorics.Paths: closed edge-path parity equals orientation transport under twisting.
* Geometry.Pairing: one geometric coherence and determinant proof for two paired vector spaces,
  with homogeneous-representative invariance. Polarity uses a bilinear form; FP uses evaluation
  between a vector space and its dual, with hyperplanes interpreted as covector kernels.
* Algebra.EdgeWeights: symmetric vertex pairings define edge weights; the shared master theorem
  follows from the fixed-point-free cancellation lemma in Algebra.Cancellation.
* Polarity and FP: typed realizations, geometric face criteria, and thin master-theorem wrappers.

The main public surface theorems are Tiling.Quadrangulation.polarity_master and
Tiling.Quadrangulation.fp_master. Their stronger versions Polarity.master and FP.master work
on QuadGluing without requiring connected links. Both allow arbitrary fields and vector-space
dimension. Polarity requires a symmetric form and nonconjugate adjacent points; FP requires
an orientable gluing and nonincident adjacent point/hyperplane labels.

The realization maps store the composite assignment on vertices. A separate formal labeling
and realization may be composed before constructing either tiling. The surface model remains
combinatorial: a topological realization and a bridge to the first Stiefel--Whitney class are
not claimed. Examples.Torus checks a two-vertex surface with repeated face vertices, while
Examples.FPGeometry checks nondegenerate coherent and noncoherent point/hyperplane tiles.
-/
