import Tiling.Combinatorics.Coloring

/-!
# A two-vertex quadrangulation

Two squares form the checkerboard double cover of the usual one-square torus.
Both diagonals repeat a vertex. The four sides still represent distinct incidences.
-/

namespace Tiling.Examples

/-- The two-square torus, before imposing the connected-link condition. -/
def twoSquareGluing : QuadGluing (ZMod 2) (ZMod 2) where
  vertex f i := f + (i.val : ZMod 2)
  across d := (d.1 + 1, d.2 + 2)
  across_involutive := by
    unfold Function.Involutive
    decide
  across_ne := by decide
  reverse _ := true
  reverse_across := by decide
  glued := by decide

private def turn (x : Flag (ZMod 2)) : Flag (ZMod 2) :=
  twoSquareGluing.edgeSwap (cornerSwap x)

private theorem reach_turn (x : Flag (ZMod 2)) :
    Relation.ReflTransGen twoSquareGluing.LinkAdjacent x (turn x) := by
  apply Relation.ReflTransGen.trans (b := cornerSwap x)
  · exact .single (Or.inr rfl)
  · exact .single (Or.inl rfl)

private theorem reach_iterate (x : Flag (ZMod 2)) (n : ℕ) :
    Relation.ReflTransGen twoSquareGluing.LinkAdjacent x (turn^[n] x) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (reach_turn _)

private theorem same_vertex_orbit : ∀ x y : Flag (ZMod 2),
    flagVertex twoSquareGluing.vertex x = flagVertex twoSquareGluing.vertex y →
    ∃ n : Fin 4, y = turn^[n.val] x ∨ y = twoSquareGluing.edgeSwap (turn^[n.val] x) := by
  decide

/-- A genuine combinatorial surface with two vertices and repeated vertices on every face. -/
def twoSquareTorus : Quadrangulation (ZMod 2) (ZMod 2) where
  toQuadGluing := twoSquareGluing
  isSurface := by
    constructor
    · intro v
      exact ⟨((v, 0), false), by simp [flagVertex, twoSquareGluing]⟩
    · intro x y h
      obtain ⟨n, hn | hn⟩ := same_vertex_orbit x y h
      · rw [hn]
        exact reach_iterate x n.val
      · rw [hn]
        exact (reach_iterate x n.val).trans (.single (Or.inl rfl))

/-- The square orientations agree because all boundary identifications reverse direction. -/
theorem twoSquareTorus_orientable : twoSquareTorus.toQuadGluing.Orientable :=
  ⟨fun _ => 0, by decide⟩

/-- The two global vertices have opposite colors. -/
def twoSquareTorus_coloring : twoSquareTorus.toQuadGluing.Coloring where
  color := id
  edge := by decide

/-- Orientability and the global coloring give the common twisting condition. -/
theorem twoSquareTorus_orientationTwisted : twoSquareTorus.toQuadGluing.OrientationTwisted :=
  twoSquareTorus.toQuadGluing.orientationTwisted_of_orientable
    twoSquareTorus_orientable twoSquareTorus_coloring

/-- Repeated opposite vertices are permitted by the surface definition. -/
theorem twoSquareTorus_repeated_vertices (f : ZMod 2) :
    twoSquareTorus.vertex f 0 = twoSquareTorus.vertex f 2 ∧
      twoSquareTorus.vertex f 1 = twoSquareTorus.vertex f 3 := by
  revert f
  decide

end Tiling.Examples
