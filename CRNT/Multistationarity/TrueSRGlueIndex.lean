import CRNT.Multistationarity.TrueSRClosedWalk

/-!
# `Connects` is symmetric, and the glue index maps

Three of the five cases of the glue construction traverse `Q` **backwards**, so they need
`Connects` in the opposite orientation from the one `Q.connects` supplies.  Since `Connects` is
a disjunction of the two orientations, symmetry is immediate — but it is needed at every seam.

Also recorded here are the two index maps of the glue, with their bounds:

  `vertex m = if m ≤ 2j+1 then P.vertex m else Q.vertex (2i+2j+2 - m)`
  `edge   m = if m ≤ 2j   then P.edge   m else Q.edge   (2i+2j+1 - m)`
-/

namespace CRNT.Network.TrueSREdge

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- **`Connects` is symmetric**: an edge joins its two endpoints in either order. -/
theorem Connects.symm {e : N.TrueSREdge} {u v : N.TrueSRVertex} (h : e.Connects u v) :
    e.Connects v u := by
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact Or.inr ⟨hv, hu⟩
  · exact Or.inl ⟨hv, hu⟩

end CRNT.Network.TrueSREdge

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- Bound for the `Q`-branch of the glue's vertex map. -/
theorem glue_vertex_bound {i j : ℕ} {m : ℕ} (hm : m < 2 * (i + j + 1))
    (hge : 2 * j + 2 ≤ m) : 2 * i + 2 * j + 2 - m < 2 * i + 1 + 1 := by omega

/-- Bound for the `Q`-branch of the glue's edge map. -/
theorem glue_edge_bound {i j : ℕ} {m : ℕ} (hm : m < 2 * (i + j + 1))
    (hge : 2 * j + 1 ≤ m) : 2 * i + 2 * j + 1 - m < 2 * i + 1 := by omega

/-- The `Q`-branch of the vertex map preserves parity. -/
theorem glue_vertex_parity {i j : ℕ} {m : ℕ} (hge : 2 * j + 2 ≤ m) (hm : m % 2 = 0) :
    (2 * i + 2 * j + 2 - m) % 2 = 0 := by omega

/-- The `Q`-branch of the vertex map sends odd positions to odd positions. -/
theorem glue_vertex_parity_odd {i j : ℕ} {m : ℕ} (hlt : m < 2 * (i + j + 1))
    (hge : 2 * j + 2 ≤ m) (hm : m % 2 ≠ 0) :
    (2 * i + 2 * j + 2 - m) % 2 ≠ 0 := by omega

/-- On the `Q`-branch, the vertex map is injective. -/
theorem glue_vertex_inj {i j : ℕ} {m m' : ℕ} (hm : m < 2 * (i + j + 1))
    (hm' : m' < 2 * (i + j + 1)) (hge : 2 * j + 2 ≤ m) (hge' : 2 * j + 2 ≤ m')
    (h : 2 * i + 2 * j + 2 - m = 2 * i + 2 * j + 2 - m') : m = m' := by omega

end CRNT.Network.TrueSRPath
