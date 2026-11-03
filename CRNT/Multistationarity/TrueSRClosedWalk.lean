import CRNT.Multistationarity.TrueSRGlueSeams

/-!
# Closed alternating walks, and cycles from them

Building the glued cycle straight from two paths needs a per-position case split with four
sub-cases in each of four field equations.  Factoring through a *closed alternating walk* of `2n`
vertices removes that: for `P : TrueSRPath (2j+1)`, `Q : TrueSRPath (2i+1)` glued along their
shared endpoints, with `n = i+j+1`,

```
W m = if m ≤ 2j+1 then P.vertex m else Q.vertex (2i+2j+2 - m)
E m = if m ≤ 2j   then P.edge m   else Q.edge (2i+2j+1 - m)
```

Both seams come out of the *same* formula — `E (2j+1) = Q.edge (2i)` joins the two halves and
`E (2n-1) = Q.edge 0` closes the cycle — so neither needs special casing.  That construction is
not carried out here; this file builds `TrueSRClosedWalk → TrueSRCycle`.

Representation note: all indices go through the named functions `walkSucc`, `evenPos`,
`nextPos`, never through inline `Fin.mk`.  Every field proof then rewrites with a plain function
equation.  Writing the indices inline instead produces "motive is not type correct" at five
separate sites, because the `Fin.mk` proof component depends on the value being rewritten.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-- The next position along a closed walk of `2n` vertices. -/
def walkSucc (m : Fin (2 * n)) : Fin (2 * n) :=
  ⟨(m.1 + 1) % (2 * n), Nat.mod_lt _ (by have := m.isLt; omega)⟩

/-- The even walk position corresponding to a cycle position. -/
def evenPos (t : Fin n) : Fin (2 * n) := ⟨2 * t.1, by have := t.isLt; omega⟩

/-- The next cycle position. -/
def nextPos (t : Fin n) : Fin n := ⟨(t.1 + 1) % n, Nat.mod_lt _ (by have := t.isLt; omega)⟩

@[simp] theorem evenPos_val (t : Fin n) : (evenPos t).1 = 2 * t.1 := rfl

theorem walkSucc_evenPos_val (t : Fin n) : (walkSucc (evenPos t)).1 = 2 * t.1 + 1 := by
  have ht := t.isLt
  show (2 * t.1 + 1) % (2 * n) = 2 * t.1 + 1
  exact Nat.mod_eq_of_lt (by omega)

theorem walkSucc_walkSucc_evenPos (t : Fin n) :
    walkSucc (walkSucc (evenPos t)) = evenPos (nextPos t) := by
  have ht := t.isLt
  apply Fin.ext
  show ((walkSucc (evenPos t)).1 + 1) % (2 * n) = 2 * ((t.1 + 1) % n)
  rw [walkSucc_evenPos_val]
  rcases Nat.lt_or_ge (t.1 + 1) n with h | h
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · have he : t.1 + 1 = n := by omega
    rw [he, Nat.mod_self]
    have h2 : 2 * t.1 + 1 + 1 = 2 * n := by omega
    rw [h2, Nat.mod_self]

/-- A closed alternating walk: `2n` vertices, species at even positions and reactions at odd
ones, consecutive vertices joined by edges, all vertices distinct. -/
structure TrueSRClosedWalk (N : Network S) (n : ℕ) where
  nontrivial : 2 ≤ n
  vertex : Fin (2 * n) → N.TrueSRVertex
  edge : Fin (2 * n) → N.TrueSREdge
  connects : ∀ m : Fin (2 * n), (edge m).Connects (vertex m) (vertex (walkSucc m))
  vertex_simple : Function.Injective vertex
  even_species : ∀ m : Fin (2 * n), m.1 % 2 = 0 → ∃ s : S, vertex m = Sum.inl s
  odd_reaction : ∀ m : Fin (2 * n), m.1 % 2 ≠ 0 →
    ∃ ρ : N.InternalTrueReaction, vertex m = Sum.inr ρ

private theorem even_ok {n : ℕ} (t : Fin n) : (evenPos t).1 % 2 = 0 := by simp

private theorem odd_ok {n : ℕ} (t : Fin n) : (walkSucc (evenPos t)).1 % 2 ≠ 0 := by
  rw [walkSucc_evenPos_val]; omega

namespace TrueSRClosedWalk

variable (W : N.TrueSRClosedWalk n)

/-- The species at an even position. -/
noncomputable def speciesAt (m : Fin (2 * n)) (hm : m.1 % 2 = 0) : S :=
  (W.even_species m hm).choose

theorem vertex_eq_speciesAt (m : Fin (2 * n)) (hm : m.1 % 2 = 0) :
    W.vertex m = Sum.inl (W.speciesAt m hm) :=
  (W.even_species m hm).choose_spec

/-- The reaction at an odd position. -/
noncomputable def reactionAt (m : Fin (2 * n)) (hm : m.1 % 2 ≠ 0) :
    N.InternalTrueReaction :=
  (W.odd_reaction m hm).choose

theorem vertex_eq_reactionAt (m : Fin (2 * n)) (hm : m.1 % 2 ≠ 0) :
    W.vertex m = Sum.inr (W.reactionAt m hm) :=
  (W.odd_reaction m hm).choose_spec



/-- **A closed alternating walk is a cycle.** -/
noncomputable def toCycle : N.TrueSRCycle n where
  nontrivial := W.nontrivial
  species := fun t => W.speciesAt (evenPos t) (even_ok t)
  reaction := fun t => (W.reactionAt (walkSucc (evenPos t)) (odd_ok t)).1
  leftEdge := fun t => W.edge (evenPos t)
  rightEdge := fun t => W.edge (walkSucc (evenPos t))
  left_species := by
    intro t
    have hv := W.vertex_eq_speciesAt (evenPos t) (even_ok t)
    rcases W.connects (evenPos t) with ⟨hu, _⟩ | ⟨hu, _⟩
    · rw [hv] at hu; exact (Sum.inl.inj hu).symm
    · rw [hv] at hu; exact absurd hu (by simp)
  left_reaction := by
    intro t
    have hv := W.vertex_eq_reactionAt (walkSucc (evenPos t)) (odd_ok t)
    rcases W.connects (evenPos t) with ⟨_, hw⟩ | ⟨_, hw⟩
    · rw [hv] at hw; exact congrArg Subtype.val (Sum.inr.inj hw).symm
    · rw [hv] at hw; exact absurd hw (by simp)
  right_reaction := by
    intro t
    have hv := W.vertex_eq_reactionAt (walkSucc (evenPos t)) (odd_ok t)
    rcases W.connects (walkSucc (evenPos t)) with ⟨hu, _⟩ | ⟨hu, _⟩
    · rw [hv] at hu; exact absurd hu (by simp)
    · rw [hv] at hu; exact congrArg Subtype.val (Sum.inr.inj hu).symm
  right_species := by
    intro t
    have hidx := walkSucc_walkSucc_evenPos t
    have hv := W.vertex_eq_speciesAt (evenPos (nextPos t)) (even_ok (nextPos t))
    rcases W.connects (walkSucc (evenPos t)) with ⟨_, hw⟩ | ⟨_, hw⟩
    · rw [hidx, hv] at hw; exact absurd hw (by simp)
    · rw [hidx, hv] at hw
      exact (Sum.inl.inj hw).symm
  species_injective := by
    intro a b hab
    have hva := W.vertex_eq_speciesAt (evenPos a) (even_ok a)
    have hvb := W.vertex_eq_speciesAt (evenPos b) (even_ok b)
    have hab' : W.speciesAt (evenPos a) (even_ok a) = W.speciesAt (evenPos b) (even_ok b) := hab
    have heq : W.vertex (evenPos a) = W.vertex (evenPos b) := by rw [hva, hvb, hab']
    have hv := congrArg Fin.val (W.vertex_simple heq)
    rw [evenPos_val, evenPos_val] at hv
    exact Fin.ext (by omega)
  reaction_injective := by
    intro a b hab
    have hva := W.vertex_eq_reactionAt (walkSucc (evenPos a)) (odd_ok a)
    have hvb := W.vertex_eq_reactionAt (walkSucc (evenPos b)) (odd_ok b)
    have heq : W.vertex (walkSucc (evenPos a)) = W.vertex (walkSucc (evenPos b)) := by
      rw [hva, hvb, Subtype.ext hab]
    have hv := congrArg Fin.val (W.vertex_simple heq)
    rw [walkSucc_evenPos_val, walkSucc_evenPos_val] at hv
    exact Fin.ext (by omega)

end TrueSRClosedWalk

end CRNT.Network
