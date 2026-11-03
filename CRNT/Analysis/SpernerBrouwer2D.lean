import CRNT.Analysis.SpernerLatticeGeometric
import CRNT.Analysis.SpernerLatticeSperner
import CRNT.Analysis.SpernerSimplexLimit
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# The two-dimensional Brouwer fixed-point theorem

The analytic payoff of the lattice Sperner development: every continuous self-map of the standard
2-simplex `stdSimplex ℝ (Fin 3)` has a fixed point. Given continuous `f`, colour each lattice point
`p` of the `N`-subdivision by a barycentric coordinate that `f` does not increase at `realize p` —
this is a proper Sperner colouring, so `exists_rainbow_cell` yields, for every `N`, a triangle with
three vertices coloured `0, 1, 2`. As `N → ∞` the triangles shrink (mesh `≤ 2/N`), and the three
sequences of vertices collapse to a common limit `z` at which `f z = z`
(`brouwer_of_meshing_sequences`).

Depends on: `CRNT.Analysis.SpernerLatticeGeometric`,
`CRNT.Analysis.SpernerLatticeSperner`, `CRNT.Analysis.SpernerSimplexLimit`.
-/

namespace CRNT.Analysis.SpernerLattice

open CRNT.Analysis.Sperner2D CRNT.Analysis Filter Topology
open scoped BigOperators

variable {N : ℕ}

/-- The simplex point realizing a lattice point. -/
noncomputable def realizePt (hN : 0 < N) (p : Pt N) : ↥(stdSimplex ℝ (Fin 3)) :=
  ⟨realize p, realize_mem_stdSimplex hN p⟩

@[simp] theorem realizePt_coe (hN : 0 < N) (p : Pt N) :
    (realizePt hN p : Fin 3 → ℝ) = realize p := rfl

/-- **There is a coordinate `f` does not increase, that is positive at `p`.** Both `realize p` and
`f (realizePt hN p)` are simplex points (coordinates sum to `1`), so some coordinate that is positive
at `realize p` is not increased by `f`. -/
theorem exists_color_index (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) :
    ∃ i : Fin 3, 0 < realize p i ∧ (f (realizePt hN p) : Fin 3 → ℝ) i ≤ realize p i := by
  set g : Fin 3 → ℝ := (f (realizePt hN p) : Fin 3 → ℝ) with hg
  have hgnn : ∀ i, 0 ≤ g i := (f (realizePt hN p)).2.1
  have hgsum : ∑ i, g i = 1 := (f (realizePt hN p)).2.2
  have hrnn : ∀ i, 0 ≤ realize p i := (realize_mem_stdSimplex hN p).1
  have hrsum : ∑ i, realize p i = 1 := (realize_mem_stdSimplex hN p).2
  by_contra hcon
  push Not at hcon
  have hex : ∃ i, 0 < realize p i := by
    by_contra h2
    push Not at h2
    have hz : ∀ i, realize p i = 0 := fun i => le_antisymm (h2 i) (hrnn i)
    rw [Finset.sum_congr rfl (fun i _ => hz i)] at hrsum
    simp at hrsum
  obtain ⟨i0, hi0⟩ := hex
  have hlt : realize p i0 < g i0 := hcon i0 hi0
  have hle : ∀ i ∈ Finset.univ, realize p i ≤ g i := by
    intro i _
    by_cases h : 0 < realize p i
    · exact (hcon i h).le
    · rw [le_antisymm (not_lt.mp h) (hrnn i)]; exact hgnn i
  have hsum_lt : ∑ i, realize p i < ∑ i, g i :=
    Finset.sum_lt_sum hle ⟨i0, Finset.mem_univ i0, hlt⟩
  rw [hrsum, hgsum] at hsum_lt
  exact lt_irrefl 1 hsum_lt

/-- The chosen non-increasing positive coordinate as a colour. -/
noncomputable def colorOf (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) : Color :=
  (exists_color_index hN f p).choose

theorem colorOf_pos (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) :
    0 < realize p (colorOf hN f p) :=
  (exists_color_index hN f p).choose_spec.1

theorem colorOf_dec (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) :
    (f (realizePt hN p) : Fin 3 → ℝ) (colorOf hN f p) ≤ realize p (colorOf hN f p) :=
  (exists_color_index hN f p).choose_spec.2

/-- **The Sperner colouring induced by a continuous self-map.** -/
noncomputable def spernerColoringOf (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) : SpernerColoring N where
  color := colorOf hN f
  proper0 p h := by
    have hp := colorOf_pos hN f p
    rw [h, realize_zero] at hp
    rcases div_pos_iff.mp hp with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  proper1 p h := by
    have hp := colorOf_pos hN f p
    rw [h, realize_one] at hp
    rcases div_pos_iff.mp hp with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  proper2 p h := by
    have hp := colorOf_pos hN f p
    rw [h, realize_two_eq] at hp
    have hnum : 0 < (N:ℝ) - p.1.1 - p.1.2 := by
      rcases div_pos_iff.mp hp with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd h2 (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)
    have : (p.1.1 : ℝ) + p.1.2 < N := by linarith
    exact_mod_cast this

@[simp] theorem spernerColoringOf_color (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3))) (p : Pt N) :
    (spernerColoringOf hN f).color p = colorOf hN f p := rfl

/-- The three colour components of a triangle are the colours of three of its vertices. -/
theorem col_components (κ : SpernerColoring N) (t : Cell N) :
    ∃ v0 v1 v2 : Pt N, v0 ∈ triVerts t ∧ v1 ∈ triVerts t ∧ v2 ∈ triVerts t ∧
      (col κ t).1 = κ.color v0 ∧ (col κ t).2.1 = κ.color v1 ∧ (col κ t).2.2 = κ.color v2 := by
  cases t with
  | inl c =>
    refine ⟨_, _, _, ?_, ?_, ?_, rfl, rfl, rfl⟩ <;>
      simp only [triVerts, Sum.elim_inl, upVerts, Finset.mem_insert, Finset.mem_singleton] <;> tauto
  | inr c =>
    refine ⟨_, _, _, ?_, ?_, ?_, rfl, rfl, rfl⟩ <;>
      simp only [triVerts, Sum.elim_inr, downVerts, Finset.mem_insert, Finset.mem_singleton] <;> tauto

/-- **Rainbow ⇒ every colour is realized by a vertex.** -/
theorem rainbow_vertex (κ : SpernerColoring N) {t : Cell N}
    (ht : isRainbow (col κ t).1 (col κ t).2.1 (col κ t).2.2 = true) (i : Color) :
    ∃ v : Pt N, v ∈ triVerts t ∧ κ.color v = i := by
  obtain ⟨v0, v1, v2, hv0, hv1, hv2, e0, e1, e2⟩ := col_components κ t
  simp only [isRainbow, decide_eq_true_eq] at ht
  have hi : i ∈ ({(col κ t).1, (col κ t).2.1, (col κ t).2.2} : Finset Color) := by
    rw [ht]; fin_cases i <;> decide
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with h | h | h
  · exact ⟨v0, hv0, by rw [← e0]; exact h.symm⟩
  · exact ⟨v1, hv1, by rw [← e1]; exact h.symm⟩
  · exact ⟨v2, hv2, by rw [← e2]; exact h.symm⟩

/-- **Two vertices of the same triangle differ by at most one in each lattice coordinate.** -/
theorem triVerts_coord_bound (t : Cell N) {v w : Pt N}
    (hv : v ∈ triVerts t) (hw : w ∈ triVerts t) :
    |(v.1.1 : ℝ) - w.1.1| ≤ 1 ∧ |(v.1.2 : ℝ) - w.1.2| ≤ 1 := by
  cases t with
  | inl c =>
    simp only [triVerts, Sum.elim_inl, upVerts, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      refine ⟨?_, ?_⟩ <;>
        · simp only [mkPt]; rw [abs_le]; push_cast; constructor <;> linarith
  | inr c =>
    simp only [triVerts, Sum.elim_inr, downVerts, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      refine ⟨?_, ?_⟩ <;>
        · simp only [mkPt]; rw [abs_le]; push_cast; constructor <;> linarith

/-- **The two-dimensional Brouwer fixed-point theorem.** Every continuous self-map of the standard
2-simplex `stdSimplex ℝ (Fin 3)` has a fixed point. -/
theorem brouwer_stdSimplex_fin3 (f : ↥(stdSimplex ℝ (Fin 3)) → ↥(stdSimplex ℝ (Fin 3)))
    (hf : Continuous f) : ∃ z, f z = z := by
  have hcell : ∀ n : ℕ, ∃ t : Cell (n + 1),
      isRainbow (col (spernerColoringOf (Nat.succ_pos n) f) t).1
        (col (spernerColoringOf (Nat.succ_pos n) f) t).2.1
        (col (spernerColoringOf (Nat.succ_pos n) f) t).2.2 = true :=
    fun n => exists_rainbow_cell (spernerColoringOf (Nat.succ_pos n) f)
  choose t ht using hcell
  have hvtx : ∀ (i : Color) (n : ℕ), ∃ v : Pt (n + 1),
      v ∈ triVerts (t n) ∧ (spernerColoringOf (Nat.succ_pos n) f).color v = i :=
    fun i n => rainbow_vertex _ (ht n) i
  choose v hv hvcol using hvtx
  set x : Fin 3 → ℕ → ↥(stdSimplex ℝ (Fin 3)) :=
    fun i n => realizePt (Nat.succ_pos n) (v i n) with hx
  refine brouwer_of_meshing_sequences f hf x ?_ ?_
  · intro i j
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hc : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ => (2 : ℝ) / (n + 1)) atTop (𝓝 0) := hc.div_atTop hden
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h2
    have hd : dist (x i n) (x j n) = dist (realize (v i n)) (realize (v j n)) := by
      rw [hx]; exact Subtype.dist_eq _ _
    rw [hd]
    obtain ⟨h1, h2'⟩ := triVerts_coord_bound (t n) (hv i n) (hv j n)
    have hb := realize_dist_le (Nat.succ_pos n) (v i n) (v j n) h1 h2'
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]; exact hb
  · intro n i
    have hdec := colorOf_dec (Nat.succ_pos n) f (v i n)
    rw [show colorOf (Nat.succ_pos n) f (v i n) = i from hvcol i n] at hdec
    simpa [hx, realizePt_coe] using hdec

end CRNT.Analysis.SpernerLattice
