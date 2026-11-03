import CRNT.Analysis.SpernerNGeometric
import CRNT.Analysis.SpernerNClose
import CRNT.Analysis.SpernerSimplexLimitN
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# The n-dimensional Brouwer fixed-point theorem

The analytic payoff of the n-dimensional Kuhn-Sperner development: every continuous self-map of the
standard `n`-simplex `stdSimplex ℝ (Fin (n+1))` has a fixed point. Given continuous `f`, color each
lattice point `p` of the `N`-subdivision by a barycentric coordinate that `f` does not increase at
`realize p` — this is a proper Sperner coloring, so `sperner_exists_rainbow` yields, for every `N`, a
Kuhn cell whose `n+1` vertices realize all `n+1` colors. As `N → ∞` the cells shrink
(mesh `≤ 1/N`), and the `n+1` vertex sequences collapse to a common limit `z` at which `f z = z`
(`brouwer_of_meshing_sequences_fintype`).

Depends on: `CRNT.Analysis.SpernerNGeometric`,
`CRNT.Analysis.SpernerNClose`, `CRNT.Analysis.SpernerSimplexLimitN`.
-/

namespace CRNT.Analysis.SpernerN

open CRNT.Analysis Filter Topology
open scoped BigOperators

variable {n N : ℕ}

/-- The simplex point realizing a lattice point. -/
noncomputable def realizePt (hN : 0 < N) (p : Pt n N) : ↥(stdSimplex ℝ (Fin (n + 1))) :=
  ⟨realize p, realize_mem_stdSimplex hN p⟩

@[simp] theorem realizePt_coe (hN : 0 < N) (p : Pt n N) :
    (realizePt hN p : Fin (n + 1) → ℝ) = realize p := rfl

/-- **There is a coordinate `f` does not increase, that is positive at `p`.** Both `realize p` and
`f (realizePt hN p)` are simplex points (coordinates sum to `1`), so some coordinate that is positive
at `realize p` is not increased by `f`. -/
theorem exists_color_index (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) :
    ∃ i : Fin (n + 1), 0 < realize p i ∧ (f (realizePt hN p) : Fin (n + 1) → ℝ) i ≤ realize p i := by
  set g : Fin (n + 1) → ℝ := (f (realizePt hN p) : Fin (n + 1) → ℝ) with hg
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

/-- The chosen non-increasing positive coordinate as a color. -/
noncomputable def colorOf (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) :
    Fin (n + 1) :=
  (exists_color_index hN f p).choose

theorem colorOf_pos (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) :
    0 < realize p (colorOf hN f p) :=
  (exists_color_index hN f p).choose_spec.1

theorem colorOf_dec (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) :
    (f (realizePt hN p) : Fin (n + 1) → ℝ) (colorOf hN f p) ≤ realize p (colorOf hN f p) :=
  (exists_color_index hN f p).choose_spec.2

/-- **The Sperner coloring induced by a continuous self-map.** -/
noncomputable def spernerColoringOf (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) : SpernerColoring n N where
  color := colorOf hN f
  proper p i h := by
    have hp := colorOf_pos hN f p
    rw [h, realize_apply] at hp
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rcases div_pos_iff.mp hp with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact_mod_cast h1
    · exact absurd h2 (by linarith)

@[simp] theorem spernerColoringOf_color (hN : 0 < N)
    (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (p : Pt n N) :
    (spernerColoringOf hN f).color p = colorOf hN f p := rfl

/-- **The n-dimensional Brouwer fixed-point theorem.** Every continuous self-map of the standard
`n`-simplex `stdSimplex ℝ (Fin (n+1))` has a fixed point. -/
theorem brouwer_stdSimplex_fin (n : ℕ)
    (f : ↥(stdSimplex ℝ (Fin (n + 1))) → ↥(stdSimplex ℝ (Fin (n + 1)))) (hf : Continuous f) :
    ∃ z, f z = z := by
  -- For each refinement `N = k+1`, the induced coloring has a rainbow Kuhn cell.
  have hcell : ∀ k : ℕ, ∃ c : Cell n (k + 1),
      IsRainbowCell (spernerColoringOf (Nat.succ_pos k) f) c :=
    fun k => sperner_exists_rainbow (spernerColoringOf (Nat.succ_pos k) f) (Nat.succ_pos k)
  choose c hc using hcell
  -- Each rainbow cell realizes every color: pick a vertex of each color `i`.
  have hvtx : ∀ (i : Fin (n + 1)) (k : ℕ), ∃ v : Pt n (k + 1),
      v ∈ (Finset.univ : Finset (Fin (n + 1))).image (c k).vertex ∧
        (spernerColoringOf (Nat.succ_pos k) f).color v = i := by
    intro i k
    obtain ⟨l, hl⟩ := (hc k).2 i
    exact ⟨(c k).vertex l, Finset.mem_image_of_mem _ (Finset.mem_univ l), hl⟩
  choose v hvmem hvcol using hvtx
  -- The meshing sequences: vertex `i` of the rainbow cell at refinement `k`.
  set x : Fin (n + 1) → ℕ → ↥(stdSimplex ℝ (Fin (n + 1))) :=
    fun i k => realizePt (Nat.succ_pos k) (v i k) with hx
  refine brouwer_of_meshing_sequences_fintype f hf x ?_ ?_
  · -- Pairwise distances vanish (mesh `≤ 1/(k+1) → 0`).
    intro i j
    have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) h1
    have hd : dist (x i k) (x j k) = dist (realize (v i k)) (realize (v j k)) := by
      rw [hx]; exact Subtype.dist_eq _ _
    rw [hd]
    -- Both vertices come from the same cell `c k`.
    obtain ⟨li, _, hli⟩ := Finset.mem_image.mp (hvmem i k)
    obtain ⟨lj, _, hlj⟩ := Finset.mem_image.mp (hvmem j k)
    rw [← hli, ← hlj]
    have hb := cell_vertex_dist_le (Nat.succ_pos k) (c k) li lj
    have hcast : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]; exact hb
  · -- `f` does not increase coordinate `i` at vertex `i`.
    intro k i
    have hdec := colorOf_dec (Nat.succ_pos k) f (v i k)
    rw [show colorOf (Nat.succ_pos k) f (v i k) = i from hvcol i k] at hdec
    simpa [hx, realizePt_coe] using hdec

end CRNT.Analysis.SpernerN
