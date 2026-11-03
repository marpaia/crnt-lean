import CRNT.Decision.RankExact
import CRNT.Decision.GaussianRank
import CRNT.Deficiency.DeficiencyOne
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Rat

/-!
# An exact computable deficiency certificate

The stoichiometric rank `s = finrank ℝ stoichSubspace` and Mathlib's matrix rank are
noncomputable. `CRNT.Decision.RankExact` supplies only a one-sided computable lower bound
`computeStoichRankLB ≤ s`, because Mathlib lacks a theorem identifying a matrix rank with the
maximal nonsingular minor size. `CRNT.Decision.GaussianRank` now provides exactly that theorem,
but only over `ℚ` (`computeRank_eq_rank`).

This module bridges the two. The stoichiometric matrix has integer entries — each reaction
vector is `target − source` of `ℕ`-valued complex coefficient vectors — so it embeds in `ℚ`.
The rational stoichiometric matrix `stoichMatrixQ` is therefore *computable*, and its `ℚ`-rank
equals the real stoichiometric rank by field-extension invariance of rank: casting columns along
the injective `ℚ`-linear map `castSpeciesLM : (S → ℚ) →ₗ[ℚ] (S → ℝ)` preserves linear
independence in both directions, so

* `stoichRank_eq_computeRank : N.stoichRank = computeRank N.stoichMatrixQ`,

upgrading `RankExact`'s one-sided bound to an exact rank. The rank `computeRank
stoichMatrixQ` is exact and evaluates by compiled reduction (`#eval`), but it does **not** reduce
under kernel `decide`: `computeRank` expands a determinant over a permutation sum, which the kernel
does not reduce. The exact deficiency

* `computeDeficiency N := numComplexes − numLinkageClasses − computeRank stoichMatrixQ`,

is moreover `noncomputable` as written, because `numLinkageClasses` is a quotient cardinality
(`Nat.card (Quotient linkedSetoid)`). So `deficiency_eq_computeDeficiency : N.deficiency =
N.computeDeficiency` (valid for *every* deficiency value) and the `δ = 0` / `δ = 1` corollaries are
exact equality/`iff` bridges to the computable rank — concrete deficiency values come through the
bridge or `#eval`, not by `decide`. (The decidable deficiency-*one algorithm* runs through the
structural conditions, e.g. `OneTerminalSLCPerLinkageClass`, which do `decide`-reduce — a path
independent of the rank.)

The field-extension invariance is proved directly: `GaussianRank`'s minor machinery is hardcoded
to `Matrix _ _ ℚ`, so the `ℝ` side cannot reuse it. Instead, `(stoichMatrixQ.map (Rat.castHom ℝ)).rank
= stoichMatrixQ.rank` follows from `LinearIndependent.restrict_scalars` and the injective
`ℚ`-linear cast, together with `GaussianRank.exists_injOn_linearIndependent_of_le_finrank_span`.

Depends on: `CRNT.Decision.RankExact`,
`CRNT.Decision.GaussianRank`, `CRNT.Deficiency.DeficiencyOne`,
`Mathlib.LinearAlgebra.Matrix.Rank`, `Mathlib.LinearAlgebra.Pi`, `Mathlib.Algebra.Algebra.Rat`.
-/

namespace CRNT

namespace Network

open Matrix Module Submodule Set Function CRNT.GaussianRank

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The rational stoichiometric matrix.** Rows indexed by species, columns by reactions; entry
`(s, r)` is the rational reaction-vector coordinate `target(s) − source(s)`. Because the complex
coefficients are `ℕ`-valued, every entry is rational, so this matrix is computable. -/
def stoichMatrixQ (N : Network S) : Matrix S N.R ℚ :=
  Matrix.of fun s r => ((N.reaction r).target s : ℚ) - ((N.reaction r).source s : ℚ)

/-- Casting the rational stoichiometric matrix to `ℝ` recovers the reaction vectors as its
columns. -/
theorem stoichMatrixQ_map_col (N : Network S) (r : N.R) :
    (N.stoichMatrixQ.map (Rat.castHom ℝ)).col r = N.reactionVector r := by
  funext s
  simp [stoichMatrixQ, Matrix.col_apply, Matrix.map_apply, reactionVector_apply]

/-- The stoichiometric rank is the column rank of the real-cast rational stoichiometric matrix. -/
theorem stoichRank_eq_rank_map (N : Network S) :
    N.stoichRank = (N.stoichMatrixQ.map (Rat.castHom ℝ)).rank := by
  rw [Matrix.rank_eq_finrank_span_cols, stoichRank, stoichSubspace, reactionVectors]
  have hfun : N.reactionVector = (N.stoichMatrixQ.map (Rat.castHom ℝ)).col := by
    funext r
    exact (N.stoichMatrixQ_map_col r).symm
  rw [hfun]

/-- **The injective `ℚ`-linear cast of species vectors.** The componentwise embedding
`(S → ℚ) → (S → ℝ)`, packaged as a `ℚ`-linear map. It carries the columns of `stoichMatrixQ` to
the columns of its real cast, transporting linear independence in both directions. -/
noncomputable def castSpeciesLM (S : Type) : (S → ℚ) →ₗ[ℚ] (S → ℝ) where
  toFun f := fun s => ((f s : ℚ) : ℝ)
  map_add' f g := by funext s; simp
  map_smul' q f := by funext s; simp [Rat.smul_def]

omit [DecidableEq S] [Fintype S] in
/-- The species-vector cast is injective. -/
theorem castSpeciesLM_injective (S : Type) : Injective (castSpeciesLM S) := by
  intro f g h
  funext s
  have : ((f s : ℚ) : ℝ) = ((g s : ℚ) : ℝ) := congrFun h s
  exact_mod_cast this

/-- The cast sends each column of `stoichMatrixQ` to the corresponding column of its real cast. -/
theorem castSpeciesLM_col (N : Network S) (r : N.R) :
    castSpeciesLM S (N.stoichMatrixQ.col r) = (N.stoichMatrixQ.map (Rat.castHom ℝ)).col r := by
  funext s
  simp [castSpeciesLM, stoichMatrixQ, Matrix.col_apply, Matrix.map_apply]

/-- **Field extension does not increase rank.** The real-cast rational stoichiometric matrix has
rank at most that of the rational matrix: a set of independent columns over `ℝ` lifts, via the
injective `ℚ`-linear cast, to the same number of independent columns over `ℚ`. -/
theorem rank_map_le_rank (N : Network S) :
    (N.stoichMatrixQ.map (Rat.castHom ℝ)).rank ≤ N.stoichMatrixQ.rank := by
  classical
  set k := (N.stoichMatrixQ.map (Rat.castHom ℝ)).rank with hk
  -- Extract `k` independent real columns.
  have hle : k ≤ finrank ℝ (span ℝ (range (N.stoichMatrixQ.map (Rat.castHom ℝ)).col)) := by
    rw [← Matrix.rank_eq_finrank_span_cols]
  obtain ⟨a, _hainj, hali⟩ :=
    exists_injOn_linearIndependent_of_le_finrank_span
      (N.stoichMatrixQ.map (Rat.castHom ℝ)).col k hle
  -- The same selection of rational columns is `ℚ`-independent.
  have hinj : Injective fun q : ℚ => q • (1 : ℝ) := by
    intro p q h; simpa using h
  -- `ℝ`-independence restricts to `ℚ`-independence of the real columns.
  have hQli : LinearIndependent ℚ ((N.stoichMatrixQ.map (Rat.castHom ℝ)).col ∘ a) :=
    hali.restrict_scalars hinj
  -- Rewrite the real columns as the cast of the rational columns.
  have hcomp : (N.stoichMatrixQ.map (Rat.castHom ℝ)).col ∘ a
      = (castSpeciesLM S) ∘ (N.stoichMatrixQ.col ∘ a) := by
    funext i
    simp only [Function.comp_apply]
    exact (N.castSpeciesLM_col (a i)).symm
  rw [hcomp] at hQli
  -- The rational columns are `ℚ`-independent.
  have hQli' : LinearIndependent ℚ (N.stoichMatrixQ.col ∘ a) :=
    LinearIndependent.of_comp (castSpeciesLM S) hQli
  -- Hence `k` independent rational columns inside the column span; bound the rank below.
  set W : Submodule ℚ (S → ℚ) := span ℚ (range N.stoichMatrixQ.col) with hW
  have hmem : ∀ i, (N.stoichMatrixQ.col ∘ a) i ∈ W := by
    intro i; exact subset_span ⟨a i, rfl⟩
  have hWli : LinearIndependent ℚ
      (fun i : Fin k => (⟨(N.stoichMatrixQ.col ∘ a) i, hmem i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hQli'
  have hcard := hWli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  -- `k ≤ finrank ℚ W = rank stoichMatrixQ`.
  have hWrank : finrank ℚ W = N.stoichMatrixQ.rank := by
    rw [hW, Matrix.rank_eq_finrank_span_cols]
  rw [hWrank] at hcard
  exact hcard

/-- **The rational rank is at most the stoichiometric rank.** A nonsingular `k × k` minor of the
rational stoichiometric matrix (witnessing `k ≤ rank`) is, after the row/column index swap, the
minor certificate consumed by `stoichRank_ge_of_det_ne_zero`. -/
theorem rank_le_stoichRank (N : Network S) :
    N.stoichMatrixQ.rank ≤ N.stoichRank := by
  set k := N.stoichMatrixQ.rank with hk
  -- A nonsingular minor of size exactly the rank exists.
  obtain ⟨r, c, hdet⟩ :=
    le_rank_iff_hasNonsingularMinor.mp (le_refl N.stoichMatrixQ.rank)
  -- The certificate `stoichRank_ge_of_det_ne_zero` takes reactions then species; the minor has
  -- rows = species (`r`), cols = reactions (`c`).
  apply N.stoichRank_ge_of_det_ne_zero c r
  -- The certificate matrix is exactly `stoichMatrixQ.submatrix r c`.
  have hsub : (Matrix.of fun i j : Fin k =>
        ((N.reaction (c j)).target (r i) : ℚ) - ((N.reaction (c j)).source (r i) : ℚ))
      = N.stoichMatrixQ.submatrix r c := by
    ext i j
    rfl
  rw [hsub]
  exact hdet

/-- **The stoichiometric rank equals the computable rational rank.** Chaining
`stoichRank = rank (map)` (`stoichRank_eq_rank_map`), `rank (map) ≤ rank Q` (`rank_map_le_rank`),
`rank Q ≤ stoichRank` (`rank_le_stoichRank`), and `computeRank = rank` (`computeRank_eq_rank`)
pins the stoichiometric rank to the computable `computeRank stoichMatrixQ`. -/
theorem stoichRank_eq_computeRank (N : Network S) :
    N.stoichRank = computeRank N.stoichMatrixQ := by
  have h1 := N.stoichRank_eq_rank_map
  have h2 := N.rank_map_le_rank
  have h3 := N.rank_le_stoichRank
  rw [computeRank_eq_rank]
  omega

/-- **The exact deficiency in terms of the computable rank.** With the stoichiometric rank now
exactly computable, `δ = n − ℓ − s = numComplexes − numLinkageClasses − computeRank stoichMatrixQ`.
This `def` is `noncomputable` because `numLinkageClasses` is a quotient cardinality, and `computeRank`
itself does not reduce under kernel `decide`; the deficiency value is obtained through
`deficiency_eq_computeDeficiency` or `#eval`, not by `decide`. -/
noncomputable def computeDeficiency (N : Network S) : ℕ :=
  N.numComplexes - N.numLinkageClasses - computeRank N.stoichMatrixQ

/-- **The deficiency equals its computable form**, for every deficiency value. -/
theorem deficiency_eq_computeDeficiency (N : Network S) :
    N.deficiency = N.computeDeficiency := by
  have hadd := N.numComplexes_eq_add
  have hrank := N.stoichRank_eq_computeRank
  rw [computeDeficiency, ← hrank]
  omega

/-- **Exact deficiency-zero criterion** in terms of the computable rank (an `iff` bridge, not a
kernel-`decide` reduction). -/
theorem deficiencyZero_iff_computeDeficiency_eq_zero (N : Network S) :
    N.DeficiencyZero ↔ N.computeDeficiency = 0 := by
  rw [deficiencyZero_iff_deficiency_eq_zero, deficiency_eq_computeDeficiency]

/-- **Exact deficiency-one criterion** in terms of the computable rank (an `iff` bridge, not a
kernel-`decide` reduction). -/
theorem deficiencyOne_iff_computeDeficiency_eq_one (N : Network S) :
    N.DeficiencyOne ↔ N.computeDeficiency = 1 := by
  rw [deficiencyOne_iff_deficiency_eq_one, deficiency_eq_computeDeficiency]

end Network

end CRNT
