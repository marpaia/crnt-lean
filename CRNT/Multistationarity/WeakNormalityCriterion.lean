import CRNT.Multistationarity.WeakNormality
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite minor certificates for weak normality

This file formalizes the rank-`r` criterion of Shinar--Feinberg: a rank-`r`
network is weakly normal if one can choose `r` reactions and source-supported
nonnegative influence vectors so that the pairing matrix

`Mᵢⱼ = pᵢ · (y'ⱼ-yⱼ)`

has nonzero determinant.  The important point is mathematical rather than
algorithmic: weak normality can be certified by one finite nonsingular minor.

The special choice `pᵢ = yᵢ` gives the standard source-complex criterion and,
in fact, a normality certificate.
-/

namespace CRNT
namespace Network

open scoped BigOperators Matrix
open Filter Topology

variable {S : Type} [DecidableEq S] [Fintype S]

private lemma exists_pos_injective_add_smul
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A B : V →ₗ[ℝ] V) (hA : Function.Injective A) :
    ∃ t : ℝ, 0 < t ∧ Function.Injective (A + t • B) := by
  let Ac : V →L[ℝ] V := A.toContinuousLinearMap
  let Bc : V →L[ℝ] V := B.toContinuousLinearMap
  let f : ℝ → V →L[ℝ] V := fun t => Ac + t • Bc
  have hf : Continuous f := by fun_prop
  let U : Set (V →L[ℝ] V) := {L | Function.Injective L}
  have hopen : IsOpen U := ContinuousLinearMap.isOpen_injective
  have hmem0 : f 0 ∈ U := by simpa [f, Ac, U] using hA
  have hpre : f ⁻¹' U ∈ 𝓝 (0 : ℝ) := hf.continuousAt (hopen.mem_nhds hmem0)
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨δ, hδ, hball⟩ := hpre
  refine ⟨δ / 2, by linarith, ?_⟩
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith : 0 ≤ δ / 2)]
    linarith
  have hm : δ / 2 ∈ f ⁻¹' U := hball hdist
  intro x y hxy
  apply hm
  exact hxy

/-- Data for a square weak-normality minor.  `I` indexes a selected set of
reactions whose cardinality equals the stoichiometric rank. -/
structure WeakNormalMinorData (N : Network S) (I : Type)
    [Fintype I] [DecidableEq I] where
  reaction : I → N.R
  influence : ∀ i : I, SourceInfluence (N.reaction (reaction i)).source
  card_eq_rank : Fintype.card I = N.stoichRank

/-- The Shinar--Feinberg weak-normality test matrix. -/
noncomputable def WeakNormalMinorData.matrix {N : Network S} {I : Type}
    [Fintype I] [DecidableEq I] (D : N.WeakNormalMinorData I) : Matrix I I ℝ :=
  fun i j => ∑ s : S, (D.influence i).vec s * N.reactionVector (D.reaction j) s

/-- A finite minor certificate for weak normality. -/
structure WeakNormalMinorCertificate (N : Network S) (I : Type)
    [Fintype I] [DecidableEq I] extends N.WeakNormalMinorData I where
  det_ne_zero : (WeakNormalMinorData.matrix toWeakNormalMinorData).det ≠ 0

/-- Nonzero determinant makes the selected reaction vectors linearly independent.
This is the linear-algebra heart of Proposition 7.14. -/
theorem WeakNormalMinorCertificate.selected_reactionVectors_linearIndependent
    {N : Network S} {I : Type} [Fintype I] [DecidableEq I]
    (C : N.WeakNormalMinorCertificate I) :
    LinearIndependent ℝ (fun i : I => N.reactionVector (C.reaction i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hgcoord : ∀ s : S, ∑ j : I, g j * N.reactionVector (C.reaction j) s = 0 := by
    intro s
    have hs := congrFun hg s
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hs
  have hmul : C.matrix *ᵥ g = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct, WeakNormalMinorData.matrix]
    calc
      (∑ j : I, (∑ s : S, (C.influence k).vec s *
          N.reactionVector (C.reaction j) s) * g j)
          = ∑ s : S, (C.influence k).vec s *
              (∑ j : I, g j * N.reactionVector (C.reaction j) s) := by
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro s _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        rw [hgcoord s, mul_zero]
  have hz : g = 0 := Matrix.eq_zero_of_mulVec_eq_zero C.det_ne_zero hmul
  exact congrFun hz i

/-- Because there are exactly `rank S` selected independent reaction vectors,
they form a basis of the stoichiometric subspace. -/
theorem WeakNormalMinorCertificate.spans_stoichSubspace
    {N : Network S} {I : Type} [Fintype I] [DecidableEq I]
    (C : N.WeakNormalMinorCertificate I) :
    Submodule.span ℝ (Set.range fun i : I => N.reactionVector (C.reaction i)) =
      N.stoichSubspace := by
  have hli := C.selected_reactionVectors_linearIndependent
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact N.reactionVector_mem_stoichSubspace (C.reaction i)
  · rw [finrank_span_eq_card hli, C.card_eq_rank]
    rfl

/-- **Finite-minor weak-normality criterion (Shinar--Feinberg Proposition 7.14).** -/
theorem weaklyNormal_of_minorCertificate
    (N : Network S) {I : Type} [Fintype I] [DecidableEq I]
    (C : N.WeakNormalMinorCertificate I) : N.WeaklyNormal := by
  classical
  let v : I → N.stoichSubspace := fun i =>
    ⟨N.reactionVector (C.reaction i), N.reactionVector_mem_stoichSubspace _⟩
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : ∑ j : I, g j • N.reactionVector (C.reaction j) = 0 := by
      have hgv := congrArg Subtype.val hg
      simpa [v] using hgv
    exact (Fintype.linearIndependent_iff.mp C.selected_reactionVectors_linearIndependent g hg') i
  have hcard : Fintype.card I = Module.finrank ℝ N.stoichSubspace := by
    simpa [Network.stoichRank] using C.card_eq_rank
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  let b : Module.Basis I ℝ N.stoichSubspace := Module.Basis.mk hli hspan.ge
  let A : N.stoichSubspace →ₗ[ℝ] N.stoichSubspace := {
    toFun := fun σ => ⟨∑ i : I,
      (∑ s : S, (C.influence i).vec s * σ.1 s) • N.reactionVector (C.reaction i),
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
        (N.reactionVector_mem_stoichSubspace (C.reaction i)))⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      change (∑ i : I, (∑ s : S, (C.influence i).vec s * (x.1 s + y.1 s)) •
          N.reactionVector (C.reaction i)) =
        (∑ i : I, (∑ s : S, (C.influence i).vec s * x.1 s) •
          N.reactionVector (C.reaction i)) +
        (∑ i : I, (∑ s : S, (C.influence i).vec s * y.1 s) •
          N.reactionVector (C.reaction i))
      simp only [mul_add, Finset.sum_add_distrib, add_smul]
    map_smul' := by
      intro c x
      apply Subtype.ext
      change (∑ i : I, (∑ s : S, (C.influence i).vec s * (c * x.1 s)) •
          N.reactionVector (C.reaction i)) =
        c • (∑ i : I, (∑ s : S, (C.influence i).vec s * x.1 s) •
          N.reactionVector (C.reaction i))
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring }
  have hmat : LinearMap.toMatrix b b A = C.matrix := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hb : b j = v j := Module.Basis.mk_apply hli hspan.ge j
    rw [hb]
    have hAv : A (v j) = ∑ k : I,
        (∑ s : S, (C.influence k).vec s *
          N.reactionVector (C.reaction j) s) • v k := by
      apply Subtype.ext
      simp [A, v]
    rw [hAv]
    calc
      b.coord i (∑ k : I,
          (∑ s : S, (C.influence k).vec s * N.reactionVector (C.reaction j) s) • v k)
          = ∑ k : I, (∑ s : S, (C.influence k).vec s *
              N.reactionVector (C.reaction j) s) * b.coord i (v k) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro k _
              rw [map_smul]
              rfl
      _ = ∑ s : S, (C.influence i).vec s * N.reactionVector (C.reaction j) s := by
        rw [Finset.sum_eq_single i]
        · rw [Module.Basis.mk_coord_apply_eq, mul_one]
        · intro k _ hki
          rw [Module.Basis.mk_coord_apply_ne hki, mul_zero]
        · simp
      _ = C.matrix i j := rfl
  have hdetA : A.det ≠ 0 := by
    rw [← LinearMap.det_toMatrix b, hmat]
    exact C.det_ne_zero
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    have hz : A.det = 0 := (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hne
    exact hdetA hz
  let Q : N.SourceInfluenceFamily := {
    influence := fun r => {
      vec := fun s => ((N.reaction r).source s : ℝ)
      nonneg := fun s => Nat.cast_nonneg _
      pos_iff_source := fun s => by
        simpa using (Nat.cast_pos : 0 < ((N.reaction r).source s : ℝ) ↔
          0 < (N.reaction r).source s).trans Nat.pos_iff_ne_zero } }
  let B : N.stoichSubspace →ₗ[ℝ] N.stoichSubspace :=
    N.weakNormalityOperatorOnStoich Q
  obtain ⟨ε, hε, hABinj⟩ := exists_pos_injective_add_smul A B hAinj
  have hCzero : ∀ (i : I) (s : S),
      (N.reaction (C.reaction i)).source s = 0 → (C.influence i).vec s = 0 := by
    intro i s hs
    apply le_antisymm
    · apply not_lt.mp
      intro hp
      exact ((C.influence i).pos_iff_source s |>.mp hp) hs
    · exact (C.influence i).nonneg s
  let P : N.SourceInfluenceFamily := {
    influence := fun r => {
      vec := fun s => ε * (Q.influence r).vec s +
        ∑ i : I, if C.reaction i = r then (C.influence i).vec s else 0
      nonneg := fun s => by
        apply add_nonneg
        · exact mul_nonneg hε.le ((Q.influence r).nonneg s)
        · exact Finset.sum_nonneg fun i _ => by
            split
            · exact (C.influence i).nonneg s
            · exact le_rfl
      pos_iff_source := fun s => by
        constructor
        · intro hp
          by_contra hs
          have hs0 : (N.reaction r).source s = 0 := hs
          have hq0 : (Q.influence r).vec s = 0 := by
            apply le_antisymm
            · apply not_lt.mp
              intro hqp
              exact ((Q.influence r).pos_iff_source s |>.mp hqp) hs0
            · exact (Q.influence r).nonneg s
          have hsum0 : (∑ i : I, if C.reaction i = r then (C.influence i).vec s else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            split_ifs with hir
            · exact hCzero i s (by simpa [hir] using hs0)
            · rfl
          rw [hq0, hsum0, mul_zero, add_zero] at hp
          exact lt_irrefl 0 hp
        · intro hs
          have hqpos : 0 < (Q.influence r).vec s := (Q.influence r).pos_iff_source s |>.2 hs
          have hsum_nonneg : 0 ≤ ∑ i : I,
              if C.reaction i = r then (C.influence i).vec s else 0 := by
            apply Finset.sum_nonneg
            intro i _
            split
            · exact (C.influence i).nonneg s
            · exact le_rfl
          nlinarith } }
  refine ⟨⟨P, ?_⟩⟩
  have hop : N.weakNormalityOperatorOnStoich P = A + ε • B := by
    apply LinearMap.ext
    intro σ
    apply Subtype.ext
    change N.weakNormalityOperator P σ.1 =
      (A σ).1 + ε • (N.weakNormalityOperatorOnStoich Q σ).1
    change (∑ r : N.R,
        (∑ s : S, (P.influence r).vec s * σ.1 s) • N.reactionVector r) =
      (∑ i : I, (∑ s : S, (C.influence i).vec s * σ.1 s) •
        N.reactionVector (C.reaction i)) +
      ε • (∑ r : N.R,
        (∑ s : S, (Q.influence r).vec s * σ.1 s) • N.reactionVector r)
    ext s
    dsimp [P]
    let qp : N.R → ℝ := fun r => ∑ u : S, (Q.influence r).vec u * σ.1 u
    let cp : I → ℝ := fun i => ∑ u : S, (C.influence i).vec u * σ.1 u
    have hpair : ∀ r : N.R,
        (∑ u : S, (ε * (Q.influence r).vec u +
            ∑ i : I, if C.reaction i = r then (C.influence i).vec u else 0) * σ.1 u) =
          ε * qp r + ∑ i : I, if C.reaction i = r then cp i else 0 := by
      intro r
      dsimp [qp, cp]
      calc
        (∑ u : S, (ε * (Q.influence r).vec u +
            ∑ i : I, if C.reaction i = r then (C.influence i).vec u else 0) * σ.1 u)
            = (∑ u : S, ε * ((Q.influence r).vec u * σ.1 u)) +
              ∑ u : S, (∑ i : I,
                if C.reaction i = r then (C.influence i).vec u else 0) * σ.1 u := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro u _
                ring
        _ = ε * (∑ u : S, (Q.influence r).vec u * σ.1 u) +
              ∑ i : I, if C.reaction i = r then
                (∑ u : S, (C.influence i).vec u * σ.1 u) else 0 := by
                congr 1
                · rw [Finset.mul_sum]
                · calc
                    (∑ u : S, (∑ i : I,
                        if C.reaction i = r then (C.influence i).vec u else 0) * σ.1 u)
                        = ∑ u : S, ∑ i : I,
                            (if C.reaction i = r then (C.influence i).vec u else 0) * σ.1 u := by
                              apply Finset.sum_congr rfl
                              intro u _
                              rw [Finset.sum_mul]
                    _ = ∑ i : I, ∑ u : S,
                          (if C.reaction i = r then (C.influence i).vec u else 0) * σ.1 u := by
                            rw [Finset.sum_comm]
                    _ = ∑ i : I, if C.reaction i = r then
                          (∑ u : S, (C.influence i).vec u * σ.1 u) else 0 := by
                            apply Finset.sum_congr rfl
                            intro i _
                            split_ifs with hir
                            · simp [hir]
                            · simp [hir]
        _ = _ := rfl
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    rw [show (∑ r : N.R,
        (∑ u : S, (ε * (Q.influence r).vec u +
          ∑ i : I, if C.reaction i = r then (C.influence i).vec u else 0) * σ.1 u) *
          N.reactionVector r s) =
        ∑ r : N.R, (ε * qp r + ∑ i : I,
          if C.reaction i = r then cp i else 0) * N.reactionVector r s by
          apply Finset.sum_congr rfl
          intro r _
          rw [hpair r]]
    calc
      (∑ r : N.R, (ε * qp r + ∑ i : I,
          if C.reaction i = r then cp i else 0) * N.reactionVector r s)
          = (∑ r : N.R, (∑ i : I,
              if C.reaction i = r then cp i else 0) * N.reactionVector r s) +
            ∑ r : N.R, (ε * qp r) * N.reactionVector r s := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro r _
              ring
      _ = (∑ i : I, cp i * N.reactionVector (C.reaction i) s) +
            ∑ r : N.R, (ε * qp r) * N.reactionVector r s := by
              congr 1
              calc
                (∑ r : N.R, (∑ i : I,
                    if C.reaction i = r then cp i else 0) * N.reactionVector r s)
                    = ∑ r : N.R, ∑ i : I,
                        (if C.reaction i = r then cp i else 0) *
                          N.reactionVector r s := by
                          apply Finset.sum_congr rfl
                          intro r _
                          rw [Finset.sum_mul]
                    _ = ∑ i : I, ∑ r : N.R,
                        (if C.reaction i = r then cp i else 0) *
                          N.reactionVector r s := by rw [Finset.sum_comm]
                    _ = ∑ i : I, cp i * N.reactionVector (C.reaction i) s := by
                          apply Finset.sum_congr rfl
                          intro i _
                          rw [Finset.sum_eq_single (C.reaction i)]
                          · simp
                          · intro r _ hr
                            simp [Ne.symm hr]
                          · simp
      _ = (∑ i : I, (∑ u : S, (C.influence i).vec u * σ.1 u) *
              N.reactionVector (C.reaction i) s) +
            ε * ∑ r : N.R, (∑ u : S, (Q.influence r).vec u * σ.1 u) *
              N.reactionVector r s := by
              dsimp [cp, qp]
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r _
              ring
  rw [hop]
  exact hABinj

/-- The source complex itself is a canonical source-influence vector. -/
noncomputable def sourceInfluence (y : Complex S) : SourceInfluence y where
  vec := fun s => (y s : ℝ)
  nonneg := fun s => Nat.cast_nonneg _
  pos_iff_source := fun s => by
    simpa using (Nat.cast_pos : 0 < (y s : ℝ) ↔ 0 < y s).trans
      (Nat.pos_iff_ne_zero)

/-- Data for the source-complex normality test matrix
`Mᵢⱼ = yᵢ · (y'ⱼ-yⱼ)`. -/
structure SourceMinorData (N : Network S) (I : Type)
    [Fintype I] [DecidableEq I] where
  reaction : I → N.R
  card_eq_rank : Fintype.card I = N.stoichRank

noncomputable def SourceMinorData.matrix {N : Network S} {I : Type}
    [Fintype I] [DecidableEq I] (D : N.SourceMinorData I) : Matrix I I ℝ :=
  fun i j => ∑ s : S, ((N.reaction (D.reaction i)).source s : ℝ) *
    N.reactionVector (D.reaction j) s

/-- Source-minor certificate. -/
structure SourceMinorCertificate (N : Network S) (I : Type)
    [Fintype I] [DecidableEq I] extends N.SourceMinorData I where
  det_ne_zero : (SourceMinorData.matrix toSourceMinorData).det ≠ 0

/-- A nonzero source-complex minor implies weak normality. -/
theorem weaklyNormal_of_sourceMinorCertificate
    (N : Network S) {I : Type} [Fintype I] [DecidableEq I]
    (C : N.SourceMinorCertificate I) : N.WeaklyNormal := by
  let D : N.WeakNormalMinorData I := {
    reaction := C.reaction
    influence := fun i => sourceInfluence (N.reaction (C.reaction i)).source
    card_eq_rank := C.card_eq_rank }
  have hmat : D.matrix = C.matrix := by
    ext i j
    rfl
  have hdet : D.matrix.det ≠ 0 := by
    rw [hmat]
    exact C.det_ne_zero
  exact N.weaklyNormal_of_minorCertificate
    { toWeakNormalMinorData := D, det_ne_zero := hdet }

/-- Classical stronger conclusion: the source-minor criterion actually gives
normality, not merely weak normality (Shinar--Feinberg Corollary 7.15). -/
theorem normal_of_sourceMinorCertificate
    (N : Network S) {I : Type} [Fintype I] [DecidableEq I]
    (C : N.SourceMinorCertificate I) : N.Normal := by
  classical
  let D : N.WeakNormalMinorData I := {
    reaction := C.reaction
    influence := fun i => sourceInfluence (N.reaction (C.reaction i)).source
    card_eq_rank := C.card_eq_rank }
  have hmatDC : D.matrix = C.matrix := by ext i j; rfl
  let W : N.WeakNormalMinorCertificate I := {
    toWeakNormalMinorData := D
    det_ne_zero := by simpa [hmatDC] using C.det_ne_zero }
  let v : I → N.stoichSubspace := fun i =>
    ⟨N.reactionVector (C.reaction i), N.reactionVector_mem_stoichSubspace _⟩
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : ∑ j : I, g j • N.reactionVector (C.reaction j) = 0 := by
      have hgv := congrArg Subtype.val hg
      simpa [v] using hgv
    exact (Fintype.linearIndependent_iff.mp W.selected_reactionVectors_linearIndependent g hg') i
  have hcard : Fintype.card I = Module.finrank ℝ N.stoichSubspace := by
    simpa [Network.stoichRank] using C.card_eq_rank
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  let b : Module.Basis I ℝ N.stoichSubspace := Module.Basis.mk hli hspan.ge
  let A : N.stoichSubspace →ₗ[ℝ] N.stoichSubspace := {
    toFun := fun σ => ⟨∑ i : I,
      (∑ s : S, ((N.reaction (C.reaction i)).source s : ℝ) * σ.1 s) •
        N.reactionVector (C.reaction i),
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
        (N.reactionVector_mem_stoichSubspace (C.reaction i)))⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      change (∑ i : I, (∑ s : S, ((N.reaction (C.reaction i)).source s : ℝ) *
          (x.1 s + y.1 s)) • N.reactionVector (C.reaction i)) =
        (∑ i : I, (∑ s : S, ((N.reaction (C.reaction i)).source s : ℝ) * x.1 s) •
          N.reactionVector (C.reaction i)) +
        (∑ i : I, (∑ s : S, ((N.reaction (C.reaction i)).source s : ℝ) * y.1 s) •
          N.reactionVector (C.reaction i))
      simp only [mul_add, Finset.sum_add_distrib, add_smul]
    map_smul' := by
      intro c x
      apply Subtype.ext
      change (∑ i : I, (∑ s : S, ((N.reaction (C.reaction i)).source s : ℝ) *
          (c * x.1 s)) • N.reactionVector (C.reaction i)) =
        c • (∑ i : I, (∑ s : S, ((N.reaction (C.reaction i)).source s : ℝ) *
          x.1 s) • N.reactionVector (C.reaction i))
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring }
  have hmat : LinearMap.toMatrix b b A = C.matrix := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hb : b j = v j := Module.Basis.mk_apply hli hspan.ge j
    rw [hb]
    have hAv : A (v j) = ∑ k : I,
        (∑ s : S, ((N.reaction (C.reaction k)).source s : ℝ) *
          N.reactionVector (C.reaction j) s) • v k := by
      apply Subtype.ext
      simp [A, v]
    rw [hAv]
    calc
      b.coord i (∑ k : I,
          (∑ s : S, ((N.reaction (C.reaction k)).source s : ℝ) *
            N.reactionVector (C.reaction j) s) • v k)
          = ∑ k : I, (∑ s : S, ((N.reaction (C.reaction k)).source s : ℝ) *
              N.reactionVector (C.reaction j) s) * b.coord i (v k) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro k _
              rw [map_smul]
              rfl
      _ = ∑ s : S, ((N.reaction (C.reaction i)).source s : ℝ) *
          N.reactionVector (C.reaction j) s := by
        rw [Finset.sum_eq_single i]
        · rw [Module.Basis.mk_coord_apply_eq, mul_one]
        · intro k _ hki
          rw [Module.Basis.mk_coord_apply_ne hki, mul_zero]
        · simp
      _ = C.matrix i j := rfl
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    have hz : A.det = 0 := (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hne
    have hdetA : A.det ≠ 0 := by
      rw [← LinearMap.det_toMatrix b, hmat]
      exact C.det_ne_zero
    exact hdetA hz
  let q : PositiveSpeciesWeights S := {
    weight := fun _ => 1
    positive := fun _ => one_pos }
  let eta0 : PositiveReactionWeights N := {
    weight := fun _ => 1
    positive := fun _ => one_pos }
  let B : N.stoichSubspace →ₗ[ℝ] N.stoichSubspace :=
    N.normalityOperatorOnStoich q eta0
  obtain ⟨ε, hε, hABinj⟩ := exists_pos_injective_add_smul A B hAinj
  let eta : PositiveReactionWeights N := {
    weight := fun r => ε + ∑ i : I, if C.reaction i = r then 1 else 0
    positive := fun r => by
      have hnonneg : 0 ≤ ∑ i : I, if C.reaction i = r then (1 : ℝ) else 0 := by
        apply Finset.sum_nonneg
        intro i _
        split <;> norm_num
      linarith }
  refine ⟨⟨q, eta, ?_⟩⟩
  have hop : N.normalityOperatorOnStoich q eta = A + ε • B := by
    apply LinearMap.ext
    intro σ
    apply Subtype.ext
    change N.normalityOperator q eta σ.1 =
      (A σ).1 + ε • (N.normalityOperatorOnStoich q eta0 σ).1
    have hAval : (A σ).1 = ∑ i : I,
        (∑ u : S, ((N.reaction (C.reaction i)).source u : ℝ) * σ.1 u) •
          N.reactionVector (C.reaction i) := rfl
    have hBval : (N.normalityOperatorOnStoich q eta0 σ).1 =
        N.normalityOperator q eta0 σ.1 := rfl
    rw [hAval, hBval]
    ext s
    simp only [normalityOperator, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
      weightedComplexPairing, q, eta, eta0, one_mul]
    let cp : I → ℝ := fun i => ∑ u : S,
      ((N.reaction (C.reaction i)).source u : ℝ) * σ.1 u
    let qp : N.R → ℝ := fun r => ∑ u : S,
      ((N.reaction r).source u : ℝ) * σ.1 u
    change (∑ r : N.R,
        ((ε + ∑ i : I, if C.reaction i = r then 1 else 0) * qp r) *
          N.reactionVector r s) =
      (∑ i : I, cp i * N.reactionVector (C.reaction i) s) +
        ε * ∑ r : N.R, qp r * N.reactionVector r s
    calc
      (∑ r : N.R,
          ((ε + ∑ i : I, if C.reaction i = r then 1 else 0) * qp r) *
            N.reactionVector r s)
          = (∑ r : N.R, ((∑ i : I, if C.reaction i = r then 1 else 0) * qp r) *
              N.reactionVector r s) +
            ∑ r : N.R, (ε * qp r) * N.reactionVector r s := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro r _
              ring
      _ = (∑ i : I, cp i * N.reactionVector (C.reaction i) s) +
            ∑ r : N.R, (ε * qp r) * N.reactionVector r s := by
              congr 1
              calc
                (∑ r : N.R, ((∑ i : I, if C.reaction i = r then 1 else 0) * qp r) *
                    N.reactionVector r s)
                    = ∑ r : N.R, ∑ i : I,
                        (if C.reaction i = r then qp r else 0) * N.reactionVector r s := by
                          apply Finset.sum_congr rfl
                          intro r _
                          rw [Finset.sum_mul, Finset.sum_mul]
                          apply Finset.sum_congr rfl
                          intro i _
                          split_ifs <;> ring
                    _ = ∑ i : I, ∑ r : N.R,
                        (if C.reaction i = r then qp r else 0) * N.reactionVector r s := by
                          rw [Finset.sum_comm]
                    _ = ∑ i : I, cp i * N.reactionVector (C.reaction i) s := by
                          apply Finset.sum_congr rfl
                          intro i _
                          rw [Finset.sum_eq_single (C.reaction i)]
                          · simp [cp, qp]
                          · intro r _ hr
                            simp [Ne.symm hr]
                          · simp
      _ = (∑ i : I, cp i * N.reactionVector (C.reaction i) s) +
            ε * ∑ r : N.R, qp r * N.reactionVector r s := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r _
              ring
  rw [hop]
  exact hABinj

end Network
end CRNT
