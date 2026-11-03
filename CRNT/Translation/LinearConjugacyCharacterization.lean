import CRNT.Translation.LinearConjugacy
import CRNT.Identifiability.RateConstants

/-!
# Characterization of linear conjugacy (Johnston–Siegel 2011)

Two mass-action systems `(N, κ)` and `(M, κ')` on the same species are **linearly conjugate**
by the positive diagonal map `x ↦ c ∘ x` when `f'_{κ'}(c ∘ x) = c ∘ f_κ(x)`
(`CRNT.Network.MassActionLinearlyConjugate`). Writing `W_y = ∑_{source r = y} κ_r (y'_r - y)`
for the source-wise weighted reaction vectors, `f_κ(x) = ∑_y x^y W_y`, and comparing
coefficients of the (linearly independent) monomials `x^y` gives the network-level
characterization (Johnston–Siegel, *Linear conjugacy of chemical reaction networks*,
J. Math. Chem. 49 (2011), Theorem 2): the systems are conjugate by `c` iff for every complex `y`

`c^y · W'_y = c ∘ W_y`.

Main results:
* `CRNT.Network.sum_regroup_by_source`: `f_κ(x) = ∑_y x^y W_y` over any finite set of complexes
  containing the sources.
* `CRNT.Network.massActionLinearlyConjugate_iff`: the Johnston–Siegel characterization.
* `CRNT.Network.massActionLinearlyConjugate_of_eqOn_positive`: agreement on the positive
  orthant already forces conjugacy on all of `ℝ^S`.
* `CRNT.Network.dynamicallyEquivalent_iff_sourceWeightedSum_eq`: the case `c = 1`
  (dynamical equivalence, Craciun–Pantea 2008).
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Regrouping by source complex.** For any finite set `U` of complexes containing every
source, `∑_r (c_r v_r(s)) x^{y_r} = ∑_{y ∈ U} W_y(s) x^y`. -/
theorem sum_regroup_by_source (N : Network S) (c : N.R → ℝ) (U : Finset (Complex S))
    (hU : ∀ r, (N.reaction r).source ∈ U) (x : Concentration S) (s : S) :
    ∑ r, (c r * N.reactionVector r s) * (N.reaction r).source.massActionMonomial x =
      ∑ y ∈ U, N.sourceWeightedSum c y s * y.massActionMonomial x := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun r => (N.reaction r).source) (t := U)
    (fun r _ => hU r)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [sourceWeightedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [(Finset.mem_filter.mp hr).2]

omit [DecidableEq S] in
theorem massActionMonomial_mul (y : Complex S) (a x : Concentration S) :
    y.massActionMonomial (fun s => a s * x s) = y.massActionMonomial a * y.massActionMonomial x := by
  unfold Complex.massActionMonomial
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s _ => mul_pow _ _ _

/-- **Johnston–Siegel characterization of linear conjugacy.** `(N, κ)` and `(M, κ')` are
linearly conjugate by the positive diagonal change `c` iff `c^y W'_y = c ∘ W_y` for every
complex `y`. -/
theorem massActionLinearlyConjugate_iff (N M : Network S) (κN : N.RateConstants)
    (κM : M.RateConstants) (D : PositiveDiagonalChange S) :
    MassActionLinearlyConjugate N M κN κM D ↔
      ∀ (y : Complex S) (s : S),
        y.massActionMonomial D.scale * M.sourceWeightedSum κM.k y s =
          D.scale s * N.sourceWeightedSum κN.k y s := by
  classical
  constructor
  · intro h y s
    -- compare coefficients over the disjoint union of reaction index types
    let src : M.R ⊕ N.R → Complex S := fun i => match i with
      | Sum.inl r => (M.reaction r).source
      | Sum.inr r => (N.reaction r).source
    let a : M.R ⊕ N.R → ℝ := fun i => match i with
      | Sum.inl r => (κM.k r * M.reactionVector r s) * (M.reaction r).source.massActionMonomial D.scale
      | Sum.inr r => -(D.scale s * (κN.k r * N.reactionVector r s))
    have hz := Complex.sum_massActionMonomial_eq_zero src a (fun x _ => by
      have hx := congrFun (h x) s
      simp only [massActionVectorField_apply, massActionRate, PositiveDiagonalChange.map] at hx
      rw [Fintype.sum_sum_type]
      simp only [src, a]
      rw [Finset.mul_sum] at hx
      have e1 : ∀ r : M.R, (κM.k r * M.reactionVector r s) *
          (M.reaction r).source.massActionMonomial D.scale *
            (M.reaction r).source.massActionMonomial x =
          κM.k r * (M.reaction r).source.massActionMonomial (D.map x) *
            M.reactionVector r s := by
        intro r
        rw [show D.map x = fun s => D.scale s * x s from rfl, massActionMonomial_mul]; ring
      have e2 : ∀ r : N.R, -(D.scale s * (κN.k r * N.reactionVector r s)) *
          (N.reaction r).source.massActionMonomial x =
          -(D.scale s * (κN.k r * (N.reaction r).source.massActionMonomial x *
            N.reactionVector r s)) := by
        intro r; ring
      simp_rw [e1, e2, Finset.sum_neg_distrib, hx]
      ring) y
    rw [Finset.sum_filter, Fintype.sum_sum_type] at hz
    simp only [src, a] at hz
    simp only [sourceWeightedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_filter]
    have h1 : ∑ r : M.R, (if (M.reaction r).source = y then
          (κM.k r * M.reactionVector r s) * (M.reaction r).source.massActionMonomial D.scale
          else 0) =
        ∑ r : M.R, y.massActionMonomial D.scale *
          (if (M.reaction r).source = y then κM.k r * M.reactionVector r s else 0) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs with hr
      · rw [hr]; ring
      · simp
    have h2 : ∑ r : N.R, (if (N.reaction r).source = y then
          -(D.scale s * (κN.k r * N.reactionVector r s)) else 0) =
        -∑ r : N.R, D.scale s *
          (if (N.reaction r).source = y then κN.k r * N.reactionVector r s else 0) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> simp
    rw [h1, h2] at hz
    linarith
  · intro h x
    funext s
    let U := Finset.univ.image (fun r => (M.reaction r).source) ∪
      Finset.univ.image (fun r => (N.reaction r).source)
    have hUM : ∀ r, (M.reaction r).source ∈ U := fun r =>
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))
    have hUN : ∀ r, (N.reaction r).source ∈ U := fun r =>
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))
    simp only [PositiveDiagonalChange.map]
    rw [massActionVectorField_apply_eq_sum_monomial, massActionVectorField_apply_eq_sum_monomial,
      sum_regroup_by_source M κM.k U hUM, sum_regroup_by_source N κN.k U hUN, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show D.map x = fun s => D.scale s * x s from rfl, massActionMonomial_mul]
    have := h y s
    calc M.sourceWeightedSum κM.k y s *
          (y.massActionMonomial D.scale * y.massActionMonomial x)
        = (y.massActionMonomial D.scale * M.sourceWeightedSum κM.k y s) *
            y.massActionMonomial x := by ring
      _ = D.scale s * (N.sourceWeightedSum κN.k y s * y.massActionMonomial x) := by
          rw [this]; ring

/-- Conjugacy on the positive orthant already implies conjugacy everywhere. -/
theorem massActionLinearlyConjugate_of_eqOn_positive (N M : Network S) (κN : N.RateConstants)
    (κM : M.RateConstants) (D : PositiveDiagonalChange S)
    (h : ∀ x : Concentration S, x.Positive →
      M.massActionVectorField κM (D.map x) = D.map (N.massActionVectorField κN x)) :
    MassActionLinearlyConjugate N M κN κM D := by
  classical
  rw [massActionLinearlyConjugate_iff]
  intro y s
  -- rerun the coefficient comparison using only positive points
  let src : M.R ⊕ N.R → Complex S := fun i => match i with
    | Sum.inl r => (M.reaction r).source
    | Sum.inr r => (N.reaction r).source
  let a : M.R ⊕ N.R → ℝ := fun i => match i with
    | Sum.inl r => (κM.k r * M.reactionVector r s) * (M.reaction r).source.massActionMonomial D.scale
    | Sum.inr r => -(D.scale s * (κN.k r * N.reactionVector r s))
  have hz := Complex.sum_massActionMonomial_eq_zero src a (fun x hx => by
    have hx' := congrFun (h x hx) s
    simp only [massActionVectorField_apply, massActionRate, PositiveDiagonalChange.map] at hx'
    rw [Fintype.sum_sum_type]
    simp only [src, a]
    rw [Finset.mul_sum] at hx'
    have e1 : ∀ r : M.R, (κM.k r * M.reactionVector r s) *
        (M.reaction r).source.massActionMonomial D.scale *
          (M.reaction r).source.massActionMonomial x =
        κM.k r * (M.reaction r).source.massActionMonomial (D.map x) *
          M.reactionVector r s := by
      intro r
      rw [show D.map x = fun s => D.scale s * x s from rfl, massActionMonomial_mul]; ring
    have e2 : ∀ r : N.R, -(D.scale s * (κN.k r * N.reactionVector r s)) *
        (N.reaction r).source.massActionMonomial x =
        -(D.scale s * (κN.k r * (N.reaction r).source.massActionMonomial x *
          N.reactionVector r s)) := by
      intro r; ring
    simp_rw [e1, e2, Finset.sum_neg_distrib, hx']
    ring) y
  rw [Finset.sum_filter, Fintype.sum_sum_type] at hz
  simp only [src, a] at hz
  simp only [sourceWeightedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_filter]
  have h1 : ∑ r : M.R, (if (M.reaction r).source = y then
        (κM.k r * M.reactionVector r s) * (M.reaction r).source.massActionMonomial D.scale
        else 0) =
      ∑ r : M.R, y.massActionMonomial D.scale *
        (if (M.reaction r).source = y then κM.k r * M.reactionVector r s else 0) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs with hr
    · rw [hr]; ring
    · simp
  have h2 : ∑ r : N.R, (if (N.reaction r).source = y then
        -(D.scale s * (κN.k r * N.reactionVector r s)) else 0) =
      -∑ r : N.R, D.scale s *
        (if (N.reaction r).source = y then κN.k r * N.reactionVector r s else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> simp
  rw [h1, h2] at hz
  linarith

/-- **Dynamical equivalence** (conjugacy by the identity): two mass-action systems have the
same vector field iff their source-wise weighted reaction vectors agree at every complex. -/
theorem dynamicallyEquivalent_iff_sourceWeightedSum_eq (N M : Network S)
    (κN : N.RateConstants) (κM : M.RateConstants) :
    (∀ x : Concentration S, M.massActionVectorField κM x = N.massActionVectorField κN x) ↔
      ∀ y : Complex S, M.sourceWeightedSum κM.k y = N.sourceWeightedSum κN.k y := by
  have hc := massActionLinearlyConjugate_iff N M κN κM (identityDiagonalChange S)
  have hmap : ∀ x : Concentration S, (identityDiagonalChange S).map x = x := by
    intro x; funext s; simp [PositiveDiagonalChange.map, identityDiagonalChange]
  have hmono : ∀ y : Complex S, y.massActionMonomial (identityDiagonalChange S).scale = 1 := by
    intro y; simp [Complex.massActionMonomial, identityDiagonalChange]
  unfold MassActionLinearlyConjugate at hc
  simp only [hmap, hmono, one_mul] at hc
  have hs : ∀ s, (identityDiagonalChange S).scale s = 1 := by
    intro s; simp [identityDiagonalChange]
  simp only [hs, one_mul] at hc
  rw [hc]
  exact ⟨fun h y => funext (h y), fun h y s => congrFun (h y) s⟩

end Network

end CRNT
