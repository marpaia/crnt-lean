import CRNT.Equilibria.SteadyState
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.BigOperators.Fin

/-!
# Descartes' rule of signs for one-species networks

For a network with a single species the mass-action vector field is the real polynomial
`p_κ(t) = ∑_r κ_r (y'_r - y_r) t ^ {y_r}` in the concentration `t` of that species. Positive
steady states are the positive roots of `p_κ`, so Descartes' rule of signs
(`Polynomial.roots_countP_pos_le_signVariations`) bounds their number by the number of sign
changes in the coefficient sequence of `p_κ`. This is the simplest instance of the
real-root bounds for steady-state counting (Bihan–Dickenstein–Giaroli 2020; Joshi–Shiu 2017
for one-species networks).

Main results:
* `CRNT.Network.oneSpeciesPoly_eval`: the polynomial is the vector field.
* `CRNT.Network.oneSpecies_steadyState_iff_isRoot`.
* `CRNT.Network.card_positiveSteadyStates_le_signVariations`: the Descartes bound.
* `CRNT.Network.positiveSteadyState_unique_of_signVariations_le_one`: at most one sign change
  rules out multistationarity.
-/

/-! ## Sign variations are bounded by the number of monomials -/

section
open Polynomial

theorem List.signVariations_le_length_filter {α : Type*} [Zero α] [LinearOrder α] (l : List α) :
    l.signVariations ≤ (l.filter (· ≠ 0)).length - 1 := by
  unfold List.signVariations
  have h1 := (((l.map SignType.sign).filter (· ≠ 0)).destutter_sublist (· ≠ ·)).length_le
  have h2 : ((l.map SignType.sign).filter (· ≠ 0)).length = (l.filter (· ≠ 0)).length := by
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro x _
    simp [sign_eq_zero_iff]
  omega

theorem List.length_filter_range_ne_zero {R : Type*} [Zero R] [DecidableEq R] (f : ℕ → R)
    (n : ℕ) : ((List.range n).filter (fun i => decide (f i ≠ 0))).length =
      ∑ i ∈ Finset.range n, if f i ≠ 0 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : f n = 0 <;> simp [h]

theorem Polynomial.length_filter_coeffList {R : Type*} [Semiring R] [LinearOrder R] (P : R[X]) :
    (P.coeffList.filter (· ≠ 0)).length = P.support.card := by
  classical
  by_cases hP : P = 0
  · simp [hP]
  unfold coeffList
  rw [withBotSucc_degree_eq_natDegree_add_one hP, List.filter_map, List.length_map,
    List.filter_reverse, List.length_reverse]
  have : P.support = (Finset.range (P.natDegree + 1)).filter (fun i => P.coeff i ≠ 0) := by
    ext i
    simp only [mem_support_iff, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact ⟨Nat.lt_succ_of_le (le_natDegree_of_ne_zero h), h⟩
    · exact fun h => h.2
  rw [this, Finset.card_filter, ← List.length_filter_range_ne_zero]
  rfl

theorem Polynomial.signVariations_le_card_support_sub_one {R : Type*} [Semiring R]
    [LinearOrder R] (P : Polynomial R) : P.signVariations ≤ P.support.card - 1 := by
  rw [Polynomial.signVariations, ← Polynomial.length_filter_coeffList]
  exact List.signVariations_le_length_filter _

end

namespace CRNT

namespace Network

open Polynomial
open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] [Unique S]

/-- The mass-action vector field of a one-species network, as a polynomial in the
concentration of the unique species. -/
noncomputable def oneSpeciesPoly (N : Network S) (κ : RateConstants N) : ℝ[X] :=
  ∑ r, C (κ.k r * N.reactionVector r default) * X ^ ((N.reaction r).source default)

/-- The constant concentration `t` of the unique species. -/
def oneSpeciesConc (t : ℝ) : Concentration S := fun _ => t

theorem oneSpeciesPoly_eval (N : Network S) (κ : RateConstants N) (t : ℝ) (s : S) :
    (N.oneSpeciesPoly κ).eval t = N.massActionVectorField κ (oneSpeciesConc t) s := by
  rw [Unique.eq_default s, oneSpeciesPoly, eval_finsetSum, massActionVectorField_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, massActionRate, Complex.massActionMonomial,
    Fintype.prod_unique]
  simp only [oneSpeciesConc]
  ring

theorem oneSpecies_steadyState_iff_isRoot (N : Network S) (κ : RateConstants N) (t : ℝ) :
    N.IsMassActionSteadyState κ (oneSpeciesConc t) ↔ (N.oneSpeciesPoly κ).IsRoot t := by
  constructor
  · intro h
    rw [IsRoot.def, oneSpeciesPoly_eval N κ t default]
    exact h default
  · intro h s
    rw [← oneSpeciesPoly_eval N κ t s]
    exact h

omit [DecidableEq S] [Fintype S] in
/-- Every concentration of a one-species network is constant. -/
theorem eq_oneSpeciesConc (x : Concentration S) : x = oneSpeciesConc (x default) := by
  funext s; rw [Unique.eq_default s]; rfl

/-- **Descartes' bound.** If the one-species polynomial is not identically zero, any finite
set of positive steady-state concentrations has at most `signVariations` elements. -/
theorem card_positiveSteadyStates_le_signVariations (N : Network S) (κ : RateConstants N)
    (hP : N.oneSpeciesPoly κ ≠ 0) (T : Finset ℝ)
    (hT : ∀ t ∈ T, 0 < t ∧ N.IsMassActionSteadyState κ (oneSpeciesConc t)) :
    T.card ≤ (N.oneSpeciesPoly κ).signVariations := by
  classical
  set P := N.oneSpeciesPoly κ
  have hsub : T ⊆ (P.roots.filter (0 < ·)).toFinset := by
    intro t ht
    obtain ⟨hpos, hss⟩ := hT t ht
    rw [Multiset.mem_toFinset, Multiset.mem_filter, mem_roots hP]
    exact ⟨(oneSpecies_steadyState_iff_isRoot N κ t).mp hss, hpos⟩
  calc T.card ≤ (P.roots.filter (0 < ·)).toFinset.card := Finset.card_le_card hsub
    _ ≤ (P.roots.filter (0 < ·)).card := Multiset.toFinset_card_le _
    _ = P.roots.countP (0 < ·) := (Multiset.countP_eq_card_filter _ _).symm
    _ ≤ P.signVariations := roots_countP_pos_le_signVariations P

/-- **No multistationarity with at most one sign change.** -/
theorem positiveSteadyState_unique_of_signVariations_le_one (N : Network S)
    (κ : RateConstants N) (hP : N.oneSpeciesPoly κ ≠ 0)
    (hsv : (N.oneSpeciesPoly κ).signVariations ≤ 1) {x z : Concentration S}
    (hx : x.Positive) (hz : z.Positive) (hxs : N.IsMassActionSteadyState κ x)
    (hzs : N.IsMassActionSteadyState κ z) : x = z := by
  classical
  rw [eq_oneSpeciesConc x] at hxs
  rw [eq_oneSpeciesConc z] at hzs
  by_contra hne
  have hne' : x default ≠ z default := fun e => hne (by
    rw [eq_oneSpeciesConc x, eq_oneSpeciesConc z, e])
  have := card_positiveSteadyStates_le_signVariations N κ hP {x default, z default} (by
    intro t ht
    rcases Finset.mem_insert.mp ht with h | h
    · exact h ▸ ⟨hx default, hxs⟩
    · rw [Finset.mem_singleton] at h; exact h ▸ ⟨hz default, hzs⟩)
  rw [Finset.card_pair hne'] at this
  omega

/-- The one-species polynomial only has monomials at the reactant coefficients. -/
theorem oneSpeciesPoly_support_subset (N : Network S) (κ : RateConstants N) :
    (N.oneSpeciesPoly κ).support ⊆ Finset.univ.image (fun r => (N.reaction r).source default) := by
  classical
  intro i hi
  rw [mem_support_iff, oneSpeciesPoly, finsetSum_coeff] at hi
  by_contra hni
  apply hi
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs with h
  · exact absurd (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ r)) hni
  · rfl

/-- **Reactant-count bound.** A one-species network whose polynomial is not identically zero
has at most `m - 1` positive steady states, where `m` is the number of distinct reactant
(source) coefficients. -/
theorem card_positiveSteadyStates_le_numSources (N : Network S) (κ : RateConstants N)
    (hP : N.oneSpeciesPoly κ ≠ 0) (T : Finset ℝ)
    (hT : ∀ t ∈ T, 0 < t ∧ N.IsMassActionSteadyState κ (oneSpeciesConc t)) :
    T.card ≤ (Finset.univ.image (fun r => (N.reaction r).source default)).card - 1 := by
  classical
  calc T.card ≤ (N.oneSpeciesPoly κ).signVariations :=
        card_positiveSteadyStates_le_signVariations N κ hP T hT
    _ ≤ (N.oneSpeciesPoly κ).support.card - 1 :=
        Polynomial.signVariations_le_card_support_sub_one _
    _ ≤ _ := Nat.sub_le_sub_right (Finset.card_le_card (N.oneSpeciesPoly_support_subset κ)) 1

/-- **One-species networks with at most two reactant coefficients are not multistationary**
(cf. Joshi–Shiu, *Which small reaction networks are multistationary?*, 2017). -/
theorem positiveSteadyState_unique_of_numSources_le_two (N : Network S) (κ : RateConstants N)
    (hP : N.oneSpeciesPoly κ ≠ 0)
    (h2 : (Finset.univ.image (fun r => (N.reaction r).source default)).card ≤ 2)
    {x z : Concentration S} (hx : x.Positive) (hz : z.Positive)
    (hxs : N.IsMassActionSteadyState κ x) (hzs : N.IsMassActionSteadyState κ z) : x = z := by
  refine positiveSteadyState_unique_of_signVariations_le_one N κ hP ?_ hx hz hxs hzs
  calc (N.oneSpeciesPoly κ).signVariations ≤ (N.oneSpeciesPoly κ).support.card - 1 :=
        Polynomial.signVariations_le_card_support_sub_one _
    _ ≤ (Finset.univ.image (fun r => (N.reaction r).source default)).card - 1 :=
        Nat.sub_le_sub_right (Finset.card_le_card (N.oneSpeciesPoly_support_subset κ)) 1
    _ ≤ 1 := by omega

end Network

end CRNT
