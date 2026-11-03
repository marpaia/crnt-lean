import CRNT.Deficiency.RangeKineticWR
import CRNT.Deficiency.TerminalKernelDimension
import CRNT.Deficiency.KernelDimension
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The kinetic subspace and the Feinberg–Horn coincidence theorem

For a mass-action system `(N, κ)` the **kinetic subspace** is the span of the velocities
`f(x) = ∑ r, κ r x^{y_r} (y'_r - y_r)` over all positive concentrations `x`.  It is always
contained in the stoichiometric subspace `S`, and it can be smaller.

**Theorem (Feinberg–Horn 1977).**  If every linkage class contains exactly one terminal strong
linkage class (`t = ℓ`), then the kinetic subspace equals `S` for every choice of rate
constants.  In particular this holds for every weakly reversible network.

The proof factors `f(x) = Y A_κ ψ(x)` (`massActionVectorField_eq`):

* `span {ψ(x) | x > 0}` is the whole complex space (`span_complexMonomialVector_eq_top`): a
  functional killing every `ψ(x)` defines a polynomial `∑ λ_y X^y` that vanishes on the open
  positive orthant, hence is zero by `MvPolynomial.funext_set`, and its coefficients are the
  `λ_y` because distinct complexes give distinct monomials;
* `dim ker A_κ = t` (`finrank_ker_kineticMap_eq_numTerminalSLC`) and `rank ∂ = n - ℓ`, so
  `t = ℓ` gives `Im A_κ = Im ∂` (`range_kineticMap_eq_range_incidenceMap_of_numTerminalSLC`);
* `Y (Im ∂) = S` (`complexMap_comp_incidenceMap`, `range_stoichMap`).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The kinetic subspace: the span of the mass-action velocities at positive states. -/
noncomputable def kineticSubspace (N : Network S) (κ : RateConstants N) : Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ (Set.range fun x : {x : Concentration S // x.Positive} =>
    N.massActionVectorField κ x.1)

/-- The kinetic subspace lies in the stoichiometric subspace. -/
theorem kineticSubspace_le_stoichSubspace (N : Network S) (κ : RateConstants N) :
    N.kineticSubspace κ ≤ N.stoichSubspace := by
  rw [kineticSubspace, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  show N.massActionVectorField κ x.1 ∈ N.stoichSubspace
  rw [N.massActionVectorField_eq κ x.1, ← N.range_stoichMap, ← N.complexMap_comp_incidenceMap]
  obtain ⟨v, hv⟩ := N.kineticMap_mem_range_incidenceMap κ (N.complexMonomialVector x.1)
  exact ⟨v, by rw [LinearMap.comp_apply, hv]⟩

/-- The exponent of a complex as a finitely supported function. -/
noncomputable def complexFinsuppExp (c : Complex S) : S →₀ ℕ := Finsupp.equivFunOnFinite.symm c

theorem complexFinsuppExp_injective : Function.Injective (complexFinsuppExp (S := S)) :=
  Finsupp.equivFunOnFinite.symm.injective

theorem eval_monomial_complexFinsuppExp (c : Complex S) (x : Concentration S) :
    MvPolynomial.eval x (MvPolynomial.monomial (complexFinsuppExp c) (1 : ℝ)) =
      c.massActionMonomial x := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_pow]
  rfl

/-- **Monomial vectors span.**  The vectors `ψ(x) = (x^y)_y`, `x > 0`, span the whole complex
space. -/
theorem span_complexMonomialVector_eq_top (N : Network S) :
    Submodule.span ℝ (Set.range fun x : {x : Concentration S // x.Positive} =>
      N.complexMonomialVector x.1) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set lam : N.ComplexIdx → ℝ := fun y => f (Pi.single y 1) with hlam
  have hfapply : ∀ v : N.ComplexIdx → ℝ, f v = ∑ y, lam y * v y := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show Pi.single y (v y) = v y • (Pi.single y 1 : N.ComplexIdx → ℝ) by
      ext z; by_cases h : z = y
      · subst h; simp
      · simp [h]]
    rw [map_smul, smul_eq_mul, hlam]; ring
  -- the polynomial `∑ λ_y X^y`
  set p : MvPolynomial S ℝ := ∑ y : N.ComplexIdx,
    MvPolynomial.monomial (complexFinsuppExp y.val) (lam y) with hp
  have hpeval : ∀ x : Concentration S, x.Positive → MvPolynomial.eval x p = 0 := by
    intro x hx
    have hker : f (N.complexMonomialVector x) = 0 :=
      LinearMap.mem_ker.mp (hle (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩))
    rw [hfapply] at hker
    rw [hp, map_sum]
    rw [← hker]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show MvPolynomial.monomial (complexFinsuppExp y.val) (lam y) =
      MvPolynomial.C (lam y) * MvPolynomial.monomial (complexFinsuppExp y.val) 1 by
        rw [MvPolynomial.C_mul_monomial, mul_one]]
    rw [map_mul, MvPolynomial.eval_C, eval_monomial_complexFinsuppExp]
    rfl
  have hp0 : p = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ)) (fun _ => Set.Ioi_infinite 0)
    intro x hx
    rw [map_zero]
    exact hpeval x fun s => hx s (Set.mem_univ s)
  have hlam0 : ∀ y, lam y = 0 := by
    intro y
    have hcoeff := congrArg (fun q : MvPolynomial S ℝ => q.coeff (complexFinsuppExp y.val)) hp0
    change p.coeff (complexFinsuppExp y.val) = (0 : MvPolynomial S ℝ).coeff (complexFinsuppExp y.val)
      at hcoeff
    rw [hp, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
    simp only [MvPolynomial.coeff_monomial] at hcoeff
    rw [Finset.sum_eq_single y] at hcoeff
    · simpa using hcoeff
    · intro z _ hzy
      rw [if_neg]
      intro h
      exact hzy (Subtype.ext (complexFinsuppExp_injective h))
    · intro h; exact absurd (Finset.mem_univ y) h
  apply hf0
  refine LinearMap.ext fun v => ?_
  rw [hfapply]
  simp [hlam0]

/-- **`Im A_κ = Im ∂` when every linkage class has one terminal strong linkage class.** -/
theorem range_kineticMap_eq_range_incidenceMap_of_numTerminalSLC (N : Network S)
    (ht : N.numTerminalSLC = N.numLinkageClasses) (κ : RateConstants N) :
    LinearMap.range (N.kineticMap κ) = LinearMap.range N.incidenceMap := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, rfl⟩; exact N.kineticMap_mem_range_incidenceMap κ v
  · have hrn := LinearMap.finrank_range_add_finrank_ker (N.kineticMap κ)
    have hdom : Module.finrank ℝ (N.ComplexIdx → ℝ) = N.numComplexes := by
      rw [Module.finrank_fintype_fun_eq_card]; simp only [Fintype.card_coe, numComplexes]
    have hker := N.finrank_ker_kineticMap_eq_numTerminalSLC κ
    have hinc := N.incidenceRank_add_numLinkageClasses
    have hrange_inc : Module.finrank ℝ (LinearMap.range N.incidenceMap) = N.incidenceRank := rfl
    rw [hdom, hker, ht] at hrn
    rw [hrange_inc]
    omega

/-- The kinetic subspace is the image of the kinetic map's range under `Y`. -/
theorem kineticSubspace_eq_map_range (N : Network S) (κ : RateConstants N) :
    N.kineticSubspace κ = (LinearMap.range (N.kineticMap κ)).map N.complexMap := by
  have hrange : (Set.range fun x : {x : Concentration S // x.Positive} =>
      N.massActionVectorField κ x.1) =
      (N.complexMap.comp (N.kineticMap κ)) '' (Set.range fun x : {x : Concentration S //
        x.Positive} => N.complexMonomialVector x.1) := by
    ext v
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, by rw [LinearMap.comp_apply, ← N.massActionVectorField_eq]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, by rw [LinearMap.comp_apply, ← N.massActionVectorField_eq]⟩
  rw [kineticSubspace, hrange, Submodule.span_image, N.span_complexMonomialVector_eq_top,
    Submodule.map_top, LinearMap.range_comp]

/-- **Feinberg–Horn coincidence theorem.**  If every linkage class contains exactly one terminal
strong linkage class, the kinetic subspace equals the stoichiometric subspace for every choice
of rate constants. -/
theorem kineticSubspace_eq_stoichSubspace_of_numTerminalSLC (N : Network S)
    (ht : N.numTerminalSLC = N.numLinkageClasses) (κ : RateConstants N) :
    N.kineticSubspace κ = N.stoichSubspace := by
  rw [N.kineticSubspace_eq_map_range κ, N.range_kineticMap_eq_range_incidenceMap_of_numTerminalSLC
    ht κ, ← LinearMap.range_comp, N.complexMap_comp_incidenceMap, N.range_stoichMap]

/-- Weakly reversible networks: the kinetic and stoichiometric subspaces coincide. -/
theorem kineticSubspace_eq_stoichSubspace_of_weaklyReversible (N : Network S)
    (hwr : N.WeaklyReversible) (κ : RateConstants N) :
    N.kineticSubspace κ = N.stoichSubspace := by
  rw [N.kineticSubspace_eq_map_range κ,
    N.range_kineticMap_eq_range_incidenceMap_of_weaklyReversible hwr κ,
    ← LinearMap.range_comp, N.complexMap_comp_incidenceMap, N.range_stoichMap]

end Network
end CRNT
