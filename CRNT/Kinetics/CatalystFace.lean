import CRNT.Kinetics.MassAction
import CRNT.Stoich.Subspace
import Mathlib.Algebra.CharZero.Infinite

/-!
# Catalyst faces of the mass-action field

Call a species `c` a **global catalyst** of a network when it occurs in every source complex.
Every mass-action rate then carries a factor `x c`, so the whole mass-action field vanishes
identically on the face `{x | x c = 0}` of concentration space — not just at isolated points.

This is elementary but it has a sharp consequence for degree-theoretic arguments on a
stoichiometric compatibility class.  Inside the affine chart `x₀ + S` of a class, the face
`{x | x c = 0}` is a coset of the hyperplane `ker (u ↦ u c)` of `S`, which is infinite whenever
`S` has dimension at least two and some reaction changes the amount of `c`.  A degree
certificate may therefore never require the zero set of the field to be finite on the whole
chart: for a network such as `A + C ⇌ 2C ⇌ B + C` it is a line.  See
`CRNT.Theorems.DeficiencyOne.DegreeExistence`, where the certificate is consequently stated
relative to its admissible domain.

* `massActionMonomial_eq_zero_of_coord_zero` — a monomial vanishes if a species it uses is absent.
* `massActionVectorField_eq_zero_of_catalyst` — the field vanishes on a global-catalyst face.
* `stoichCoord` — the coordinate functional `u ↦ u c` on the stoichiometric subspace.
* `infinite_catalystFace` — the face is infinite in the chart when `2 ≤ dim S` and `c` varies.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

omit [DecidableEq S] in
/-- A mass-action monomial vanishes whenever one of the species it involves is absent. -/
theorem massActionMonomial_eq_zero_of_coord_zero {c : Complex S} {x : Concentration S}
    {s : S} (hs : c s ≠ 0) (hx : x s = 0) : c.massActionMonomial x = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
  rw [hx]
  exact zero_pow hs

/-- **Global-catalyst faces are stationary.**  If the species `c` occurs in every source
complex then every reaction rate carries a factor `x c`, so the mass-action field vanishes
identically on the face `{x | x c = 0}`. -/
theorem massActionVectorField_eq_zero_of_catalyst
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} {c : S}
    (hsrc : ∀ r : N.R, (N.reaction r).source c ≠ 0) (hx : x c = 0) :
    N.massActionVectorField κ x = 0 := by
  funext s
  simp only [massActionVectorField_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero ?_
  intro r _
  have hr : N.massActionRate κ r x = 0 := by
    unfold massActionRate
    rw [massActionMonomial_eq_zero_of_coord_zero (hsrc r) hx, mul_zero]
  rw [hr, zero_mul]

/-- The coordinate functional `u ↦ u c` on the stoichiometric subspace. -/
def stoichCoord (N : Network S) (c : S) : N.stoichSubspace →ₗ[ℝ] ℝ :=
  (LinearMap.proj c).comp N.stoichSubspace.subtype

@[simp] theorem stoichCoord_apply (N : Network S) (c : S) (u : N.stoichSubspace) :
    N.stoichCoord c u = u.1 c := rfl

/-- **The catalyst face of a chart is infinite.**  If some reaction changes the amount of `c`
and the stoichiometric subspace has dimension at least two, the set of chart coordinates at
which `c` is absent contains a line. -/
theorem infinite_catalystFace (N : Network S) (x₀ : Concentration S) (c : S)
    (hvar : ∃ r : N.R, N.reactionVector r c ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ N.stoichSubspace) :
    {u : N.stoichSubspace | N.stoichCoord c u = -(x₀ c)}.Infinite := by
  obtain ⟨r, hr⟩ := hvar
  set w : N.stoichSubspace :=
    ⟨N.reactionVector r, N.reactionVector_mem_stoichSubspace r⟩ with hwdef
  have hw : N.stoichCoord c w ≠ 0 := hr
  set u₀ : N.stoichSubspace := (-(x₀ c) / N.stoichCoord c w) • w with hu₀def
  have hu₀ : N.stoichCoord c u₀ = -(x₀ c) := by
    rw [hu₀def, map_smul, smul_eq_mul]
    exact div_mul_cancel₀ _ hw
  have hker : LinearMap.ker (N.stoichCoord c) ≠ ⊥ := by
    intro h
    have hinj := LinearMap.ker_eq_bot.mp h
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_self] at hle
    omega
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hv0 : N.stoichCoord c v = 0 := LinearMap.mem_ker.mp hvmem
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℝ => u₀ + t • v) ?_ ?_
  · intro a b hab
    simp only [add_right_inj] at hab
    exact smul_left_injective ℝ hvne hab
  · intro t
    simp only [Set.mem_setOf_eq, map_add, hu₀, map_smul, hv0, smul_eq_mul, mul_zero, add_zero]

end Network
end CRNT
