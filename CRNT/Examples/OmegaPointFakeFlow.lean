import CRNT.Dynamics.GlobalAttractorTheorem
import CRNT.Dynamics.GlobalPersistence
import CRNT.Dynamics.Siphon

/-!
# Historical counterexample to unrestricted omega-point predicates

The original `PositiveOmegaPointForRates`, restated below as `UnrestrictedPositiveOmegaPoint`,
and the current `BoundaryOmegaExcluded` impose the mass-action ODE only on omega-limit points.
An arbitrary contracting flow can therefore satisfy their premises while sending a positive
initial condition to a boundary steady state. The repaired `PositiveOmegaPointForRates` also
requires the initial orbit to solve the ODE; `fake_orbit_not_massAction` verifies that this
counterexample fails that new premise.

The network is `2A ⇌ A + B`, which is weakly reversible of deficiency `2 - 1 - 1 = 0`, hence
complex-balanced at every rate vector; here `κ ≡ 1` and `x* = (1,1)`.  Its stoichiometric
subspace is `span {(-1,1)}`, and `dx_A/dt = x_A (k₂ x_B - k₁ x_A)` vanishes on `x_A = 0`, so
`b = (0,1)` is a boundary steady state lying in the positive class of `x₀ = (1/2,1/2)`.

The fake flow is `ϕ t x = b + exp (-t) • (x - b)`, a genuine `Flow ℝ≥0`.  Its orbit from `x₀` is
bounded, its omega-limit set is exactly `{b}`, and `b`'s own forward orbit is constant, so it
*does* solve the mass-action ODE.  Every listed hypothesis holds and the conclusion fails.

This refutes the two unrestricted helper predicates.  It does **not** refute
`complexBalanced_genuinePermanent`, and it does not refute
`omegaLimit_positive_of_hasNoCriticalSiphon`: the same network has the critical siphon `{A}`
(`gacN_isCriticalSiphon_A`), so that theorem's hypothesis fails here.
-/

namespace CRNT.Network

open Filter Topology Set
open scoped NNReal

/-- `r₀ : 2A → A + B`, `r₁ : A + B → 2A`. -/
private abbrev gacN : Network (Fin 2) where
  R := Fin 2
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r =>
    if r = 0 then
      { source := fun s => if s = 0 then 2 else 0
        target := fun _ => 1 }
    else
      { source := fun _ => 1
        target := fun s => if s = 0 then 2 else 0 }

private def kap : gacN.RateConstants where
  k := fun _ => 1
  positive := fun _ => one_pos

@[simp] private theorem gacN_r0 : gacN.reaction 0 =
    { source := fun s => if s = 0 then 2 else 0, target := fun _ => 1 } := rfl
@[simp] private theorem gacN_r1 : gacN.reaction 1 =
    { source := fun _ => 1, target := fun s => if s = 0 then 2 else 0 } := rfl
@[simp] private theorem rv0_A : gacN.reactionVector 0 0 = -1 := by
  norm_num [Network.reactionVector]
@[simp] private theorem rv0_B : gacN.reactionVector 0 1 = 1 := by
  norm_num [Network.reactionVector]

/-- The boundary steady state `b = (0,1)`. -/
private def bpt : Concentration (Fin 2) := fun s => if s = 0 then 0 else 1

/-- The positive initial condition `x₀ = (1/2,1/2)`. -/
private noncomputable def xz : Concentration (Fin 2) := fun _ => 1 / 2

/-- The positive complex-balanced equilibrium `x* = (1,1)`. -/
private def xst : Concentration (Fin 2) := fun _ => 1

/-! ### The network is complex-balanced at `κ ≡ 1`, `x* = (1,1)` -/

private theorem gacN_complexBalanced : gacN.IsComplexBalanced kap xst := by
  intro c _
  have hr : gacN.massActionRate kap 0 xst = gacN.massActionRate kap 1 xst := by
    simp [massActionRate, Complex.massActionMonomial, kap, xst, Fin.prod_univ_two]
  have ht0 : (gacN.reaction 0).target = (gacN.reaction 1).source := rfl
  have ht1 : (gacN.reaction 1).target = (gacN.reaction 0).source := rfl
  unfold inflow outflow
  rw [Fin.sum_univ_two, Fin.sum_univ_two, ht0, ht1, hr]
  ring

private theorem xstar_positive : Concentration.Positive xst :=
  fun _ => one_pos

/-! ### `b` is a steady state -/

private theorem v_bpt : gacN.massActionVectorField kap bpt = 0 := by
  funext s
  simp [massActionVectorField, massActionRate, Complex.massActionMonomial, kap, bpt,
    gacN_r0, gacN_r1, Fin.sum_univ_two, Fin.prod_univ_two]

/-! ### The fake flow -/

private noncomputable def gam : Concentration (Fin 2) → ℝ → Concentration (Fin 2) :=
  fun x t s => bpt s + Real.exp (-t) * (x s - bpt s)

private noncomputable def fakeFlow : Flow ℝ≥0 (Concentration (Fin 2)) where
  toFun := fun t x => gam x (t : ℝ)
  cont' := by
    apply continuous_pi
    intro s
    have h1 : Continuous fun a : ℝ≥0 × Concentration (Fin 2) => Real.exp (-(a.1 : ℝ)) :=
      Real.continuous_exp.comp (continuous_neg.comp (NNReal.continuous_coe.comp continuous_fst))
    have h2 : Continuous fun a : ℝ≥0 × Concentration (Fin 2) => a.2 s - bpt s :=
      ((continuous_apply s).comp continuous_snd).sub continuous_const
    exact continuous_const.add (h1.mul h2)
  map_add' := by
    intro t₁ t₂ x
    funext s
    simp only [gam, NNReal.coe_add, neg_add, Real.exp_add, add_sub_cancel_left]
    ring
  map_zero' := by
    intro x
    funext s
    simp [gam]

private theorem fakeFlow_apply (t : ℝ≥0) (x : Concentration (Fin 2)) :
    fakeFlow t x = gam x (t : ℝ) := rfl

private theorem coe_atTop : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
  NNReal.tendsto_coe_atTop.mpr tendsto_id

/-! ### The orbit is bounded and converges to `b` -/

private theorem fake_tendsto :
    Tendsto (fun t : ℝ≥0 => fakeFlow t xz) atTop (𝓝 bpt) := by
  rw [tendsto_pi_nhds]
  intro s
  have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-(t : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp coe_atTop
  have hm : Tendsto (fun t : ℝ≥0 => Real.exp (-(t : ℝ)) * (xz s - bpt s)) atTop (𝓝 0) := by
    simpa using hexp.mul_const (xz s - bpt s)
  simpa [fakeFlow_apply, gam] using tendsto_const_nhds.add hm

private theorem fake_bounded :
    ∃ K : Set (Concentration (Fin 2)), IsCompact K ∧ ∀ t : ℝ≥0, fakeFlow t xz ∈ K := by
  refine ⟨(fun r : ℝ => (fun s => bpt s + r * (xz s - bpt s) : Concentration (Fin 2))) ''
      Set.Icc 0 1, ?_, ?_⟩
  · refine isCompact_Icc.image ?_
    apply continuous_pi
    intro s
    exact continuous_const.add (continuous_id.mul continuous_const)
  · intro t
    refine ⟨Real.exp (-(t : ℝ)), ⟨(Real.exp_pos _).le, ?_⟩, rfl⟩
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.coe_nonneg)

private theorem fake_omega : omegaLimit atTop fakeFlow {xz} = {bpt} := by
  apply Set.Subset.antisymm
  · intro y hy
    rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hy
    have hle : 𝓝 y ⊓ map (fun t : ℝ≥0 => fakeFlow t xz) atTop ≤ 𝓝 y ⊓ 𝓝 bpt :=
      inf_le_inf_left _ fake_tendsto
    have hne : (𝓝 y ⊓ map (fun t : ℝ≥0 => fakeFlow t xz) atTop).NeBot := hy
    exact Set.mem_singleton_iff.mpr (eq_of_nhds_neBot (hne.mono hle))
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [mem_omegaLimit_singleton_iff_mapClusterPt]
    exact fake_tendsto.mapClusterPt

/-! ### Every listed hypothesis holds -/

private theorem hyp_nn : ∀ y ∈ omegaLimit atTop fakeFlow {xz}, (y : Concentration (Fin 2)).Nonnegative := by
  intro y hy
  rw [fake_omega, Set.mem_singleton_iff] at hy
  subst hy
  intro s
  fin_cases s <;> simp [bpt]

private theorem hyp_gen : ∀ y ∈ omegaLimit atTop fakeFlow {xz}, ∀ t : ℝ, 0 ≤ t →
    HasDerivAt (gam y) (gacN.massActionVectorField kap (gam y t)) t := by
  intro y hy t _
  rw [fake_omega, Set.mem_singleton_iff] at hy
  subst hy
  have hconst : gam bpt = fun _ => bpt := by
    funext u s; simp [gam]
  rw [hconst, v_bpt]
  exact hasDerivAt_const t bpt

private theorem hyp_aff : ∀ z ∈ omegaLimit atTop fakeFlow {xz},
    (z - xz : Concentration (Fin 2)) ∈ gacN.stoichSubspace := by
  intro z hz
  rw [fake_omega, Set.mem_singleton_iff] at hz
  subst hz
  have hb : (bpt - xz : Concentration (Fin 2)) = (1 / 2 : ℝ) • gacN.reactionVector 0 := by
    funext s
    fin_cases s <;> norm_num [bpt, xz]
  rw [hb]
  exact Submodule.smul_mem _ _ (gacN.reactionVector_mem_stoichSubspace 0)

private theorem hyp_x0 : xz.Positive := by
  intro s; norm_num [xz]

/-! ### The refutations -/

/-- The **original, unrestricted** form of `PositiveOmegaPointForRates`, restated here verbatim
so that the refutation below is independent of any later repair to the library definition.  The
only difference from the repaired `PositiveOmegaPointForRates` is the absence of the orbit-ODE
premise on `γ x₀`. -/
def UnrestrictedPositiveOmegaPoint {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S},
    (∀ x (t : ℝ≥0), ϕ t x = γ x t) →
    (∃ K : Set (Concentration S), IsCompact K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t) →
    (∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace) →
    x₀.Positive →
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive

/-- **The unrestricted omega-point predicate is false**, even at complex-balanced rates. -/
theorem gacN_not_unrestrictedPositiveOmegaPoint :
    ¬ gacN.UnrestrictedPositiveOmegaPoint kap := by
  intro h
  obtain ⟨p, hp, hppos⟩ :=
    h (ϕ := fakeFlow) (γ := gam) (x₀ := xz) (fun _ _ => rfl) fake_bounded
      hyp_nn hyp_gen hyp_aff hyp_x0
  rw [fake_omega, Set.mem_singleton_iff] at hp
  subst hp
  exact absurd (hppos 0) (by simp [bpt])

/-- **`BoundaryOmegaExcluded` is false**, by the same construction.  Left unrepaired for now:
the counterexample network fails the `HasNoCriticalSiphon` hypothesis of the only theorem that
produces it, so the conditional result is untouched. -/
theorem gacN_not_boundaryOmegaExcluded : ¬ gacN.BoundaryOmegaExcluded kap := by
  intro h
  have hb : bpt ∈ omegaLimit atTop fakeFlow {xz} := by
    rw [fake_omega]; exact Set.mem_singleton _
  have hpos := h (ϕ := fakeFlow) (γ := gam) (x₀ := xz) (fun _ _ => rfl) fake_bounded
    hyp_nn hyp_gen hyp_aff hyp_x0 bpt hb
  exact absurd (hpos 0) (by simp [bpt])

/-- The repair is exactly what blocks this construction: the fake flow's orbit through `x₀` is
**not** a mass-action solution.  Its derivative at `0` is `-(x₀ - b) = (-1/2, 1/2)`, while the
mass-action field vanishes at `x₀` because the two reaction rates are both `1/4` there and the
reaction vectors cancel.

So the repaired `PositiveOmegaPointForRates`, which demands the orbit ODE, is *not* refuted by
this flow. -/
theorem fake_orbit_not_massAction :
    ¬ (∀ t : ℝ, 0 ≤ t →
        HasDerivAt (gam xz) (gacN.massActionVectorField kap (gam xz t)) t) := by
  intro h
  have hv : gacN.massActionVectorField kap xz = 0 := by
    funext s
    simp only [massActionVectorField, massActionRate, Complex.massActionMonomial, kap,
      Fin.sum_univ_two, Fin.prod_univ_two]
    fin_cases s <;> norm_num [Network.reactionVector, xz]
  have hg0 : gam xz 0 = xz := by funext s; simp [gam]
  have hd0 : HasDerivAt (gam xz) 0 0 := by
    have := h 0 le_rfl
    rwa [hg0, hv] at this
  have hx : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1 : ℝ) 0 := by
    simpa using (hasDerivAt_neg' (x := (0 : ℝ))).exp
  have hsmul : HasDerivAt (fun t : ℝ => bpt + Real.exp (-t) • (xz - bpt))
      ((-1 : ℝ) • (xz - bpt)) 0 :=
    HasDerivAt.const_add bpt (hx.smul_const (xz - bpt))
  have heq : (fun t : ℝ => bpt + Real.exp (-t) • (xz - bpt)) = gam xz := by
    funext t s; simp [gam]
  rw [heq] at hsmul
  have h0 := congrFun (hd0.unique hsmul) 0
  norm_num [xz, bpt] at h0

/-! ### …but the conditional no-critical-siphon theorem is untouched -/

/-- `{A}` is a siphon: both reactions produce `A` and both consume `A`. -/
private theorem gacN_isSiphon_A : gacN.IsSiphon {0} := by
  intro r _
  refine ⟨0, Finset.mem_singleton_self 0, ?_⟩
  fin_cases r <;> simp [Network.IsReactant]

/-- `{A}` is *critical*: any conservation vector supported exactly on `A` would have to be
orthogonal to `reactionVector r₀ = (-1,1)`, forcing `v A = 0`. -/
theorem gacN_isCriticalSiphon_A : gacN.IsCriticalSiphon {0} := by
  refine ⟨⟨0, Finset.mem_singleton_self 0⟩, gacN_isSiphon_A, ?_⟩
  rintro ⟨v, hvnn, hvsupp, hvcons⟩
  have hA : 0 < v 0 := (hvsupp 0).mpr (Finset.mem_singleton_self 0)
  have hB : v 1 = 0 := by
    have h1 : ¬ (0 < v 1) := by
      intro hlt
      exact absurd ((hvsupp 1).mp hlt) (by simp)
    exact le_antisymm (not_lt.mp h1) (hvnn 1)
  have hcons := hvcons 0
  rw [Fin.sum_univ_two] at hcons
  rw [rv0_A, rv0_B, hB] at hcons
  linarith

/-- So the network of the counterexample does **not** satisfy `HasNoCriticalSiphon`. -/
theorem gacN_not_hasNoCriticalSiphon : ¬ gacN.HasNoCriticalSiphon :=
  fun h => h {0} gacN_isCriticalSiphon_A

/-- The uniform comparable-growth helper also lacks the initial-orbit ODE premise.
Its conclusion would force a positive omega-point for the same fake flow, so complex balance
alone cannot supply this helper in its current unrestricted form. -/
theorem gacN_not_comparableGrowthDescentForRates :
    ¬ gacN.ComparableGrowthDescentForRates kap := by
  intro h
  obtain ⟨K, hK, hmaps⟩ := fake_bounded
  have hdesc : gacN.ComparableGrowthDescent fakeFlow xz :=
    h (ϕ := fakeFlow) (γ := gam) (x₀ := xz) (fun _ _ => rfl)
      ⟨K, hK, hK.isClosed, hmaps⟩ hyp_nn hyp_gen hyp_aff hyp_x0
  obtain ⟨p, hp, hppos⟩ :=
    gacN.omegaLimit_positive_of_comparableGrowthDescent kap
      (ϕ := fakeFlow) (γ := gam) (fun _ _ => rfl)
      hK hK.isClosed hmaps hyp_nn hyp_gen hyp_aff hyp_x0 hdesc
  rw [fake_omega, Set.mem_singleton_iff] at hp
  subst p
  exact absurd (hppos 0) (by simp [bpt])

/-! ### Summary

`gacN`/`kap` meets every hypothesis of `complexBalanced_genuinePermanent` (a positive
complex-balanced equilibrium) and refutes the original unrestricted omega-point helper.
It does not refute the repaired helper. It also has a critical siphon, so
`omegaLimit_positive_of_hasNoCriticalSiphon`
and `boundaryOmegaExcluded_of_hasNoCriticalSiphon` are *not* contradicted: their hypothesis
fails here.  `complexBalanced_genuinePermanent` itself is neither proved nor refuted. -/
theorem omegaPoint_route_dead :
    Concentration.Positive xst ∧ gacN.IsComplexBalanced kap xst ∧
      ¬ gacN.UnrestrictedPositiveOmegaPoint kap ∧
      ¬ gacN.BoundaryOmegaExcluded kap ∧
      ¬ gacN.HasNoCriticalSiphon :=
  ⟨xstar_positive, gacN_complexBalanced, gacN_not_unrestrictedPositiveOmegaPoint,
    gacN_not_boundaryOmegaExcluded, gacN_not_hasNoCriticalSiphon⟩

end CRNT.Network
