import CRNT.Dynamics.HighCodimensionSiphonFace
import CRNT.Examples.CatalyticChain
import CRNT.Examples.OmegaPointFakeFlow

/-!
# A static model of the codimension-≥2 residual: exactly one load-bearing hypothesis

`CRNT.Dynamics.HighCodimensionSiphonFace.exists_positive_omegaPoint_of_highCodimension_siphonFace`
is the residual obligation of the Global Attractor Theorem chain.  Its consistency was debated
on the standing claim that "the model `ω = {wmax}` satisfies every static hypothesis".  This file
turns that claim into a machine-checked statement and pins down its exact scope, using the
adversarial-flow idiom of `CRNT.Examples.OmegaPointFakeFlow` on the concrete network of
`CRNT.Examples.CatalyticChain` (`A + C ⇌ 2C ⇌ B + C`, weakly reversible of deficiency zero,
`stoichRank = 2`).

**The data.**  `kap ≡ 1`, complex-balanced reference `x* = (1,1,1)` (which doubles as the start
point `x₀`), boundary equilibrium `wmax = (3,0,0)` — a genuine equilibrium, since the species `C`
occurs in every source complex and `wmax C = 0` — and the face `Pmax = {B, C}` of size two whose
projection of the stoichiometric subspace has rank two.  The flow is the contraction
`ϕ t x = wmax + e^{-t}·(x - wmax)` toward `wmax`; its orbit from `x₀` is bounded, its ω-limit set
is the singleton `{wmax}`, and `wmax` itself is a fixed point solving the ODE.

**What is machine-checked.**

* `codimTwoModel_all_but_hsol`: every hypothesis of the residual **except `hsol`** (the orbit-ODE
  premise `HasDerivAt (γ x₀) …`) holds for this data, *and the conclusion fails* — no ω-point is
  positive.  In particular `hωnn`, `hgenω`, `hωaff`, `hmaxExact`, `hzcard`, `hcodim`, `hcard`,
  `hrank` are simultaneously satisfiable with the goal false; `wmax = (3,0,1 − 1)` lies in the
  compatibility class of `x₀`, and `Pmax` is exactly its zero set.
* `codimTwoModel_not_hsol`: the model falsifies `hsol` — its orbit through `x₀` is not a
  mass-action solution.
* `codimTwoModel_not_derivable_without_hsol`: consequently the residual's conclusion is **not
  derivable from the residual's hypotheses with `hsol` deleted**.  Any proof of the residual must
  use `hsol` essentially; no argument confined to the static hypotheses (or to `hgenω`,
  `hωaff`, `hK`, …, everything else) can close it.

**What the model cannot be.**  A *genuine* mass-action orbit (`hsol`) from a positive point
converging to a boundary equilibrium while `x*` is complex balanced would contradict the Global
Attractor Conjecture itself, so no model of the full hypothesis list with the goal false can
exist once the conjecture's Theorem B is available.  The model above therefore isolates the
dynamical content of the residual precisely in `hsol`: everything else is satisfiable, and the
inconsistency of the full list (if found) must consume `hsol` — that is the toric-differential-
inclusion / zero-separating-surface content of Craciun's Theorem B.

`#print axioms` on the theorems below reports `[propext, Classical.choice, Quot.sound]`.
-/

namespace CRNT.Network

open Filter Topology Set
open scoped NNReal
open CRNT.Examples.CatalyticChain (N rxn source target rv0 rv1 rv2 rv3 stoichRank_eq)

/-- The boundary equilibrium `wmax = (3,0,0)`: species `B` and `C` vanish. -/
private def wmax : Concentration (Fin 3) := fun s => if s = 0 then 3 else 0

/-- The positive start point `x₀ = (1,1,1)`, doubling as the complex-balanced reference. -/
private def xz : Concentration (Fin 3) := fun _ => 1

/-- The codimension-two face `Pmax = {B, C}`. -/
private def Pmax : Finset (Fin 3) := {1, 2}

/-- Rate constants `κ ≡ 1`. -/
private def kap : N.RateConstants where
  k := fun _ => 1
  positive := fun _ => one_pos

/-- The contraction flow `ϕ t x = wmax + e^{-t}·(x - wmax)` toward the boundary equilibrium. -/
private noncomputable def gam : Concentration (Fin 3) → ℝ → Concentration (Fin 3) :=
  fun x t s => wmax s + Real.exp (-t) * (x s - wmax s)

private noncomputable def fakeFlow : Flow ℝ≥0 (Concentration (Fin 3)) where
  toFun := fun t x => gam x (t : ℝ)
  cont' := by
    apply continuous_pi
    intro s
    have h1 : Continuous fun a : ℝ≥0 × Concentration (Fin 3) => Real.exp (-(a.1 : ℝ)) :=
      Real.continuous_exp.comp (continuous_neg.comp (NNReal.continuous_coe.comp continuous_fst))
    have h2 : Continuous fun a : ℝ≥0 × Concentration (Fin 3) => a.2 s - wmax s :=
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

private theorem fakeFlow_apply (t : ℝ≥0) (x : Concentration (Fin 3)) :
    fakeFlow t x = gam x (t : ℝ) := rfl

private theorem coe_atTop : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
  NNReal.tendsto_coe_atTop.mpr tendsto_id

/-! ### The orbit converges to `wmax`, is bounded, and `ω = {wmax}` -/

private theorem fake_tendsto :
    Tendsto (fun t : ℝ≥0 => fakeFlow t xz) atTop (𝓝 wmax) := by
  rw [tendsto_pi_nhds]
  intro s
  have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-(t : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp coe_atTop
  have hm : Tendsto (fun t : ℝ≥0 => Real.exp (-(t : ℝ)) * (xz s - wmax s)) atTop (𝓝 0) := by
    simpa using hexp.mul_const (xz s - wmax s)
  simpa [fakeFlow_apply, gam] using tendsto_const_nhds.add hm

private theorem fake_bounded :
    ∃ K : Set (Concentration (Fin 3)), IsCompact K ∧ ∀ t : ℝ≥0, fakeFlow t xz ∈ K := by
  refine ⟨(fun r : ℝ => (fun s => wmax s + r * (xz s - wmax s) : Concentration (Fin 3))) ''
      Set.Icc 0 1, ?_, ?_⟩
  · refine isCompact_Icc.image ?_
    apply continuous_pi
    intro s
    exact continuous_const.add (continuous_id.mul continuous_const)
  · intro t
    refine ⟨Real.exp (-(t : ℝ)), ⟨(Real.exp_pos _).le, ?_⟩, rfl⟩
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.coe_nonneg)

private theorem fake_omega : omegaLimit atTop fakeFlow {xz} = {wmax} := by
  apply Set.Subset.antisymm
  · intro y hy
    rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hy
    have hle : 𝓝 y ⊓ map (fun t : ℝ≥0 => fakeFlow t xz) atTop ≤ 𝓝 y ⊓ 𝓝 wmax :=
      inf_le_inf_left _ fake_tendsto
    have hne : (𝓝 y ⊓ map (fun t : ℝ≥0 => fakeFlow t xz) atTop).NeBot := hy
    exact Set.mem_singleton_iff.mpr (eq_of_nhds_neBot (hne.mono hle))
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [mem_omegaLimit_singleton_iff_mapClusterPt]
    exact fake_tendsto.mapClusterPt

/-! ### Complex balance of `x* = (1,1,1)` -/

private theorem xz_positive : xz.Positive := fun _ => one_pos

private theorem xz_complexBalanced : N.IsComplexBalanced kap xz := by
  intro c _
  have hr01 : N.massActionRate kap (0 : Fin 4) xz = N.massActionRate kap (1 : Fin 4) xz := by
    simp [massActionRate, Complex.massActionMonomial, kap, xz]
  have hr23 : N.massActionRate kap (2 : Fin 4) xz = N.massActionRate kap (3 : Fin 4) xz := by
    simp [massActionRate, Complex.massActionMonomial, kap, xz]
  have ht0 : (N.reaction (0 : Fin 4)).target = (N.reaction (1 : Fin 4)).source := rfl
  have ht1 : (N.reaction (1 : Fin 4)).target = (N.reaction (0 : Fin 4)).source := rfl
  have ht2 : (N.reaction (2 : Fin 4)).target = (N.reaction (3 : Fin 4)).source := rfl
  have ht3 : (N.reaction (3 : Fin 4)).target = (N.reaction (2 : Fin 4)).source := rfl
  unfold inflow outflow
  show (∑ r : Fin 4, if (N.reaction r).target = c then N.massActionRate kap r xz else 0) =
    (∑ r : Fin 4, if (N.reaction r).source = c then N.massActionRate kap r xz else 0)
  rw [Fin.sum_univ_four, Fin.sum_univ_four, ht0, ht1, ht2, ht3, hr01, hr23]
  ring

/-! ### `wmax` is a genuine equilibrium: `C` occurs in every source complex -/

private theorem catalyst_src : ∀ r : N.R, (N.reaction r).source 2 ≠ 0 := by
  intro r
  fin_cases r <;> simp [N, rxn, source]

private theorem v_wmax : N.massActionVectorField kap wmax = 0 :=
  N.massActionVectorField_eq_zero_of_catalyst kap (c := 2) catalyst_src (by simp [wmax])

private theorem v_xz : N.massActionVectorField kap xz = 0 := by
  funext s
  exact (N.isMassActionSteadyState_of_isComplexBalanced kap xz_complexBalanced) s

/-! ### The zero set of `wmax` is exactly `Pmax` -/

private theorem hzeroMax_model : ∀ s, s ∈ Pmax ↔ wmax s = 0 := by
  intro s
  fin_cases s <;> simp [Pmax, wmax]

private theorem zeros_wmax :
    Finset.univ.filter (fun s => wmax s = 0) = Pmax := by
  apply Finset.ext
  intro s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  fin_cases s <;> simp [Pmax, wmax]

private theorem hwmax_model : wmax ∈ omegaLimit atTop fakeFlow {xz} := by
  rw [fake_omega]
  exact Set.mem_singleton wmax

private theorem hPmaxne_model : Pmax.Nonempty := ⟨1, by simp [Pmax]⟩

private theorem hzcard_model : ∀ z ∈ omegaLimit atTop fakeFlow {xz},
    (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card := by
  intro z hz
  rw [fake_omega, Set.mem_singleton_iff] at hz
  subst hz
  rw [zeros_wmax]

private theorem hmaxExact_model : ∀ z ∈ omegaLimit atTop fakeFlow {xz},
    (∀ s ∈ Pmax, z s = 0) → ∀ s, z s = 0 ↔ s ∈ Pmax := by
  intro z hz _ s
  rw [fake_omega, Set.mem_singleton_iff] at hz
  subst hz
  exact (hzeroMax_model s).symm

/-! ### Orbit hypotheses -/

private theorem hyp_nn : ∀ y ∈ omegaLimit atTop fakeFlow {xz},
    (y : Concentration (Fin 3)).Nonnegative := by
  intro y hy
  rw [fake_omega, Set.mem_singleton_iff] at hy
  subst hy
  intro s
  fin_cases s <;> norm_num [wmax]

private theorem hyp_gen : ∀ y ∈ omegaLimit atTop fakeFlow {xz}, ∀ t : ℝ, 0 ≤ t →
    HasDerivAt (gam y) (N.massActionVectorField kap (gam y t)) t := by
  intro y hy t _
  rw [fake_omega, Set.mem_singleton_iff] at hy
  subst hy
  have hconst : gam wmax = fun _ => wmax := by
    funext u s; simp [gam]
  rw [hconst, v_wmax]
  exact hasDerivAt_const t wmax

private theorem hyp_aff : ∀ z ∈ omegaLimit atTop fakeFlow {xz},
    (z - xz : Concentration (Fin 3)) ∈ N.stoichSubspace := by
  intro z hz
  rw [fake_omega, Set.mem_singleton_iff] at hz
  subst hz
  have hb : (wmax - xz : Concentration (Fin 3)) =
      (-2 : ℝ) • N.reactionVector (0 : Fin 4) + (-1 : ℝ) • N.reactionVector (2 : Fin 4) := by
    funext s
    fin_cases s <;> norm_num [wmax, xz, rv0, rv2]
  rw [hb]
  exact N.stoichSubspace.add_mem
    (N.stoichSubspace.smul_mem _ (N.reactionVector_mem_stoichSubspace (0 : Fin 4)))
    (N.stoichSubspace.smul_mem _ (N.reactionVector_mem_stoichSubspace (2 : Fin 4)))

/-! ### The face is codimension two: `hcodim`, `hcard`, `hrank` -/

private def pbasis : Fin 2 → Concentration (Fin 3)
  | 0 => projOn Pmax (N.reactionVector (2 : Fin 4))
  | 1 => projOn Pmax (N.reactionVector (0 : Fin 4))

private theorem pbasis_li : LinearIndependent ℝ pbasis := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h2 := congrFun h 2
    norm_num [pbasis, projOn_apply, Pmax, rv0] at h2
  · intro a h
    have h1 := congrFun h 1
    norm_num [pbasis, projOn_apply, Pmax, rv0, rv2, Pi.smul_apply] at h1

private theorem span_pbasis_eq :
    Submodule.span ℝ (Set.range pbasis) = N.stoichSubspace.map (projOn Pmax) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro q ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.mem_map_of_mem (N.reactionVector_mem_stoichSubspace (2 : Fin 4))
    · exact Submodule.mem_map_of_mem (N.reactionVector_mem_stoichSubspace (0 : Fin 4))
  · rintro q hq
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
    have hp' : p ∈ Submodule.span ℝ (Set.range N.reactionVector) := hp
    have hproj : projOn Pmax p ∈
        Submodule.span ℝ (projOn Pmax '' Set.range N.reactionVector) := by
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem hp'
    have hle : Submodule.span ℝ (projOn Pmax '' Set.range N.reactionVector)
        ≤ Submodule.span ℝ (Set.range pbasis) := by
      rw [Submodule.span_le]
      rintro q ⟨a, ha, rfl⟩
      rw [Set.mem_range] at ha
      obtain ⟨r, rfl⟩ := ha
      fin_cases r
      · exact Submodule.subset_span ⟨1, rfl⟩
      · show projOn Pmax (N.reactionVector (1 : Fin 4)) ∈
            Submodule.span ℝ (Set.range pbasis)
        rw [rv1]
        have hneg := (projOn Pmax).map_neg (N.reactionVector (0 : Fin 4))
        rw [hneg]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨1, rfl⟩)
      · exact Submodule.subset_span ⟨0, rfl⟩
      · show projOn Pmax (N.reactionVector (3 : Fin 4)) ∈
            Submodule.span ℝ (Set.range pbasis)
        rw [rv3]
        have hneg := (projOn Pmax).map_neg (N.reactionVector (2 : Fin 4))
        rw [hneg]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨0, rfl⟩)
    exact hle hproj

private theorem hcodim_model :
    2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax)) := by
  rw [← span_pbasis_eq]
  rw [finrank_span_eq_card pbasis_li]
  norm_num

private theorem hcard_model : 2 ≤ Pmax.card := by decide

private theorem hrank_model : N.stoichRank ≠ 1 := by
  rw [stoichRank_eq]
  norm_num

/-! ### The model falsifies the conclusion — and falsifies exactly `hsol` -/

private theorem goal_false : ¬ ∃ p ∈ omegaLimit atTop fakeFlow {xz}, p.Positive := by
  rintro ⟨p, hp, hpp⟩
  rw [fake_omega, Set.mem_singleton_iff] at hp
  subst hp
  have := hpp 1
  norm_num [wmax] at this

/-- **`hsol` fails for the model**: the orbit through `x₀` is not a mass-action solution.  Its
derivative at `0` is `-(x₀ - wmax) = (2,-1,-1) ≠ 0 = f(x₀)`. -/
theorem codimTwoModel_not_hsol :
    ¬ ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (gam xz) (N.massActionVectorField kap (gam xz t)) t := by
  intro h
  have hv : N.massActionVectorField kap xz = 0 := v_xz
  have hg0 : gam xz 0 = xz := by funext s; simp [gam]
  have hd0 : HasDerivAt (gam xz) 0 0 := by
    have := h 0 le_rfl
    rwa [hg0, hv] at this
  have hx : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1 : ℝ) 0 := by
    simpa using (hasDerivAt_neg' (x := (0 : ℝ))).exp
  have hsmul : HasDerivAt (fun t : ℝ => wmax + Real.exp (-t) • (xz - wmax))
      ((-1 : ℝ) • (xz - wmax)) 0 :=
    HasDerivAt.const_add wmax (hx.smul_const (xz - wmax))
  have heq : (fun t : ℝ => wmax + Real.exp (-t) • (xz - wmax)) = gam xz := by
    funext t s; simp [gam]
  rw [heq] at hsmul
  have h0 := congrFun (hd0.unique hsmul) 0
  norm_num [xz, wmax] at h0

/-- **The model.** Every hypothesis of
`exists_positive_omegaPoint_of_highCodimension_siphonFace` except the orbit-ODE premise `hsol`
holds for `N`/`kap`/`xz`/`fakeFlow`/`Pmax`/`wmax`, and the conclusion is false.  (`xz` plays
both the reference `xstar` and the start `x₀`.)  See the module docstring for the exact scope. -/
theorem codimTwoModel_all_but_hsol :
    -- `hxs`, `hcb`
    xz.Positive ∧ N.IsComplexBalanced kap xz ∧
    -- `hϕγ`
    (∀ x (t : ℝ≥0), fakeFlow t x = gam x t) ∧
    -- `hK`, `hmaps`
    (∃ K : Set (Concentration (Fin 3)), IsCompact K ∧ ∀ t : ℝ≥0, fakeFlow t xz ∈ K) ∧
    -- `hωnn`
    (∀ y ∈ omegaLimit atTop fakeFlow {xz}, Concentration.Nonnegative y) ∧
    -- `hgenω`
    (∀ y ∈ omegaLimit atTop fakeFlow {xz}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (gam y) (N.massActionVectorField kap (gam y t)) t) ∧
    -- `hωaff`
    (∀ z ∈ omegaLimit atTop fakeFlow {xz},
      (z - xz : Concentration (Fin 3)) ∈ N.stoichSubspace) ∧
    -- `hx₀` (the same point is positive)
    xz.Positive ∧
    -- `hPmaxne`, `hwmax`, `hzeroMax`, `hmaxExact`, `hzcard`
    Pmax.Nonempty ∧
    (wmax ∈ omegaLimit atTop fakeFlow {xz}) ∧
    (∀ s, s ∈ Pmax ↔ wmax s = 0) ∧
    (∀ z ∈ omegaLimit atTop fakeFlow {xz}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax) ∧
    (∀ z ∈ omegaLimit atTop fakeFlow {xz},
      (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card) ∧
    -- `hcodim`, `hcard`, `hrank`
    (2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax))) ∧
    (2 ≤ Pmax.card) ∧
    (N.stoichRank ≠ 1) ∧
    -- the conclusion fails
    ¬ ∃ p ∈ omegaLimit atTop fakeFlow {xz}, p.Positive :=
  ⟨xz_positive, xz_complexBalanced, fun _ _ => rfl, fake_bounded, hyp_nn, hyp_gen, hyp_aff,
    xz_positive, hPmaxne_model, hwmax_model, hzeroMax_model, hmaxExact_model, hzcard_model,
    hcodim_model, hcard_model, hrank_model, goal_false⟩

/-- **The residual's conclusion is not derivable from its hypotheses without `hsol`.**  This is
the precise, machine-checked form of "no static argument closes the residual": instantiate the
residual-minus-`hsol` implication at the model above and contradict the failing conclusion.  Any
proof of the residual must therefore consume `hsol` (the orbit genuinely solving the mass-action
ODE) essentially. -/
theorem codimTwoModel_not_derivable_without_hsol :
    ¬ ∀ (N : Network (Fin 3)) (κ : N.RateConstants)
        {xstar : Concentration (Fin 3)}
        {ϕ : Flow ℝ≥0 (Concentration (Fin 3))}
        {γ : Concentration (Fin 3) → ℝ → Concentration (Fin 3)}
        {x₀ : Concentration (Fin 3)} {K : Set (Concentration (Fin 3))}
        {Pmax : Finset (Fin 3)} {wmax : Concentration (Fin 3)},
      xstar.Positive → N.IsComplexBalanced κ xstar →
      (∀ x (t : ℝ≥0), ϕ t x = γ x t) →
      IsCompact K →
      (∀ t : ℝ≥0, ϕ t x₀ ∈ K) →
      (∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y) →
      (∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t) →
      (∀ z ∈ omegaLimit atTop ϕ {x₀},
        (z - x₀ : Concentration (Fin 3)) ∈ N.stoichSubspace) →
      x₀.Positive →
      Pmax.Nonempty →
      wmax ∈ omegaLimit atTop ϕ {x₀} →
      (∀ s, s ∈ Pmax ↔ wmax s = 0) →
      (∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
        ∀ s, z s = 0 ↔ s ∈ Pmax) →
      (∀ z ∈ omegaLimit atTop ϕ {x₀},
        (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card) →
      2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax)) →
      2 ≤ Pmax.card →
      N.stoichRank ≠ 1 →
      ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  intro h
  obtain ⟨K, hK, hmaps⟩ := fake_bounded
  exact goal_false
    (h N kap (xstar := xz) (ϕ := fakeFlow) (γ := gam) (x₀ := xz) (K := K)
      (Pmax := Pmax) (wmax := wmax)
      xz_positive xz_complexBalanced (fun _ _ => rfl) hK hmaps hyp_nn hyp_gen hyp_aff
      xz_positive hPmaxne_model hwmax_model hzeroMax_model hmaxExact_model hzcard_model
      hcodim_model hcard_model hrank_model)

end CRNT.Network
