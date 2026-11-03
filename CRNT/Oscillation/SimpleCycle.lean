import CRNT.Oscillation.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Least periods and simplicity of autonomous periodic trajectories

Bendixson--Dulac and Jordan-curve arguments need the geometric periodic orbit to be a simple closed
curve.  A raw `PeriodicTrajectory` may carry a nonminimal period, so injectivity on one displayed
period is not automatic.

For an autonomous ODE with global uniqueness, a trajectory equipped with its **least positive
period** cannot meet itself twice before that period: two such meetings would, by time translation
and uniqueness, create a smaller positive period.  This file formalizes that standard reduction.
It removes orbit-simplicity from the eventual Green/Jordan frontier.
-/

open Filter Topology

namespace CRNT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {field : E → E}

/-- Global uniqueness for exact entire solutions of an autonomous vector field.  Locally Lipschitz
fields provide this property once the corresponding global solutions exist. -/
def GlobalSolutionUnique (field : E → E) : Prop :=
  ∀ γ₁ γ₂ : ℝ → E,
    (∀ t, HasDerivAt γ₁ (field (γ₁ t)) t) →
    (∀ t, HasDerivAt γ₂ (field (γ₂ t)) t) →
    γ₁ 0 = γ₂ 0 → γ₁ = γ₂

/-- Local Lipschitz regularity gives uniqueness of entire exact solutions with the same initial
condition.  The proof globalizes local ODE uniqueness by showing the equality-time set is nonempty,
open, and closed in connected `ℝ`. -/
theorem globalSolutionUnique_of_locallyLipschitz
    (hfield : LocallyLipschitz field) : GlobalSolutionUnique field := by
  intro γ₁ γ₂ hγ₁ hγ₂ h0
  have hcont₁ : Continuous γ₁ :=
    continuous_iff_continuousAt.2 fun t => (hγ₁ t).continuousAt
  have hcont₂ : Continuous γ₂ :=
    continuous_iff_continuousAt.2 fun t => (hγ₂ t).continuousAt
  let A : Set ℝ := {t | γ₁ t = γ₂ t}
  have hclosed : IsClosed A := by
    exact isClosed_eq hcont₁ hcont₂
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change γ₁ t = γ₂ t at ht
    let xstar : E := γ₁ t
    obtain ⟨K, U, hU, hLip⟩ := hfield xstar
    have hxU : xstar ∈ U := mem_of_mem_nhds hU
    have hγ₁U : ∀ᶠ u in 𝓝 t, γ₁ u ∈ U := by
      have htend : Tendsto γ₁ (𝓝 t) (𝓝 xstar) := (hγ₁ t).continuousAt
      exact htend hU
    have hγ₂U : ∀ᶠ u in 𝓝 t, γ₂ u ∈ U := by
      have htend : Tendsto γ₂ (𝓝 t) (𝓝 xstar) := by
        have hc : Tendsto γ₂ (𝓝 t) (𝓝 (γ₂ t)) := (hγ₂ t).continuousAt
        rwa [← ht] at hc
      exact htend hU
    have hv : ∀ᶠ u in 𝓝 t,
        LipschitzOnWith K ((fun _ : ℝ => field) u) U :=
      Filter.Eventually.of_forall fun _ => hLip
    have hf : ∀ᶠ u in 𝓝 t,
        HasDerivAt γ₁ ((fun _ : ℝ => field) u (γ₁ u)) u ∧ γ₁ u ∈ U := by
      filter_upwards [hγ₁U] with u hu
      exact ⟨hγ₁ u, hu⟩
    have hg : ∀ᶠ u in 𝓝 t,
        HasDerivAt γ₂ ((fun _ : ℝ => field) u (γ₂ u)) u ∧ γ₂ u ∈ U := by
      filter_upwards [hγ₂U] with u hu
      exact ⟨hγ₂ u, hu⟩
    have huniq : γ₁ =ᶠ[𝓝 t] γ₂ :=
      ODE_solution_unique_of_eventually (v := fun _ : ℝ => field) (s := fun _ => U)
        hv hf hg ht
    show A ∈ 𝓝 t
    filter_upwards [huniq] with u hu
    exact hu
  have hclopen : IsClopen A := ⟨hclosed, hopen⟩
  have hA : A = Set.univ := hclopen.eq_univ ⟨0, h0⟩
  funext t
  have htA : t ∈ A := by rw [hA]; exact Set.mem_univ t
  exact htA

namespace PeriodicTrajectory

/-- The displayed period is the least strictly positive period of the trajectory. -/
def HasLeastPositivePeriod (P : PeriodicTrajectory field) : Prop :=
  ∀ T : ℝ, 0 < T → Function.Periodic P.orbit T → P.period ≤ T

/-- The additive subgroup of all real periods of a function. -/
def periodAddSubgroup (f : ℝ → E) : AddSubgroup ℝ where
  carrier := {T | Function.Periodic f T}
  zero_mem' := by
    intro x
    simp
  add_mem' := by
    intro a b ha hb
    exact ha.add_period hb
  neg_mem' := by
    intro a ha
    exact ha.neg

@[simp] theorem mem_periodAddSubgroup {f : ℝ → E} {T : ℝ} :
    T ∈ periodAddSubgroup f ↔ Function.Periodic f T :=
  Iff.rfl

/-- If the period subgroup of a continuous function is dense in `ℝ`, the function is constant.
Indeed, for fixed `x`, the functions `T ↦ f (x+T)` and `T ↦ f x` agree on the dense set of periods,
so continuity forces equality everywhere. -/
theorem constant_of_dense_periods
    {f : ℝ → E} (hf : Continuous f)
    (hdense : Dense (periodAddSubgroup f : Set ℝ)) :
    ∀ x y : ℝ, f x = f y := by
  intro x y
  let g : ℝ → E := fun T => f (x + T)
  let c : ℝ → E := fun _ => f x
  have hg : Continuous g := by
    dsimp [g]
    exact hf.comp (continuous_const.add continuous_id)
  have hc : Continuous c := continuous_const
  have heq : Set.EqOn g c (periodAddSubgroup f : Set ℝ) := by
    intro T hT
    change Function.Periodic f T at hT
    dsimp [g, c]
    exact hT x
  have hclosure : (Set.univ : Set ℝ) ⊆ closure (periodAddSubgroup f : Set ℝ) := by
    intro T _
    exact hdense T
  have hall : Set.EqOn g c (Set.univ : Set ℝ) :=
    heq.of_subset_closure hg.continuousOn hc.continuousOn
      (Set.subset_univ _) hclosure
  have hxy := hall (Set.mem_univ (y - x))
  dsimp [g, c] at hxy
  -- `hxy : f (x + (y - x)) = f x`; simplify the argument and flip
  rw [show x + (y - x) = y by ring] at hxy
  exact hxy.symm

/-- **Existence of a least positive period.** Every nonconstant exact periodic trajectory has some
least strictly positive period.  The proof classifies its additive subgroup of periods: the dense
case would make the continuous orbit constant, so the subgroup is cyclic; the positive generator
is then the least period.

The returned period need not equal the period originally stored in `P`; it is a canonicalization
existence theorem, not a normalization side effect on the input object. -/
theorem exists_leastPositivePeriod (P : PeriodicTrajectory field) :
    ∃ T : ℝ, 0 < T ∧ Function.Periodic P.orbit T ∧
      ∀ U : ℝ, 0 < U → Function.Periodic P.orbit U → T ≤ U := by
  let H : AddSubgroup ℝ := periodAddSubgroup P.orbit
  rcases AddSubgroup.dense_or_cyclic H with hdense | ⟨a, ha⟩
  · have hconst : ∀ x y : ℝ, P.orbit x = P.orbit y :=
      constant_of_dense_periods P.continuous_orbit hdense
    obtain ⟨t, ht⟩ := P.nonconstant
    exact False.elim (ht (hconst t 0))
  · have ha0 : a ≠ 0 := by
      intro ha_zero
      subst a
      have hp : P.period ∈ H := by
        change Function.Periodic P.orbit P.period
        exact P.periodic
      rw [ha] at hp
      have hp0 : P.period = 0 := by
        rwa [AddSubgroup.closure_singleton_zero, AddSubgroup.mem_bot] at hp
      linarith [P.period_pos]
    have habs : 0 < |a| := abs_pos.mpr ha0
    have hleast0 :
        IsLeast {y : ℝ | y ∈ AddSubgroup.closure {a} ∧ 0 < y} |a| :=
      (AddSubgroup.isLeast_of_closure_iff_eq_abs).2 ⟨rfl, habs⟩
    have habs_mem_H : |a| ∈ H := by
      rw [ha]
      exact hleast0.1.1
    refine ⟨|a|, habs, ?_, ?_⟩
    · exact habs_mem_H
    · intro U hU hper
      have hUmem : U ∈ H := hper
      rw [ha] at hUmem
      exact hleast0.2 ⟨hUmem, hU⟩

/-- A selected least positive period. -/
noncomputable def leastPositivePeriod (P : PeriodicTrajectory field) : ℝ :=
  Classical.choose P.exists_leastPositivePeriod

/-- The selected least period is positive. -/
theorem leastPositivePeriod_pos (P : PeriodicTrajectory field) :
    0 < P.leastPositivePeriod :=
  (Classical.choose_spec P.exists_leastPositivePeriod).1

/-- The selected least period is genuinely a period. -/
theorem leastPositivePeriod_periodic (P : PeriodicTrajectory field) :
    Function.Periodic P.orbit P.leastPositivePeriod :=
  (Classical.choose_spec P.exists_leastPositivePeriod).2.1

/-- Minimality of the selected positive period. -/
theorem leastPositivePeriod_le (P : PeriodicTrajectory field)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic P.orbit T) :
    P.leastPositivePeriod ≤ T :=
  (Classical.choose_spec P.exists_leastPositivePeriod).2.2 T hT hper

/-- Repackage a periodic trajectory using a least positive period while preserving its orbit and
ODE solution exactly. -/
noncomputable def leastPeriodRepresentative (P : PeriodicTrajectory field) :
    PeriodicTrajectory field where
  orbit := P.orbit
  period := P.leastPositivePeriod
  period_pos := P.leastPositivePeriod_pos
  solution := P.solution
  periodic := P.leastPositivePeriod_periodic
  nonconstant := P.nonconstant

@[simp] theorem leastPeriodRepresentative_orbit (P : PeriodicTrajectory field) :
    P.leastPeriodRepresentative.orbit = P.orbit :=
  rfl

@[simp] theorem leastPeriodRepresentative_period (P : PeriodicTrajectory field) :
    P.leastPeriodRepresentative.period = P.leastPositivePeriod :=
  rfl

/-- The normalized representative really carries its least positive period. -/
theorem leastPeriodRepresentative_hasLeastPositivePeriod (P : PeriodicTrajectory field) :
    P.leastPeriodRepresentative.HasLeastPositivePeriod := by
  intro T hT hper
  exact P.leastPositivePeriod_le hT hper

/-- Time translation preserves the exact autonomous ODE solution property. -/
theorem shifted_solution (P : PeriodicTrajectory field) (a : ℝ) :
    ∀ t, HasDerivAt (fun u => P.orbit (u + a))
      (field (P.orbit (t + a))) t := by
  intro t
  have hshift : HasDerivAt (fun u : ℝ => u + a) 1 t := by
    simpa using (hasDerivAt_id t).add_const a
  simpa [Function.comp_def] using (P.solution (t + a)).scomp t hshift

/-- If two points of an autonomous periodic orbit coincide, uniqueness makes their time difference
a period (in the forward orientation when `s ≤ t`). -/
theorem period_sub_of_eq (P : PeriodicTrajectory field)
    (huniq : GlobalSolutionUnique field) {s t : ℝ}
    (hst : s ≤ t) (heq : P.orbit s = P.orbit t) :
    Function.Periodic P.orbit (t - s) := by
  have hfun : (fun u => P.orbit (u + s)) = (fun u => P.orbit (u + t)) := by
    apply huniq
    · exact P.shifted_solution s
    · exact P.shifted_solution t
    · simpa using heq
  intro x
  have hx := congrFun hfun (x - s)
  have hleft : (x - s) + s = x := by ring
  have hright : (x - s) + t = x + (t - s) := by ring
  simpa [hleft, hright] using hx.symm

/-- **Simplicity before the least period.** With uniqueness and a least positive period, the orbit
is injective on `[0,T)`. -/
theorem injectiveOn_Ico_of_leastPeriod (P : PeriodicTrajectory field)
    (huniq : GlobalSolutionUnique field) (hleast : P.HasLeastPositivePeriod) :
    Set.InjOn P.orbit (Set.Ico 0 P.period) := by
  intro s hs t ht heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hper : Function.Periodic P.orbit (t - s) :=
      P.period_sub_of_eq huniq hst.le heq
    have hpos : 0 < t - s := sub_pos.mpr hst
    have hsmall : t - s < P.period := by
      have hs0 : 0 ≤ s := hs.1
      linarith [ht.2]
    have hlarge := hleast (t - s) hpos hper
    linarith
  · have hper : Function.Periodic P.orbit (s - t) :=
      P.period_sub_of_eq huniq hts.le heq.symm
    have hpos : 0 < s - t := sub_pos.mpr hts
    have hsmall : s - t < P.period := by
      have ht0 : 0 ≤ t := ht.1
      linarith [hs.2]
    have hlarge := hleast (s - t) hpos hper
    linarith

/-- A periodic trajectory together with the two dynamical facts that make one least-period traverse
a simple closed curve. -/
structure SimpleClosedCycle (P : PeriodicTrajectory field) : Prop where
  uniqueSolutions : GlobalSolutionUnique field
  leastPeriod : P.HasLeastPositivePeriod

/-- Every periodic trajectory of a locally Lipschitz autonomous field has a simple closed
least-period representative.  Thus simple-cycle geometry is not an extra assumption for smooth
ODEs. -/
theorem leastPeriodRepresentative_simpleClosedCycle
    (P : PeriodicTrajectory field) (hfield : LocallyLipschitz field) :
    P.leastPeriodRepresentative.SimpleClosedCycle where
  uniqueSolutions := globalSolutionUnique_of_locallyLipschitz hfield
  leastPeriod := P.leastPeriodRepresentative_hasLeastPositivePeriod

namespace SimpleClosedCycle

/-- A certified simple cycle is injective on the half-open fundamental interval. -/
theorem injOn_Ico {P : PeriodicTrajectory field} (C : P.SimpleClosedCycle) :
    Set.InjOn P.orbit (Set.Ico 0 P.period) :=
  P.injectiveOn_Ico_of_leastPeriod C.uniqueSolutions C.leastPeriod

/-- On the closed fundamental interval, the only allowed repeated endpoint is the standard closure
`0 ~ T`.  This is the exact curve-level input used by a Jordan-curve construction. -/
theorem eq_or_endpoints_of_eq {P : PeriodicTrajectory field} (C : P.SimpleClosedCycle)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) P.period)
    (ht : t ∈ Set.Icc (0 : ℝ) P.period) (heq : P.orbit s = P.orbit t) :
    s = t ∨ (s = 0 ∧ t = P.period) ∨ (s = P.period ∧ t = 0) := by
  by_cases hsT : s = P.period
  · subst s
    by_cases htT : t = P.period
    · exact Or.inl htT.symm
    · have htIco : t ∈ Set.Ico (0 : ℝ) P.period := ⟨ht.1, lt_of_le_of_ne ht.2 htT⟩
      have h0Ico : (0 : ℝ) ∈ Set.Ico 0 P.period := ⟨le_rfl, P.period_pos⟩
      have hEq0 : P.orbit t = P.orbit 0 := by
        rw [← P.closes]
        exact heq.symm
      have ht0 := C.injOn_Ico htIco h0Ico hEq0
      exact Or.inr (Or.inr ⟨rfl, ht0⟩)
  · by_cases htT : t = P.period
    · subst t
      have hsIco : s ∈ Set.Ico (0 : ℝ) P.period := ⟨hs.1, lt_of_le_of_ne hs.2 hsT⟩
      have h0Ico : (0 : ℝ) ∈ Set.Ico 0 P.period := ⟨le_rfl, P.period_pos⟩
      have hs0 : P.orbit s = P.orbit 0 := by
        rw [← P.closes]
        exact heq
      have hseq0 := C.injOn_Ico hsIco h0Ico hs0
      exact Or.inr (Or.inl ⟨hseq0, rfl⟩)
    · have hsIco : s ∈ Set.Ico (0 : ℝ) P.period := ⟨hs.1, lt_of_le_of_ne hs.2 hsT⟩
      have htIco : t ∈ Set.Ico (0 : ℝ) P.period := ⟨ht.1, lt_of_le_of_ne ht.2 htT⟩
      exact Or.inl (C.injOn_Ico hsIco htIco heq)

end SimpleClosedCycle

end PeriodicTrajectory

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {κ : N.RateConstants}

/-- Every positive mass-action periodic orbit has a simple closed representative with exactly the
same geometric orbit.  Polynomial mass-action fields are `C¹`, hence locally Lipschitz. -/
theorem PositivePeriodicOrbit.exists_simpleClosedRepresentative
    (P : N.PositivePeriodicOrbit κ) :
    ∃ Q : PeriodicTrajectory (N.massActionVectorField κ),
      Q.orbit = P.orbit ∧ Q.SimpleClosedCycle := by
  let R := P.toPeriodicTrajectory.leastPeriodRepresentative
  have hlip : LocallyLipschitz (N.massActionVectorField κ) :=
    (N.massActionVectorField_contDiff κ (n := 1)).locallyLipschitz
  exact ⟨R, rfl, P.toPeriodicTrajectory.leastPeriodRepresentative_simpleClosedCycle hlip⟩

end Network

end CRNT
