import CRNT.Dynamics.Contraction
import CRNT.Dynamics.EuclideanContraction
import CRNT.Dynamics.Monotone
import CRNT.Dynamics.MonotoneComparison
import CRNT.Dynamics.LaSalle
import CRNT.Dynamics.FlowConstruction
import CRNT.Dynamics.NegativeInvariance
import CRNT.Dynamics.StrongMonotone
import CRNT.Dynamics.OrthantMonotone
import CRNT.Dynamics.MassActionField
import CRNT.Kinetics.MassActionJacobian
import CRNT.Kinetics.Concentration
import Mathlib.Dynamics.Flow

/-!
# LaSalle convergence with a unique equilibrium from a strongly monotone operator

`StronglyMonotoneOperator` is the metric condition
`c * ‖x-y‖² ≤ ⟨f(x)-f(y), x-y⟩`. The combined predicate also requires
coordinate order preservation of the field. With `c > 0` it gives uniqueness of
an equilibrium. Compact absorbing-tail and strict Lyapunov/critical-set
hypotheses then yield convergence by LaSalle.

This increasing-operator condition is different from strong order preservation
of an ODE flow. These results do not formalize Hirsch's almost-everywhere
generic convergence theorem for strongly monotone flows.
-/

open Set Filter Topology
open scoped BigOperators NNReal

namespace CRNT

variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable def euclideanInner (x y : Concentration S) : ℝ := ∑ s, x s * y s

noncomputable def euclideanSqNorm (x : Concentration S) : ℝ := ∑ s, x s ^ 2

def StronglyMonotoneOperator (f : Concentration S → Concentration S) (c : ℝ) : Prop :=
  ∀ x y, c * euclideanSqNorm (x - y) ≤ euclideanInner (f x - f y) (x - y)

def OrderPreservingStronglyMonotoneOperator (f : Concentration S → Concentration S) (c : ℝ) : Prop :=
  (∀ x y, x ≤ y → f x ≤ f y) ∧ StronglyMonotoneOperator f c

theorem stronglyMonotoneOperator_mono {f : Concentration S → Concentration S} {c : ℝ}
    (h : OrderPreservingStronglyMonotoneOperator f c) : ∀ x y, x ≤ y → f x ≤ f y :=
  h.1

theorem stronglyMonotoneOperator_unique_equilibrium {f : Concentration S → Concentration S} {c : ℝ}
    (hc : 0 < c) (h : OrderPreservingStronglyMonotoneOperator f c) {a b : Concentration S}
    (ha : f a = 0) (hb : f b = 0) : a = b := by
  have hsm := h.2
  have h1 : c * euclideanSqNorm (a - b) ≤ 0 := by
    have := hsm a b
    rw [ha, hb] at this
    have hinner : euclideanInner (0 : Concentration S) (a - b) = 0 := by
      unfold euclideanInner; simp
    simpa [hinner] using this
  have hsq : euclideanSqNorm (a - b) ≤ 0 := by
    nlinarith [hc, h1]
  have hzero : ∀ s, a s - b s = 0 := by
    intro s
    have hterm : (a s - b s) ^ 2 ≤ euclideanSqNorm (a - b) := by
      unfold euclideanSqNorm
      apply Finset.single_le_sum (f := fun s' => (a s' - b s') ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ s)
    have : (a s - b s) ^ 2 = 0 := by
      nlinarith [hterm, hsq, sq_nonneg (a s - b s)]
    exact sq_eq_zero_iff.mp this
  funext s
  linarith [hzero s]

theorem stronglyMonotoneOperator_equilibrium_orderConvex {f : Concentration S → Concentration S} {c : ℝ}
    (hc : 0 < c) (h : OrderPreservingStronglyMonotoneOperator f c) (E : Set (Concentration S))
    (hE : E = {x | f x = 0}) :
    ∀ x y z, x ∈ E → y ∈ E → x ≤ z → z ≤ y → z ∈ E := by
  intro x y z hx hy hxz hzy
  rw [hE, Set.mem_setOf]
  have hmon := h.1
  have hfx : f x = 0 := by rw [hE, Set.mem_setOf] at hx; exact hx
  have hfy : f y = 0 := by rw [hE, Set.mem_setOf] at hy; exact hy
  have h1 : f x ≤ f z := hmon x z hxz
  have h2 : f z ≤ f y := hmon z y hzy
  rw [hfx] at h1
  rw [hfy] at h2
  have hz : ∀ s, f z s = 0 := by
    intro s
    have a : 0 ≤ f z s := h1 s
    have b : f z s ≤ 0 := h2 s
    linarith
  funext s
  exact hz s

theorem omegaLimit_subset_equilibria (ϕ : Flow ℝ≥0 (Concentration S))
    (f : Concentration S → Concentration S) (V : Concentration S → ℝ)
    (hV : Continuous V) (x : Concentration S) (K : Set (Concentration S))
    (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x}) ⊆ K)
    (hmono : ∀ s t : ℝ≥0, s ≤ t → V (ϕ t x) ≤ V (ϕ s x))
    (hVcrit : ∀ y ∈ K, (∀ t : ℝ≥0, V (ϕ t y) = V y) → f y = 0) :
    ∀ y ∈ omegaLimit atTop ϕ {x}, f y = 0 := by
  intro y hy
  obtain ⟨c, _, hinv, hVc⟩ := Flow.laSalle ϕ hV x hK habs hmono
  have hωK : omegaLimit atTop ϕ {x} ⊆ K := by
    obtain ⟨v, hv, hvK⟩ := habs
    exact (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x}) (u := v) hv).trans hvK
  have hall : ∀ t : ℝ≥0, V (ϕ t y) = V y := by
    intro t
    have hmem : ϕ t y ∈ omegaLimit atTop ϕ {x} := hinv t hy
    have hVt : V (ϕ t y) = c := hVc (ϕ t y) hmem
    have hVy : V y = c := hVc y hy
    rw [hVt, hVy]
  exact hVcrit y (hωK hy) hall

theorem omegaLimit_orderConvex_of_assumed_orderConvex (ϕ : Flow ℝ≥0 (Concentration S)) (x : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x}) ⊆ K)
    (hmon : CRNT.Monotone.IsMonotoneFlow ϕ)
    (hωoc : ∀ a b z : Concentration S,
        a ∈ omegaLimit atTop ϕ {x} → b ∈ omegaLimit atTop ϕ {x} →
        a ≤ z → z ≤ b → z ∈ omegaLimit atTop ϕ {x}) :
    ∀ a b z, a ∈ omegaLimit atTop ϕ {x} → b ∈ omegaLimit atTop ϕ {x} →
        a ≤ z → z ≤ b → z ∈ omegaLimit atTop ϕ {x} :=
  hωoc

theorem converges_of_lasalle_of_stronglyMonotoneOperator (ϕ : Flow ℝ≥0 (Concentration S))
    (f : Concentration S → Concentration S) (V : Concentration S → ℝ)
    (hV : Continuous V) (x₀ : Concentration S) (K : Set (Concentration S))
    (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hmonoV : ∀ s t : ℝ≥0, s ≤ t → V (ϕ t x₀) ≤ V (ϕ s x₀))
    (hVcrit : ∀ y ∈ K, (∀ t : ℝ≥0, V (ϕ t y) = V y) → f y = 0)
    (hc : ℝ) (hsm : OrderPreservingStronglyMonotoneOperator f hc) (hcpos : 0 < hc)
    (hωoc : ∀ a b z, a ∈ omegaLimit atTop ϕ {x₀} → b ∈ omegaLimit atTop ϕ {x₀} →
        a ≤ z → z ≤ b → z ∈ omegaLimit atTop ϕ {x₀})
    (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ) :
    ∃ xstar : Concentration S, f xstar = 0 ∧
      Tendsto (fun t : ℝ≥0 => ϕ t x₀) atTop (𝓝 xstar) := by
  have hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, f y = 0 :=
    omegaLimit_subset_equilibria ϕ f V hV x₀ K hK habs hmonoV hVcrit
  have hne : (omegaLimit atTop ϕ {x₀}).Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs (Set.singleton_nonempty x₀)
  obtain ⟨xstar, hxstarmem⟩ := hne
  have hxstar0 : f xstar = 0 := hΩE xstar hxstarmem
  have huniq : ∀ y ∈ omegaLimit atTop ϕ {x₀}, y = xstar := by
    intro y hy
    have hy0 : f y = 0 := hΩE y hy
    exact (stronglyMonotoneOperator_unique_equilibrium (f := f) (c := hc) (a := xstar) (b := y) hcpos hsm hxstar0 hy0).symm
  have hΩsingle : omegaLimit atTop ϕ {x₀} = {xstar} := by
    apply (Set.eq_singleton_iff_unique_mem).mpr
    constructor
    · exact hxstarmem
    · intro y hy
      exact huniq y hy
  have hevK : ∀ᶠ t in atTop, ϕ t x₀ ∈ K := by
    obtain ⟨v, hv, hvK⟩ := habs
    filter_upwards [hv] with t ht
    have hmem : ϕ t x₀ ∈ closure (Set.image2 ϕ v {x₀}) :=
      subset_closure (Set.mem_image2_of_mem ht (Set.mem_singleton x₀))
    exact hvK hmem
  have htend : Tendsto (fun t : ℝ≥0 => ϕ t x₀) atTop (𝓝 xstar) :=
    hK.tendsto_nhds_of_unique_mapClusterPt hevK (by
      intro z _ hmc
      have hzω : z ∈ omegaLimit atTop ϕ {x₀} :=
        (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) (ϕ := ϕ) (x := x₀) (y := z)).mpr hmc
      rw [hΩsingle] at hzω
      exact Set.mem_singleton_iff.mp hzω)
  exact ⟨xstar, hxstar0, htend⟩

theorem massAction_stronglyMonotoneOperator_of_jacobian (N : Network S) (κ : N.RateConstants)
    {C : Set (Concentration S)} (hC : Convex ℝ C) {c : ℝ} (hc : 0 < c)
    (hJ : ∀ x ∈ C, ∀ u : S → ℝ,
        c * euclideanSqNorm u ≤ euclideanInner u (N.massActionJacobianCLM κ x u)) :
    ∀ a b, a ∈ C → b ∈ C →
      c * euclideanSqNorm (a - b) ≤
        euclideanInner (N.massActionVectorField κ a - N.massActionVectorField κ b) (a - b) := by
  intro a b ha hb
  have hf' : ∀ x ∈ C, HasFDerivAt (fun z => -N.massActionVectorField κ z)
      (-(N.massActionJacobianCLM κ x)) x := by
    intro x hx
    have h := N.massActionVectorField_hasFDerivAt κ x
    simpa using h.neg
  have hJ' : ∀ x ∈ C, ∀ u : S → ℝ,
      ∑ s, u s * (-(N.massActionJacobianCLM κ x)) u s ≤
        -c * euclideanSqNorm u := by
    intro x hx u
    have h1 := hJ x hx u
    have heq : euclideanInner u (N.massActionJacobianCLM κ x u) =
        ∑ s, u s * (N.massActionJacobianCLM κ x u) s := rfl
    -- the negated sum is the negative of the original sum
    have hnegsum : ∑ s, u s * (-(N.massActionJacobianCLM κ x)) u s =
        -∑ s, u s * (N.massActionJacobianCLM κ x u) s := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro s _
      simp [ContinuousLinearMap.coe_neg, Pi.neg_apply]
    rw [hnegsum]
    have : -∑ s, u s * (N.massActionJacobianCLM κ x u) s ≤ -c * euclideanSqNorm u := by
      linarith [h1]
    exact this
  have hone := CRNT.Network.oneSided_of_jacobian hC hf' hJ' ha hb
  have hLHS : ∑ s, (a s - b s) * ((-N.massActionVectorField κ a) s - (-N.massActionVectorField κ b) s) =
      -euclideanInner (a - b) (N.massActionVectorField κ a - N.massActionVectorField κ b) := by
    unfold euclideanInner
    simp only [Pi.sub_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    simp [Pi.neg_apply]
    ring
  have hsq : CRNT.Network.sqDist a b = euclideanSqNorm (a - b) := by
    unfold CRNT.Network.sqDist euclideanSqNorm; simp [Pi.sub_apply]
  have hone' : -euclideanInner (a - b) (N.massActionVectorField κ a - N.massActionVectorField κ b) ≤
      -c * euclideanSqNorm (a - b) := by
    rwa [hLHS, hsq] at hone
  have hfinal := neg_le_neg hone'
  have hsym : euclideanInner (a - b) (N.massActionVectorField κ a - N.massActionVectorField κ b) =
      euclideanInner (N.massActionVectorField κ a - N.massActionVectorField κ b) (a - b) := by
    unfold euclideanInner; apply Finset.sum_congr rfl; intro s _; ring
  have hfinal2 : c * euclideanSqNorm (a - b) ≤
      euclideanInner (N.massActionVectorField κ a - N.massActionVectorField κ b) (a - b) := by
    rw [hsym] at hfinal
    simpa [neg_neg] using hfinal
  exact hfinal2

theorem massAction_converges_of_lasalle_of_stronglyMonotoneOperator (N : Network S) (κ : N.RateConstants)
    {c : ℝ} (hc : 0 < c) (hsm : OrderPreservingStronglyMonotoneOperator (N.massActionVectorField κ) c)
    (ϕ : Flow ℝ≥0 (Concentration S)) (f : Concentration S → Concentration S)
    (V : Concentration S → ℝ) (hV : Continuous V) (x₀ : Concentration S)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hmonoV : ∀ s t : ℝ≥0, s ≤ t → V (ϕ t x₀) ≤ V (ϕ s x₀))
    (hVcrit : ∀ y ∈ K, (∀ t : ℝ≥0, V (ϕ t y) = V y) → f y = 0)
    (hωoc : ∀ a b z, a ∈ omegaLimit atTop ϕ {x₀} → b ∈ omegaLimit atTop ϕ {x₀} →
        a ≤ z → z ≤ b → z ∈ omegaLimit atTop ϕ {x₀})
    (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ)
    (hf : f = N.massActionVectorField κ) :
    ∃ xstar : Concentration S, N.massActionVectorField κ xstar = 0 ∧
      Tendsto (fun t : ℝ≥0 => ϕ t x₀) atTop (𝓝 xstar) := by
  have hsm' : OrderPreservingStronglyMonotoneOperator f c := by
    rw [hf]; exact hsm
  have hVcrit' : ∀ y ∈ K, (∀ t : ℝ≥0, V (ϕ t y) = V y) → f y = 0 := hVcrit
  obtain ⟨xstar, hxstar0, htend⟩ :=
    converges_of_lasalle_of_stronglyMonotoneOperator ϕ f V hV x₀ K hK habs hmonoV hVcrit' c hsm' hc hωoc hmonFlow
  refine ⟨xstar, ?_, htend⟩
  rw [hf] at hxstar0
  exact hxstar0

end CRNT

namespace CRNT
namespace Examples
namespace StronglyMonotoneOperatorInstance

open Network

abbrev net : Network (Fin 1) :=
  ⟨Fin 1, inferInstance, inferInstance, fun _ => ⟨![1], ![2]⟩⟩

def κ : net.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩

theorem field_eq (x : Concentration (Fin 1)) :
    net.massActionVectorField κ x = x := by
  funext s
  simp only [massActionVectorField_apply, massActionRate, κ]
  fin_cases s
  simp [Complex.massActionMonomial, Reaction.vector]
  norm_num

theorem jacobian_eq (x u : Concentration (Fin 1)) :
    net.massActionJacobianCLM κ x u = u := by
  funext s
  fin_cases s
  simp [massActionJacobianCLM, massActionMonomialGrad, κ, Reaction.vector]
  norm_num

theorem jacobian_bound (x u : Concentration (Fin 1)) :
    1 * CRNT.euclideanSqNorm u ≤ CRNT.euclideanInner u (net.massActionJacobianCLM κ x u) := by
  rw [jacobian_eq]
  unfold CRNT.euclideanInner CRNT.euclideanSqNorm
  simp
  exact le_of_eq (by ring)

theorem stronglyMonotoneOperator :
    CRNT.OrderPreservingStronglyMonotoneOperator (net.massActionVectorField κ) 1 := by
  constructor
  · intro x y hxy s
    rw [field_eq, field_eq]
    exact hxy s
  · intro x y
    rw [field_eq, field_eq]
    unfold CRNT.euclideanInner CRNT.euclideanSqNorm
    simp [Pi.sub_apply]
    exact le_of_eq (by ring)

end StronglyMonotoneOperatorInstance
end Examples
end CRNT
