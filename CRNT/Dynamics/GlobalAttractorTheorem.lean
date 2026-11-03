import CRNT.Dynamics.ComplexBalanceCycleDecomposition
import CRNT.Dynamics.ComplexBalanceStoichFan
import CRNT.Dynamics.FacetRepulsionAndersonShiu
import CRNT.Dynamics.FaceCodimension
import CRNT.Dynamics.HighCodimensionSiphonFace
import CRNT.Dynamics.GlobalPersistence
import CRNT.Dynamics.SiphonDimensionDescent
import CRNT.Dynamics.ToricInclusion
import CRNT.Dynamics.ZeroSeparating
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Equilibria.ComplexBalanceGeometry
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Geometry.ToricUniformWallMargin
import CRNT.Geometry.CompatibilityFaces

/-!
# The Global Attractor Theorem for complex-balanced mass-action systems

The former Global Attractor Conjecture is a theorem: every positive complex-balanced
equilibrium is the global attractor of the positive part of its stoichiometric compatibility
class.  Equivalently, every positive trajectory in that class is persistent and converges to
the unique positive complex-balanced equilibrium.

This module states the full theorem independently of single-linkage, no-critical-siphon, or
strongly-endotactic special cases.  The hard proof kernel is Craciun's toric-differential-
inclusion / zero-separating-surface construction; the surrounding CRNT consequences are
ordinary deductions from the persistence + Horn--Jackson machinery already formalized.
-/

open scoped NNReal ENNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A positive equilibrium globally attracts its positive stoichiometric compatibility class for
a specified genuine mass-action flow. -/
def IsGlobalAttractorForPositiveClass (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S)
    (ϕ : Flow ℝ≥0 (Concentration S))
    (γ : Concentration S → ℝ → Concentration S) : Prop :=
  N.IsMassActionFlow κ ϕ γ ∧
  ∀ x₀ : Concentration S,
    x₀.Positive → N.StoichCompatible x₀ xstar →
      omegaLimit atTop ϕ {x₀} = {xstar}

/-- Flow-independent form of the Global Attractor property. -/
def HasGlobalAttractorProperty (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S) : Prop :=
  ∀ (ϕ : Flow ℝ≥0 (Concentration S))
    (γ : Concentration S → ℝ → Concentration S),
    N.IsMassActionFlow κ ϕ γ →
      N.IsGlobalAttractorForPositiveClass κ xstar ϕ γ

/-- **Trajectory-level standard permanence on one positive class.**  There is a single
compact subset of the open positive compatibility class that eventually absorbs every genuine
forward mass-action trajectory started in that class.  Unlike `PermanentOnPositiveClass`, this
formulation does not presuppose the existence of a global flow on the whole ambient real space. -/
def GenuinePermanentOnPositiveClass (N : Network S) (κ : N.RateConstants)
    (xref : Concentration S) : Prop :=
  ∃ K : Set (Concentration S), IsCompact K ∧
    K ⊆ N.positiveCompatibilityClass xref ∧
    ∀ x₀ : Concentration S, x₀ ∈ N.positiveCompatibilityClass xref →
      ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → Γ t ∈ K

/-- Trajectory-level standard permanence for every positive compatibility class of fixed rates. -/
def GenuinePermanentForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ xref : Concentration S, xref.Positive → N.GenuinePermanentOnPositiveClass κ xref

/-- Pointwise strong persistence for fixed complex-balanced rates already implies convergence
of any genuine positive trajectory to the complex-balanced equilibrium in its class.  This isolates
the persistence input from the stronger class-uniform eventual-absorption API used below. -/
theorem trajectory_converges_of_persistentForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hx₀ : x₀.Positive) (hcompat : N.StoichCompatible x₀ xstar)
    (hpersRates : N.PersistentForRates κ)
    {Γ : ℝ → Concentration S} (hΓ0 : Γ 0 = x₀)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    Tendsto Γ atTop (𝓝 xstar) := by
  have hpers : N.PersistentFrom κ x₀ := hpersRates x₀ hx₀
  rcases hpers with ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  obtain ⟨ϕ, γ, hγ0, hϕγ, hsol, hω⟩ :=
    N.gac_of_persistent hwr κ hxs hcb hx₀ hcompat
      ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have horbitK : ∀ t : ℝ≥0, ϕ t x₀ ∈ K₀ := by
    intro t
    rw [hϕγ]
    exact hgen (γ x₀) (hγ0 x₀) hsol (t : ℝ) t.coe_nonneg
  have htendNN : Tendsto (fun t : ℝ≥0 => ϕ t x₀) atTop (𝓝 xstar) := by
    apply hK₀cpt.tendsto_nhds_of_unique_mapClusterPt
    · exact Filter.Eventually.of_forall horbitK
    · intro y _hy hcluster
      have hyω : y ∈ omegaLimit atTop ϕ {x₀} :=
        (mem_omegaLimit_singleton_iff_mapClusterPt atTop ϕ x₀ y).2 hcluster
      rw [hω, Set.mem_singleton_iff] at hyω
      exact hyω
  have htendReal : Tendsto (fun t : ℝ => ϕ (Real.toNNReal t) x₀) atTop (𝓝 xstar) :=
    htendNN.comp Real.tendsto_toNNReal_atTop
  have hevent : (fun t : ℝ => ϕ (Real.toNNReal t) x₀) =ᶠ[atTop] Γ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hϕγ, Real.coe_toNNReal t ht]
    exact (N.genuineOrbit_unique κ hxs hcb hx₀ hΓ0 (hγ0 x₀)
      hΓd hsol t ht).symm
  exact Filter.Tendsto.congr' hevent htendReal

/-- If the cutoff semiflow through a positive start has no boundary omega-limit points, then
that start has the repository's strong compact-interior persistence certificate.  This is the
omega-boundary analogue of `persistentFrom_of_omegaLimit_singleton`: singleton identification is
not needed for persistence itself. -/
theorem persistentFrom_of_omegaLimit_positive
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hωpos : ∀ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) :
    N.PersistentFrom κ x₀ := by
  set C₀ := relEntropy xstar x₀ with hC₀
  set B : ℝ := 1 + |C₀| + ∑ s, Real.exp 2 * xstar s with hBdef
  have hsumnn : 0 ≤ ∑ s, Real.exp 2 * xstar s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxs s)).le
  have hBnn : 0 ≤ B := by rw [hBdef]; have := abs_nonneg C₀; linarith
  have hBbig : ∀ s, max (Real.exp 2 * xstar s) C₀ < B := by
    intro s
    have hsum : Real.exp 2 * xstar s ≤ ∑ s', Real.exp 2 * xstar s' :=
      Finset.single_le_sum (fun s' _ => (mul_pos (Real.exp_pos 2) (hxs s')).le) (Finset.mem_univ s)
    rw [max_lt_iff, hBdef]
    exact ⟨by linarith [abs_nonneg C₀], by linarith [le_abs_self C₀]⟩
  have hγ0x0 : γ x₀ 0 = x₀ := hγ0 x₀
  have hΓ0pos : (γ x₀ 0).Positive := by rw [hγ0x0]; exact hx0
  have hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive := N.genuineOrbit_pos κ hΓ0pos hsol
  have hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ x₀ t) ≤ C₀ := by
    intro t ht
    have := N.genuineOrbit_relEntropy_le κ hxs hcb hpos hsol t ht
    rwa [hγ0x0] at this
  have hboxOf : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → ∀ s, |Γ t s| ≤ B := by
    intro Γ hΓ0 hΓd t ht s
    have hΓ0p : (Γ 0).Positive := by rw [hΓ0]; exact hx0
    have hp := N.genuineOrbit_pos κ hΓ0p hΓd t ht
    have hre : relEntropy xstar (Γ t) ≤ C₀ := by
      have := N.genuineOrbit_relEntropy_le κ hxs hcb (N.genuineOrbit_pos κ hΓ0p hΓd) hΓd t ht
      rwa [hΓ0] at this
    rw [abs_le]
    exact ⟨by linarith [hp s], le_of_lt (lt_of_le_of_lt
      (relEntropy_coord_le hxs hp.nonnegative hre s) (hBbig s))⟩
  set SC : Set (Concentration S) := {y | y.Nonnegative ∧ relEntropy xstar y ≤ C₀} with hSCdef
  have hSCcpt : IsCompact SC := isCompact_relEntropy_sublevel hxs C₀
  set O : Set (Concentration S) := γ x₀ '' Set.Ici (0 : ℝ) with hOdef
  have hOSC : O ⊆ SC := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨(hpos t ht).nonnegative, hrele t ht⟩
  have hclOSC : closure O ⊆ SC := (IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hOSC
  have hclOcpt : IsCompact (closure O) := hSCcpt.of_isClosed_subset isClosed_closure hclOSC
  have hclOpos : ∀ p ∈ closure O, p.Positive := by
    intro p hp
    by_cases hpO : p ∈ O
    · obtain ⟨t, ht, rfl⟩ := hpO; exact hpos t ht
    · have htail : ∀ T' : ℝ≥0, p ∈ closure (Set.image2 ϕ (Set.Ici T') {x₀}) := by
        intro T'
        have hT0 : (0 : ℝ) ≤ (T' : ℝ) := T'.coe_nonneg
        have hcontOn : ContinuousOn (γ x₀) (Set.Icc 0 (T' : ℝ)) :=
          fun t ht => (hsol t ht.1).continuousAt.continuousWithinAt
        have hdecomp : O = γ x₀ '' Set.Icc 0 (T' : ℝ) ∪ γ x₀ '' Set.Ici (T' : ℝ) := by
          rw [hOdef, ← Set.image_union, Set.Icc_union_Ici_eq_Ici hT0]
        have hcompactInit : IsCompact (γ x₀ '' Set.Icc 0 (T' : ℝ)) :=
          isCompact_Icc.image_of_continuousOn hcontOn
        have hpInTail : p ∈ closure (γ x₀ '' Set.Ici (T' : ℝ)) := by
          have hpcl : p ∈ closure (γ x₀ '' Set.Icc 0 (T' : ℝ))
              ∪ closure (γ x₀ '' Set.Ici (T' : ℝ)) := by
            rw [← closure_union, ← hdecomp]; exact hp
          rcases hpcl with hpic | hpit
          · rw [hcompactInit.isClosed.closure_eq] at hpic
            exact absurd (Set.image_mono Set.Icc_subset_Ici_self hpic) hpO
          · exact hpit
        have hconv : γ x₀ '' Set.Ici (T' : ℝ) = Set.image2 ϕ (Set.Ici T') {x₀} := by
          rw [Set.image2_singleton_right]
          have hfeq : (fun s : ℝ≥0 => ϕ s x₀) = γ x₀ ∘ NNReal.toReal := by
            funext s; exact hϕγ x₀ s
          rw [hfeq, Set.image_comp, NNReal.image_coe_Ici]
        rwa [hconv] at hpInTail
      have hpω : p ∈ omegaLimit atTop ϕ {x₀} := by
        rw [omegaLimit_def]
        simp only [Set.mem_iInter]
        intro u hu
        obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.mp hu
        exact closure_mono (Set.image2_subset (fun b hb => ha b hb) (subset_refl _)) (htail a)
      exact hωpos p hpω
  refine ⟨closure O, hclOcpt, hclOpos, ?_⟩
  intro Γ hΓ0 hΓd t ht
  have heq : Γ t = γ x₀ t :=
    N.genuineOrbit_unique_of_box κ hBnn hΓd hsol (hboxOf Γ hΓ0 hΓd)
      (hboxOf (γ x₀) hγ0x0 hsol) (by rw [hΓ0, hγ0x0]) t ht
  rw [heq]
  exact subset_closure ⟨t, ht, rfl⟩

/-- One positive omega-limit point, together with the standard complex-balanced LaSalle data,
is already enough for the strong compact-interior `PersistentFrom` certificate.  The positive
omega-point collapses the whole omega-limit set to the class equilibrium, after which
`persistentFrom_of_omegaLimit_positive` supplies the compact certificate. -/
theorem persistentFrom_of_omegaLimit_mem_positive
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hex : ∃ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p) :
    N.PersistentFrom κ x₀ := by
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  have hωeq : omegaLimit atTop ϕ {x₀} = {xstar} :=
    N.omegaLimit_eq_singleton_of_mem_positive hwr κ hxs hcb hx0compat hγ0 hϕγ
      hgenω hωnn hωaff hωc hposorbit hex
  apply N.persistentFrom_of_omegaLimit_positive κ hxs hcb hx0 hγ0 hϕγ hsol
  intro p hp
  rw [hωeq, Set.mem_singleton_iff] at hp
  simpa [hp] using hxs

/-- Anderson's carried-siphon comparable-growth descent is sufficient for the strong
`PersistentFrom` certificate once the standard bounded-orbit/LaSalle data are available.  This
isolates the remaining analytic content to the strictly-decreasing carried-critical-siphon step. -/
theorem persistentFrom_of_comparableGrowthDescent
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hKcl : IsClosed K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hdesc : N.ComparableGrowthDescent ϕ x₀) :
    N.PersistentFrom κ x₀ := by
  apply N.persistentFrom_of_omegaLimit_mem_positive κ hxs hcb hx0 hx0compat
    hγ0 hϕγ hsol hgenω hωnn hωaff hωc hposorbit
  exact N.omegaLimit_positive_of_comparableGrowthDescent κ hϕγ hK hKcl hmaps
    hωnn hgenω hωaff hx0 hdesc

/-- **Weak omega-interior certificate for fixed rates.**  For every positive bounded genuine
mass-action orbit whose omega-limit dynamics are genuine, nonnegative, and remain in the
stoichiometric affine class, the omega-limit set contains at least one strictly positive point.
This is strictly weaker than
`BoundaryOmegaExcluded`: complex-balanced LaSalle theory upgrades a single positive omega-point to
the full singleton omega-limit conclusion. -/
def PositiveOmegaPointForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S},
    (∀ x (t : ℝ≥0), ϕ t x = γ x t) →
    -- The initial orbit must solve the ODE as well as its omega-limit orbits.
    -- Otherwise the contracting flow in `CRNT.Examples.OmegaPointFakeFlow` refutes this.
    (∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) →
    (∃ K : Set (Concentration S), IsCompact K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t) →
    (∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace) →
    x₀.Positive →
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive

omit [DecidableEq S] [Fintype S] in
/-- Craciun's invariant upper region keeps every concentration coordinate uniformly positive.
Together with a compact orbit, these coordinate lower bounds pass to the omega-limit set and
provide the positive omega-point needed by `PositiveOmegaPointForRates`. -/
theorem exists_positive_omegaPoint_of_uniform_coordinate_lower_bounds
    {ϕ : Flow ℝ≥0 (Concentration S)}
    {γ : Concentration S → ℝ → Concentration S} {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hbounded : ∃ K : Set (Concentration S), IsCompact K ∧
      ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hlower : ∀ s, ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → ε ≤ γ x₀ t s) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  obtain ⟨K, hKcpt, hmaps⟩ := hbounded
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem,
      (IsClosed.closure_subset_iff hKcpt.isClosed).mpr hsubK⟩
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hKcpt habs
      (Set.singleton_nonempty x₀)
  refine ⟨p, hp, ?_⟩
  intro s
  obtain ⟨ε, hε, hcoordinate⟩ := hlower s
  have hclosed : IsClosed {y : Concentration S | ε ≤ y s} :=
    isClosed_Ici.preimage (continuous_apply s)
  have horbit : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆
      {y : Concentration S | ε ≤ y s} := by
    rintro y ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [hϕγ]
    exact hcoordinate t t.coe_nonneg
  have hpclosed : p ∈ {y : Concentration S | ε ≤ y s} := by
    have hωsub : omegaLimit atTop ϕ {x₀} ⊆
        closure (Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀}) :=
      omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
        (u := Set.univ) univ_mem
    have hclosure := (IsClosed.closure_subset_iff hclosed).mpr horbit
    exact (hωsub.trans hclosure) hp
  exact lt_of_lt_of_le hε hpclosed

/-- The positive-omega kernel closes when the stoichiometric subspace is trivial: compactness
makes the omega-limit set nonempty, and affine invariance pins every omega-point to the positive
initial state. This is the zero-dimensional base case for a dimension-inductive proof of the full
complex-balanced theorem. -/
theorem positiveOmegaPointForRates_of_trivialStoichSubspace
    (N : Network S) (κ : N.RateConstants)
    (hzero : N.stoichSubspace = ⊥) :
    N.PositiveOmegaPointForRates κ := by
  intro ϕ γ x₀ hϕγ _hsol hbounded _hωnn _hgenω hωaff hx₀
  obtain ⟨K, hKcpt, hmaps⟩ := hbounded
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem,
      (IsClosed.closure_subset_iff hKcpt.isClosed).mpr hsubK⟩
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hKcpt habs
      (Set.singleton_nonempty x₀)
  have hpaff : (p - x₀ : Concentration S) ∈ N.stoichSubspace := hωaff p hp
  rw [hzero] at hpaff
  simp only [Submodule.mem_bot] at hpaff
  have hpeq : p = x₀ := sub_eq_zero.mp hpaff
  exact ⟨p, hp, by simpa [hpeq] using hx₀⟩

/-- Boundary omega-exclusion implies the weaker positive-omega-point certificate. -/
theorem positiveOmegaPointForRates_of_boundaryOmegaExcluded
    (N : Network S) (κ : N.RateConstants)
    (hboundary : N.BoundaryOmegaExcluded κ) :
    N.PositiveOmegaPointForRates κ := by
  intro ϕ γ x₀ hϕγ _hsol hbounded hωnn hgenω hωaff hx0
  obtain ⟨K, hKcpt, hmaps⟩ := hbounded
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hKcpt.isClosed).mpr hsubK⟩
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hKcpt habs (Set.singleton_nonempty x₀)
  exact ⟨p, hp, hboundary hϕγ ⟨K, hKcpt, hmaps⟩ hωnn hgenω hωaff hx0 p hp⟩

/-- A uniform carried-siphon comparable-growth descent supplies the weak omega-interior certificate.
This exposes Anderson's finite siphon-cardinality descent as one concrete route to the remaining
analytic kernel. -/
def ComparableGrowthDescentForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S},
    (∀ x (t : ℝ≥0), ϕ t x = γ x t) →
    (∃ K : Set (Concentration S), IsCompact K ∧ IsClosed K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y) →
    (∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t) →
    (∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace) →
    x₀.Positive →
    N.ComparableGrowthDescent ϕ x₀

/-- Uniform comparable-growth descent implies that every admissible bounded orbit has a positive
omega-limit point. -/
theorem positiveOmegaPointForRates_of_comparableGrowthDescentForRates
    (N : Network S) (κ : N.RateConstants)
    (hdescRates : N.ComparableGrowthDescentForRates κ) :
    N.PositiveOmegaPointForRates κ := by
  intro ϕ γ x₀ hϕγ _hsol hbounded hωnn hgenω hωaff hx0
  obtain ⟨K, hKcpt, hmaps⟩ := hbounded
  have hdesc : N.ComparableGrowthDescent ϕ x₀ :=
    hdescRates hϕγ ⟨K, hKcpt, hKcpt.isClosed, hmaps⟩ hωnn hgenω hωaff hx0
  exact N.omegaLimit_positive_of_comparableGrowthDescent κ hϕγ hKcpt hKcpt.isClosed hmaps
    hωnn hgenω hωaff hx0 hdesc

/-- The weak positive-omega-point certificate is sufficient for pointwise strong persistence of
complex-balanced fixed-rate dynamics.  The proof constructs the standard entropy-confined cutoff
flow, obtains one positive omega-point from the certificate, and then uses LaSalle plus
`omegaLimit_eq_singleton_of_mem_positive` to collapse the whole omega-limit set to the unique
complex-balanced equilibrium in the start's compatibility class. -/
theorem complexBalanced_persistentForRates_of_positiveOmegaPointForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hpositiveOmega : N.PositiveOmegaPointForRates κ) :
    N.PersistentForRates κ := by
  intro x₀ hx0
  obtain ⟨xeq, hxeqclass, hxeqcb⟩ :=
    N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx0
  have hx0compat : N.StoichCompatible x₀ xeq := hxeqclass.1
  set C₀ := relEntropy xeq x₀ with hC₀
  set B : ℝ := 1 + |C₀| + ∑ s, Real.exp 2 * xeq s with hBdef
  have hsumnn : 0 ≤ ∑ s, Real.exp 2 * xeq s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxeqclass.2 s)).le
  have hBnn : 0 ≤ B := by rw [hBdef]; have := abs_nonneg C₀; linarith
  have hBbig : ∀ s, max (Real.exp 2 * xeq s) C₀ < B := by
    intro s
    have hsum : Real.exp 2 * xeq s ≤ ∑ s', Real.exp 2 * xeq s' :=
      Finset.single_le_sum
        (fun s' _ => (mul_pos (Real.exp_pos 2) (hxeqclass.2 s')).le) (Finset.mem_univ s)
    rw [max_lt_iff, hBdef]
    exact ⟨by linarith [abs_nonneg C₀], by linarith [le_abs_self C₀]⟩
  obtain ⟨L, hLnn, hbound⟩ := N.exists_field_lower_bound κ B
  obtain ⟨Klip, M, hlip, hbd⟩ := N.exists_cutoff κ hBnn
  obtain ⟨ϕ, γ, hγ0, hγd, hϕγ⟩ := ODE.exists_flow hlip hbd
  have hΓd : ∀ t, HasDerivAt (γ x₀) (N.massActionVectorField κ (clampBox B (γ x₀ t))) t :=
    fun t => hγd x₀ t
  have hΓ0pos : Concentration.Positive (γ x₀ 0) := by rw [hγ0]; exact hx0
  have hpos : ∀ t, 0 ≤ t → Concentration.Positive (γ x₀ t) :=
    orbit_pos N κ hBnn hLnn hbound hΓ0pos hΓd
  have hrele : ∀ t, 0 ≤ t → relEntropy xeq (γ x₀ t) ≤ C₀ := by
    have hB' : ∀ s, max (Real.exp 2 * xeq s) (relEntropy xeq (γ x₀ 0)) < B := by
      intro s; rw [hγ0]; exact hBbig s
    intro t ht
    have := orbit_relEntropy_le N κ hxeqclass.2 hxeqcb hpos hΓd hB' t ht
    rw [hγ0, ← hC₀] at this
    exact this
  have hclamp : ∀ t, 0 ≤ t → clampBox B (γ x₀ t) = γ x₀ t := fun t ht =>
    clampBox_eq_of_sublevel hxeqclass.2 (hpos t ht).nonnegative (hrele t ht) hBbig
  have hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t := by
    intro t ht
    have := hΓd t
    rwa [hclamp t ht] at this
  set SC : Set (Concentration S) :=
      {y : Concentration S | Concentration.Nonnegative y ∧ relEntropy xeq y ≤ C₀} with hSCdef
  have hSCcpt : IsCompact SC := isCompact_relEntropy_sublevel hxeqclass.2 C₀
  have horbit_SC : ∀ t : ℝ≥0, ϕ t x₀ ∈ SC := by
    intro t
    rw [hϕγ]
    exact ⟨(hpos t t.coe_nonneg).nonnegative, hrele t t.coe_nonneg⟩
  have hsubSC : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ SC := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact horbit_SC t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ SC :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hsubSC⟩
  have hωSC : omegaLimit atTop ϕ {x₀} ⊆ SC :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
      (u := Set.univ) univ_mem).trans
      ((IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hsubSC)
  have hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y :=
    fun y hy => (hωSC hy).1
  have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
    N.stoichSubspace.closed_of_finiteDimensional
  have haffclosed : IsClosed {z : Concentration S | z - x₀ ∈ N.stoichSubspace} :=
    IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
  have horbit_aff : ∀ t : ℝ≥0, ϕ t x₀ - x₀ ∈ N.stoichSubspace := by
    intro t
    rw [hϕγ]
    have hsol' : ∀ τ ∈ Set.Icc (0 : ℝ) ↑t,
        HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ τ)) τ :=
      fun τ hτ => hsol τ hτ.1
    have := sub_mem_stoichSubspace_of_solution N κ t.coe_nonneg hsol'
    rwa [hγ0] at this
  have hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace := by
    have hsub : omegaLimit atTop ϕ {x₀} ⊆ {z | z - x₀ ∈ N.stoichSubspace} := by
      refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
        (u := Set.univ) univ_mem).trans ?_
      refine (IsClosed.closure_subset_iff haffclosed).mpr ?_
      rintro z ⟨t, -, x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact horbit_aff t
    exact fun z hz => hsub hz
  have hyωt_gen : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      γ y t ∈ omegaLimit atTop ϕ {x₀} := by
    intro y hy t ht
    let tNonneg : ℝ≥0 := ⟨t, ht⟩
    have hmem := (Flow.isInvariant_omegaLimit atTop ϕ {x₀}
      (fun s => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) tNonneg) hy
    have htime : (↑tNonneg : ℝ) = t := rfl
    have hϕ' : ϕ.toFun tNonneg y = γ y t := by
      calc
        ϕ.toFun tNonneg y = γ y ↑tNonneg := hϕγ y tNonneg
        _ = γ y t := congrArg (γ y) htime
    rw [hϕ'] at hmem
    exact hmem
  have hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t := by
    intro y hy t ht
    have hmemω : γ y t ∈ omegaLimit atTop ϕ {x₀} := hyωt_gen y hy t ht
    have hclt : clampBox B (γ y t) = γ y t :=
      clampBox_eq_of_sublevel hxeqclass.2 (hωSC hmemω).1 (hωSC hmemω).2 hBbig
    rw [← hclt]
    exact hγd y t
  have hex : ∃ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p :=
    hpositiveOmega hϕγ hsol ⟨SC, hSCcpt, horbit_SC⟩ hωnn hgenω hωaff hx0
  have hAnti : AntitoneOn (fun t => relEntropy xeq (γ x₀ t)) (Set.Ici 0) := by
    have hcont : Continuous (fun t => relEntropy xeq (γ x₀ t)) :=
      (relEntropy_continuous hxeqclass.2).comp
        (Differentiable.continuous fun t => (hΓd t).differentiableAt)
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn ?_ ?_
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      exact (relEntropy_hasDerivAt hxeqclass.2 (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(relEntropy_hasDerivAt hxeqclass.2 (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxeqclass.2 hxeqcb
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xeq (ϕ b x₀) ≤ relEntropy xeq (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg)
      (by exact_mod_cast hab)
  obtain ⟨c, _, hωinv, hωc⟩ :=
    Flow.laSalle ϕ (relEntropy_continuous hxeqclass.2) x₀ hSCcpt habs hmono
  have hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t) := by
    intro p hp hpp t ht
    have hp0 : Concentration.Positive (γ p 0) := by rw [hγ0]; exact hpp
    exact N.genuineOrbit_pos κ hp0 (hgenω p hp) t ht
  exact N.persistentFrom_of_omegaLimit_mem_positive κ hxeqclass.2 hxeqcb hx0 hx0compat
    hγ0 hϕγ hsol hgenω hωnn hωaff hωc hposorbit hex

/-- The orbit-local omega-boundary exclusion predicate is already sufficient to produce
`PersistentForRates` for complex-balanced rates.  The only flow used here is the standard globally
Lipschitz cutoff flow; entropy confinement makes the cutoff collapse on the orbit and on its
omega-limit set, so `BoundaryOmegaExcluded` applies to the genuine mass-action dynamics there. -/
theorem complexBalanced_persistentForRates_of_boundaryOmegaExcluded
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hboundary : N.BoundaryOmegaExcluded κ) :
    N.PersistentForRates κ := by
  intro x₀ hx0
  set C₀ := relEntropy xstar x₀ with hC₀
  set B : ℝ := 1 + |C₀| + ∑ s, Real.exp 2 * xstar s with hBdef
  have hsumnn : 0 ≤ ∑ s, Real.exp 2 * xstar s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxs s)).le
  have hBnn : 0 ≤ B := by rw [hBdef]; have := abs_nonneg C₀; linarith
  have hBbig : ∀ s, max (Real.exp 2 * xstar s) C₀ < B := by
    intro s
    have hsum : Real.exp 2 * xstar s ≤ ∑ s', Real.exp 2 * xstar s' :=
      Finset.single_le_sum (fun s' _ => (mul_pos (Real.exp_pos 2) (hxs s')).le) (Finset.mem_univ s)
    rw [max_lt_iff, hBdef]
    exact ⟨by linarith [abs_nonneg C₀], by linarith [le_abs_self C₀]⟩
  obtain ⟨L, hLnn, hbound⟩ := N.exists_field_lower_bound κ B
  obtain ⟨Klip, M, hlip, hbd⟩ := N.exists_cutoff κ hBnn
  obtain ⟨ϕ, γ, hγ0, hγd, hϕγ⟩ := ODE.exists_flow hlip hbd
  have hΓd : ∀ t, HasDerivAt (γ x₀) (N.massActionVectorField κ (clampBox B (γ x₀ t))) t :=
    fun t => hγd x₀ t
  have hΓ0pos : Concentration.Positive (γ x₀ 0) := by rw [hγ0]; exact hx0
  have hpos : ∀ t, 0 ≤ t → Concentration.Positive (γ x₀ t) :=
    orbit_pos N κ hBnn hLnn hbound hΓ0pos hΓd
  have hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ x₀ t) ≤ C₀ := by
    have hB' : ∀ s, max (Real.exp 2 * xstar s) (relEntropy xstar (γ x₀ 0)) < B := by
      intro s; rw [hγ0]; exact hBbig s
    intro t ht
    have := orbit_relEntropy_le N κ hxs hcb hpos hΓd hB' t ht
    rw [hγ0, ← hC₀] at this
    exact this
  have hclamp : ∀ t, 0 ≤ t → clampBox B (γ x₀ t) = γ x₀ t := fun t ht =>
    clampBox_eq_of_sublevel hxs (hpos t ht).nonnegative (hrele t ht) hBbig
  have hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t := by
    intro t ht
    have := hΓd t
    rwa [hclamp t ht] at this
  set SC : Set (Concentration S) :=
      {y : Concentration S | Concentration.Nonnegative y ∧ relEntropy xstar y ≤ C₀} with hSCdef
  have hSCcpt : IsCompact SC := isCompact_relEntropy_sublevel hxs C₀
  have horbit_SC : ∀ t : ℝ≥0, ϕ t x₀ ∈ SC := by
    intro t
    rw [hϕγ]
    exact ⟨(hpos t t.coe_nonneg).nonnegative, hrele t t.coe_nonneg⟩
  have hsubSC : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ SC := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact horbit_SC t
  have hωSC : omegaLimit atTop ϕ {x₀} ⊆ SC :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
      (u := Set.univ) univ_mem).trans
      ((IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hsubSC)
  have hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y :=
    fun y hy => (hωSC hy).1
  have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
    N.stoichSubspace.closed_of_finiteDimensional
  have haffclosed : IsClosed {z : Concentration S | z - x₀ ∈ N.stoichSubspace} :=
    IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
  have horbit_aff : ∀ t : ℝ≥0, ϕ t x₀ - x₀ ∈ N.stoichSubspace := by
    intro t
    rw [hϕγ]
    have hsol' : ∀ τ ∈ Set.Icc (0 : ℝ) ↑t,
        HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ τ)) τ :=
      fun τ hτ => hsol τ hτ.1
    have := sub_mem_stoichSubspace_of_solution N κ t.coe_nonneg hsol'
    rwa [hγ0] at this
  have hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace := by
    have hsub : omegaLimit atTop ϕ {x₀} ⊆ {z | z - x₀ ∈ N.stoichSubspace} := by
      refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
        (u := Set.univ) univ_mem).trans ?_
      refine (IsClosed.closure_subset_iff haffclosed).mpr ?_
      rintro z ⟨t, -, x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact horbit_aff t
    exact fun z hz => hsub hz
  have hyωt_gen : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      γ y t ∈ omegaLimit atTop ϕ {x₀} := by
    intro y hy t ht
    let tNonneg : ℝ≥0 := ⟨t, ht⟩
    have hmem := (Flow.isInvariant_omegaLimit atTop ϕ {x₀}
      (fun s => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) tNonneg) hy
    have htime : (↑tNonneg : ℝ) = t := rfl
    have hϕ' : ϕ.toFun tNonneg y = γ y t := by
      calc
        ϕ.toFun tNonneg y = γ y ↑tNonneg := hϕγ y tNonneg
        _ = γ y t := congrArg (γ y) htime
    rw [hϕ'] at hmem
    exact hmem
  have hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t := by
    intro y hy t ht
    have hmemω : γ y t ∈ omegaLimit atTop ϕ {x₀} := hyωt_gen y hy t ht
    have hclt : clampBox B (γ y t) = γ y t :=
      clampBox_eq_of_sublevel hxs (hωSC hmemω).1 (hωSC hmemω).2 hBbig
    rw [← hclt]
    exact hγd y t
  have hωpos : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive y := by
    intro y hy
    exact hboundary hϕγ ⟨SC, hSCcpt, horbit_SC⟩ hωnn hgenω hωaff hx0 y hy
  exact N.persistentFrom_of_omegaLimit_positive κ hxs hcb hx0 hγ0 hϕγ hsol hωpos

/-- For complex-balanced fixed rates, the repository's pointwise compact persistence certificate
already upgrades to the class-uniform eventual compactness formulation used by
`GenuinePermanentForRates`.  Consequently the genuinely new kernel needed below can be reduced to
`PersistentForRates κ`. -/
theorem complexBalanced_genuinePermanent_of_persistentForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hpersRates : N.PersistentForRates κ) :
    N.GenuinePermanentForRates κ := by
  intro xref hxref
  obtain ⟨xeq, hxeqclass, hxeqcb⟩ :=
    N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hxref
  have hopenPos : IsOpen ({y : Concentration S | y.Positive} : Set (Concentration S)) := by
    have heq : ({y : Concentration S | y.Positive} : Set (Concentration S)) =
        ⋂ s : S, {y : Concentration S | 0 < y s} := by
      ext y
      simp [Concentration.Positive]
    rw [heq]
    exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const (continuous_apply s)
  obtain ⟨ε, hεpos, hball⟩ := (Metric.isOpen_iff.mp hopenPos) xeq hxeqclass.2
  let r : ℝ := ε / 2
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < ε := by dsimp [r]; linarith
  let K : Set (Concentration S) := Metric.closedBall xeq r ∩ N.compatibilityClass xref
  refine ⟨K, ?_, ?_, ?_⟩
  · have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
      N.stoichSubspace.closed_of_finiteDimensional
    have hclassClosed : IsClosed (N.compatibilityClass xref) :=
      IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
    exact (isCompact_closedBall xeq r).inter_right hclassClosed
  · intro y hy
    refine ⟨hy.2, ?_⟩
    apply hball
    exact Metric.closedBall_subset_ball hrlt hy.1
  · intro x₀ hx₀class Γ hΓ0 hΓd
    have hx₀xeq : N.StoichCompatible x₀ xeq := hx₀class.1.symm.trans hxeqclass.1
    have htend : Tendsto Γ atTop (𝓝 xeq) :=
      N.trajectory_converges_of_persistentForRates κ hxeqclass.2 hxeqcb
        hx₀class.2 hx₀xeq hpersRates hΓ0 hΓd
    have hev : ∀ᶠ t : ℝ in atTop, Γ t ∈ Metric.ball xeq r :=
      htend (Metric.ball_mem_nhds xeq hrpos)
    obtain ⟨T₀, hT₀⟩ := (Filter.mem_atTop_sets.mp hev)
    let T : ℝ := max 0 T₀
    refine ⟨T, le_max_left 0 T₀, ?_⟩
    intro t ht
    have htT₀ : T₀ ≤ t := (le_max_right 0 T₀).trans ht
    have hΓball : Γ t ∈ Metric.ball xeq r := hT₀ t htT₀
    have ht0 : 0 ≤ t := (le_max_left 0 T₀).trans ht
    have hdisp : Γ t - Γ 0 ∈ N.stoichSubspace :=
      N.sub_mem_stoichSubspace_of_solution κ ht0 (fun u hu => hΓd u hu.1)
    have hx₀Γ : N.StoichCompatible x₀ (Γ t) := by
      rw [Network.StoichCompatible, ← hΓ0]
      exact hdisp
    refine ⟨Metric.ball_subset_closedBall hΓball, ?_⟩
    exact hx₀class.1.trans hx₀Γ

/-- The weak omega-interior certificate is sufficient for the exact class-uniform genuine
permanence API consumed by the Global Attractor Theorem. -/
theorem complexBalanced_genuinePermanent_of_positiveOmegaPointForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hpositiveOmega : N.PositiveOmegaPointForRates κ) :
    N.GenuinePermanentForRates κ :=
  N.complexBalanced_genuinePermanent_of_persistentForRates κ hxs hcb
    (N.complexBalanced_persistentForRates_of_positiveOmegaPointForRates κ hxs hcb hpositiveOmega)

/-- Uniform Anderson-style carried-siphon descent is a sufficient analytic certificate for
the full class-uniform complex-balanced permanence conclusion. -/
theorem complexBalanced_genuinePermanent_of_comparableGrowthDescentForRates
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hdescRates : N.ComparableGrowthDescentForRates κ) :
    N.GenuinePermanentForRates κ :=
  N.complexBalanced_genuinePermanent_of_positiveOmegaPointForRates κ hxs hcb
    (N.positiveOmegaPointForRates_of_comparableGrowthDescentForRates κ hdescRates)

/-- The no-critical-siphon structural regime closes the exact trajectory-level permanence API as a
special case of the general omega-boundary interface. -/
theorem complexBalanced_genuinePermanent_of_hasNoCriticalSiphon
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hncs : N.HasNoCriticalSiphon) :
    N.GenuinePermanentForRates κ :=
  N.complexBalanced_genuinePermanent_of_positiveOmegaPointForRates κ hxs hcb
    (N.positiveOmegaPointForRates_of_boundaryOmegaExcluded κ
      (N.boundaryOmegaExcluded_of_hasNoCriticalSiphon κ hncs))

/-- For complex-balanced rates, omega-boundary exclusion is enough for the exact class-uniform
permanence API consumed by the Global Attractor Theorem. -/
theorem complexBalanced_genuinePermanent_of_boundaryOmegaExcluded
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hboundary : N.BoundaryOmegaExcluded κ) :
    N.GenuinePermanentForRates κ :=
  N.complexBalanced_genuinePermanent_of_persistentForRates κ hxs hcb
    (N.complexBalanced_persistentForRates_of_boundaryOmegaExcluded κ hxs hcb hboundary)

/-- Along a nonzero stoichiometric direction, relative entropy has strictly positive radial
derivative away from its reference point. This is the scalar monotonicity ingredient for the
rank-one persistence case. -/
theorem relativeEntropy_logDirection_smul_pos
    {xstar v : Concentration S} (hxs : xstar.Positive) (hv : v ≠ 0)
    {a : ℝ} (ha : a ≠ 0) (hx : (xstar + a • v).Positive) :
    0 < a * ∑ s, (Real.log ((xstar + a • v) s) - Real.log (xstar s)) * v s := by
  have hterm_pos : ∀ s, v s ≠ 0 →
      0 < a * ((Real.log ((xstar + a • v) s) - Real.log (xstar s)) * v s) := by
    intro s hvs
    have hprod_ne : a * v s ≠ 0 := mul_ne_zero ha hvs
    by_cases hprod : 0 < a * v s
    · have horder : xstar s < (xstar + a • v) s := by
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hprod
      have hlog : 0 < Real.log ((xstar + a • v) s) - Real.log (xstar s) :=
        sub_pos.mpr (Real.log_lt_log (hxs s) horder)
      have hmul : 0 < (a * v s) *
          (Real.log ((xstar + a • v) s) - Real.log (xstar s)) :=
        mul_pos hprod hlog
      convert hmul using 1 <;> ring
    · have hprod : a * v s < 0 := lt_of_le_of_ne (le_of_not_gt hprod) hprod_ne
      have horder : (xstar + a • v) s < xstar s := by
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hprod
      have hlog : Real.log ((xstar + a • v) s) - Real.log (xstar s) < 0 :=
        sub_neg.mpr (Real.log_lt_log (hx s) horder)
      have hmul : 0 < (a * v s) *
          (Real.log ((xstar + a • v) s) - Real.log (xstar s)) :=
        mul_pos_of_neg_of_neg hprod hlog
      convert hmul using 1 <;> ring
  have hterm_nonneg : ∀ s,
      0 ≤ a * ((Real.log ((xstar + a • v) s) - Real.log (xstar s)) * v s) := by
    intro s
    by_cases hvs : v s = 0
    · simp [hvs]
    · exact (hterm_pos s hvs).le
  have ⟨s₀, hs₀⟩ : ∃ s, v s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  have hsum : 0 < ∑ s, a *
      ((Real.log ((xstar + a • v) s) - Real.log (xstar s)) * v s) :=
    Finset.sum_pos' (fun s _ => hterm_nonneg s)
      ⟨s₀, Finset.mem_univ s₀, hterm_pos s₀ hs₀⟩
  calc
    0 < ∑ s, a *
        ((Real.log ((xstar + a • v) s) - Real.log (xstar s)) * v s) := hsum
    _ = a * ∑ s, (Real.log ((xstar + a • v) s) - Real.log (xstar s)) * v s := by
      rw [Finset.mul_sum]

/-- In stoichiometric rank one, a positive complex-balanced orbit stays on the line segment
between its initial state and the positive equilibrium in that class. Relative entropy dissipation
makes the scalar displacement move monotonically toward zero; compactness then supplies a positive
omega-limit point. -/
theorem positiveOmegaPointForRates_of_complexBalanced_of_stoichRank_one
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hrank : N.stoichRank = 1) :
    N.PositiveOmegaPointForRates κ := by
  intro ϕ γ x₀ hϕγ hsol hbounded _hωnn _hgenω _hωaff hx₀
  have hwr : N.WeaklyReversible := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  obtain ⟨xeq, hxeqClass, hxeqcb⟩ :=
    N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx₀
  obtain ⟨hx₀compat, hxeqpos⟩ := hxeqClass
  have hfinrank : Module.finrank ℝ N.stoichSubspace = 1 := by
    simpa [Network.stoichRank] using hrank
  have hSneq : N.stoichSubspace ≠ ⊥ := by
    intro hbot
    rw [hbot] at hfinrank
    simp at hfinrank
  obtain ⟨v, hvS, hv0⟩ := N.stoichSubspace.ne_bot_iff.mp hSneq
  have hspan : N.stoichSubspace = ℝ ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfinrank hvS hv0
  obtain ⟨s₀, hs₀⟩ : ∃ s, v s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  let α : ℝ → ℝ := fun t => (γ x₀ t s₀ - xeq s₀) / v s₀
  let β : ℝ → ℝ := fun t => N.massActionVectorField κ (γ x₀ t) s₀ / v s₀
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ 0
    simpa using h.symm
  have hΓ0pos : (γ x₀ 0).Positive := by rw [hγ0]; exact hx₀
  have hΓpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive := N.genuineOrbit_pos κ hΓ0pos hsol
  have hdisp : ∀ t, 0 ≤ t → γ x₀ t - xeq ∈ N.stoichSubspace := by
    intro t ht
    have hsol' : ∀ τ ∈ Set.Icc (0 : ℝ) t,
        HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ τ)) τ := by
      intro τ hτ
      exact hsol τ hτ.1
    have hmove := N.sub_mem_stoichSubspace_of_solution κ ht hsol'
    rw [hγ0] at hmove
    have hcompat : x₀ - xeq ∈ N.stoichSubspace := hx₀compat.symm
    have heq : γ x₀ t - xeq = (γ x₀ t - x₀) + (x₀ - xeq) := by ring
    rw [heq]
    exact N.stoichSubspace.add_mem hmove hcompat
  have hαrepr : ∀ t, 0 ≤ t → γ x₀ t = xeq + α t • v := by
    intro t ht
    have hmem : γ x₀ t - xeq ∈ ℝ ∙ v := by rw [← hspan]; exact hdisp t ht
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hmem
    have hbcoord : b * v s₀ = γ x₀ t s₀ - xeq s₀ := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hb s₀
    have hbval : b = α t := by
      dsimp [α]
      calc
        b = (b * v s₀) / v s₀ := by field_simp [hs₀]
        _ = (γ x₀ t s₀ - xeq s₀) / v s₀ := by rw [hbcoord]
    have hvect : γ x₀ t - xeq = α t • v := by rw [← hbval]; exact hb.symm
    have hadd := congrArg (fun z => z + xeq) hvect
    simpa [add_comm] using hadd
  have hx₀repr : x₀ = xeq + α 0 • v := by
    have h := hαrepr 0 le_rfl
    rw [hγ0] at h
    exact h
  have hαderiv : ∀ t, 0 ≤ t → HasDerivAt α (β t) t := by
    intro t ht
    dsimp [α, β]
    exact ((hasDerivAt_pi.mp (hsol t ht)) s₀).sub_const (xeq s₀) |>.div_const (v s₀)
  have hfieldrepr : ∀ t, 0 ≤ t →
      N.massActionVectorField κ (γ x₀ t) = β t • v := by
    intro t ht
    have hfmem := N.massActionVectorField_mem_stoichSubspace κ (γ x₀ t)
    have hfspan : N.massActionVectorField κ (γ x₀ t) ∈ ℝ ∙ v := by
      rw [← hspan]
      exact hfmem
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hfspan
    have hbcoord : b * v s₀ = N.massActionVectorField κ (γ x₀ t) s₀ := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hb s₀
    have hbval : b = β t := by
      dsimp [β]
      calc
        b = (b * v s₀) / v s₀ := by field_simp [hs₀]
        _ = N.massActionVectorField κ (γ x₀ t) s₀ / v s₀ := by rw [hbcoord]
    rw [← hbval]
    exact hb.symm
  have hαbeta : ∀ t, 0 ≤ t → α t * β t ≤ 0 := by
    intro t ht
    by_cases hα0 : α t = 0
    · simp [hα0]
    · have hposrepr : (xeq + α t • v).Positive := by
        rw [← hαrepr t ht]
        exact hΓpos t ht
      have hdir := relativeEntropy_logDirection_smul_pos hxeqpos hv0 hα0 hposrepr
      rw [← hαrepr t ht] at hdir
      have hdiss := N.dissipation_nonpos κ (hΓpos t ht) hxeqpos hxeqcb
      have hfactor :
          (∑ s, (Real.log (γ x₀ t s) - Real.log (xeq s)) *
              N.massActionVectorField κ (γ x₀ t) s) =
            β t * ∑ s, (Real.log (γ x₀ t s) - Real.log (xeq s)) * v s := by
        calc
          _ = ∑ s, β t * ((Real.log (γ x₀ t s) - Real.log (xeq s)) * v s) := by
            apply Finset.sum_congr rfl
            intro s _
            rw [hfieldrepr t ht]
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
          _ = β t * ∑ s, (Real.log (γ x₀ t s) - Real.log (xeq s)) * v s := by
            rw [Finset.mul_sum]
      rw [hfactor] at hdiss
      by_cases hαpos : 0 < α t
      · have hdirpos : 0 < ∑ s, (Real.log (γ x₀ t s) - Real.log (xeq s)) * v s := by
          nlinarith [hdir]
        have hβnonpos : β t ≤ 0 := by
          by_contra hβ
          have hβpos : 0 < β t := lt_of_not_ge hβ
          exact (not_le_of_gt (mul_pos hβpos hdirpos)) hdiss
        exact mul_nonpos_of_nonneg_of_nonpos hαpos.le hβnonpos
      · have hαneg : α t < 0 := by
          rcases lt_or_eq_of_le (le_of_not_gt hαpos) with hlt | heq
          · exact hlt
          · exact (hα0 heq).elim
        have hdirneg : ∑ s, (Real.log (γ x₀ t s) - Real.log (xeq s)) * v s < 0 := by
          nlinarith [hdir]
        have hβnonneg : 0 ≤ β t := by
          by_contra hβ
          have hβneg : β t < 0 := lt_of_not_ge hβ
          exact (not_le_of_gt (mul_pos_of_neg_of_neg hβneg hdirneg)) hdiss
        exact mul_nonpos_of_nonpos_of_nonneg hαneg.le hβnonneg
  let E : ℝ → ℝ := α * α
  have hEderiv : ∀ t, 0 ≤ t → HasDerivAt E (β t * α t + α t * β t) t := by
    intro t ht
    have h := (hαderiv t ht).mul (hαderiv t ht)
    simpa [E] using h
  have hEanti : AntitoneOn E (Set.Ici 0) := by
    have hcont : ContinuousOn E (Set.Ici 0) := by
      intro t ht
      exact (hEderiv t ht).continuousAt.continuousWithinAt
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont ?_ ?_
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      exact (hEderiv t ht.le).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(hEderiv t ht.le).deriv]
      nlinarith [hαbeta t ht.le]
  have hsqle : ∀ t, 0 ≤ t → α t ^ 2 ≤ α 0 ^ 2 := by
    intro t ht
    have hE := hEanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simpa [E, Pi.mul_apply, pow_two] using hE
  have hαcont : ∀ T, 0 ≤ T → ContinuousOn α (Set.Icc 0 T) := by
    intro T hT t ht
    exact (hαderiv t ht.1).continuousAt.continuousWithinAt
  have horbit_segment : ∀ t, 0 ≤ t → ∀ s,
      min (x₀ s) (xeq s) ≤ γ x₀ t s := by
    intro t ht s
    have hsquare := hsqle t ht
    by_cases hαstart : α 0 = 0
    · have hαt : α t = 0 := by rw [hαstart] at hsquare; nlinarith [sq_nonneg (α t)]
      have hcoord : γ x₀ t s = xeq s := by
        rw [hαrepr t ht, hαt]
        simp
      rw [hcoord]
      exact min_le_right (x₀ s) (xeq s)
    · by_cases hαstartpos : 0 < α 0
      · have hαtnonneg : 0 ≤ α t := by
          by_contra h
          have hαtneg : α t < 0 := lt_of_not_ge h
          have hzero_mem : 0 ∈ Set.Icc (α t) (α 0) := ⟨hαtneg.le, hαstartpos.le⟩
          obtain ⟨u, hu, huzero⟩ :=
            intermediate_value_Icc' ht (hαcont t ht) hzero_mem
          have hEut := hEanti (Set.mem_Ici.mpr hu.1) (Set.mem_Ici.mpr ht) hu.2
          change α t * α t ≤ α u * α u at hEut
          rw [huzero] at hEut
          nlinarith [sq_nonneg (α t)]
        have hαtle : α t ≤ α 0 := by nlinarith [hsquare, sq_nonneg (α t - α 0)]
        let θ : ℝ := α t / α 0
        have hθ0 : 0 ≤ θ := div_nonneg hαtnonneg hαstartpos.le
        have hθ1 : θ ≤ 1 := (div_le_one hαstartpos).2 hαtle
        have hcoord : γ x₀ t s = (1 - θ) * xeq s + θ * x₀ s := by
          rw [hαrepr t ht, hx₀repr]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          dsimp [θ]
          field_simp [ne_of_gt hαstartpos]
          ring
        rw [hcoord]
        calc
          min (x₀ s) (xeq s) = (1 - θ) * min (x₀ s) (xeq s) +
              θ * min (x₀ s) (xeq s) := by ring
          _ ≤ (1 - θ) * xeq s + θ * x₀ s := add_le_add
              (mul_le_mul_of_nonneg_left (min_le_right (x₀ s) (xeq s)) (sub_nonneg.mpr hθ1))
              (mul_le_mul_of_nonneg_left (min_le_left (x₀ s) (xeq s)) hθ0)
      · have hαstartne : α 0 ≠ 0 := hαstart
        have hαstartneg : α 0 < 0 := by
          rcases lt_or_eq_of_le (le_of_not_gt hαstartpos) with hlt | heq
          · exact hlt
          · exact (hαstartne heq).elim
        have hαtnonpos : α t ≤ 0 := by
          by_contra h
          have hαtpos : 0 < α t := lt_of_not_ge h
          have hzero_mem : 0 ∈ Set.Icc (α 0) (α t) := ⟨hαstartneg.le, hαtpos.le⟩
          obtain ⟨u, hu, huzero⟩ := intermediate_value_Icc ht (hαcont t ht) hzero_mem
          have hEut := hEanti (Set.mem_Ici.mpr hu.1) (Set.mem_Ici.mpr ht) hu.2
          change α t * α t ≤ α u * α u at hEut
          rw [huzero] at hEut
          nlinarith [sq_nonneg (α t)]
        have hαstartle : α 0 ≤ α t := by nlinarith [hsquare, sq_nonneg (α t - α 0)]
        let θ : ℝ := α t / α 0
        have hθ0 : 0 ≤ θ := by
          dsimp [θ]
          have hnum : 0 ≤ -α t := by linarith
          have hden : 0 < -α 0 := by linarith
          have hdiv := div_nonneg hnum hden.le
          simpa using hdiv
        have hθ1 : θ ≤ 1 := (div_le_one_of_neg hαstartneg).2 hαstartle
        have hcoord : γ x₀ t s = (1 - θ) * xeq s + θ * x₀ s := by
          rw [hαrepr t ht, hx₀repr]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          dsimp [θ]
          field_simp [ne_of_lt hαstartneg]
          ring
        rw [hcoord]
        calc
          min (x₀ s) (xeq s) = (1 - θ) * min (x₀ s) (xeq s) +
              θ * min (x₀ s) (xeq s) := by ring
          _ ≤ (1 - θ) * xeq s + θ * x₀ s := add_le_add
              (mul_le_mul_of_nonneg_left (min_le_right (x₀ s) (xeq s)) (sub_nonneg.mpr hθ1))
              (mul_le_mul_of_nonneg_left (min_le_left (x₀ s) (xeq s)) hθ0)
  obtain ⟨K, hK, hmaps⟩ := hbounded
  have himageK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ u ∈ (atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ u {x₀}) ⊆ K := by
    refine ⟨Set.univ, univ_mem, ?_⟩
    exact (IsClosed.closure_subset_iff hK.isClosed).mpr himageK
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs
      (Set.singleton_nonempty x₀)
  refine ⟨p, hp, ?_⟩
  intro s
  have hclosed : IsClosed {z : Concentration S | min (x₀ s) (xeq s) ≤ z s} :=
    isClosed_le continuous_const (continuous_apply s)
  have horbit : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆
      {z : Concentration S | min (x₀ s) (xeq s) ≤ z s} := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [hϕγ x₀ t]
    exact horbit_segment t t.coe_nonneg s
  have hcl := hclosed.closure_subset_iff.mpr horbit
  have hpcoord : min (x₀ s) (xeq s) ≤ p s := by
    have hsub := (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ)
      (s := {x₀}) (u := Set.univ) univ_mem)
    exact (hsub.trans hcl) hp
  exact lt_of_lt_of_le (lt_min (hx₀ s) (hxeqpos s)) hpcoord

/-- **LaSalle for a supplied mass-action semiflow.**  Relative entropy to a positive
complex-balanced reference is constant on the ω-limit set of a bounded positive genuine orbit.

Unlike `omegaLimit_relEntropy_const_of_absorbed`, this does not build the flow: it works with
whatever semiflow `ϕ` is handed to `PositiveOmegaPointForRates`, and its hypotheses are exactly
the ones that predicate supplies.  Every theorem in `CRNT.Dynamics.GACOmegaPositive` consumes the
constant `hωc` as an assumption, while `PositiveOmegaPointForRates` does not provide it; this
lemma closes that mismatch and makes the boundary-face analysis usable at this interface. -/
theorem exists_relEntropy_const_on_omegaLimit
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hx₀ : x₀.Positive) :
    ∃ c : ℝ, ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c := by
  have hγ0 : γ x₀ 0 = x₀ := by simpa using (hϕγ x₀ 0).symm
  have hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos κ (by rw [hγ0]; exact hx₀) hsol
  have hd := fun (t : ℝ) (ht : 0 ≤ t) =>
    relEntropy_hasDerivAt hxs (hpos t ht) (fun s => (hasDerivAt_pi.mp (hsol t ht)) s)
  have hAnti : AntitoneOn (fun t => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt) ?_ ?_
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      exact (hd t ht.le).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(hd t ht.le).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxs hcb
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hK.isClosed).mpr hsubK⟩
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xstar (ϕ b x₀) ≤ relEntropy xstar (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg)
      (by exact_mod_cast hab)
  obtain ⟨c, -, -, hωc⟩ := Flow.laSalle ϕ (relEntropy_continuous hxs) x₀ hK habs hmono
  exact ⟨c, hωc⟩

/-- **Sharp boundary dichotomy at the `PositiveOmegaPointForRates` interface.**  For a positive
complex-balanced reference and exactly the data `PositiveOmegaPointForRates` supplies, either the
ω-limit set already contains a strictly positive point, or it contains a point `w` which is

* an equilibrium of the full mass-action field,
* nonnegative and stoichiometrically compatible with `x₀`, vanishing exactly on a nonempty `P`,
  so that `P`'s coordinate face *meets the compatibility class of* `x₀`,
* with `P` a critical siphon whose avoiding-face subnetwork is complex-balanced at the filled
  state and has strictly smaller stoichiometric rank.

This is `positiveOmega_or_lowerRankCriticalBoundaryFace` with the LaSalle constant derived rather
than assumed, plus the face-membership data made explicit. -/
theorem positiveOmega_or_criticalSiphonFaceEquilibrium
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive) :
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
      ∃ w ∈ omegaLimit atTop ϕ {x₀}, ∃ P : Finset S,
        P.Nonempty ∧ (∀ s, s ∈ P ↔ w s = 0) ∧ N.IsCriticalSiphon P ∧
        N.StoichCompatible x₀ w ∧ Concentration.Nonnegative w ∧
        N.massActionVectorField κ w = 0 ∧
        (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced
          (κ.restrict (N.avoidingSiphonReactions P)) (fillSiphonFace P xstar w) ∧
        (N.restrictReactions (N.avoidingSiphonReactions P)).stoichRank < N.stoichRank := by
  have hwr : N.WeaklyReversible := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  have hγ0 : ∀ x, γ x 0 = x := fun x => by simpa using (hϕγ x 0).symm
  obtain ⟨c, hωc⟩ :=
    N.exists_relEntropy_const_on_omegaLimit κ hxs hcb hϕγ hsol hK hmaps hx₀
  rcases N.positiveOmega_or_lowerRankCriticalBoundaryFace hwr κ hxs hcb hγ0 hϕγ hK hmaps
      hgenω hωnn hωaff hx₀ hωc with hgood | hbad
  · exact Or.inl hgood
  · obtain ⟨w, hw, P, hPne, hzeroSet, hPcrit, hfacecb, hranklt, hsteady⟩ := hbad
    exact Or.inr ⟨w, hw, P, hPne, hzeroSet, hPcrit, hωaff w hw, hωnn w hw, hsteady,
      hfacecb, hranklt⟩

/-- **Class-relative Angeli–De Leenheer–Sontag criterion.**  A sufficient condition for the
omega-interior certificate that is strictly weaker than `HasNoCriticalSiphon`: critical siphons
are permitted, provided no critical siphon's coordinate face meets a positive compatibility
class.  `positiveOmegaPointForRates_of_boundaryOmegaExcluded` needs the *global* structural
condition; this needs only that the faces miss the classes. -/
theorem positiveOmegaPointForRates_of_criticalSiphonFaces_miss_classes
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hmiss : ∀ y₀ : Concentration S, y₀.Positive → ∀ P : Finset S, N.IsCriticalSiphon P →
      ∀ z : Concentration S, N.StoichCompatible y₀ z → Concentration.Nonnegative z →
        (∀ s ∈ P, z s = 0) → False) :
    N.PositiveOmegaPointForRates κ := by
  intro ϕ γ x₀ hϕγ hsol hbounded hωnn hgenω hωaff hx₀
  obtain ⟨K, hK, hmaps⟩ := hbounded
  rcases N.positiveOmega_or_criticalSiphonFaceEquilibrium κ hxs hcb hϕγ hsol hK hmaps
      hωnn hgenω hωaff hx₀ with hgood | hbad
  · exact hgood
  · obtain ⟨w, -, P, -, hzeroSet, hPcrit, hcompat, hwnn, -, -, -⟩ := hbad
    exact (hmiss x₀ hx₀ P hPcrit w hcompat hwnn (fun s hs => (hzeroSet s).1 hs)).elim

/-- **Every ω-point of a complex-balanced orbit is a fixed point of the semiflow.**  Relative
entropy is constant on the ω-limit set, so every ω-point is an equilibrium of the mass-action
field (`massActionVectorField_eq_zero_on_omegaLimit`); the constant curve is then a solution
through it, and box-confined ODE uniqueness (`genuineOrbit_unique_of_box`, which needs no
positivity) identifies the two.  The box bound comes from the compact absorbing set.

Consequence: the Butler–McGehee escape machinery of `Dynamics/EscapeSiphonFace.lean` is
**vacuous** on the ω-limit set of a complex-balanced orbit — see
`omegaLimit_singleton_of_mem_omegaLimit`. -/
theorem omegaLimit_fixed_of_complexBalanced
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hx₀ : x₀.Positive) :
    ∀ w ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t → γ w t = w := by
  have hwr : N.WeaklyReversible := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  have hγ0 : ∀ x, γ x 0 = x := fun x => by simpa using (hϕγ x 0).symm
  obtain ⟨c, hωc⟩ :=
    N.exists_relEntropy_const_on_omegaLimit κ hxs hcb hϕγ hsol hK hmaps hx₀
  have hsteady : ∀ w ∈ omegaLimit atTop ϕ {x₀}, N.massActionVectorField κ w = 0 :=
    N.massActionVectorField_eq_zero_on_omegaLimit hwr κ hxs hcb hγ0 hϕγ hK hmaps hgenω hωnn hωc
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have hωK : omegaLimit atTop ϕ {x₀} ⊆ K := by
    refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ)
      (s := {x₀}) (u := Set.univ) univ_mem).trans ?_
    exact (IsClosed.closure_subset_iff hK.isClosed).mpr hsubK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Concentration S)
  have hB : (0 : ℝ) ≤ max r 0 := le_max_right _ _
  have hbound : ∀ y ∈ K, ∀ s, |y s| ≤ max r 0 := by
    intro y hy s
    have h1 : ‖y‖ ≤ r := by simpa [Metric.mem_closedBall] using hr hy
    have h2 : ‖y s‖ ≤ ‖y‖ := norm_le_pi_norm y s
    calc |y s| = ‖y s‖ := rfl
      _ ≤ ‖y‖ := h2
      _ ≤ r := h1
      _ ≤ max r 0 := le_max_left _ _
  have hinv : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      γ y t ∈ omegaLimit atTop ϕ {x₀} := by
    intro y hy t ht
    have h := (Flow.isInvariant_omegaLimit atTop ϕ {x₀}
      (fun s => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) ⟨t, ht⟩) hy
    exact (hϕγ y ⟨t, ht⟩) ▸ h
  intro w hw t ht
  have hconstd : ∀ τ : ℝ, 0 ≤ τ →
      HasDerivAt (fun _ : ℝ => w) (N.massActionVectorField κ ((fun _ : ℝ => w) τ)) τ := by
    intro τ _
    simpa [hsteady w hw] using (hasDerivAt_const τ w)
  have hbox₁ : ∀ τ : ℝ, 0 ≤ τ → ∀ s, |γ w τ s| ≤ max r 0 :=
    fun τ hτ s => hbound _ (hωK (hinv w hw τ hτ)) s
  have hbox₂ : ∀ τ : ℝ, 0 ≤ τ → ∀ s, |(fun _ : ℝ => w) τ s| ≤ max r 0 :=
    fun _ _ s => hbound _ (hωK hw) s
  exact N.genuineOrbit_unique_of_box κ hB (hgenω w hw) hconstd hbox₁ hbox₂
    (by simpa using hγ0 w) t ht

/-- **The ω-limit set of a complex-balanced orbit consists of semiflow fixed points, each its own
forward limit.**  Hence `Dynamics/ButlerMcGehee.lean` and
`exists_escape_forwardLimit_criticalSiphonFace` cannot produce a siphon-dimension descent here:
the forward limit `ω{q}` of an escaping ω-point `q` is just `{q}`, so no new boundary structure is
exposed.  This records a closed-off route, not a step toward the residual obligation. -/
theorem omegaLimit_singleton_of_mem_omegaLimit
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hx₀ : x₀.Positive)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀}) :
    (∀ t : ℝ≥0, ϕ t w = w) ∧ omegaLimit atTop ϕ {w} = {w} := by
  have hfix : ∀ t : ℝ≥0, ϕ t w = w := by
    intro t
    exact (hϕγ w t).trans
      (N.omegaLimit_fixed_of_complexBalanced κ hxs hcb hϕγ hsol hK hmaps hωnn hgenω hx₀
        w hw (t : ℝ) t.coe_nonneg)
  refine ⟨hfix, ?_⟩
  have horb : Set.image2 ϕ (Set.univ : Set ℝ≥0) {w} = {w} := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, -, x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst x
      rw [hfix t]
      exact Set.mem_singleton w
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨0, Set.mem_univ _, w, Set.mem_singleton w, hfix 0⟩
  have hsub : omegaLimit atTop ϕ {w} ⊆ {w} := by
    refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ)
      (s := {w}) (u := Set.univ) univ_mem).trans ?_
    rw [horb, closure_singleton]
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {w}) ⊆ ({w} : Set (Concentration S)) := by
    refine ⟨Set.univ, univ_mem, ?_⟩
    rw [horb, closure_singleton]
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {w} isCompact_singleton habs
      (Set.singleton_nonempty w)
  apply Set.Subset.antisymm hsub
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  have hpw : p = w := Set.mem_singleton_iff.mp (hsub hp)
  exact hpw ▸ hp

/-- **An orbit that ever reaches an equilibrium has a positive ω-point.**  If the genuine orbit
through a positive `x₀` is stationary at some `t₀ ≥ 0`, box-confined ODE uniqueness makes it
constant from `t₀` on, so the ω-limit set is the singleton `{γ x₀ t₀}`, and that point is positive
because genuine orbits from positive starts stay positive.  This discharges the stationary
subcase of the residual Global Attractor obligation. -/
theorem positiveOmegaPoint_of_orbit_stationary
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hx₀ : x₀.Positive)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hstat : N.massActionVectorField κ (γ x₀ t₀) = 0) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  have hγ0 : γ x₀ 0 = x₀ := by simpa using (hϕγ x₀ 0).symm
  have hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos κ (by rw [hγ0]; exact hx₀) hsol
  set q : Concentration S := γ x₀ t₀ with hqdef
  -- a uniform coordinate bound on the compact absorbing set
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Concentration S)
  have hB : (0 : ℝ) ≤ max r 0 := le_max_right _ _
  have hbound : ∀ y ∈ K, ∀ s, |y s| ≤ max r 0 := by
    intro y hy s
    have h1 : ‖y‖ ≤ r := by simpa [Metric.mem_closedBall] using hr hy
    calc |y s| = ‖y s‖ := rfl
      _ ≤ ‖y‖ := norm_le_pi_norm y s
      _ ≤ r := h1
      _ ≤ max r 0 := le_max_left _ _
  have horbK : ∀ t : ℝ, 0 ≤ t → γ x₀ t ∈ K := by
    intro t ht
    have := hmaps ⟨t, ht⟩
    rwa [hϕγ x₀ ⟨t, ht⟩] at this
  -- the shifted orbit and the constant curve are both solutions from `q`
  have hshiftd : ∀ τ : ℝ, 0 ≤ τ →
      HasDerivAt (fun u : ℝ => γ x₀ (u + t₀))
        (N.massActionVectorField κ ((fun u : ℝ => γ x₀ (u + t₀)) τ)) τ := by
    intro τ hτ
    exact HasDerivAt.comp_add_const τ t₀ (hsol (τ + t₀) (by linarith))
  have hconstd : ∀ τ : ℝ, 0 ≤ τ →
      HasDerivAt (fun _ : ℝ => q) (N.massActionVectorField κ ((fun _ : ℝ => q) τ)) τ := by
    intro τ _
    have hz : N.massActionVectorField κ ((fun _ : ℝ => q) τ) = 0 := hstat
    rw [hz]
    exact hasDerivAt_const τ q
  have hbox₁ : ∀ τ : ℝ, 0 ≤ τ → ∀ s, |(fun u : ℝ => γ x₀ (u + t₀)) τ s| ≤ max r 0 :=
    fun τ hτ s => hbound _ (horbK (τ + t₀) (by linarith)) s
  have hbox₂ : ∀ τ : ℝ, 0 ≤ τ → ∀ s, |(fun _ : ℝ => q) τ s| ≤ max r 0 :=
    fun _ _ s => hbound _ (horbK t₀ ht₀) s
  have htail : ∀ τ : ℝ, 0 ≤ τ → γ x₀ (τ + t₀) = q :=
    N.genuineOrbit_unique_of_box κ hB hshiftd hconstd hbox₁ hbox₂ (by simp [hqdef])
  -- hence the flow is eventually constant at `q`
  let a : ℝ≥0 := ⟨t₀, ht₀⟩
  have hflowtail : ∀ t : ℝ≥0, a ≤ t → ϕ t x₀ = q := by
    intro t hat
    have hle : t₀ ≤ (t : ℝ) := by exact_mod_cast hat
    have := htail ((t : ℝ) - t₀) (by linarith)
    rw [hϕγ x₀ t]
    simpa using this
  have horb : Set.image2 ϕ (Set.Ici a) {x₀} = {q} := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst x
      rw [hflowtail t (Set.mem_Ici.mp ht)]
      exact Set.mem_singleton q
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨a, Set.mem_Ici.mpr le_rfl, x₀, Set.mem_singleton x₀, hflowtail a le_rfl⟩
  have hsub : omegaLimit atTop ϕ {x₀} ⊆ {q} := by
    refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ)
      (s := {x₀}) (u := Set.Ici a) (Filter.Ici_mem_atTop a)).trans ?_
    rw [horb, closure_singleton]
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {x₀}) ⊆ ({q} : Set (Concentration S)) := by
    refine ⟨Set.Ici a, Filter.Ici_mem_atTop a, ?_⟩
    rw [horb, closure_singleton]
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} isCompact_singleton habs
      (Set.singleton_nonempty x₀)
  have hpq : p = q := Set.mem_singleton_iff.mp (hsub hp)
  exact ⟨p, hp, by rw [hpq, hqdef]; exact hpos t₀ ht₀⟩

/-- **Residual dichotomy, with the stationary subcase removed.**  Either the ω-limit set already
contains a strictly positive point, or the orbit is *never* stationary — equivalently, relative
entropy is strictly decreasing along it — *and* the ω-limit set contains a critical-siphon
boundary equilibrium with the structural data of
`positiveOmega_or_criticalSiphonFaceEquilibrium`.  The nonstationarity conjunct is what the
Anderson--Shiu near-facet estimate expects as its starting point. -/
theorem positiveOmega_or_nonstationary_criticalSiphonFaceEquilibrium
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive) :
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
      ((∀ t : ℝ, 0 ≤ t → N.massActionVectorField κ (γ x₀ t) ≠ 0) ∧
        ∃ w ∈ omegaLimit atTop ϕ {x₀}, ∃ P : Finset S,
          P.Nonempty ∧ (∀ s, s ∈ P ↔ w s = 0) ∧ N.IsCriticalSiphon P ∧
          N.StoichCompatible x₀ w ∧ Concentration.Nonnegative w ∧
          N.massActionVectorField κ w = 0 ∧
          (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced
            (κ.restrict (N.avoidingSiphonReactions P)) (fillSiphonFace P xstar w) ∧
          (N.restrictReactions (N.avoidingSiphonReactions P)).stoichRank < N.stoichRank) := by
  by_cases hstat : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ N.massActionVectorField κ (γ x₀ t₀) = 0
  · obtain ⟨t₀, ht₀, hz⟩ := hstat
    exact Or.inl
      (N.positiveOmegaPoint_of_orbit_stationary κ hϕγ hsol hK hmaps hx₀ ht₀ hz)
  · have hns : ∀ t : ℝ, 0 ≤ t → N.massActionVectorField κ (γ x₀ t) ≠ 0 := by
      intro t ht hz
      exact hstat ⟨t, ht, hz⟩
    rcases N.positiveOmega_or_criticalSiphonFaceEquilibrium κ hxs hcb hϕγ hsol hK hmaps
        hωnn hgenω hωaff hx₀ with hgood | hbad
    · exact Or.inl hgood
    · exact Or.inr ⟨hns, hbad⟩

/-- **No boundary equilibrium in any positive class ⇒ the omega-interior certificate.**  This is
the sharpest *structural* sufficient condition the residual dichotomy yields, and it is strictly
weaker than both `HasNoCriticalSiphon` and
`positiveOmegaPointForRates_of_criticalSiphonFaces_miss_classes`: critical siphons are permitted,
their coordinate faces may meet positive compatibility classes, and all that is required is that
no *equilibrium* sits on such a face.  Every ω-point of a complex-balanced orbit is an equilibrium
in the class, so the hypothesis applies to it directly.

Beyond this the structural line is exhausted: for a weakly reversible complex-balanced network
with a critical siphon, the face subnetwork is itself complex-balanced
(`positiveOmega_or_criticalSiphonFaceEquilibrium`) and so normally *does* carry a boundary
equilibrium.  Excluding it is no longer a structural question but the analytic content of the
Global Attractor Conjecture. -/
theorem positiveOmegaPointForRates_of_no_boundary_equilibrium_in_classes
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hno : ∀ y₀ : Concentration S, y₀.Positive → ∀ z : Concentration S,
      N.StoichCompatible y₀ z → Concentration.Nonnegative z →
        N.massActionVectorField κ z = 0 → z.Positive) :
    N.PositiveOmegaPointForRates κ := by
  intro ϕ γ x₀ hϕγ hsol hbounded hωnn hgenω hωaff hx₀
  obtain ⟨K, hK, hmaps⟩ := hbounded
  rcases N.positiveOmega_or_criticalSiphonFaceEquilibrium κ hxs hcb hϕγ hsol hK hmaps
      hωnn hgenω hωaff hx₀ with hgood | hbad
  · exact hgood
  · obtain ⟨w, hw, P, -, -, -, hcompat, hwnn, hsteady, -, -⟩ := hbad
    exact ⟨w, hw, hno x₀ hx₀ w hcompat hwnn hsteady⟩

/-- **The two structural criteria are ordered.**  If no critical siphon's coordinate face meets a
positive compatibility class, then a fortiori no *equilibrium* sits on such a face.  The zero set
of a nonnegative equilibrium is forced to be a siphon by strict inflow
(`massActionVectorField_pos_of_not_isSiphon`), and a siphon face meeting a positive class is
critical (`criticalSiphon_of_compatibilityFace_nonempty`).  So
`positiveOmegaPointForRates_of_no_boundary_equilibrium_in_classes` subsumes
`positiveOmegaPointForRates_of_criticalSiphonFaces_miss_classes`, which in turn subsumes the
`HasNoCriticalSiphon` branch. -/
theorem no_boundary_equilibrium_of_criticalSiphonFaces_miss_classes
    (N : Network S) (κ : N.RateConstants)
    (hmiss : ∀ y₀ : Concentration S, y₀.Positive → ∀ P : Finset S, N.IsCriticalSiphon P →
      ∀ z : Concentration S, N.StoichCompatible y₀ z → Concentration.Nonnegative z →
        (∀ s ∈ P, z s = 0) → False) :
    ∀ y₀ : Concentration S, y₀.Positive → ∀ z : Concentration S,
      N.StoichCompatible y₀ z → Concentration.Nonnegative z →
        N.massActionVectorField κ z = 0 → z.Positive := by
  classical
  intro y₀ hy₀ z hcompat hznn hsteady s₁
  by_contra hns₁
  have hs₁0 : z s₁ = 0 := le_antisymm (not_lt.mp hns₁) (hznn s₁)
  set P : Finset S := Finset.univ.filter (fun s => z s = 0) with hPdef
  have hP : ∀ s, s ∈ P ↔ z s = 0 := by
    intro s
    simp [hPdef]
  have hPne : P.Nonempty := ⟨s₁, (hP s₁).2 hs₁0⟩
  have hzeros : ∀ s ∈ P, z s = 0 := fun s hs => (hP s).1 hs
  have hsiph : N.IsSiphon P := by
    by_contra hns
    obtain ⟨s, -, hpos⟩ := N.massActionVectorField_pos_of_not_isSiphon κ hznn hP hns
    rw [hsteady] at hpos
    simpa using hpos
  have hcrit : N.IsCriticalSiphon P :=
    N.criticalSiphon_of_compatibilityFace_nonempty hy₀ hPne hsiph
      ⟨z, hcompat, hznn, hzeros⟩
  exact (hmiss y₀ hy₀ P hcrit z hcompat hznn hzeros).elim

/-- **Deep permanence kernel for the Global Attractor Theorem.**  Every positive
complex-balanced mass-action system is class-uniformly permanent for genuine forward
trajectories.  This is the toric-differential-inclusion / zero-separating-surface content of
Craciun's theorem, stated without the potentially vacuous assumption of a global ambient flow. -/
theorem complexBalanced_genuinePermanent
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.GenuinePermanentForRates κ := by
  apply N.complexBalanced_genuinePermanent_of_positiveOmegaPointForRates κ hxs hcb
  by_cases hncs : N.HasNoCriticalSiphon
  · exact N.positiveOmegaPointForRates_of_boundaryOmegaExcluded κ
      (N.boundaryOmegaExcluded_of_hasNoCriticalSiphon κ hncs)
  · by_cases hzero : N.stoichSubspace = ⊥
    · exact N.positiveOmegaPointForRates_of_trivialStoichSubspace κ hzero
    · by_cases hrank : N.stoichRank = 1
      · exact N.positiveOmegaPointForRates_of_complexBalanced_of_stoichRank_one
          κ hxs hcb hrank
      · -- Remaining deep kernel, narrowed to its sharp form by
        -- `positiveOmega_or_criticalSiphonFaceEquilibrium`.  The dichotomy discharges every
        -- orbit that already has a positive omega-point, so what is left is exactly the
        -- critical-siphon boundary case.
        intro hϕγ hsol hbounded hωnn hgenω hωaff hx₀
        obtain ⟨K, hK, hmaps⟩ := hbounded
        rcases N.positiveOmega_or_nonstationary_criticalSiphonFaceEquilibrium κ hxs hcb
            hϕγ hsol hK hmaps hωnn hgenω hωaff hx₀ with hgood | ⟨_, hbad⟩
        · exact hgood
        · obtain ⟨w, hw, P, hPne, hzeroSet, -, -, -, -, -, -⟩ := hbad
          obtain ⟨wmax, hwmax, Pmax, hPmaxne, hzeroMax, hmaxExact, hzcard⟩ :=
            exists_maximal_zeroSet_omegaPoint hw hPne hzeroSet
          by_cases hfacet : Module.finrank ℝ
              (LinearMap.ker ((projOn Pmax).domRestrict N.stoichSubspace)) + 1 =
                Module.finrank ℝ N.stoichSubspace
          · have hwr : N.WeaklyReversible :=
              N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
            exact False.elim
              (N.no_omegaLimit_meets_locally_repelling_face κ hϕγ hK hmaps
                hPmaxne
                ⟨wmax, hwmax, fun s hs => (hzeroMax s).1 hs⟩
                (N.genuineOrbit_pos κ (by
                  have hγ0 := fun x => by simpa using (hϕγ x 0).symm
                  rw [hγ0]
                  exact hx₀) hsol)
                hsol
                (by
                  intro z hz hzP
                  have hpositiveOutside : ∀ s, s ∈ Pmaxᶜ → 0 < z s := by
                    intro s hs
                    have hsnot : s ∉ Pmax := by simpa using hs
                    have hnonzero : z s ≠ 0 := by
                      intro hzs
                      exact hsnot ((hmaxExact z hz hzP s).1 hzs)
                    rcases lt_or_eq_of_le (hωnn z hz s) with hpos | heq
                    · exact hpos
                    · exact (hnonzero heq.symm).elim
                  exact N.facet_repelling_near_facet_point_of_facet κ hwr hPmaxne hfacet hx₀
                    (hωaff z hz) (hωnn z hz) hzP hpositiveOutside))
          · -- Remaining case: the maximal boundary face is not a facet.  The degenerate failure
            -- (the `Pmax`-projection of the stoichiometric subspace being zero) is impossible,
            -- because every stoichiometric displacement would then vanish on `Pmax` and force
            -- `wmax s = x₀ s > 0` against `wmax s = 0`; `highCodimension_of_not_facet` also
            -- returns `2 ≤ Pmax.card`, since a one-species face always satisfies the facet
            -- count.  So this branch is exactly the codimension `≥ 2` case, and the whole
            -- residual content is isolated in
            -- `CRNT.Dynamics.HighCodimensionSiphonFace`.
            have hcompatMax := hωaff wmax hwmax
            have hzerosMax : ∀ s ∈ Pmax, wmax s = 0 := fun s hs => (hzeroMax s).1 hs
            obtain ⟨hcodim, hcard⟩ :=
              N.highCodimension_of_not_facet hx₀ hcompatMax hzerosMax hPmaxne hfacet
            exact N.exists_positive_omegaPoint_of_highCodimension_siphonFace κ hxs hcb
              hϕγ hsol hK hmaps hωnn hgenω hωaff hx₀ hPmaxne hwmax hzeroMax hmaxExact hzcard
              hcodim hcard hrank

/-- The trajectory-level permanence theorem implies the older flow-quantified standard
permanence API whenever a genuine global mass-action flow is supplied. -/
theorem complexBalanced_permanent
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.PermanentForRates κ := by
  intro ϕ γ hflow xref hxref
  obtain ⟨K, hKcpt, hKclass, habs⟩ :=
    N.complexBalanced_genuinePermanent κ hxs hcb xref hxref
  refine ⟨K, hKcpt, hKclass, ?_⟩
  intro x₀ hxclass
  rcases hflow with ⟨hγ0, hϕγ, hγd⟩
  obtain ⟨T, hT0, htail⟩ := habs x₀ hxclass (γ x₀) (hγ0 x₀) (hγd x₀)
  let a : ℝ≥0 := ⟨T, hT0⟩
  refine ⟨Set.Ici a, Filter.Ici_mem_atTop a, ?_⟩
  rw [IsClosed.closure_subset_iff hKcpt.isClosed]
  rintro y ⟨t, ht, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at hx
  subst x
  rw [hϕγ]
  apply htail (t : ℝ)
  change T ≤ (t : ℝ)
  exact_mod_cast ht

/-- Eventual class-uniform genuine permanence plus genuine-orbit uniqueness upgrades one
specified genuine trajectory to the all-time compact persistence certificate consumed by the
cutoff-flow GAC machinery. -/
theorem GenuinePermanentOnPositiveClass.persistentFrom_of_trajectory
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hperm : N.GenuinePermanentOnPositiveClass κ xstar)
    (hxclass : x₀ ∈ N.positiveCompatibilityClass xstar)
    {Γ : ℝ → Concentration S} (hΓ0 : Γ 0 = x₀)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    N.PersistentFrom κ x₀ := by
  obtain ⟨K, hKcpt, hKclass, habs⟩ := hperm
  obtain ⟨T, hT0, htail⟩ := habs x₀ hxclass Γ hΓ0 hΓd
  have hx₀ : x₀.Positive := hxclass.2
  have hΓpos : ∀ t, 0 ≤ t → (Γ t).Positive := by
    apply N.genuineOrbit_pos κ
    · simpa [hΓ0] using hx₀
    · exact hΓd
  have hcont : ContinuousOn Γ (Set.Icc (0 : ℝ) T) :=
    fun t ht => (hΓd t ht.1).continuousAt.continuousWithinAt
  have hIcpt : IsCompact (Γ '' Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.image_of_continuousOn hcont
  let K₀ : Set (Concentration S) := Γ '' Set.Icc (0 : ℝ) T ∪ K
  refine ⟨K₀, hIcpt.union hKcpt, ?_, ?_⟩
  · intro y hy
    rcases hy with hy | hy
    · rcases hy with ⟨t, ht, rfl⟩
      exact hΓpos t ht.1
    · exact (hKclass hy).2
  · intro Ψ hΨ0 hΨd t ht
    have heq : Ψ t = Γ t :=
      N.genuineOrbit_unique κ hxs hcb hx₀ hΨ0 hΓ0 hΨd hΓd t ht
    rw [heq]
    by_cases htT : t ≤ T
    · exact Set.mem_union_left K ⟨t, ⟨ht, htT⟩, rfl⟩
    · exact Set.mem_union_right _ (htail t (le_of_lt (lt_of_not_ge htT)))

/-- **Global Attractor Theorem.** A positive complex-balanced equilibrium globally attracts
its entire positive stoichiometric compatibility class. -/
theorem complexBalanced_globalAttractor
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.HasGlobalAttractorProperty κ xstar := by
  intro ϕ γ hflow
  refine ⟨hflow, ?_⟩
  intro x₀ hx₀ hcompat
  have hpermClass : N.PermanentOnPositiveClass ϕ xstar :=
    N.complexBalanced_permanent κ hxs hcb ϕ γ hflow xstar hxs
  have hx₀class : x₀ ∈ N.positiveCompatibilityClass xstar :=
    ⟨hcompat.symm, hx₀⟩
  have hpermOrbit : Permanent ϕ x₀ := hpermClass.permanent hx₀class
  rcases hflow with ⟨hγ0, hϕγ, hγd⟩
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  have hpos : ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ x₀ t) :=
    N.genuineOrbit_pos κ (by simpa [hγ0] using hx₀) (hγd x₀)
  have hcontOn : ContinuousOn (fun t : ℝ => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    intro t ht
    exact (relEntropy_continuous hxs).continuousAt.comp_continuousWithinAt
      ((hγd x₀ t ht).continuousAt.continuousWithinAt)
  have hAnti : AntitoneOn (fun t : ℝ => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcontOn ?_ ?_
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      exact (relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hγd x₀ t ht.le)) s)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hγd x₀ t ht.le)) s)).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxs hcb
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xstar (ϕ b x₀) ≤ relEntropy xstar (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg)
      (by exact_mod_cast hab)
  rcases hpermOrbit with ⟨K, hKcpt, hKpos, v, hv, hvK⟩
  obtain ⟨c, _, _hωinv, hωc⟩ :=
    Flow.laSalle ϕ (relEntropy_continuous hxs) x₀ hKcpt ⟨v, hv, hvK⟩ hmono
  have hωK : omegaLimit atTop ϕ {x₀} ⊆ K := by
    exact (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) hv).trans hvK
  have hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y := by
    intro y hy
    exact (hKpos y (hωK hy)).nonnegative
  have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
    N.stoichSubspace.closed_of_finiteDimensional
  have haffclosed : IsClosed {z : Concentration S | z - x₀ ∈ N.stoichSubspace} :=
    IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
  have horbit_aff : ∀ t : ℝ≥0, ϕ t x₀ - x₀ ∈ N.stoichSubspace := by
    intro t
    rw [hϕγ]
    have hsol' : ∀ τ ∈ Set.Icc (0:ℝ) ↑t,
        HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ τ)) τ :=
      fun τ hτ => hγd x₀ τ hτ.1
    have hs := sub_mem_stoichSubspace_of_solution N κ t.coe_nonneg hsol'
    rwa [hγ0] at hs
  have hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace := by
    have hsub : omegaLimit atTop ϕ {x₀} ⊆ {z | z - x₀ ∈ N.stoichSubspace} := by
      refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
        univ_mem).trans ?_
      refine (IsClosed.closure_subset_iff haffclosed).mpr ?_
      rintro z ⟨t, -, x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact horbit_aff t
    exact fun z hz => hsub hz
  have hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t := by
    intro y _ t ht
    exact hγd y t ht
  have hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t) := by
    intro p _ hp
    apply N.genuineOrbit_pos κ
    · simpa [hγ0] using hp
    · exact hγd p
  apply N.gac_of_permanent hwr κ hxs hcb hcompat hγ0 hϕγ hgenω hωnn hωaff hωc hposorbit
  exact ⟨K, hKcpt, hKpos, v, hv, hvK⟩

/-- The theorem does not need weak reversibility as a separate hypothesis: existence of a
positive complex-balanced equilibrium already implies weak reversibility. -/
theorem globalAttractor_implies_weaklyReversible
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) : N.WeaklyReversible := by
  exact N.weaklyReversible_of_positive_complexBalanced κ hxs hcb

/-- Trajectory-level convergence formulation of the Global Attractor Theorem. -/
def PositiveClassTrajectoryConverges (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S) : Prop :=
  ∀ γ : ℝ → Concentration S,
    γ 0 |>.Positive →
    N.StoichCompatible (γ 0) xstar →
    (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
    Tendsto γ atTop (𝓝 xstar)

/-- Equivalent convergence form: every genuine positive trajectory in the class tends to the
complex-balanced equilibrium. -/
theorem complexBalanced_trajectory_converges
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.PositiveClassTrajectoryConverges κ xstar := by
  intro Γ hΓ0pos hcompat hΓd
  have hxclass : Γ 0 ∈ N.positiveCompatibilityClass xstar :=
    ⟨hcompat.symm, hΓ0pos⟩
  have hpermClass : N.GenuinePermanentOnPositiveClass κ xstar :=
    N.complexBalanced_genuinePermanent κ hxs hcb xstar hxs
  have hpers : N.PersistentFrom κ (Γ 0) :=
    GenuinePermanentOnPositiveClass.persistentFrom_of_trajectory
      (N := N) κ hxs hcb hpermClass hxclass rfl hΓd
  rcases hpers with ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  obtain ⟨ϕ, γ, hγ0, hϕγ, hsol, hω⟩ :=
    N.gac_of_persistent hwr κ hxs hcb hΓ0pos hcompat
      ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have horbitK : ∀ t : ℝ≥0, ϕ t (Γ 0) ∈ K₀ := by
    intro t
    rw [hϕγ]
    exact hgen (γ (Γ 0)) (hγ0 (Γ 0)) hsol (t : ℝ) t.coe_nonneg
  have htendNN : Tendsto (fun t : ℝ≥0 => ϕ t (Γ 0)) atTop (𝓝 xstar) := by
    apply hK₀cpt.tendsto_nhds_of_unique_mapClusterPt
    · exact Filter.Eventually.of_forall horbitK
    · intro y _hy hcluster
      have hyω : y ∈ omegaLimit atTop ϕ {Γ 0} :=
        (mem_omegaLimit_singleton_iff_mapClusterPt atTop ϕ (Γ 0) y).2 hcluster
      rw [hω, Set.mem_singleton_iff] at hyω
      exact hyω
  have htendReal : Tendsto (fun t : ℝ => ϕ (Real.toNNReal t) (Γ 0)) atTop (𝓝 xstar) :=
    htendNN.comp Real.tendsto_toNNReal_atTop
  have hevent : (fun t : ℝ => ϕ (Real.toNNReal t) (Γ 0)) =ᶠ[atTop] Γ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hϕγ, Real.coe_toNNReal t ht]
    exact (N.genuineOrbit_unique κ hxs hcb hΓ0pos rfl (hγ0 (Γ 0))
      hΓd hsol t ht).symm
  exact Filter.Tendsto.congr' hevent htendReal

/-- Every positive class of a complex-balanced system has exactly one positive equilibrium and
that equilibrium is globally asymptotically stable relative to the class. -/
theorem complexBalanced_uniqueGlobalEquilibrium_in_class
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx₀ : x₀.Positive) :
    ∃! x : Concentration S,
      N.StoichCompatible x₀ x ∧ x.Positive ∧ N.IsMassActionSteadyState κ x := by
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  obtain ⟨x, hxclass, hxcb⟩ :=
    N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx₀
  refine ⟨x, ⟨hxclass.1, hxclass.2, hxcb.isMassActionSteadyState N κ⟩, ?_⟩
  intro y hy
  have hycb : N.IsComplexBalanced κ y := by
    apply N.complexBalanced_of_dissipation_eq_zero κ hy.2.1 hxs hcb
    apply Finset.sum_eq_zero
    intro s _
    rw [hy.2.2 s, mul_zero]
  exact N.isComplexBalanced_unique_in_positiveClass
    (x₀ := x₀) (x := x) (y := y) hwr κ
    hxclass ⟨hy.1, hy.2.1⟩ hxcb hycb |>.symm

end Network
end CRNT
