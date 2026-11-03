import CRNT.Theorems.DeficiencyZero.AsymptoticStability
import CRNT.Dynamics.LaSalle

/-!
# Global asymptotic stability under persistence

For a weakly reversible network with a positive complex-balanced reference `x*`, the relative
entropy `relEntropy x* ·` is a strict Lyapunov function whose dissipation vanishes only at the
complex-balanced equilibria. The local stability theorem
(`omegaLimit_eq_singleton_of_local`) closes the orbit's ω-limit set onto `{x*}` whenever the
start `x₀` is close enough that its relative entropy lies below every reference coordinate,
which keeps every ω-point off the orthant boundary.

`omegaLimit_eq_singleton_of_persistent` removes that closeness assumption and replaces it with
**persistence**: the orbit is absorbed by a compact set `K₀` of strictly positive
concentrations. Persistence is exactly the input that rules out boundary ω-limit points for an
arbitrary positive start, so its single hypothesis upgrades local convergence to convergence
from any persistent positive trajectory in `x*`'s compatibility class: `ω(x₀) = {x*}`.

The relative-entropy sublevel confinement (`orbit_relEntropy_le`, `orbit_pos`,
`clampBox_eq_of_sublevel`) still forces the bounded-Lipschitz cutoff orbit to solve the genuine
mass-action field, so the cutoff is invisible to the conclusion. Persistence enters only where
the local theorem used its closeness assumption: certifying that the ω-limit set and the orbit
points of its members are strictly positive, hence that the vanishing dissipation forces each
ω-point to be complex-balanced and therefore equal to `x*` by deficiency-zero uniqueness
(`isComplexBalanced_unique_in_positiveClass`).

This is the persistence-conditional form of single-linkage-class global asymptotic stability
(Anderson). Persistence itself — the no-boundary-attraction estimate — is the isolated
hypothesis here.

Depends on:
CRNT.Theorems.DeficiencyZero.AsymptoticStability, CRNT.Dynamics.LaSalle.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Global asymptotic stability under persistence.** For a weakly reversible network, a
positive complex-balanced reference `x*`, and a positive start `x₀` in the same compatibility
class, suppose the genuine mass-action orbit of `x₀` is **persistent**: absorbed by a compact
set `K₀ ⊆` the open positive orthant (`hpersist`/`hK₀pos`). Then the mass-action semiflow built
from the bounded-Lipschitz cutoff has the genuine dynamics as its orbit through `x₀`, and that
orbit's ω-limit set is exactly `{x*}`.

Persistence is the single isolated hypothesis: it is what keeps the ω-limit set off the orthant
boundary, the only role the relative-entropy closeness assumption plays in the local theorem
`omegaLimit_eq_singleton_of_local`. -/
theorem omegaLimit_eq_singleton_of_persistent
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    {K₀ : Set (Concentration S)} (hK₀cpt : IsCompact K₀)
    (hK₀pos : ∀ y ∈ K₀, y.Positive)
    (hpersist : ∀ {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S},
      (∀ x, γ x 0 = x) → (∀ x (t : ℝ≥0), ϕ t x = γ x t) →
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) →
      ∀ t : ℝ≥0, ϕ t x₀ ∈ K₀) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} := by
  set C₀ := relEntropy xstar x₀ with hC₀
  -- choose `B` past the coercivity bound of the initial relative-entropy sublevel set
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
  -- the field's linear lower bound, the cutoff, and the resulting semiflow
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
    rw [hγ0, ← hC₀] at this; exact this
  have hclamp : ∀ t, 0 ≤ t → clampBox B (γ x₀ t) = γ x₀ t := fun t ht =>
    clampBox_eq_of_sublevel hxs (hpos t ht).nonnegative (hrele t ht) hBbig
  have hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t := by
    intro t ht; have := hΓd t; rwa [hclamp t ht] at this
  -- the orbit is absorbed by the persistent compact set `K₀`
  have horbitK₀ : ∀ t : ℝ≥0, ϕ t x₀ ∈ K₀ := hpersist hγ0 hϕγ hsol
  have hsubK₀ : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K₀ := by
    rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact horbitK₀ t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K₀ :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hK₀cpt.isClosed).mpr hsubK₀⟩
  -- Lyapunov descent along the orbit (monotonicity for LaSalle)
  have hAnti : AntitoneOn (fun t => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    have hcont : Continuous (fun t => relEntropy xstar (γ x₀ t)) :=
      (relEntropy_continuous hxs).comp (Differentiable.continuous fun t => (hΓd t).differentiableAt)
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn ?_ ?_
    · intro t ht; rw [interior_Ici, Set.mem_Ioi] at ht
      exact (relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxs hcb
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xstar (ϕ b x₀) ≤ relEntropy xstar (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg) (by exact_mod_cast hab)
  obtain ⟨c, _, hωinv, hωc⟩ :=
    Flow.laSalle ϕ (relEntropy_continuous hxs) x₀ hK₀cpt habs hmono
  have hωne : (omegaLimit atTop ϕ {x₀}).Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing _ _ _ hK₀cpt habs (Set.singleton_nonempty x₀)
  -- ω ⊆ K₀, so every ω-point is strictly positive (persistence keeps it off the boundary)
  have hωK₀ : omegaLimit atTop ϕ {x₀} ⊆ K₀ :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ) univ_mem).trans
      ((IsClosed.closure_subset_iff hK₀cpt.isClosed).mpr hsubK₀)
  -- every orbit point of `x₀` has relative entropy ≤ C₀ (Lyapunov descent from the start)
  have horbit_rele : ∀ t : ℝ≥0, relEntropy xstar (ϕ t x₀) ≤ C₀ := by
    intro t
    have h0 : relEntropy xstar (ϕ 0 x₀) = C₀ := by
      rw [hϕγ]; simp only [NNReal.coe_zero]; rw [hγ0, ← hC₀]
    have hmt := hmono 0 t bot_le
    rwa [h0] at hmt
  -- hence every ω-point has relative entropy ≤ C₀ (cluster point of values in the closed `Iic C₀`)
  have hω_rele : ∀ y ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar y ≤ C₀ := by
    intro y hy
    rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hy
    have hcl : ClusterPt (relEntropy xstar y) (Filter.map (fun t => relEntropy xstar (ϕ t x₀)) atTop) :=
      hy.continuousAt_comp (relEntropy_continuous hxs).continuousAt
    have hev : Set.Iic C₀ ∈ Filter.map (fun t => relEntropy xstar (ϕ t x₀)) atTop := by
      rw [Filter.mem_map]
      exact Filter.Eventually.of_forall fun t => horbit_rele t
    -- a cluster point of a filter that contains the closed set `Iic C₀` lies in it
    by_contra hgt
    have hopen : Set.Ioi C₀ ∈ 𝓝 (relEntropy xstar y) := Ioi_mem_nhds (not_le.mp hgt)
    have hdisj : Set.Ioi C₀ ∩ Set.Iic C₀ = (∅ : Set ℝ) := by
      ext z; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false, not_and, not_le]; intro h; exact h
    haveI hne : (𝓝 (relEntropy xstar y) ⊓ Filter.map (fun t => relEntropy xstar (ϕ t x₀)) atTop).NeBot :=
      hcl
    have hmemInf := Filter.inter_mem (Filter.mem_inf_of_left hopen) (Filter.mem_inf_of_right hev)
    rw [hdisj] at hmemInf
    exact Filter.empty_notMem _ hmemInf
  -- ω lies in the affine compatibility class of x₀
  have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
    N.stoichSubspace.closed_of_finiteDimensional
  have haffclosed : IsClosed {z : Concentration S | z - x₀ ∈ N.stoichSubspace} :=
    IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
  have horbit_aff : ∀ t : ℝ≥0, ϕ t x₀ - x₀ ∈ N.stoichSubspace := by
    intro t; rw [hϕγ]
    have hsol' : ∀ τ ∈ Set.Icc (0:ℝ) ↑t,
        HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ τ)) τ := fun τ hτ => hsol τ hτ.1
    have := sub_mem_stoichSubspace_of_solution N κ t.coe_nonneg hsol'
    rwa [hγ0] at this
  have hωaff : omegaLimit atTop ϕ {x₀} ⊆ {z | z - x₀ ∈ N.stoichSubspace} := by
    refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ) univ_mem).trans ?_
    refine (IsClosed.closure_subset_iff haffclosed).mpr ?_
    rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact horbit_aff t
  -- every ω-point equals x*
  have hxstarmem : xstar ∈ N.positiveCompatibilityClass x₀ := ⟨hx0compat, hxs⟩
  have hsub : omegaLimit atTop ϕ {x₀} ⊆ {xstar} := by
    intro y hy
    rw [Set.mem_singleton_iff]
    have hyaff : y - x₀ ∈ N.stoichSubspace := hωaff hy
    -- orbit points of `y` stay in ω (invariance), hence in `K₀`, hence strictly positive
    have hyωt : ∀ t : ℝ, 0 ≤ t → γ y t ∈ omegaLimit atTop ϕ {x₀} := by
      intro t ht
      have hflow := hωinv ⟨t, ht⟩ hy
      exact (hϕγ y ⟨t, ht⟩) ▸ hflow
    have hposyt : ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ y t) := fun t ht =>
      hK₀pos _ (hωK₀ (hyωt t ht))
    -- the cutoff is the identity along the orbit of `y`: each orbit point stays in ω,
    -- so its relative entropy is `≤ C₀`, the same confinement that holds for `x₀`
    have hyrele : ∀ t : ℝ, 0 ≤ t → relEntropy xstar (γ y t) ≤ C₀ := fun t ht =>
      hω_rele _ (hyωt t ht)
    have hyt_eq : ∀ t₀ : ℝ, 0 < t₀ → γ y t₀ = xstar := by
      intro t₀ ht₀
      have hclt : clampBox B (γ y t₀) = γ y t₀ :=
        clampBox_eq_of_sublevel hxs (hposyt t₀ ht₀.le).nonnegative (hyrele t₀ ht₀.le) hBbig
      have hydt : HasDerivAt (γ y) (N.massActionVectorField κ (γ y t₀)) t₀ := by
        rw [← hclt]; exact hγd y t₀
      have hposy : Concentration.Positive (γ y t₀) := hposyt t₀ ht₀.le
      -- dissipation vanishes: relative entropy is locally constant `= c` on the orbit ⊆ ω
      have hconst : ∀ t : ℝ, 0 ≤ t → relEntropy xstar (γ y t) = c := fun t ht => hωc _ (hyωt t ht)
      have hchain := relEntropy_hasDerivAt hxs hposy (fun s => (hasDerivAt_pi.mp hydt) s)
      have heqc : (fun τ => relEntropy xstar (γ y τ)) =ᶠ[𝓝 t₀] (fun _ => c) := by
        filter_upwards [Ioi_mem_nhds ht₀] with τ hτ; exact hconst τ (le_of_lt hτ)
      have hd0 : HasDerivAt (fun τ => relEntropy xstar (γ y τ)) 0 t₀ :=
        (heqc.hasDerivAt_iff).mpr (hasDerivAt_const t₀ c)
      have hdiss : (∑ s, (Real.log (γ y t₀ s) - Real.log (xstar s))
          * N.massActionVectorField κ (γ y t₀) s) = 0 := hchain.unique hd0
      have hCB : N.IsComplexBalanced κ (γ y t₀) :=
        complexBalanced_of_dissipation_eq_zero N κ hposy hxs hcb hdiss
      -- and it lies in x₀'s positive class
      have hmem : γ y t₀ ∈ N.positiveCompatibilityClass x₀ := by
        refine ⟨?_, hposy⟩
        show γ y t₀ - x₀ ∈ N.stoichSubspace
        have h1 : γ y t₀ - y ∈ N.stoichSubspace := by
          have hsoly : ∀ τ ∈ Set.Icc (0:ℝ) t₀,
              HasDerivAt (γ y) (N.massActionVectorField κ (γ y τ)) τ := by
            intro τ hτ
            have hcl : clampBox B (γ y τ) = γ y τ :=
              clampBox_eq_of_sublevel hxs (hposyt τ hτ.1).nonnegative (hyrele τ hτ.1) hBbig
            rw [← hcl]; exact hγd y τ
          have := sub_mem_stoichSubspace_of_solution N κ ht₀.le hsoly
          rwa [hγ0] at this
        have heq : γ y t₀ - x₀ = (γ y t₀ - y) + (y - x₀) := by ring
        rw [heq]; exact N.stoichSubspace.add_mem h1 hyaff
      exact N.isComplexBalanced_unique_in_positiveClass hwr κ hmem hxstarmem hCB hcb
    -- pass to the limit `t₀ → 0⁺`
    have hγycont : Continuous (γ y) :=
      Differentiable.continuous fun t => (hγd y t).differentiableAt
    have htend1 : Tendsto (γ y) (𝓝[>] (0:ℝ)) (𝓝 y) := by
      have : Tendsto (γ y) (𝓝[>] (0:ℝ)) (𝓝 (γ y 0)) :=
        hγycont.continuousAt.continuousWithinAt
      rwa [hγ0] at this
    have htend2 : Tendsto (γ y) (𝓝[>] (0:ℝ)) (𝓝 xstar) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact (hyt_eq τ hτ).symm
    exact tendsto_nhds_unique htend1 htend2
  refine ⟨ϕ, γ, hγ0, hϕγ, hsol, ?_⟩
  exact (Set.subset_singleton_iff_eq.mp hsub).resolve_left hωne.ne_empty

end Network

end CRNT
