import CRNT.Dynamics.NoCriticalSiphonPersistence
import CRNT.Dynamics.ForwardInvariance

/-!
# Unconditional global attractor conjecture for no-critical-siphon networks

For a weakly reversible network with a positive complex-balanced reference `x*`, the global
attractor conjecture holds **unconditionally** on the class of networks with no critical siphon:
every positive trajectory of a compatibility class converges to the unique complex-balanced
equilibrium of that class.

This is the Angeli–De Leenheer–Sontag persistence criterion delivering global stability. The
proof builds the mass-action semiflow on the relative-entropy sublevel set `K` of the start
`x₀` — a compact absorbing region (`isCompact_relEntropy_sublevel`) that, unlike the open-orthant
region of `gac_of_local_confinement`, is allowed to touch the boundary. The Lyapunov descent of
the relative entropy and LaSalle pin every ω-limit point to relative entropy ≤ `C₀` and to the
affine compatibility class, and — crucially without any positivity assumption — the clamp of the
bounded-Lipschitz cutoff collapses along ω-orbits (nonnegativity plus the entropy bound suffice).
`omegaLimit_positive_of_hasNoCriticalSiphon` then upgrades `HasNoCriticalSiphon` to strict
positivity of every ω-limit point, which is exactly the no-boundary-attraction input the
convergence argument needs: vanishing dissipation forces each ω-point complex-balanced, hence
equal to `x*` by deficiency-zero uniqueness.

Depends on:
`CRNT.Dynamics.NoCriticalSiphonPersistence`, `CRNT.Dynamics.ForwardInvariance`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Unconditional GAC for no-critical-siphon networks.** For a weakly reversible network with no
critical siphon, a positive complex-balanced reference `x*`, and any positive start `x₀` in `x*`'s
compatibility class, the genuine mass-action semiflow's ω-limit set through `x₀` is exactly
`{x*}`. No persistence or closeness hypothesis: `HasNoCriticalSiphon` supplies it. -/
theorem gac_of_hasNoCriticalSiphon
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (hncs : N.HasNoCriticalSiphon)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} := by
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
    rw [hγ0, ← hC₀] at this; exact this
  have hclamp : ∀ t, 0 ≤ t → clampBox B (γ x₀ t) = γ x₀ t := fun t ht =>
    clampBox_eq_of_sublevel hxs (hpos t ht).nonnegative (hrele t ht) hBbig
  have hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t := by
    intro t ht; have := hΓd t; rwa [hclamp t ht] at this
  -- the relative-entropy sublevel set is a compact absorbing region (may touch the boundary)
  set SC : Set (Concentration S) :=
      {y : Concentration S | Concentration.Nonnegative y ∧ relEntropy xstar y ≤ C₀} with hSCdef
  have hSCcpt : IsCompact SC := isCompact_relEntropy_sublevel hxs C₀
  have horbit_SC : ∀ t : ℝ≥0, ϕ t x₀ ∈ SC := by
    intro t
    rw [hϕγ]
    exact ⟨(hpos t t.coe_nonneg).nonnegative, hrele t t.coe_nonneg⟩
  have hsubSC : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ SC := by
    rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact horbit_SC t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ SC :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hsubSC⟩
  -- Lyapunov descent of the relative entropy along the orbit
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
    Flow.laSalle ϕ (relEntropy_continuous hxs) x₀ hSCcpt habs hmono
  have hωne : (omegaLimit atTop ϕ {x₀}).Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing _ _ _ hSCcpt habs (Set.singleton_nonempty x₀)
  have hωSC : omegaLimit atTop ϕ {x₀} ⊆ SC :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ) univ_mem).trans
      ((IsClosed.closure_subset_iff hSCcpt.isClosed).mpr hsubSC)
  -- every orbit point of `x₀`, and hence every ω-point, has relative entropy ≤ C₀
  have horbit_rele : ∀ t : ℝ≥0, relEntropy xstar (ϕ t x₀) ≤ C₀ := by
    intro t
    have h0 : relEntropy xstar (ϕ 0 x₀) = C₀ := by
      rw [hϕγ]; simp only [NNReal.coe_zero]; rw [hγ0, ← hC₀]
    have hmt := hmono 0 t bot_le
    rwa [h0] at hmt
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
  have hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace := by
    have hsub : omegaLimit atTop ϕ {x₀} ⊆ {z | z - x₀ ∈ N.stoichSubspace} := by
      refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
        univ_mem).trans ?_
      refine (IsClosed.closure_subset_iff haffclosed).mpr ?_
      rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact horbit_aff t
    exact fun z hz => hsub hz
  -- forward invariance keeps ω-orbits inside ω
  have hyωt_gen : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      γ y t ∈ omegaLimit atTop ϕ {x₀} := by
    intro y hy t ht
    have hflow := hωinv ⟨t, ht⟩ hy
    exact (hϕγ y ⟨t, ht⟩) ▸ hflow
  -- nonnegativity of ω-points (from the sublevel set)
  have hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y :=
    fun y hy => (hωSC hy).1
  -- ω-orbits solve the genuine field: the clamp collapses by nonnegativity + the entropy bound
  have hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t := by
    intro y hy t ht
    have hmemω : γ y t ∈ omegaLimit atTop ϕ {x₀} := hyωt_gen y hy t ht
    have hclt : clampBox B (γ y t) = γ y t :=
      clampBox_eq_of_sublevel hxs (hωSC hmemω).1 (hωSC hmemω).2 hBbig
    rw [← hclt]; exact hγd y t
  -- no critical siphon ⇒ every ω-point is strictly positive
  have hωpos : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive y :=
    fun y hy => N.omegaLimit_positive_of_hasNoCriticalSiphon κ hϕγ hSCcpt horbit_SC hωnn hgenω
      hωaff hx0 hncs hy
  -- every ω-point equals x*
  have hxstarmem : xstar ∈ N.positiveCompatibilityClass x₀ := ⟨hx0compat, hxs⟩
  have hsub : omegaLimit atTop ϕ {x₀} ⊆ {xstar} := by
    intro y hy
    rw [Set.mem_singleton_iff]
    have hyaff : y - x₀ ∈ N.stoichSubspace := hωaff y hy
    have hyωt : ∀ t : ℝ, 0 ≤ t → γ y t ∈ omegaLimit atTop ϕ {x₀} := hyωt_gen y hy
    have hposyt : ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ y t) := fun t ht =>
      hωpos _ (hyωt t ht)
    have hyrele : ∀ t : ℝ, 0 ≤ t → relEntropy xstar (γ y t) ≤ C₀ := fun t ht =>
      (hωSC (hyωt t ht)).2
    have hyt_eq : ∀ t₀ : ℝ, 0 < t₀ → γ y t₀ = xstar := by
      intro t₀ ht₀
      have hposy : Concentration.Positive (γ y t₀) := hposyt t₀ ht₀.le
      have hydt : HasDerivAt (γ y) (N.massActionVectorField κ (γ y t₀)) t₀ :=
        hgenω y hy t₀ ht₀.le
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
      have hmem : γ y t₀ ∈ N.positiveCompatibilityClass x₀ := by
        refine ⟨?_, hposy⟩
        show γ y t₀ - x₀ ∈ N.stoichSubspace
        have h1 : γ y t₀ - y ∈ N.stoichSubspace := by
          have hsoly : ∀ τ ∈ Set.Icc (0:ℝ) t₀,
              HasDerivAt (γ y) (N.massActionVectorField κ (γ y τ)) τ :=
            fun τ hτ => hgenω y hy τ hτ.1
          have := sub_mem_stoichSubspace_of_solution N κ ht₀.le hsoly
          rwa [hγ0] at this
        have heq : γ y t₀ - x₀ = (γ y t₀ - y) + (y - x₀) := by ring
        rw [heq]; exact N.stoichSubspace.add_mem h1 hyaff
      exact N.isComplexBalanced_unique_in_positiveClass hwr κ hmem hxstarmem hCB hcb
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
