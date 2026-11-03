import CRNT.Dynamics.GenuineConfinement
import CRNT.Dynamics.SingletonFacetEscape
import CRNT.Dynamics.SiphonFacetEscape

/-!
# Asymptotic facet repulsion from a near-facet dissipation bound

At a critical siphon `{s*}` the mass-action field is tangent to the facet `{x_{s*} = 0}`, so the
finite-time influx bound `m_P(t) ≥ m_P(0)·e^{-ct}` of `SiphonFacetEscape` — which decays — does not
keep the ω-limit set off the facet. The repulsion that does is the integral mechanism of Anderson &
Shiu, _The dynamics of weakly reversible population processes near facets_: the relative-entropy
dissipation is integrable in time, so the orbit can spend only a bounded total time near a facet on
which the dissipation is bounded below, and the field's bounded log-derivative then holds the species
off the facet by a fixed positive margin.

This module formalizes that mechanism. The genuinely analytic content — that the dissipation is at
least a positive constant `ε` whenever `x_{s*}` is within `δ` of the facet — is carried as the
hypothesis `hnear`; it is the sharp Anderson–Shiu near-facet estimate, strictly weaker than the
persistence conclusion and dischargeable from the absence of a steady state near the facet. The
field's linear lower bound `-(G·x_{s*}) ≤ f_{s*}` (`hlog`) is the singleton-siphon influx bound of
`CriticalSiphonNearFacetInflux`/`SiphonFacetEscape`. From those two inputs the repulsion is proven
outright, with no further hypothesis.

## The argument

The relative entropy `V = relEntropy x*` is nonincreasing along the genuine orbit
(`genuineOrbit_relEntropy_le`), with dissipation `D = -V̇ ≥ 0`. Fix a time `t` at which `x_{s*} < δ`
and let `τ` be the last time before `t` at which `x_{s*} ≥ δ`. On `[τ, t]` the orbit stays within `δ`
of the facet, so `D ≥ ε`, hence `V̇ ≤ -ε`; integrating, `ε·(t − τ) ≤ V(γ τ) − V(γ t) ≤ V(γ 0)`, so
the excursion length is bounded: `t − τ ≤ V(γ 0)/ε`. On the same interval `d/dt log x_{s*} ≥ -G`, so
`x_{s*}(t) ≥ x_{s*}(τ)·e^{-G(t−τ)} ≥ δ·e^{-G·V(γ 0)/ε}`. The dissipation budget thus becomes a
**uniform positive floor** under the facet — the asymptotic repulsion the finite-time bound could not
give.

## Contents

* `Network.siphonFacet_floor_of_nearFacet_dissipation` — the genuine orbit through a positive start
  stays a fixed positive distance above the facet of `s*`, given the near-facet dissipation bound and
  the field's linear lower bound.

Depends on: `CRNT.Dynamics.GenuineConfinement`.
-/

open scoped BigOperators NNReal Topology
open Set

namespace CRNT

/-! ## Scalar near-facet repulsion -/

/-- A positive scalar quantity cannot approach its zero face when its logarithmic decay is
bounded and a decreasing Lyapunov function has uniformly positive dissipation near that face.
The Lyapunov budget bounds each excursion's duration; the logarithmic differential inequality
then gives a time-uniform positive floor. -/
theorem scalar_floor_of_nearBand_dissipation
    {f V f' V' : ℝ → ℝ} {δ ε G : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hG : 0 ≤ G)
    (hfpos : ∀ t, 0 ≤ t → 0 < f t)
    (hfd : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    (hVd : ∀ t, 0 ≤ t → HasDerivAt V (V' t) t)
    (hVnn : ∀ t, 0 ≤ t → 0 ≤ V t)
    (hVle : ∀ t, 0 ≤ t → V t ≤ V 0)
    (hlog : ∀ t, 0 ≤ t → -(G * f t) ≤ f' t)
    (hstart : δ ≤ f 0)
    (hnear : ∀ t, 0 ≤ t → f t ≤ δ → ε ≤ -(V' t))
    {t : ℝ} (ht : 0 ≤ t) :
    δ * Real.exp (-(G * (V 0 / ε))) ≤ f t := by
  have hV0nn : 0 ≤ V 0 := hVnn 0 le_rfl
  have hfcont : ContinuousOn f (Icc 0 t) := fun s hs =>
    (hfd s hs.1).continuousAt.continuousWithinAt
  have hVcont : ContinuousOn V (Icc 0 t) := fun s hs =>
    (hVd s hs.1).continuousAt.continuousWithinAt
  have hφd : ∀ s, 0 ≤ s → HasDerivAt (fun u => V u + ε * u) (V' s + ε) s := by
    intro s hs
    have hε : HasDerivAt (fun u : ℝ => ε * u) ε s := by
      simpa using (hasDerivAt_id s).const_mul ε
    exact (hVd s hs).add hε
  have hψd : ∀ s, 0 ≤ s → HasDerivAt (fun u => Real.log (f u) + G * u)
      (f' s / f s + G) s := by
    intro s hs
    have hlogf : HasDerivAt (fun u => Real.log (f u)) (f' s / f s) s :=
      (hfd s hs).log (hfpos s hs).ne'
    have hGu : HasDerivAt (fun u : ℝ => G * u) G s := by
      simpa using (hasDerivAt_id s).const_mul G
    exact hlogf.add hGu
  by_cases hge : δ ≤ f t
  · have hexp : Real.exp (-(G * (V 0 / ε))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : 0 ≤ G * (V 0 / ε) := mul_nonneg hG (div_nonneg hV0nn hε.le)
        linarith)
    calc
      δ * Real.exp (-(G * (V 0 / ε))) ≤ δ * 1 := mul_le_mul_of_nonneg_left hexp hδ.le
      _ = δ := mul_one δ
      _ ≤ f t := hge
  · rw [not_le] at hge
    let A : Set ℝ := Icc 0 t ∩ (fun s => f s) ⁻¹' Ici δ
    have hAcl : IsClosed A := hfcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hAne : A.Nonempty := ⟨0, ⟨Set.left_mem_Icc.mpr ht, hstart⟩⟩
    have hAbdd : BddAbove A := ⟨t, fun s hs => hs.1.2⟩
    let τ : ℝ := sSup A
    have hτA : τ ∈ A := hAcl.csSup_mem hAne hAbdd
    have hτ0 : 0 ≤ τ := hτA.1.1
    have hτt : τ ≤ t := hτA.1.2
    have hτδ : δ ≤ f τ := hτA.2
    have hτlt : τ < t := lt_of_le_of_ne hτt (fun h => absurd (h ▸ hτδ) (not_le.mpr hge))
    have hIccsub : Icc τ t ⊆ Icc 0 t := Set.Icc_subset_Icc hτ0 le_rfl
    have hbelow : ∀ s, τ < s → s ≤ t → f s < δ := by
      intro s hsτ hst
      by_contra hh
      rw [not_lt] at hh
      exact absurd (le_csSup hAbdd ⟨⟨le_trans hτ0 hsτ.le, hst⟩, hh⟩) (not_le.mpr hsτ)
    have hφanti : AntitoneOn (fun s => V s + ε * s) (Icc τ t) := by
      have hcont : ContinuousOn (fun s => V s + ε * s) (Icc τ t) :=
        (hVcont.mono hIccsub).add (by fun_prop)
      refine antitoneOn_of_deriv_nonpos (convex_Icc τ t) hcont ?_ ?_
      · intro s hs
        rw [interior_Icc] at hs
        exact (hφd s (le_trans hτ0 hs.1.le)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hφd s (le_trans hτ0 hs.1.le)).deriv]
        have hbnd := hnear s (le_trans hτ0 hs.1.le)
          (le_of_lt (hbelow s hs.1 hs.2.le))
        linarith
    have hVdesc : ε * (t - τ) ≤ V 0 := by
      have hle := hφanti (Set.left_mem_Icc.mpr hτlt.le)
        (Set.right_mem_Icc.mpr hτlt.le) hτlt.le
      have hVtnn : 0 ≤ V t := hVnn t ht
      have hVτ : V τ ≤ V 0 := hVle τ hτ0
      nlinarith
    have htmτ : t - τ ≤ V 0 / ε := by
      rw [le_div_iff₀ hε, mul_comm]
      exact hVdesc
    have hψmono : MonotoneOn (fun s => Real.log (f s) + G * s) (Icc τ t) := by
      have hcont : ContinuousOn (fun s => Real.log (f s) + G * s) (Icc τ t) :=
        ((hfcont.mono hIccsub).log (fun s hs => (hfpos s (le_trans hτ0 hs.1)).ne')).add
          (by fun_prop)
      refine monotoneOn_of_deriv_nonneg (convex_Icc τ t) hcont ?_ ?_
      · intro s hs
        rw [interior_Icc] at hs
        exact (hψd s (le_trans hτ0 hs.1.le)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have h0s : 0 ≤ s := le_trans hτ0 hs.1.le
        rw [(hψd s h0s).deriv]
        have hdiv : -G ≤ f' s / f s := by
          rw [le_div_iff₀ (hfpos s h0s)]
          nlinarith [hlog s h0s]
        linarith
    have hlogle : Real.log (f τ) - G * (t - τ) ≤ Real.log (f t) := by
      have hmono := hψmono (Set.left_mem_Icc.mpr hτlt.le)
        (Set.right_mem_Icc.mpr hτlt.le) hτlt.le
      have hGexp : G * (t - τ) = G * t - G * τ := by ring
      linarith [hmono, hGexp]
    have hkey : f τ * Real.exp (-(G * (t - τ))) ≤ f t := by
      have e1 : f τ * Real.exp (-(G * (t - τ))) =
          Real.exp (Real.log (f τ) + -(G * (t - τ))) := by
        rw [Real.exp_add, Real.exp_log (hfpos τ hτ0)]
      rw [e1, ← Real.exp_log (hfpos t ht)]
      exact Real.exp_le_exp.mpr (by linarith [hlogle])
    have hexpmono : Real.exp (-(G * (V 0 / ε))) ≤ Real.exp (-(G * (t - τ))) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left htmτ hG))
    calc
      δ * Real.exp (-(G * (V 0 / ε))) ≤ δ * Real.exp (-(G * (t - τ))) :=
        mul_le_mul_of_nonneg_left hexpmono hδ.le
      _ ≤ f τ * Real.exp (-(G * (t - τ))) :=
        mul_le_mul_of_nonneg_right hτδ (Real.exp_pos _).le
      _ ≤ f t := hkey

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Asymptotic facet repulsion from a near-facet dissipation bound.** Let `γ` be the genuine
mass-action orbit through a positive start of a positive complex-balanced class. For a species `s*`
and band width `δ > 0`, suppose:

* `hlog` — the field's linear lower bound `-(G·γ_{s*}) ≤ f_{s*}(γ)` (the singleton-siphon influx
  bound), giving `d/dt log γ_{s*} ≥ -G`;
* `hnear` — the **near-facet dissipation bound**: the relative-entropy dissipation
  `-∑_s (log γ_s − log x*_s)·f_s(γ)` is at least `ε > 0` whenever `γ_{s*} ≤ δ`;
* `hstart` — the start is off the facet, `δ ≤ γ_0 s*`.

Then `γ_{s*}` stays above the fixed positive floor `δ·exp(−G·V(γ 0)/ε)` for all forward time, with
`V = relEntropy x*`. The orbit is repelled from the facet of `s*` by a uniform margin — the
asymptotic statement the finite-time Grönwall bound does not provide. -/
theorem siphonFacet_floor_of_nearFacet_dissipation (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} {sstar : S} {δ ε G : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hG : 0 ≤ G)
    (hpos : ∀ t, 0 ≤ t → (γ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hlog : ∀ t, 0 ≤ t → -(G * γ t sstar) ≤ N.massActionVectorField κ (γ t) sstar)
    (hstart : δ ≤ γ 0 sstar)
    (hnear : ∀ t, 0 ≤ t → γ t sstar ≤ δ →
      ε ≤ -(∑ s, (Real.log (γ t s) - Real.log (xstar s)) * N.massActionVectorField κ (γ t) s)) :
    ∀ t, 0 ≤ t → δ * Real.exp (-(G * (relEntropy xstar (γ 0) / ε))) ≤ γ t sstar := by
  intro t ht
  let f : ℝ → ℝ := fun t => γ t sstar
  let f' : ℝ → ℝ := fun t => N.massActionVectorField κ (γ t) sstar
  let V : ℝ → ℝ := fun t => relEntropy xstar (γ t)
  let V' : ℝ → ℝ := fun t =>
    ∑ s, (Real.log (γ t s) - Real.log (xstar s)) *
      N.massActionVectorField κ (γ t) s
  have hfpos : ∀ t, 0 ≤ t → 0 < f t := by
    intro t ht
    exact hpos t ht sstar
  have hfd : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t := by
    intro t ht
    simpa [f, f'] using (hasDerivAt_pi.mp (hsol t ht)) sstar
  have hVd : ∀ t, 0 ≤ t → HasDerivAt V (V' t) t := by
    intro t ht
    simpa [V, V'] using
      (relEntropy_hasDerivAt hxs (hpos t ht)
        (fun s => (hasDerivAt_pi.mp (hsol t ht)) s))
  have hVnn : ∀ t, 0 ≤ t → 0 ≤ V t := by
    intro t ht
    exact relEntropy_nonneg (hpos t ht).nonnegative hxs
  have hVle : ∀ t, 0 ≤ t → V t ≤ V 0 := by
    intro t ht
    simpa [V] using N.genuineOrbit_relEntropy_le κ hxs hcb hpos hsol t ht
  have hlog' : ∀ t, 0 ≤ t → -(G * f t) ≤ f' t := by
    intro t ht
    simpa [f, f'] using hlog t ht
  have hnear' : ∀ t, 0 ≤ t → f t ≤ δ → ε ≤ -(V' t) := by
    intro t ht hband
    simpa [f, V'] using hnear t ht hband
  have hfloor := scalar_floor_of_nearBand_dissipation hδ hε hG hfpos hfd hVd
    hVnn hVle hlog' (by simpa [f] using hstart) hnear' ht
  simpa [f, V] using hfloor


/-! ## From a uniform facet floor to omega-limit exclusion -/

/-- A uniform coordinate floor along a forward orbit passes to every omega-limit point.  This is a
general topological bridge: the orbit is eventually (indeed always) in the closed half-space
`{x | ε ≤ x s}`, so every cluster point is there as well. -/
theorem omegaLimit_coord_ge_of_orbit_floor (_N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {sstar : S} {ε : ℝ}
    (hfloor : ∀ t : ℝ, 0 ≤ t → ε ≤ γ x₀ t sstar)
    {w : Concentration S} (hw : w ∈ omegaLimit Filter.atTop ϕ {x₀}) :
    ε ≤ w sstar := by
  rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hw
  have hcl : ClusterPt (w sstar)
      (Filter.map (fun t : ℝ≥0 => (ϕ t x₀) sstar) Filter.atTop) :=
    hw.continuousAt_comp (continuous_apply sstar).continuousAt
  have hev : Set.Ici ε ∈ Filter.map (fun t : ℝ≥0 => (ϕ t x₀) sstar) Filter.atTop := by
    rw [Filter.mem_map]
    exact Filter.Eventually.of_forall fun t => by
      dsimp only
      rw [hϕγ]
      exact hfloor t t.coe_nonneg
  by_contra hnot
  have hlt : w sstar < ε := lt_of_not_ge hnot
  have hopen : Set.Iio ε ∈ 𝓝 (w sstar) := Iio_mem_nhds hlt
  have hdisj : Set.Iio ε ∩ Set.Ici ε = (∅ : Set ℝ) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hz
    exact not_le.mpr hz
  haveI hne :
      (𝓝 (w sstar) ⊓ Filter.map (fun t : ℝ≥0 => (ϕ t x₀) sstar) Filter.atTop).NeBot := hcl
  have hmem := Filter.inter_mem (Filter.mem_inf_of_left hopen) (Filter.mem_inf_of_right hev)
  rw [hdisj] at hmem
  exact Filter.empty_notMem _ hmem

/-- A uniform lower bound on the total mass in `P` transfers from a forward orbit to each of its
omega-limit points. This is the aggregate counterpart of the coordinate floor lemma above. -/
theorem omegaLimit_siphonMass_ge_of_orbit_floor (_N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {P : Finset S} {ε : ℝ}
    (hfloor : ∀ t : ℝ, 0 ≤ t → ε ≤ ∑ s ∈ P, γ x₀ t s)
    {w : Concentration S} (hw : w ∈ omegaLimit Filter.atTop ϕ {x₀}) :
    ε ≤ ∑ s ∈ P, w s := by
  rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hw
  let mass : Concentration S → ℝ := fun x => ∑ s ∈ P, x s
  have hmassCont : Continuous mass :=
    continuous_finsetSum _ fun s _ => continuous_apply s
  have hcl : ClusterPt (mass w)
      (Filter.map (fun t : ℝ≥0 => mass (ϕ t x₀)) Filter.atTop) :=
    hw.continuousAt_comp hmassCont.continuousAt
  have hev : Set.Ici ε ∈ Filter.map (fun t : ℝ≥0 => mass (ϕ t x₀)) Filter.atTop := by
    rw [Filter.mem_map]
    exact Filter.Eventually.of_forall fun t => by
      dsimp [mass]
      rw [hϕγ x₀ t]
      exact hfloor (t : ℝ) t.coe_nonneg
  by_contra hnot
  have hlt : mass w < ε := lt_of_not_ge hnot
  have hopen : Set.Iio ε ∈ 𝓝 (mass w) := Iio_mem_nhds hlt
  have hdisj : Set.Iio ε ∩ Set.Ici ε = (∅ : Set ℝ) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hz
    exact not_le.mpr hz
  haveI hne : (𝓝 (mass w) ⊓
      Filter.map (fun t : ℝ≥0 => mass (ϕ t x₀)) Filter.atTop).NeBot := hcl
  have hmem := Filter.inter_mem (Filter.mem_inf_of_left hopen) (Filter.mem_inf_of_right hev)
  rw [hdisj] at hmem
  exact Filter.empty_notMem _ hmem

/-- **The near-facet dissipation estimate really excludes the singleton facet from omega.**  The
analytic theorem above supplies the fixed positive floor
`δ * exp (-(G * V₀ / ε))`; `omegaLimit_coord_ge_of_orbit_floor` transfers it to every omega-point.
Thus an omega-limit point cannot have the critical species coordinate equal to zero. -/
theorem notMem_omegaLimit_singletonFacet_of_nearFacet_dissipation
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {sstar : S} {δ ε G : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hG : 0 ≤ G)
    (hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hlog : ∀ t, 0 ≤ t → -(G * γ x₀ t sstar) ≤ N.massActionVectorField κ (γ x₀ t) sstar)
    (hstart : δ ≤ γ x₀ 0 sstar)
    (hnear : ∀ t, 0 ≤ t → γ x₀ t sstar ≤ δ →
      ε ≤ -(∑ s, (Real.log (γ x₀ t s) - Real.log (xstar s)) *
        N.massActionVectorField κ (γ x₀ t) s))
    {w : Concentration S} (hw : w ∈ omegaLimit Filter.atTop ϕ {x₀}) :
    w sstar ≠ 0 := by
  let floor : ℝ := δ * Real.exp (-(G * (relEntropy xstar (γ x₀ 0) / ε)))
  have hfloor_pos : 0 < floor := mul_pos hδ (Real.exp_pos _)
  have hfloor : ∀ t : ℝ, 0 ≤ t → floor ≤ γ x₀ t sstar := by
    intro t ht
    exact N.siphonFacet_floor_of_nearFacet_dissipation κ hxs hcb hδ hε hG hpos hsol hlog
      hstart hnear t ht
  have hωfloor : floor ≤ w sstar :=
    N.omegaLimit_coord_ge_of_orbit_floor hϕγ hfloor hw
  intro hw0
  rw [hw0] at hωfloor
  linarith

/-- The explicit singleton near-facet influx constant is nonnegative. -/
theorem singletonFacetInfluxConst_nonneg (N : Network S) (κ : N.RateConstants)
    (sstar : S) (M : ℝ) :
    0 ≤ N.singletonFacetInfluxConst κ sstar M := by
  rw [singletonFacetInfluxConst]
  refine Finset.sum_nonneg fun r _ => ?_
  have hbase : 0 ≤ max M 1 := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right M 1)
  exact mul_nonneg
    (mul_nonneg (κ.positive r).le (Nat.cast_nonneg _))
    (pow_nonneg hbase _)

/-- **Aggregate near-facet repulsion for any finite species set.** If relative-entropy dissipation
stays uniformly positive whenever the total mass in `P` is small, then that mass stays uniformly
positive along the whole positive bounded orbit. The aggregate influx estimate supplies the
logarithmic decay bound needed by `scalar_floor_of_nearBand_dissipation`. -/
theorem siphonMass_floor_of_nearFacet_dissipation
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} {P : Finset S} (hPne : P.Nonempty)
    {M δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hpos : ∀ t, 0 ≤ t → (γ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hγM : ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    (hstart : δ ≤ ∑ s ∈ P, γ 0 s)
    (hnear : ∀ t, 0 ≤ t → (∑ s ∈ P, γ t s) ≤ δ →
      ε ≤ -(∑ s, (Real.log (γ t s) - Real.log (xstar s)) *
        N.massActionVectorField κ (γ t) s))
    {t : ℝ} (ht : 0 ≤ t) :
    δ * Real.exp (-(N.siphonFacetInfluxConst κ M *
      (relEntropy xstar (γ 0) / ε))) ≤ ∑ s ∈ P, γ t s := by
  let f : ℝ → ℝ := fun u => ∑ s ∈ P, γ u s
  let f' : ℝ → ℝ := fun u => ∑ s ∈ P, N.massActionVectorField κ (γ u) s
  let V : ℝ → ℝ := fun u => relEntropy xstar (γ u)
  let V' : ℝ → ℝ := fun u =>
    ∑ s, (Real.log (γ u s) - Real.log (xstar s)) *
      N.massActionVectorField κ (γ u) s
  have hfpos : ∀ u, 0 ≤ u → 0 < f u := by
    intro u hu
    dsimp [f]
    exact Finset.sum_pos (fun s hs => hpos u hu s) hPne
  have hfd : ∀ u, 0 ≤ u → HasDerivAt f (f' u) u := by
    intro u hu
    have hcoord : ∀ s ∈ P,
        HasDerivAt (fun v => γ v s) (N.massActionVectorField κ (γ u) s) u := by
      intro s _
      exact (hasDerivAt_pi.mp (hsol u hu)) s
    have hsum : HasDerivAt (fun v => ∑ s ∈ P, γ v s)
        (∑ s ∈ P, N.massActionVectorField κ (γ u) s) u :=
      HasDerivAt.fun_sum (fun s hs => hcoord s hs)
    simpa [f, f'] using hsum
  have hVd : ∀ u, 0 ≤ u → HasDerivAt V (V' u) u := by
    intro u hu
    simpa [V, V'] using
      (relEntropy_hasDerivAt hxs (hpos u hu)
        (fun s => (hasDerivAt_pi.mp (hsol u hu)) s))
  have hVnn : ∀ u, 0 ≤ u → 0 ≤ V u := by
    intro u hu
    exact relEntropy_nonneg (hpos u hu).nonnegative hxs
  have hVle : ∀ u, 0 ≤ u → V u ≤ V 0 := by
    intro u hu
    exact N.genuineOrbit_relEntropy_le κ hxs hcb hpos hsol u hu
  let G : ℝ := N.siphonFacetInfluxConst κ M
  have hG : 0 ≤ G := by
    dsimp [G, siphonFacetInfluxConst]
    refine Finset.sum_nonneg fun r _ => ?_
    have hbase : 0 ≤ max M 1 := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right M 1)
    exact mul_nonneg
      (mul_nonneg (κ.positive r).le (Nat.cast_nonneg _))
      (pow_nonneg hbase _)
  have hlog : ∀ u, 0 ≤ u → -(G * f u) ≤ f' u := by
    intro u hu
    have hbound := N.massActionVectorField_siphon_facet_ge κ P
      (hpos u hu).nonnegative (fun s => hγM u hu s)
    simpa [G, f, f'] using hbound
  have hnear' : ∀ u, 0 ≤ u → f u ≤ δ → ε ≤ -(V' u) := by
    intro u hu hmass
    exact (hnear u hu (by simpa [f] using hmass))
  have hfloor := scalar_floor_of_nearBand_dissipation
    hδ hε hG hfpos hfd hVd hVnn hVle hlog (by simpa [f] using hstart) hnear' ht
  simpa [f, V, G] using hfloor

/-- **General critical-face omega exclusion from near-face dissipation.** A uniform positive
lower bound on relative-entropy dissipation while the aggregate mass in a nonempty set `P` is
small keeps that mass uniformly positive. Consequently no omega-limit point lies on the face
where every species in `P` vanishes. -/
theorem notMem_omegaLimit_siphonFace_of_nearFacet_dissipation
    (N : Network S) (κ : N.RateConstants) {xstar x₀ : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {P : Finset S} (hPne : P.Nonempty) {M δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hγM : ∀ t, 0 ≤ t → ∀ s, γ x₀ t s ≤ M)
    (hstart : δ ≤ ∑ s ∈ P, γ x₀ 0 s)
    (hnear : ∀ t, 0 ≤ t → (∑ s ∈ P, γ x₀ t s) ≤ δ →
      ε ≤ -(∑ s, (Real.log (γ x₀ t s) - Real.log (xstar s)) *
        N.massActionVectorField κ (γ x₀ t) s))
    {w : Concentration S} (hw : w ∈ omegaLimit Filter.atTop ϕ {x₀}) :
    w ∉ N.SiphonFace P := by
  let floor : ℝ := δ * Real.exp
    (-(N.siphonFacetInfluxConst κ M * (relEntropy xstar (γ x₀ 0) / ε)))
  have hfloorpos : 0 < floor := mul_pos hδ (Real.exp_pos _)
  have hfloor : ∀ t : ℝ, 0 ≤ t → floor ≤ ∑ s ∈ P, γ x₀ t s := by
    intro t ht
    exact N.siphonMass_floor_of_nearFacet_dissipation κ hxs hcb hPne hδ hε
      hpos hsol hγM hstart hnear ht
  have hωfloor : floor ≤ ∑ s ∈ P, w s := by
    exact N.omegaLimit_siphonMass_ge_of_orbit_floor hϕγ hfloor hw
  intro hface
  have hsum0 : ∑ s ∈ P, w s = 0 := Finset.sum_eq_zero (fun s hs => hface.2 s hs)
  rw [hsum0] at hωfloor
  exact (not_le_of_gt hfloorpos) hωfloor

/-- **Singleton critical-facet omega exclusion with the influx bound discharged.**  On a bounded
positive genuine orbit, the Anderson--Shiu singleton influx estimate automatically supplies the
log-coordinate lower bound required by `notMem_omegaLimit_singletonFacet_of_nearFacet_dissipation`.
Thus the only nonstructural hypothesis left in the codimension-one critical-siphon argument is the
near-facet relative-entropy dissipation bound `hnear`. -/
theorem notMem_omegaLimit_singletonFacet_of_nearFacet_dissipation_bounded
    (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {sstar : S} (hsiph : N.IsSiphon ({sstar} : Finset S))
    {M δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hγM : ∀ t, 0 ≤ t → ∀ s, γ x₀ t s ≤ M)
    (hstart : δ ≤ γ x₀ 0 sstar)
    (hnear : ∀ t, 0 ≤ t → γ x₀ t sstar ≤ δ →
      ε ≤ -(∑ s, (Real.log (γ x₀ t s) - Real.log (xstar s)) *
        N.massActionVectorField κ (γ x₀ t) s))
    {w : Concentration S} (hw : w ∈ omegaLimit Filter.atTop ϕ {x₀}) :
    w sstar ≠ 0 := by
  let G : ℝ := N.singletonFacetInfluxConst κ sstar M
  have hG : 0 ≤ G := by
    dsimp [G]
    exact N.singletonFacetInfluxConst_nonneg κ sstar M
  apply N.notMem_omegaLimit_singletonFacet_of_nearFacet_dissipation κ hxs hcb hϕγ
    hδ hε hG hpos hsol (G := G) ?_ hstart hnear hw
  intro t ht
  dsimp [G]
  exact N.massActionVectorField_singleton_facet_ge κ hsiph (hpos t ht).nonnegative (hγM t ht)

end Network

end CRNT
