import CRNT.Dynamics.StrongOrderConvex
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Order.IntermediateValue

/-!
# The remaining case of the strong-order argument: strict monotone separators and uniform gaps

This module continues leaf **D14** of the field map (*monotone systems and contraction for
reaction networks*), building on `CRNT/Dynamics/StrongOrderConvex.lean`.

## The classical background

Hirsch's **strong order** `≪` (`CRNT.StronglyBelow`, `CRNT.StronglyBelowGap`) and the monotone
separating functionals of Hirsch–Smith (*A monotonicity theorem for autonomous dynamical systems*,
J. Differential Equations 153 (1999); *Monotone dynamical systems*, Handbook of Differential
Equations vol. 2 (2002)) are the devices used to compare a ω-limit set with a test point.  In the
repository they are `CRNT.IsMonotoneSeparator`, `CRNT.sepAbove`, `CRNT.sepBelow`; the
non-ordering argument (`CRNT.omegaLimit_not_stronglyBelow_of_incomparable_below`,
`CRNT.omegaLimit_straddles_of_incomparable`, `CRNT.comparable_orbit_of_stronglyBelow`) and the
order-convexity theorem (`CRNT.omegaLimit_orderConvex_of_monotone_flow_of_strongOrder`) are in
`CRNT/Dynamics/StrongOrderConvex.lean`.

## What this module adds

The case left open there is the ω-limit point which is *merely* `≤ z` (and not `≪ z`).  This
module supplies that case in two rigorous forms.

* A **strict monotone separator** (`CRNT.IsStrictMonotoneSeparator`): a monotone separating
  functional which is *strictly* positive on every `y ≥ z` with `y ≠ z`.  The "intermediate value"
  lemma `CRNT.omegaLimit_nonneg_of_separator_of_incomparable_below` shows that when the orbit is
  incomparable with `z` no ω-limit point is a point of *negative* separation, and
  `CRNT.omegaLimit_eq_zero_or_pos_of_separator_of_incomparable_below` splits the ω-limit set into
  the zero set of `φ` and the strictly positive part.
* A **uniform gap** (`CRNT.HasUniformSeparatorGap`): the separating functional is bounded away
  from zero on a compact set carrying the forward orbit, off the down-set `↓ z`.  Under this
  hypothesis the remaining case is closed and the ω-limit set is order-convex:
  `CRNT.omegaLimit_orderConvex_of_monotone_flow_of_uniformSeparator`.
* The **discrete case**: if the ω-limit set is *finite*
  (`CRNT.omegaLimit_orderConvex_of_monotone_flow_of_discreteOmegaLimit`), the remaining case is
  closed under the strict monotone separator alone: the separating functional would have to take
  every value of the interval `(0, φ q)` at a ω-limit point, which is incompatible with the
  finiteness of the ω-limit set.

The separating functional `CRNT.sepAbove z` of Hirsch–Smith is a strict monotone separator at
every point (`CRNT.isStrictMonotoneSeparator_sepAbove`), and its truncation
`y ↦ max (0, sepAbove z y)` is even a *vanishing* separator
(`CRNT.isVanishingMonotoneSeparator_truncSepAbove`), so the hypotheses are not vacuous.

## What remains open

The *general* order-convexity of the ω-limit set of an arbitrary monotone flow is the classical
result of Hirsch–Smith and is **not** fully proved here: this module closes the specific remaining
case of the repository's argument (the ω-limit point merely `≤ z`) under the hypotheses above.
-/

open Set Filter Topology
open scoped BigOperators NNReal CRNT

namespace CRNT

section StrictSeparator

variable {S : Type}

/-- **A strict monotone separator.**  A monotone separating functional `φ` of the point `z` which
is *strictly* positive on every `y ≥ z` with `y ≠ z`.  This is the extra hypothesis that the
remaining case of the strong-order argument needs: the ordinary separator may vanish on
`y = z`, the strict one does not vanish on any `y ≥ z`, `y ≠ z`. -/
def IsStrictMonotoneSeparator (z : Concentration S) (φ : Concentration S → ℝ) : Prop :=
  IsMonotoneSeparator z φ ∧ ∀ y, z ≤ y → y ≠ z → 0 < φ y

theorem IsStrictMonotoneSeparator.isMonotoneSeparator {z : Concentration S}
    {φ : Concentration S → ℝ} (h : IsStrictMonotoneSeparator z φ) : IsMonotoneSeparator z φ :=
  h.1

/-- **The strictness.**  A strict monotone separator is strictly positive on every `y ≥ z`,
`y ≠ z`. -/
theorem IsStrictMonotoneSeparator.strict {z : Concentration S} {φ : Concentration S → ℝ}
    (h : IsStrictMonotoneSeparator z φ) {y : Concentration S} (hzy : z ≤ y) (hyz : y ≠ z) :
    0 < φ y := h.2 y hzy hyz

/-- **The separator is nonpositive exactly on the down-set `↓ z`.** -/
theorem IsStrictMonotoneSeparator.le_zero_iff {z : Concentration S} {φ : Concentration S → ℝ}
    (h : IsStrictMonotoneSeparator z φ) (y : Concentration S) : φ y ≤ 0 ↔ y ≤ z :=
  h.1.2.2.2.1 y

/-- **A strict separator is monotone.** -/
theorem IsStrictMonotoneSeparator.monotone {z : Concentration S} {φ : Concentration S → ℝ}
    (h : IsStrictMonotoneSeparator z φ) {x y : Concentration S} (hxy : x ≤ y) : φ x ≤ φ y :=
  h.1.2.1 x y hxy

/-- **A strict separator vanishes at the test point.** -/
theorem IsStrictMonotoneSeparator.zero {z : Concentration S} {φ : Concentration S → ℝ}
    (h : IsStrictMonotoneSeparator z φ) : φ z = 0 := h.1.2.2.1

/-- **A strict separator is positive off the down-set.**  If `y` is not below `z`, the separating
functional is strictly positive at `y`. -/
theorem IsStrictMonotoneSeparator.pos_of_not_le {z : Concentration S} {φ : Concentration S → ℝ}
    (h : IsStrictMonotoneSeparator z φ) {y : Concentration S} (hnot : ¬ (y ≤ z)) : 0 < φ y := by
  by_contra hc
  exact hnot ((h.le_zero_iff y).mp (le_of_not_gt hc))

/-- **The strict separator detects the test point from above.**  A point `y ≥ z` with `y ≠ z` is
*incomparable* with `z`. -/
theorem IsStrictMonotoneSeparator.not_le_of_ge {z : Concentration S} {φ : Concentration S → ℝ}
    (_h : IsStrictMonotoneSeparator z φ) {y : Concentration S} (hzy : z ≤ y) (hyz : y ≠ z) :
    ¬ (y ≤ z) := fun hle => hyz (le_antisymm hle hzy)

/-- **A strict separator is a separator.**  Every strict monotone separator is in particular a
monotone separator. -/
theorem IsStrictMonotoneSeparator.of_separator {z : Concentration S} {φ : Concentration S → ℝ}
    (hφ : IsMonotoneSeparator z φ) (hstrict : ∀ y, z ≤ y → y ≠ z → 0 < φ y) :
    IsStrictMonotoneSeparator z φ := ⟨hφ, hstrict⟩

/-- **A vanishing monotone separator.**  A monotone separating functional which vanishes *exactly*
on the down-set `↓ z`; this is the "uniform" form of the separating device, in which the
functional detects the whole down-set rather than only its boundary. -/
def IsVanishingMonotoneSeparator (z : Concentration S) (φ : Concentration S → ℝ) : Prop :=
  IsMonotoneSeparator z φ ∧ (∀ y, φ y = 0 ↔ y ≤ z)

/-- **A vanishing separator is a strict separator.**  Indeed `z ≤ y`, `y ≠ z` forces `¬ (y ≤ z)`,
hence `φ y > 0`. -/
theorem IsVanishingMonotoneSeparator.isStrict {z : Concentration S} {φ : Concentration S → ℝ}
    (h : IsVanishingMonotoneSeparator z φ) : IsStrictMonotoneSeparator z φ := by
  refine ⟨h.1, ?_⟩
  intro y hzy hyz
  have hne : ¬ (y ≤ z) := fun hle => hyz (le_antisymm hle hzy)
  have hne' : ¬ (φ y ≤ 0) := fun hh => hne ((h.1.2.2.2.1 y).mp hh)
  exact lt_of_not_ge hne'

end StrictSeparator

section ClusterValues

variable {S : Type}

/-- **Functional values along the orbit at a ω-limit point.**  If `y` is a ω-limit point of the
orbit of `x₀` and `φ` is continuous, then `φ (ϕ t x₀)` is arbitrarily close to `φ y` at late
times `t` belonging to any member `u` of the filter `atTop` (i.e. to any set of times containing
a tail). -/
lemma exists_close_omegaLimit (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S)
    {φ : Concentration S → ℝ} (hφ : Continuous φ) {y : Concentration S}
    (hy : y ∈ omegaLimit atTop ϕ {x₀}) {u : Set ℝ≥0} (hu : u ∈ (atTop : Filter ℝ≥0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ u, |φ (ϕ t x₀) - φ y| < ε := by
  have hy' : y ∈ closure (Set.image2 ϕ u {x₀}) :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := u) hu) hy
  have hV : {w : Concentration S | dist (φ w) (φ y) < ε} ∈ 𝓝 y := by
    have heq : {w : Concentration S | dist (φ w) (φ y) < ε}
        = φ ⁻¹' Metric.ball (φ y) ε := by
      ext w
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Metric.mem_ball, dist_comm]
    rw [heq]
    refine mem_nhds_iff.mpr
      ⟨φ ⁻¹' Metric.ball (φ y) ε, subset_rfl,
        Continuous.isOpen_preimage hφ (Metric.ball (φ y) ε) Metric.isOpen_ball, ?_⟩
    simp only [Set.mem_preimage, Metric.mem_ball, dist_self]
    exact hε
  obtain ⟨w, hw⟩ := (mem_closure_iff_nhds.mp hy') _ hV
  obtain ⟨t, ht, b, hb, heq⟩ := hw.2
  have hb' : b = x₀ := Set.mem_singleton_iff.mp hb
  refine ⟨t, ht, ?_⟩
  rw [← heq, hb'] at hw
  simpa [Real.dist_eq] using hw.1

/-- **The separator is nonnegative at the ω-limit points of an incomparable orbit.**  If the
forward orbit of `x₀` never goes below `z`, then no ω-limit point is a point of *negative*
separation.  This is the "intermediate value" refinement of the non-ordering argument: a
continuous functional cannot cross the zero level `φ = 0` without the orbit going below `z`. -/
theorem omegaLimit_nonneg_of_separator_of_incomparable_below
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    {φ : Concentration S → ℝ} (hφ : IsMonotoneSeparator z φ)
    (h : ¬ ∃ t : ℝ≥0, ϕ t x₀ ≤ z) :
    ∀ y ∈ omegaLimit atTop ϕ {x₀}, 0 ≤ φ y := by
  have hpos : ∀ t : ℝ≥0, 0 < φ (ϕ t x₀) := by
    intro t
    have hn : ¬ (ϕ t x₀ ≤ z) := fun hh => h ⟨t, hh⟩
    have hne : ¬ (φ (ϕ t x₀) ≤ 0) := fun hh => hn ((hφ.2.2.2.1 (ϕ t x₀)).mp hh)
    exact lt_of_not_ge hne
  intro y hy
  by_contra hc
  have hε : 0 < -φ y := by
    have : φ y < 0 := lt_of_not_ge hc
    linarith
  obtain ⟨t, ht, hclose⟩ :=
    exists_close_omegaLimit ϕ x₀ hφ.1 hy (u := Set.Ici 0) (Ici_mem_atTop 0) (ε := -φ y) hε
  have hneg : φ (ϕ t x₀) < 0 := by
    have habs : φ (ϕ t x₀) - φ y ≤ |φ (ϕ t x₀) - φ y| := le_abs_self _
    linarith
  exact (not_lt_of_gt hneg) (hpos t)

/-- **The separator splits the ω-limit set in the incomparable case.**  If the forward orbit of
`x₀` never goes below `z`, then every ω-limit point at or below `z` is a *zero* of the separating
functional, and every ω-limit point which is not below `z` is strictly positive. -/
theorem omegaLimit_eq_zero_or_pos_of_separator_of_incomparable_below
    (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S) (z : Concentration S)
    {φ : Concentration S → ℝ} (hφ : IsMonotoneSeparator z φ)
    (h : ¬ ∃ t : ℝ≥0, ϕ t x₀ ≤ z) :
    ∀ y ∈ omegaLimit atTop ϕ {x₀}, (y ≤ z ∧ φ y = 0) ∨ (¬ (y ≤ z) ∧ 0 < φ y) := by
  intro y hy
  by_cases hle : y ≤ z
  · refine Or.inl ⟨hle, ?_⟩
    have h1 : φ y ≤ 0 := (hφ.2.2.2.1 y).mpr hle
    have h2 : 0 ≤ φ y := omegaLimit_nonneg_of_separator_of_incomparable_below ϕ x₀ z hφ h y hy
    exact le_antisymm h1 h2
  · refine Or.inr ⟨hle, ?_⟩
    have h1 : ¬ (φ y ≤ 0) := fun hh => hle ((hφ.2.2.2.1 y).mp hh)
    exact lt_of_not_ge h1

end ClusterValues

section UniformGap

variable {S : Type} [Fintype S]

/-- **A uniform gap for the separating functional.**  The monotone separating functional `φ` of the
point `z` is bounded away from zero on the compact set `K` carrying the forward orbit: there is
`δ > 0` with `δ ≤ φ y` for every `y ∈ K` which is *not* below `z`.

This is the "uniform" form of the strictness of the separator; it implies the pointwise strictness
`z ≤ y → y ≠ z → 0 < φ y` on `K`, and it is the hypothesis which closes the remaining case of
the strong-order argument. -/
def HasUniformSeparatorGap (z : Concentration S) (φ : Concentration S → ℝ) (K : Set (Concentration S))
    (δ : ℝ) : Prop :=
  IsMonotoneSeparator z φ ∧ 0 < δ ∧ ∀ y ∈ K, ¬ (y ≤ z) → δ ≤ φ y

/-- **Order-convexity of the ω-limit set under a uniform gap.**  Let `ϕ` be a monotone forward
semiflow, `x₀` a point whose forward orbit is eventually absorbed by the compact set `K`, and
let `Ω = omegaLimit atTop ϕ {x₀}`.  Assume

* `hΩE` : every point of `Ω` is an equilibrium of the flow;
* `hEq` : the equilibrium set of the flow is order-convex;
* `hφ` : the monotone separating functional `φ` of the test point `z` has a *uniform gap* on `K`
  (see `CRNT.HasUniformSeparatorGap`).

Then a point `z` lying between two ω-limit points (`p ≤ z ≤ q` with `p, q ∈ Ω`) belongs to `Ω`,
**with no comparability hypothesis on the orbit**.

*Proof.*  The only case left by `CRNT.omegaLimit_orderConvex_of_monotone_flow_general` is the
incomparable-orbit one, in which the separating functional is positive along the whole orbit
(`CRNT.omegaLimit_nonneg_of_separator_of_incomparable_below` gives the nonnegativity, the
monotonicity of `φ` the strict positivity).  The uniform gap then bounds `φ` away from zero along
the tail of the orbit, whereas the ω-limit point `p ≤ z` forces `φ p ≤ 0`; the two are incompatible
because `φ (ϕ t x₀)` is arbitrarily close to `φ p` at late times. -/
theorem omegaLimit_orderConvex_of_monotone_flow_of_uniformSeparator
    (ϕ : Flow ℝ≥0 (Concentration S))
    (hmono : CRNT.Monotone.IsMonotoneFlow ϕ)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y)
    (hEq : ∀ p q z : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (p q z : Concentration S)
    (φ : Concentration S → ℝ) (δ : ℝ) (hφ : HasUniformSeparatorGap z φ K δ)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q) :
    z ∈ omegaLimit atTop ϕ {x₀} := by
  rcases (omegaLimit_orderConvex_of_monotone_flow_general ϕ hmono x₀ hΩE hEq p q z hp hq hpz hzq) with
    hz' | hrest
  · exact hz'
  · obtain ⟨hbelow, habove, hns, hnt⟩ := hrest
    -- the separating functional is strictly positive along the orbit
    have hpos : ∀ t : ℝ≥0, 0 < φ (ϕ t x₀) := by
      intro t
      have hn : ¬ (ϕ t x₀ ≤ z) := fun hh => hbelow ⟨t, hh⟩
      have hne : ¬ (φ (ϕ t x₀) ≤ 0) := fun hh => hn ((hφ.1.2.2.2.1 (ϕ t x₀)).mp hh)
      exact lt_of_not_ge hne
    -- the tail of the orbit is contained in `K`, and so is the ω-limit set
    obtain ⟨v, hv, hvK⟩ := habs
    have hΩK : ∀ y ∈ omegaLimit atTop ϕ {x₀}, y ∈ K := by
      intro y hy
      exact hvK ((omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := v) hv) hy)
    have _hΩcompact : IsCompact (omegaLimit atTop ϕ {x₀}) :=
      hK.of_isClosed_subset (isClosed_omegaLimit atTop ϕ {x₀}) hΩK
    have horbK : ∀ t ∈ v, ϕ t x₀ ∈ K := by
      intro t ht
      exact hvK (subset_closure (Set.mem_image2_of_mem ht (Set.mem_singleton x₀)))
    -- hence the separating functional is uniformly positive along the tail
    have hgap : ∀ t ∈ v, δ ≤ φ (ϕ t x₀) := by
      intro t ht
      have hK' : ϕ t x₀ ∈ K := horbK t ht
      have hn : ¬ (ϕ t x₀ ≤ z) := fun hh => hbelow ⟨t, hh⟩
      exact hφ.2.2 (ϕ t x₀) hK' hn
    -- but `p ≤ z` forces `φ p ≤ 0`, and `φ (ϕ t x₀)` is close to `φ p` at late times
    have hφp : φ p ≤ 0 := (hφ.1.2.2.2.1 p).mpr hpz
    have hδ : 0 < δ := hφ.2.1
    obtain ⟨t, ht, hclose⟩ :=
      exists_close_omegaLimit ϕ x₀ hφ.1.1 hp (u := v) hv (ε := δ / 2) (by linarith)
    have h1 : φ (ϕ t x₀) < φ p + δ / 2 := by
      have habs : φ (ϕ t x₀) - φ p ≤ |φ (ϕ t x₀) - φ p| := le_abs_self _
      linarith
    have h2 : φ (ϕ t x₀) ≤ δ / 2 := by linarith
    have h3 : δ ≤ φ (ϕ t x₀) := hgap t ht
    linarith

section MassAction

variable {S : Type} [Fintype S] [DecidableEq S]

/-- **Order-convexity of the ω-limit set of a mass-action network with an order-preserving field,
under a uniform gap.**  This is the reaction-network specialisation of
`CRNT.omegaLimit_orderConvex_of_monotone_flow_of_uniformSeparator`: the field of a cooperative
network is order-preserving, the equilibria of the flow form an order-convex set, and the
Hirsch–Smith separator `CRNT.sepAbove z` is a strict monotone separator at every point, so the
remaining case of the strong-order argument is closed whenever the separator is bounded away
from zero on the compact set carrying the orbit. -/
theorem massAction_omegaLimit_orderConvex_of_monotone_field_of_uniformSeparator
    (N : Network S) (κ : N.RateConstants)
    (hmonoF : ∀ x y : Concentration S, x ≤ y →
      N.massActionVectorField κ x ≤ N.massActionVectorField κ y)
    (ϕ : Flow ℝ≥0 (Concentration S)) (hmonFlow : CRNT.Monotone.IsMonotoneFlow ϕ)
    (hEqFlow : ∀ y : Concentration S, (∀ t : ℝ≥0, ϕ t y = y) ↔ N.massActionVectorField κ y = 0)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, N.massActionVectorField κ y = 0)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (p q z : Concentration S)
    (φ : Concentration S → ℝ) (δ : ℝ) (hφ : HasUniformSeparatorGap z φ K δ)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q) :
    z ∈ omegaLimit atTop ϕ {x₀} := by
  -- the zero set of an order-preserving field is order-convex
  have hEz : ∀ a b c : Concentration S,
      (∀ t : ℝ≥0, ϕ t a = a) → (∀ t : ℝ≥0, ϕ t b = b) → a ≤ c → c ≤ b → ∀ t : ℝ≥0, ϕ t c = c := by
    intro a b c ha hb hac hcb
    have ha' : N.massActionVectorField κ a = 0 := (hEqFlow a).mp ha
    have hb' : N.massActionVectorField κ b = 0 := (hEqFlow b).mp hb
    have hmem : c ∈ {x | N.massActionVectorField κ x = 0} :=
      monotone_equilibrium_orderConvex hmonoF {x | N.massActionVectorField κ x = 0}
        (fun x => Iff.rfl) a b c (by simp [ha']) (by simp [hb']) hac hcb
    exact (hEqFlow c).mpr hmem
  -- the ω-limit set consists of equilibria of the flow
  have hΩEflow : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y := by
    intro y hy t
    exact (hEqFlow y).mpr (hΩE y hy) t
  exact omegaLimit_orderConvex_of_monotone_flow_of_uniformSeparator ϕ hmonFlow x₀ hΩEflow hEz K hK habs
    p q z φ δ hφ hp hq hpz hzq

end MassAction

end UniformGap


section DiscreteOmegaLimit

variable {S : Type} [Fintype S]

omit [Fintype S] in
/-- **ω-limit points are detected by the tails of the orbit.**  `y` is a ω-limit point of the orbit
of `x₀` if and only if, for every neighbourhood `n` of `y` and every tail of the orbit, the orbit
meets `n` at a time beyond that tail. -/
lemma mem_omegaLimit_iff_frequently_tail (ϕ : Flow ℝ≥0 (Concentration S)) (x₀ : Concentration S)
    (y : Concentration S) :
    y ∈ omegaLimit atTop ϕ {x₀} ↔
      ∀ n ∈ 𝓝 y, ∀ T : ℝ≥0, ∃ t ≥ T, ϕ t x₀ ∈ n := by
  constructor
  · intro hy n hn T
    obtain ⟨w, hwn, hwA⟩ :=
      (mem_closure_iff_nhds.mp
        ((omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.Ici T)
          (Ici_mem_atTop T)) hy)) n hn
    obtain ⟨t, ht, b, hb, hbeq⟩ := hwA
    have hb' : b = x₀ := Set.mem_singleton_iff.mp hb
    subst hb'
    exact ⟨t, ht, hbeq ▸ hwn⟩
  · intro h
    rw [mem_omegaLimit_iff_frequently]
    intro n hn
    apply (Filter.frequently_iff).2
    intro U hU
    obtain ⟨T, hT⟩ := Filter.mem_atTop_sets.mp hU
    obtain ⟨t, ht, htn⟩ := h n hn T
    refine ⟨t, hT t ht, ?_⟩
    exact ⟨x₀, Set.mem_singleton x₀, htn⟩

/-- **Order-convexity of a discrete ω-limit set under a strict monotone separator.**  Let `ϕ` be a
monotone forward semiflow, `x₀` a point whose forward orbit is eventually absorbed by the compact set
`K`, and let `Ω = omegaLimit atTop ϕ {x₀}`.  Assume

* `hΩE` : every point of `Ω` is an equilibrium of the flow;
* `hEq` : the equilibrium set of the flow is order-convex;
* `hfin` : the ω-limit set `Ω` is *finite* (discrete);
* `hφ` : `φ` is a **strict monotone separator** of the test point `z`, i.e. `φ y > 0` for every
  `y ≥ z`, `y ≠ z` (`CRNT.IsStrictMonotoneSeparator`).

Then a point `z` lying between two ω-limit points (`p ≤ z ≤ q` with `p, q ∈ Ω`) belongs to `Ω`,
**with no comparability hypothesis on the orbit**.

*Proof.*  The only case left by `CRNT.omegaLimit_orderConvex_of_monotone_flow_general` is the
incomparable-orbit one.  There the separating functional is positive along the whole orbit, while
`p ≤ z` forces `φ p = 0`; the strictness gives `φ q > 0` for `q ≥ z`, `q ≠ z`.  A continuous
functional on a tail of the orbit cannot jump from the value `0` to a value `> φ q` without taking
every intermediate value, and each intermediate value is attained at a ω-limit point (the closures of
the tails are nested compact sets meeting the corresponding level set).  The ω-limit set would then
contain a point at each of the infinitely many levels of `(0, φ q)`, contradicting its finiteness. -/
theorem omegaLimit_orderConvex_of_monotone_flow_of_discreteOmegaLimit
    (ϕ : Flow ℝ≥0 (Concentration S))
    (hmono : CRNT.Monotone.IsMonotoneFlow ϕ)
    (x₀ : Concentration S)
    (hΩE : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ≥0, ϕ t y = y)
    (hEq : ∀ p q z : Concentration S,
      (∀ t : ℝ≥0, ϕ t p = p) → (∀ t : ℝ≥0, ϕ t q = q) → p ≤ z → z ≤ q → ∀ t : ℝ≥0, ϕ t z = z)
    (hfin : (omegaLimit atTop ϕ {x₀}).Finite)
    (K : Set (Concentration S)) (hK : IsCompact K)
    (habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (p q z : Concentration S)
    (φ : Concentration S → ℝ) (hφ : IsStrictMonotoneSeparator z φ)
    (hp : p ∈ omegaLimit atTop ϕ {x₀}) (hq : q ∈ omegaLimit atTop ϕ {x₀})
    (hpz : p ≤ z) (hzq : z ≤ q) :
    z ∈ omegaLimit atTop ϕ {x₀} := by
  rcases (omegaLimit_orderConvex_of_monotone_flow_general ϕ hmono x₀ hΩE hEq p q z hp hq hpz hzq) with
    hz' | hrest
  · exact hz'
  · obtain ⟨hbelow, habove, hns, hnt⟩ := hrest
    -- the separating functional is positive along the whole orbit
    have hpos : ∀ t : ℝ≥0, 0 < φ (ϕ t x₀) := by
      intro t
      have hn : ¬ (ϕ t x₀ ≤ z) := fun hh => hbelow ⟨t, hh⟩
      have hne : ¬ (φ (ϕ t x₀) ≤ 0) := fun hh => hn ((hφ.le_zero_iff (ϕ t x₀)).mp hh)
      exact lt_of_not_ge hne
    -- the ω-limit point `p ≤ z` is a zero of the separating functional
    have hφp : φ p = 0 := by
      have h1 : φ p ≤ 0 := (hφ.le_zero_iff p).mpr hpz
      have h2 : 0 ≤ φ p :=
        omegaLimit_nonneg_of_separator_of_incomparable_below ϕ x₀ z hφ.isMonotoneSeparator hbelow p hp
      exact le_antisymm h1 h2
    by_cases hqz : q = z
    · exact hqz ▸ hq
    · have hφq : 0 < φ q := hφ.strict hzq hqz
      obtain ⟨v, hv, hvK⟩ := habs
      obtain ⟨V, hV⟩ := Filter.mem_atTop_sets.mp hv
      -- for every level `c` strictly between `0` and `φ q` there is a ω-limit point at that level
      have hcluster : ∀ c : ℝ, 0 < c → c < φ q → ∃ y ∈ omegaLimit atTop ϕ {x₀}, φ y = c := by
        intro c hc0 hcq
        -- the level set `φ = c` is closed
        have hlevel : IsClosed {w : Concentration S | φ w = c} := by
          have heq : {w : Concentration S | φ w = c} = (fun w : Concentration S => φ w) ⁻¹' {c} := by
            ext w
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
          rw [heq]
          exact IsClosed.preimage hφ.1.1 (isClosed_singleton)
        -- every tail of the orbit meets the level set
        have hmeet : ∀ T : ℝ≥0,
            (closure (Set.image2 ϕ (Set.Ici (max V T)) {x₀}) ∩ {w | φ w = c}).Nonempty := by
          intro T
          -- a time with separation below `c`, and a later time with separation above `c`
          obtain ⟨t₁, ht₁, hclose₁⟩ :=
            exists_close_omegaLimit ϕ x₀ hφ.1.1 hp (u := Set.Ici (max V T)) (Ici_mem_atTop _)
              (ε := c / 2) (by linarith)
          have hlt : φ (ϕ t₁ x₀) < c := by
            have habs' : φ (ϕ t₁ x₀) - φ p ≤ |φ (ϕ t₁ x₀) - φ p| := le_abs_self _
            linarith [hφp, hclose₁, habs']
          obtain ⟨t₂, ht₂, hclose₂⟩ :=
            exists_close_omegaLimit ϕ x₀ hφ.1.1 hq (u := Set.Ici t₁) (Ici_mem_atTop _)
              (ε := (φ q - c) / 2) (by linarith)
          have hgt : φ (ϕ t₂ x₀) > c := by
            have habs' : φ (ϕ t₂ x₀) - φ q ≤ |φ (ϕ t₂ x₀) - φ q| := le_abs_self _
            have habs'' : -|φ (ϕ t₂ x₀) - φ q| ≤ φ (ϕ t₂ x₀) - φ q :=
              (abs_le.mp (le_rfl : |φ (ϕ t₂ x₀) - φ q| ≤ |φ (ϕ t₂ x₀) - φ q|)).1
            linarith [hclose₂, habs', habs'']
          -- the intermediate value of the separating functional along the orbit
          have hcont : ContinuousOn (fun t : ℝ≥0 => φ (ϕ t x₀)) (Set.Icc t₁ t₂) :=
            ((hφ.1.1).comp (ϕ.continuous continuous_id continuous_const)).continuousOn
          obtain ⟨t, ht, hft⟩ := (intermediate_value_Icc ht₂ hcont) ⟨hlt.le, hgt.le⟩
          refine ⟨ϕ t x₀, ⟨?_, ?_⟩⟩
          · refine subset_closure ?_
            exact Set.mem_image2_of_mem
              (mem_Ici.mpr (le_trans (mem_Ici.mp ht₁) ht.1)) (Set.mem_singleton x₀)
          · exact hft
        -- the nested compact sets `closure (tail) ∩ level` have a common point
        set G : ℕ → Set (Concentration S) := fun n =>
          closure (Set.image2 ϕ (Set.Ici (max V (n : ℝ≥0))) {x₀}) ∩ {w | φ w = c} with hGdef
        have hGK : ∀ n : ℕ, G n ⊆ K := by
          intro n w hw
          have h1 : w ∈ closure (Set.image2 ϕ v {x₀}) :=
            closure_mono (s := Set.image2 ϕ (Set.Ici (max V (n : ℝ≥0))) {x₀})
              (t := Set.image2 ϕ v {x₀})
              (image2_subset
                (fun s hs => hV s (le_trans (le_max_left V (n : ℝ≥0)) (mem_Ici.mp hs)))
                Subset.rfl) hw.1
          exact hvK h1
        have hdec : ∀ n₁ n₂ : ℕ, n₁ ≤ n₂ → G n₂ ⊆ G n₁ := by
          intro n₁ n₂ hn w hw
          have hn' : (n₁ : ℝ≥0) ≤ (n₂ : ℝ≥0) := by exact_mod_cast hn
          refine ⟨?_, hw.2⟩
          exact closure_mono (s := Set.image2 ϕ (Set.Ici (max V (n₂ : ℝ≥0))) {x₀})
            (t := Set.image2 ϕ (Set.Ici (max V (n₁ : ℝ≥0))) {x₀})
            (image2_subset
              (fun s hs =>
                mem_Ici.mpr (le_trans (max_le_max (le_refl V) hn') (mem_Ici.mp hs)))
              Subset.rfl) hw.1
        -- a convergent sequence of points, one in each `G n`
        obtain ⟨y, hy⟩ : ∃ y : ℕ → Concentration S, ∀ n : ℕ, y n ∈ G n := by
          refine ⟨fun n => Classical.choose (hmeet (n : ℝ≥0)), ?_⟩
          intro n
          exact Classical.choose_spec (hmeet (n : ℝ≥0))
        have hyK : ∀ n : ℕ, y n ∈ K := by
          intro n
          exact hGK n (hy n)
        obtain ⟨a, haK, g, hg, htend⟩ := hK.isSeqCompact (x := y) hyK
        have hgnat : ∀ k : ℕ, k ≤ g k := by
          intro k
          induction k with
          | zero => exact Nat.zero_le _
          | succ k ih =>
            have h1 := Nat.succ_le_of_lt (hg (Nat.lt_succ_self k))
            exact le_trans (Nat.succ_le_succ ih) h1
        -- the limit `a` belongs to every `G n`
        have haG : ∀ n : ℕ, a ∈ G n := by
          intro n
          have hcl : IsClosed (G n) := IsClosed.inter isClosed_closure hlevel
          refine hcl.mem_of_tendsto htend ?_
          have hev : ∀ᶠ k : ℕ in atTop, n ≤ g k := by
            exact (Filter.eventually_atTop (p := fun k : ℕ => n ≤ g k)).2
              ⟨n, fun b hb => le_trans hb (hgnat b)⟩
          filter_upwards [hev] with k hk
          exact hdec n (g k) (by exact hk) (hy (g k))
        have haI : a ∈ ⋂ n : ℕ, G n := mem_iInter.mpr haG
        -- `a` is a ω-limit point at the level `c`
        have haΩ : a ∈ omegaLimit atTop ϕ {x₀} := by
          rw [mem_omegaLimit_iff_frequently_tail]
          intro n hn T
          have ha1 : a ∈ G (Nat.ceil T) := haG (Nat.ceil T)
          obtain ⟨w, hwn, hwA⟩ := (mem_closure_iff_nhds.mp ha1.1) n hn
          obtain ⟨t, ht, b, hb, hbeq⟩ := hwA
          have hb' : b = x₀ := Set.mem_singleton_iff.mp hb
          subst hb'
          have hceil : T ≤ (Nat.ceil T : ℝ≥0) := by
            exact_mod_cast (Nat.le_ceil (T : ℝ))
          exact ⟨t,
            le_trans hceil
              (le_trans (le_max_right V (Nat.ceil T)) (mem_Ici.mp ht)), hbeq ▸ hwn⟩
        exact ⟨a, haΩ, ((mem_iInter.mp haI) 0).2⟩
      -- the separator takes every value of `(0, φ q)` at a ω-limit point: the ω-limit set is infinite
      have hIoo : Set.Ioo (0 : ℝ) (φ q) ⊆ φ '' omegaLimit atTop ϕ {x₀} := by
        intro c hc
        obtain ⟨y, hy, hφy⟩ := hcluster c hc.1 hc.2
        exact ⟨y, hy, hφy⟩
      have hIooFin : (Set.Ioo (0 : ℝ) (φ q)).Finite := (hfin.image φ).subset hIoo
      exact absurd hIooFin ((Set.Ioo_infinite (by linarith)).not_finite)

end DiscreteOmegaLimit

section Instances

variable {S : Type} [Fintype S] [Nonempty S]

/-- **The Hirsch–Smith separator is strict at every point.**  `CRNT.sepAbove z` is a strict monotone
separator of the point `z`: it is positive on every `y ≥ z` with `y ≠ z`.  Thus the hypothesis of
`CRNT.omegaLimit_orderConvex_of_monotone_flow_of_uniformSeparator` is not vacuous. -/
theorem isStrictMonotoneSeparator_sepAbove (z : Concentration S) :
    IsStrictMonotoneSeparator z (sepAbove z) := by
  refine ⟨isMonotoneSeparator_sepAbove z, ?_⟩
  intro y hzy hyz
  have hne : ¬ (y ≤ z) := fun hle => hyz (le_antisymm hle hzy)
  have hne' : ¬ (sepAbove z y ≤ 0) := fun hh => hne (sepAbove_le_zero_iff.mp hh)
  exact lt_of_not_ge hne'

/-- **The truncated Hirsch–Smith separator is a vanishing separator.**  The functional
`y ↦ max (0, sepAbove z y)` vanishes exactly on the down-set `↓ z` and is strictly positive off
it; it is therefore a strict monotone separator of `z`. -/
theorem isVanishingMonotoneSeparator_truncSepAbove (z : Concentration S) :
    IsVanishingMonotoneSeparator z (fun y : Concentration S => max (0 : ℝ) (sepAbove z y)) := by
  have hcont : Continuous (fun y : Concentration S => max (0 : ℝ) (sepAbove z y)) :=
    continuous_const.max (sepAbove_continuous z)
  have hsep : Monotone (sepAbove z) := by
    intro a b hab
    exact sepAbove_mono hab
  have hmono : Monotone (fun y : Concentration S => max (0 : ℝ) (sepAbove z y)) :=
    Monotone.max monotone_const hsep
  refine ⟨⟨hcont, fun x y hxy => hmono hxy, ?_, ?_, ?_⟩, ?_⟩
  · show max (0 : ℝ) (sepAbove z z) = 0
    rw [sepAbove_self z, max_eq_left (le_refl 0)]
  · intro y
    constructor
    · intro h
      have h' : sepAbove z y ≤ 0 := le_trans (le_max_right 0 (sepAbove z y)) h
      exact sepAbove_le_zero_iff.mp h'
    · intro h
      have h' : sepAbove z y ≤ 0 := sepAbove_le_zero_iff.mpr h
      show max (0 : ℝ) (sepAbove z y) ≤ 0
      rw [max_eq_left h']
  · intro y hy
    exact absurd hy (not_lt_of_ge (le_max_left 0 (sepAbove z y)))
  · intro y
    constructor
    · intro h
      have h' : sepAbove z y ≤ 0 := by
        have hle : sepAbove z y ≤ max (0 : ℝ) (sepAbove z y) := le_max_right 0 (sepAbove z y)
        have h'' : max (0 : ℝ) (sepAbove z y) = 0 := h
        linarith
      exact sepAbove_le_zero_iff.mp h'
    · intro h
      have h' : sepAbove z y ≤ 0 := sepAbove_le_zero_iff.mpr h
      show max (0 : ℝ) (sepAbove z y) = 0
      rw [max_eq_left h']

/-- **The truncated Hirsch–Smith separator is strict at every point.** -/
theorem isStrictMonotoneSeparator_truncSepAbove (z : Concentration S) :
    IsStrictMonotoneSeparator z (fun y : Concentration S => max (0 : ℝ) (sepAbove z y)) :=
  (isVanishingMonotoneSeparator_truncSepAbove z).isStrict

end Instances

end CRNT

#print axioms CRNT.IsStrictMonotoneSeparator
#print axioms CRNT.exists_close_omegaLimit
#print axioms CRNT.omegaLimit_nonneg_of_separator_of_incomparable_below
#print axioms CRNT.omegaLimit_eq_zero_or_pos_of_separator_of_incomparable_below
#print axioms CRNT.mem_omegaLimit_iff_frequently_tail
#print axioms CRNT.omegaLimit_orderConvex_of_monotone_flow_of_uniformSeparator
#print axioms CRNT.omegaLimit_orderConvex_of_monotone_flow_of_discreteOmegaLimit
#print axioms CRNT.massAction_omegaLimit_orderConvex_of_monotone_field_of_uniformSeparator
#print axioms CRNT.isStrictMonotoneSeparator_sepAbove
#print axioms CRNT.isVanishingMonotoneSeparator_truncSepAbove
