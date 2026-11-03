import CRNT.Dynamics.EndotacticPermanence

/-!
# Global permanence quantifiers

The existing `Permanent ϕ x₀` predicate is orbit-level: one orbit is eventually confined to
some compact subset of the open positive orthant.  Standard CRNT permanence is stronger and
class-uniform: for each positive stoichiometric compatibility class there is **one** compact
interior set that eventually absorbs every positive orbit in that class.

This module keeps both levels explicit:

* `OrbitwisePermanentForFlow` / `OrbitwisePermanentForRates` quantify the old orbit-level notion;
* `PermanentOnPositiveClass` is the standard class-uniform notion;
* `PermanentForFlow`, `PermanentForRates`, and `StructurallyPermanent` quantify standard
  permanence over a genuine mass-action flow, rate constants, and finally all rate constants.

The class-uniform definition is intentionally phrased with the same tail-closure condition used by
`Permanent`, so the bridge from standard permanence to the pre-existing orbit-level API is purely
logical and does not require additional topology.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `ϕ`/`γ` represent the mass-action dynamics for `N, κ` on forward time. -/
def IsMassActionFlow (N : Network S) (κ : N.RateConstants)
    (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S) : Prop :=
  (∀ x, γ x 0 = x) ∧
  (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
  (∀ (x : Concentration S) (t : ℝ), 0 ≤ t →
    HasDerivAt (γ x) (N.massActionVectorField κ (γ x t)) t)

/-- Legacy orbitwise quantifier: every positive orbit of a fixed genuine mass-action flow is
`Permanent` in the pre-existing orbit-level sense.  This is weaker than standard CRNT permanence
because the compact set may depend on the initial condition. -/
def OrbitwisePermanentForFlow (N : Network S) (κ : N.RateConstants)
    (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S) : Prop :=
  N.IsMassActionFlow κ ϕ γ →
    ∀ x₀ : Concentration S, x₀.Positive → Permanent ϕ x₀

/-- Orbitwise permanence for every genuine flow realizing a fixed rate vector. -/
def OrbitwisePermanentForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
    N.OrbitwisePermanentForFlow κ ϕ γ

/-- Orbitwise permanence for every rate vector.  This name is retained only to distinguish the
historical per-orbit quantifier from standard class-uniform permanence below. -/
def StructurallyOrbitwisePermanent (N : Network S) : Prop :=
  ∀ κ : N.RateConstants, N.OrbitwisePermanentForRates κ

/-- **Standard permanence on one positive stoichiometric class.**

There is one compact set `K` contained in the positive compatibility class of `xref` such that
for *every* positive initial point `x₀` in that class, some forward-time tail of its orbit has
closure contained in `K`.  The tail time may depend on `x₀`; the absorbing set `K` may not. -/
def PermanentOnPositiveClass (N : Network S) (ϕ : Flow ℝ≥0 (Concentration S))
    (xref : Concentration S) : Prop :=
  ∃ K : Set (Concentration S), IsCompact K ∧
    K ⊆ N.positiveCompatibilityClass xref ∧
    ∀ x₀ : Concentration S, x₀ ∈ N.positiveCompatibilityClass xref →
      ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K

/-- Standard permanence on a class immediately gives orbit-level `Permanent` for every positive
initial condition in that class. -/
theorem PermanentOnPositiveClass.permanent {N : Network S}
    {ϕ : Flow ℝ≥0 (Concentration S)} {xref x₀ : Concentration S}
    (h : N.PermanentOnPositiveClass ϕ xref)
    (hx₀ : x₀ ∈ N.positiveCompatibilityClass xref) : Permanent ϕ x₀ := by
  obtain ⟨K, hKcpt, hKclass, hKabs⟩ := h
  obtain ⟨v, hv, hvK⟩ := hKabs x₀ hx₀
  refine ⟨K, hKcpt, ?_, v, hv, hvK⟩
  intro y hy
  exact (hKclass hy).2

/-- Every standard permanent class is, in particular, orbitwise permanent. -/
theorem PermanentOnPositiveClass.orbitwise {N : Network S}
    {ϕ : Flow ℝ≥0 (Concentration S)} {xref : Concentration S}
    (h : N.PermanentOnPositiveClass ϕ xref) :
    ∀ x₀ : Concentration S, x₀.Positive → N.StoichCompatible xref x₀ → Permanent ϕ x₀ := by
  intro x₀ hx₀ hcompat
  exact h.permanent ⟨hcompat, hx₀⟩

/-- **Standard permanence of one genuine mass-action flow.**  Each positive stoichiometric
compatibility class has a compact interior absorbing set shared by all positive starts in that
class. -/
def PermanentForFlow (N : Network S) (κ : N.RateConstants)
    (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S) : Prop :=
  N.IsMassActionFlow κ ϕ γ →
    ∀ xref : Concentration S, xref.Positive → N.PermanentOnPositiveClass ϕ xref

/-- Standard permanence for a fixed kinetic system, quantified over every genuine mass-action flow
realization. -/
def PermanentForRates (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
    N.PermanentForFlow κ ϕ γ

/-- **Structural permanence.** Every positive rate vector gives a standard class-uniform permanent
mass-action system. -/
def StructurallyPermanent (N : Network S) : Prop :=
  ∀ κ : N.RateConstants, N.PermanentForRates κ

/-- Structural permanence specializes to any fixed kinetic system. -/
theorem StructurallyPermanent.forRates {N : Network S} (h : N.StructurallyPermanent)
    (κ : N.RateConstants) : N.PermanentForRates κ :=
  h κ

/-- Structural permanence supplies the uniform absorbing set for any chosen positive compatibility
class of a genuine mass-action flow. -/
theorem StructurallyPermanent.onPositiveClass {N : Network S} (h : N.StructurallyPermanent)
    (κ : N.RateConstants) {ϕ : Flow ℝ≥0 (Concentration S)}
    {γ : Concentration S → ℝ → Concentration S} (hflow : N.IsMassActionFlow κ ϕ γ)
    {xref : Concentration S} (hxref : xref.Positive) : N.PermanentOnPositiveClass ϕ xref :=
  h κ ϕ γ hflow xref hxref

/-- Standard structural permanence specializes to the old orbit-level `Permanent` conclusion. -/
theorem StructurallyPermanent.permanent {N : Network S} (h : N.StructurallyPermanent)
    (κ : N.RateConstants) {ϕ : Flow ℝ≥0 (Concentration S)}
    {γ : Concentration S → ℝ → Concentration S} (hflow : N.IsMassActionFlow κ ϕ γ)
    {xref x₀ : Concentration S} (hxref : xref.Positive) (hx₀ : x₀.Positive)
    (hcompat : N.StoichCompatible xref x₀) : Permanent ϕ x₀ :=
  (h.onPositiveClass κ hflow hxref).permanent ⟨hcompat, hx₀⟩

/-- In particular one may choose the initial condition itself as the class representative. -/
theorem StructurallyPermanent.permanent_selfClass {N : Network S} (h : N.StructurallyPermanent)
    (κ : N.RateConstants) {ϕ : Flow ℝ≥0 (Concentration S)}
    {γ : Concentration S → ℝ → Concentration S} (hflow : N.IsMassActionFlow κ ϕ γ)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) : Permanent ϕ x₀ :=
  h.permanent κ hflow hx₀ hx₀ (Network.StoichCompatible.refl N x₀)

/-- Standard permanence is stronger than the historical orbitwise global quantifier. -/
theorem StructurallyPermanent.toOrbitwise {N : Network S} (h : N.StructurallyPermanent) :
    N.StructurallyOrbitwisePermanent := by
  intro κ ϕ γ hflow x₀ hx₀
  exact h.permanent_selfClass κ hflow hx₀

end Network
end CRNT
