import CRNT.Dynamics.SiphonDimensionDescent
import CRNT.Dynamics.FaceCodimension

/-!
# What `IsCriticalSiphon` requires, and whether `Pmax` satisfies it

This module answers a structural question about the residual hole
`CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean:111-135`): the siphon-dimension descent
`CRNT.Network.omegaLimit_positive_of_boundary_point` is launched at the maximal face
`Pmax` and demands three data items there,

* `Pmax.Nonempty`,
* `N.IsCriticalSiphon Pmax`,
* `N.SiphonCarried ϕ x₀ Pmax`,

so it is worth knowing exactly what `Network.IsCriticalSiphon` unfolds to and which of
its conjuncts the hole's own hypotheses supply.  The answer, machine-checked below, is
**all of them, from the hole's hypotheses alone**.

## The definition chain

`Network.IsCriticalSiphon` (`CRNT/Dynamics/Siphon.lean:84-87`) is a three-way conjunction,
and `Network.IsSiphon` (`CRNT/Dynamics/Siphon.lean:54-55`) a one-way implication over the
reaction index.  `isCriticalSiphon_iff_unfolded` below is the fully unfolded chain, with the
inner existential binders spelled out, proved by `Iff.rfl` — no rewriting lemma, no
hypothesis.  The three conjuncts, with their origins:

| conjunct | origin of the statement |
|---|---|
| `P.Nonempty` | finite, purely about `P` |
| `∀ r, (∃ s ∈ P, (r.target) s ≠ 0) → (∃ s ∈ P, (r.source) s ≠ 0)` | `Network.IsSiphon`, `CRNT/Dynamics/Siphon.lean:55`, itself `Network.IsProduct → Network.IsReactant` (`Siphon.lean:39,43`) |
| `¬ ∃ v, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧ (∀ r, ∑ s, v s * (r.target - r.source) s = 0)` | the conservation clause: `v` is the *supported conservation cone* element, exactly positive on `P` |

The two reformulations the tree already carries — `isCriticalSiphon_iff_mem_orthSum`
(`CRNT/Dynamics/SiphonConservation.lean:55`, replacing the per-reaction sums by
`v ∈ orthSum N.stoichSubspace`) and `isCriticalSiphon_iff_not_carriesPositiveConservationLaw`
(`CRNT/Geometry/CompatibilityFaces.lean:70`) — are *rewrites of the third conjunct only*;
the first two conjuncts pass through unchanged in both.  `isCriticalSiphon_iff_mem_orthSum_shape`
records that verbatim, so no future argument mistakes the `orthSum` form for a stronger
predicate.

## What the hole's hypotheses discharge

The hole carries `hwmax : wmax ∈ omegaLimit atTop ϕ {x₀}` and
`hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0`.  Those two, plus `hPmaxne`, are *literally* the
carriedness witness: `Network.SiphonCarried` (`CRNT/Dynamics/SiphonDimensionDescent.lean:61-63`)
is `∃ w ∈ omegaLimit atTop ϕ {x₀}, ∀ s, s ∈ P ↔ w s = 0`.  So
`N.SiphonCarried ϕ x₀ Pmax` is discharged by `⟨wmax, hwmax, hzeroMax⟩`, with no dynamics
whatsoever — `siphonCarried_Pmax` below, and `siphonCarried_iff_omegaWitness` shows the
equivalence, so the two hole hypotheses *are* the statement, not merely an implication.
This is worth flagging against the natural first guess, which is that `SiphonCarried` is
the hard conjunct because it mentions the flow.

Carriedness then discharges *criticality*: `Network.isCriticalSiphon_of_siphonCarried`
(`CRNT/Dynamics/SiphonDimensionDescent.lean:68-80`) applies
`Network.isCriticalSiphon_zeroSet_of_mem_omegaLimit`
(`CRNT/Dynamics/CriticalSiphonOmega.lean:45-79`) at `wmax`, and *that* theorem supplies all
three conjuncts of `IsCriticalSiphon Pmax` at once — the siphon clause from
`isSiphon_zeroSet_of_mem_omegaLimit`, and the conservation clause from mass conservation:
a `v` supported on `Z(wmax)` has `∑ v s · wmax s = 0`, while affine invariance of the
ω-limit set (`hωaff`) pins that total to `∑ v s · x₀ s > 0` (`hx₀` positive, `Pmax`
nonempty).  `holeA_isCriticalSiphon_Pmax` is the resulting discharge, stated with the
hole's own hypothesis list.

## What is genuinely open

**No conjunct of `IsCriticalSiphon Pmax` is open.**  With the three items above, the
descent `omegaLimit_positive_of_boundary_point`
(`CRNT/Dynamics/SiphonDimensionDescent.lean:158-178`) reduces to exactly one missing
hypothesis, `N.ComparableGrowthDescent ϕ x₀`, and the tree already proves
`comparableGrowthDescent_iff_omegaPointPositive`
(`CRNT/Dynamics/SiphonDimensionDescent.lean:368-377`) to be *equivalent* to the hole's
conclusion once a carried critical siphon is in hand.
`holeA_goal_iff_comparableGrowthDescent` is the resulting reduction of the hole; it is a
corollary of that existing theorem, cited here, not re-proved.  So the residue is the
analytic comparable-growth estimate alone, with no residual formulation gap in the
`IsCriticalSiphon` supply.

## Non-vacuity

`IsCriticalSiphon` is not vacuous: `fin4chain_isCriticalSiphon_AC` exhibits a nonempty
critical siphon of **cardinality two** — the shape the hole's `hcard : 2 ≤ Pmax.card`
demands — for the two-step chain `A → B`, `C → D` on four species.  The example is built
from scratch here; `CRNT.Examples.OmegaPointFakeFlow.gacN_isCriticalSiphon_A`
(`CRNT/Examples/OmegaPointFakeFlow.lean:276`) is a different network with a different
purpose and does not discharge it.

Depends on: `CRNT.Dynamics.SiphonDimensionDescent`, `CRNT.Dynamics.FaceCodimension`.
-/

open Filter Topology
open scoped BigOperators NNReal Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### The definition chain, fully unfolded -/

/-- **The exact unfolded definition chain of `IsCriticalSiphon`.**

`N.IsCriticalSiphon P` is, literally, `P.Nonempty ∧ N.IsSiphon P ∧` the negation of the
existence of a nonnegative species vector strictly positive exactly on `P` and orthogonal
to every reaction vector.  This instance is `Iff.rfl`: it uses no rewriting lemma and no
hypothesis, so it is a statement about the *syntax* of the predicate, not about any
network.  The middle conjunct is `Network.IsSiphon` (`CRNT/Dynamics/Siphon.lean:55`) with
`Network.IsProduct` (`:39`) and `Network.IsReactant` (`:43`) unfolded. -/
theorem isCriticalSiphon_iff_unfolded (N : Network S) (P : Finset S) :
    N.IsCriticalSiphon P ↔
      P.Nonempty ∧
        (∀ r : N.R, (∃ s, s ∈ P ∧ (N.reaction r).target s ≠ 0) →
           (∃ s, s ∈ P ∧ (N.reaction r).source s ≠ 0)) ∧
        ¬ ∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧
          (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0) := Iff.rfl

/-- **Conjunct 1 of `IsCriticalSiphon`, isolated.** -/
theorem isCriticalSiphon_nonempty {N : Network S} {P : Finset S}
    (h : N.IsCriticalSiphon P) : P.Nonempty := h.1

/-- **Conjunct 3 of `IsCriticalSiphon`, isolated**: there is no nonnegative species vector,
strictly positive precisely on `P`, orthogonal to every reaction vector.  Equivalently
`P` carries no positive conservation law. -/
theorem isCriticalSiphon_no_conservationLaw {N : Network S} {P : Finset S}
    (h : N.IsCriticalSiphon P) :
    ¬ ∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧
      (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0) := h.2.2

/-- **The `orthSum` rewrite of the conservation clause preserves the first two conjuncts
verbatim** (`CRNT/Dynamics.SiphonConservation.lean:55`).  Recorded so that no future
argument mistakes the `orthSum` form for a stronger predicate than `IsCriticalSiphon`. -/
theorem isCriticalSiphon_iff_mem_orthSum_shape (N : Network S) (P : Finset S) :
    N.IsCriticalSiphon P ↔
      P.Nonempty ∧ N.IsSiphon P ∧
        ¬ ∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧
          v ∈ orthSum N.stoichSubspace :=
  N.isCriticalSiphon_iff_mem_orthSum P

/-! ### Carriedness of `Pmax` is discharged by two of the hole's hypotheses alone -/

/-- **`Pmax` is carried by the trajectory through `x₀`, from `hwmax` and `hzeroMax` alone.**

`Network.SiphonCarried` (`CRNT/Dynamics/SiphonDimensionDescent.lean:61-63`) is
`∃ w ∈ omegaLimit atTop ϕ {x₀}, ∀ s, s ∈ P ↔ w s = 0`, and the hole's `hwmax` and
`hzeroMax` are exactly that triple at `w = wmax`.  No flow hypothesis, no κ, no orbit
hypothesis is consumed. -/
theorem siphonCarried_Pmax (N : Network S) {ϕ : Flow ℝ≥0 (Concentration S)}
    {x₀ : Concentration S} {Pmax : Finset S} {wmax : Concentration S}
    (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0) :
    N.SiphonCarried ϕ x₀ Pmax :=
  ⟨wmax, hwmax, hzeroMax⟩

/-- **`SiphonCarried` is *literally* the existence of an ω-point whose zero set is `Pmax`.**

The statement is `∃ w ∈ omegaLimit atTop ϕ {x₀}, ∀ s, s ∈ Pmax ↔ w s = 0`, so the hole's
`hwmax` and `hzeroMax` are not merely sufficient for carriedness at `Pmax` — after naming
`w = wmax` they *are* it.  This is the sense in which carriedness at `Pmax` is no residual
obligation: no flow hypothesis, no κ, no orbit hypothesis is consumed. -/
theorem siphonCarried_iff_omegaWitness (N : Network S)
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S}
    {Pmax : Finset S} :
    N.SiphonCarried ϕ x₀ Pmax ↔
      ∃ w ∈ omegaLimit atTop ϕ {x₀}, ∀ s, s ∈ Pmax ↔ w s = 0 :=
  ⟨fun h => h, fun h => h⟩

/-! ### Full discharge of `IsCriticalSiphon Pmax` -/

/-- **The hole's hypotheses discharge `N.IsCriticalSiphon Pmax` in full.**

Stated with exactly the subset of
`exists_positive_omegaPoint_of_highCodimension_siphonFace`'s hypotheses that the ω-limit
machinery consumes: `hϕγ hK hmaps hωnn hgenω hωaff hx₀` (the orbit data),
`hPmaxne hwmax hzeroMax` (the face).  The conclusion is `IsCriticalSiphon Pmax` together
with its carrier, i.e. *all three* conjuncts of the definition plus the descent's third
data item.

The proof is the existing `Network.isCriticalSiphon_of_siphonCarried`
(`CRNT/Dynamics/SiphonDimensionDescent.lean:68-80`) at `wmax`, which in turn is
`Network.isCriticalSiphon_zeroSet_of_mem_omegaLimit`
(`CRNT/Dynamics/CriticalSiphonOmega.lean:45-79`).  That theorem's own argument supplies
each conjunct: nonemptiness from `hPmaxne`; the siphon clause from
`isSiphon_zeroSet_of_mem_omegaLimit` at the zero set of `wmax`; the conservation clause
from mass conservation combined with `hωaff` and `hx₀`. -/
theorem holeA_isCriticalSiphon_Pmax
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0) :
    N.IsCriticalSiphon Pmax ∧ N.SiphonCarried ϕ x₀ Pmax :=
  have hcarr : N.SiphonCarried ϕ x₀ Pmax := siphonCarried_Pmax N hwmax hzeroMax
  have hcrit : N.IsCriticalSiphon Pmax :=
    N.isCriticalSiphon_of_siphonCarried κ hϕγ hK hmaps hωnn hgenω hωaff hx₀ hPmaxne hcarr
  ⟨hcrit, hcarr⟩

/-! ### The exact reduction of the hole -/

/-- **With the hole's hypotheses, its conclusion is equivalent to
`N.ComparableGrowthDescent ϕ x₀`.**

A corollary of `holeA_isCriticalSiphon_Pmax` and the *existing*
`Network.comparableGrowthDescent_iff_omegaPointPositive`
(`CRNT/Dynamics/SiphonDimensionDescent.lean:368-377`); cited, not re-proved.

The content of this lemma is *negative* and is the point of recording it: with criticality
and carriedness both supplied, **no conjunct of `IsCriticalSiphon Pmax` remains open**, so
the only missing hypothesis is the descent structure, which the cited tree theorem already
identifies with the conclusion.  This is a reduction of the hole, not a step toward
closing it. -/
theorem holeA_goal_iff_comparableGrowthDescent
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0) :
    N.ComparableGrowthDescent ϕ x₀ ↔ (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) := by
  obtain ⟨hcrit, hcarr⟩ := holeA_isCriticalSiphon_Pmax N κ hϕγ hK hmaps hωnn hgenω hωaff hx₀
    hPmaxne hwmax hzeroMax
  exact N.comparableGrowthDescent_iff_omegaPointPositive hcrit hcarr

/-- **The descent launch, spelled out with the hole's hypotheses substituted.**  This is
`omegaLimit_positive_of_boundary_point` with `Pmax`'s nonemptiness, carriedness and
criticality supplied by `holeA_isCriticalSiphon_Pmax`; the *only* remaining argument is
`N.ComparableGrowthDescent ϕ x₀`. -/
theorem holeA_boundary_launch
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    (hdesc : N.ComparableGrowthDescent ϕ x₀) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  obtain ⟨s₀, hs₀⟩ := hPmaxne
  exact N.omegaLimit_positive_of_boundary_point κ hϕγ hK hmaps hωnn hgenω hωaff hx₀ hdesc
    hwmax ((hzeroMax s₀).1 hs₀)

/-! ### Non-vacuity: a critical siphon of cardinality two -/

/-- **The two-step chain `A → B`, `C → D` on four species.**  Reaction `0` has source
`A` and target `B`; reaction `1` has source `C` and target `D`. -/
abbrev fin4chain : Network (Fin 4) where
  R := Fin 2
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r =>
    if r = 0 then
      { source := fun s => if s = 0 then 1 else 0
        target := fun s => if s = 1 then 1 else 0 }
    else
      { source := fun s => if s = 2 then 1 else 0
        target := fun s => if s = 3 then 1 else 0 }

@[simp] theorem fin4chain_target_0 (s : Fin 4) :
    (fin4chain.reaction 0).target s = if s = 1 then 1 else 0 := rfl

@[simp] theorem fin4chain_source_0 (s : Fin 4) :
    (fin4chain.reaction 0).source s = if s = 0 then 1 else 0 := rfl

@[simp] theorem fin4chain_target_1 (s : Fin 4) :
    (fin4chain.reaction 1).target s = if s = 3 then 1 else 0 := rfl

@[simp] theorem fin4chain_source_1 (s : Fin 4) :
    (fin4chain.reaction 1).source s = if s = 2 then 1 else 0 := rfl

/-- **The only species produced by reaction `0` is `B`.** -/
theorem fin4chain_product_0 (s : Fin 4) (h : (fin4chain.reaction 0).target s ≠ 0) : s = 1 := by
  fin_cases s <;> simp_all

/-- **The only species produced by reaction `1` is `D`.** -/
theorem fin4chain_product_1 (s : Fin 4) (h : (fin4chain.reaction 1).target s ≠ 0) : s = 3 := by
  fin_cases s <;> simp_all

/-- **`{A, C}` is a siphon of the chain: neither reaction produces a species of it.**
Reaction `0` produces only `B` and reaction `1` only `D`, both outside `{A, C}`, so the
implication defining `Network.IsSiphon` never fires. -/
theorem fin4chain_isSiphon_AC : fin4chain.IsSiphon ({0, 2} : Finset (Fin 4)) := by
  intro r ⟨s, hs, hp⟩
  have hs1 : s = 1 ∨ s = 3 := by
    rcases r with _ | _
    · exact Or.inl (fin4chain_product_0 s hp)
    · exact Or.inr (fin4chain_product_1 s hp)
  rcases hs1 with h | h <;> simp [h] at hs

/-- **`{A, C}` is critical, and has cardinality two** — a non-vacuity witness in exactly the
shape the hole's `hcard : 2 ≤ Pmax.card` demands.

The conservation clause is verified by hand.  If `v` were nonnegative, strictly positive
exactly on `{A, C}`, and orthogonal to every reaction vector, then `v B = 0` (off the
siphon, `v ≤ 0` and `v ≥ 0`), while orthogonality to `reactionVector 0 = (-1, 1, 0, 0)` reads
`- v A + v B = 0`, forcing `v A = 0` against `0 < v A`. -/
theorem fin4chain_isCriticalSiphon_AC :
    fin4chain.IsCriticalSiphon ({0, 2} : Finset (Fin 4)) :=
  ⟨⟨0, by simp⟩, fin4chain_isSiphon_AC, by
    rintro ⟨v, hvnn, hvsupp, hvcons⟩
    -- `B` lies off the siphon, so `v` vanishes there
    have hBoff : ¬ (1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by simp
    have hB : v 1 = 0 := le_antisymm (not_lt.mp fun hlt => hBoff ((hvsupp 1).mp hlt)) (hvnn 1)
    have hApos : 0 < v 0 := (hvsupp 0).mpr (by simp)
    -- orthogonality to `reactionVector 0` reads `v 0 * (-1) + v 1 * 1 = 0`
    have h0 := hvcons (0 : fin4chain.R)
    rw [Fin.sum_univ_four] at h0
    norm_num [Network.reactionVector, hB] at h0
    linarith⟩

/-- **The critical siphon of the chain has cardinality two**, matching `hcard`. -/
theorem fin4chain_card_AC : ({0, 2} : Finset (Fin 4)).card = 2 := by decide

end Network
end CRNT
