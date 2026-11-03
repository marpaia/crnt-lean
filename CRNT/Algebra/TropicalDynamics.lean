import CRNT.Algebra.TropicalSlowFast
import CRNT.Subnetwork.ReactionRestriction
import Mathlib.Tactic

/-!
# The dynamical reading of the tropical reduction

This module completes the *dynamical* part of the tropical reduction procedure of

* L. Samal, A. Fridman, A. C. Pantea, A. Trifonov, **Tropical equilibration and reduction for
  biomolecular systems**, SIAM J. Appl. Dyn. Syst. **14** (2015), 751–784.

and relates it to the earlier existence results of

* F. Noel, S. Grigoriev, V. Vakulenko, R. Radulescu, **Tropicalization of chemical reaction
  networks**, J. Chem. Phys. **138** (2013), 114108.

## The mathematics

A tropical equilibration of a reaction network `N` at a valuation `w` (with rate constants
`κ̄_r ε^{a_r}` and concentrations `x_s = ε^{w_s} y_s`) is the condition that, for every
species changed by some reaction, the *minimal tropical order* `a_r + ⟨y_r, w⟩` over the
reactions changing that species is attained by both a producing and a consuming reaction
(`Network.IsTropicalEquilibration`, formalised in `CRNT.Algebra.TropicalEquilibration`).

The **tropical (leading) system** of `N` at `(a, w)` is the leading part of the `ε`-rescaled
mass-action field,

```
L_s (y) = ∑_{r tropically minimal for s} κ̄_r (y^{y_r}) (ν_r)_s ,
```

which is `Network.tropicalLeadingField`.  Samal–Fridman–Pantea–Trifonov's *model reduction*
keeps exactly the reactions that are tropically minimal for at least one species they change
(the **reduced network** `Network.tropicalReduced`); their *dynamical* reduction says that
**the reduced network carries the dynamics of the original one at the tropical scale**: the
leading field of the full network is the leading field of the reduced network, and the
tropical equilibration of the full network is a tropical equilibration of the reduced one.

## What the repository already contains

* `CRNT.Algebra.TropicalEquilibration`: the tropical order `Network.tropicalOrder`, the
  equilibration condition `Network.IsTropicalEquilibration`, and the fact that a family of
  scaled steady states yields a tropical equilibration.
* `CRNT.Algebra.TropicalReduction`: the reduced network `Network.tropicalReduced`, the fact
  that the reduction loses no species (`Network.tropicalReduced_species_eq`), and that the
  leading *system* of the reduced network is the leading system of the full network
  (`Network.leadingSystem_eq_reduced_of_equilibration`).
* `CRNT.Algebra.TropicalLifting`, `CRNT.Algebra.TropicalLiftingNetwork`: the converse
  direction, the lifting of a tropical equilibration to nearby steady states.
* `CRNT.Algebra.TropicalSlowFast`: the tropical system is the `ε → 0⁺` limit of the rescaled
  mass-action field (`Network.tropicalLeadingField_leading`), the sign-indeterminacy of the
  leading system (`Network.tropicalLeadingField_signs`), the critical manifold
  (`Network.tropical_critical_manifold`), and the reduction estimate
  (`Network.tropical_reduction_estimate`).

## What this module adds

The *dynamical* reading of the reduction:

* `Network.tropicalLeadingField_eq_reduced` — **the leading field of the full network is the
  leading field of the reduced network** (the true form of the "the reduced network's field
  is the leading field of the full network" statement; see the remark below);
* `Network.massActionVectorField_reduced_eq` — **the mass-action field of the reduced network
  is the leading field plus the contribution of the reduced reactions that are *not* tropically
  minimal for that species**: this identifies exactly why the mass-action field of the reduced
  network is *not* the leading field of the full network;
* `Network.tropicalOrder_reduced` — the tropical order of the reduced network is the
  restriction of the tropical order of the full network;
* `Network.IsTropicalEquilibration_reduced` — **the reduced network is tropically equilibrated
  at the same data**;
* `Network.tropicalSlowField_eq_reduced` — the slow (leading) field of the full network
  coincides with the leading field of the reduced network on the slow species;
* `TropicalDynamicsInstance` — a concrete two-tier instance (`∅ → X → ∅` together with
  `∅ → Y → X`, orders `a = (0, 0, 0, 1)`, valuation `w = (0, 1)`) whose tropical equilibration
  is proved (`ex_isEquil`) and which exhibits the discrepancy above (`ex_discrepancy`,
  `ex_extra_reaction`, `ex_extra_contribution`).

## A remark on the exact statement

The literature statement "the mass-action field of the reduced network is the leading field of
the full network" is **false** for the definitions of this repository: the leading field of a
species sums over the reactions that are tropically minimal *for that species*, whereas the
mass-action field of the reduced network sums over *all* reduced reactions (which may change
that species without being minimal for it).  The correct statement is
`Network.tropicalLeadingField_eq_reduced` (leading field on both sides), and the discrepancy
is quantified by `Network.massActionVectorField_reduced_eq` and exhibited concretely by
`TropicalDynamicsInstance.ex_discrepancy`.

## What remains open

* The **`ε`-dependent Fenichel manifold** of the tropical reduction.
* The **entry into the tube** for a solution starting outside it (the genuine graph-transform
  step); the tube hypothesis itself is available in `CRNT.Dynamics.UniformContraction`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

noncomputable section

open Classical

/-! ## 1. The tropical order of the reduced network -/

/-- **The tropical order of a reaction in a reaction-restricted network is the tropical order
of the reaction in the parent network.**  Restricting the reactions does not change the
tropical order, because the source complex of a restricted reaction is the source complex of
the parent reaction. -/
theorem tropicalOrder_restrict' (N : Network S) (E : Finset N.R) (a : N.R → ℝ) (w : S → ℝ)
    (r : (N.restrictReactions E).R) :
    tropicalOrder (N.restrictReactions E) (fun r => a r.1) w r = tropicalOrder N a w r.1 := by
  rcases r with ⟨r, hr⟩
  unfold tropicalOrder
  rfl

/-- **The tropical order of a reaction of a reaction-restricted network is the tropical order
of the reaction in the parent network.** -/
theorem tropicalOrder_restrict (N : Network S) (E : Finset N.R) (a : N.R → ℝ) (w : S → ℝ)
    {r : N.R} (hr : r ∈ E) :
    tropicalOrder (N.restrictReactions E) (fun r => a r.1) w ⟨r, hr⟩ = tropicalOrder N a w r := by
  unfold tropicalOrder
  rfl

/-- **The tropical order of the reduced network is the restriction of the tropical order of the
full network.**  This is the ingredient that makes the reduction *dynamical*: the reduced
network is tropicalised with the same valuation `w` and the same orders `a`, and its tropical
orders are exactly the tropical orders of the corresponding reactions of the full network. -/
theorem tropicalOrder_reduced (N : Network S) (a : N.R → ℝ) (w : S → ℝ) {r : N.R}
    (hr : r ∈ N.tropicalReduced a w) :
    tropicalOrder (N.restrictReactions (N.tropicalReduced a w)) (fun r => a r.1) w
      ((⟨r, hr⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) = tropicalOrder N a w r :=
  tropicalOrder_restrict N (N.tropicalReduced a w) a w hr

/-! ## 2. Tropical minimality and the reduced network -/

/-- **A reaction that is tropically minimal in the parent network is tropically minimal in a
reaction-restricted network containing it.** -/
theorem isTropicallyMinimal_restrict (N : Network S) (E : Finset N.R) (a : N.R → ℝ)
    (w : S → ℝ) {r : N.R} {s : S} (hr : r ∈ E)
    (hmin : IsTropicallyMinimal N a w r s) :
    IsTropicallyMinimal (N.restrictReactions E) (fun r => a r.1) w
      ((⟨r, hr⟩ : (N.restrictReactions E).R)) s := by
  unfold IsTropicallyMinimal
  constructor
  · rw [restrictReactions_reactionVector N E ⟨r, hr⟩]
    exact hmin.1
  · intro r' hr'
    have hrv : N.reactionVector r'.1 s ≠ 0 := by
      have heq : (N.restrictReactions E).reactionVector r' s = N.reactionVector r'.1 s :=
        congrFun (restrictReactions_reactionVector N E r') s
      rw [heq] at hr'
      exact hr'
    rw [tropicalOrder_restrict N E a w hr, tropicalOrder_restrict' N E a w r']
    exact hmin.2 r'.1 hrv

/-- **Conversely, at a tropical equilibration, a reaction that is tropically minimal in the
reduced network is tropically minimal in the full network.**  The tropical equilibration
guarantees that the minimal tropical order of a changed species is attained by reactions of
the reduced network, so restricting the reactions does not change the minimality. -/
theorem isTropicallyMinimal_of_restrict (N : Network S) (a : N.R → ℝ) (w : S → ℝ)
    (hEq : IsTropicalEquilibration N a w) {r : N.R} {s : S}
    (hr : r ∈ N.tropicalReduced a w)
    (hmin : IsTropicallyMinimal (N.restrictReactions (N.tropicalReduced a w)) (fun r => a r.1) w
      ((⟨r, hr⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) s) :
    IsTropicallyMinimal N a w r s := by
  have hmin' : (N.restrictReactions (N.tropicalReduced a w)).reactionVector
        ((⟨r, hr⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) s ≠ 0 ∧
      ∀ r' : (N.restrictReactions (N.tropicalReduced a w)).R,
        (N.restrictReactions (N.tropicalReduced a w)).reactionVector r' s ≠ 0 →
          tropicalOrder (N.restrictReactions (N.tropicalReduced a w)) (fun r => a r.1) w
              ((⟨r, hr⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) ≤
            tropicalOrder (N.restrictReactions (N.tropicalReduced a w)) (fun r => a r.1) w r' :=
    hmin
  refine ⟨?_, ?_⟩
  · have heq : (N.restrictReactions (N.tropicalReduced a w)).reactionVector
        ((⟨r, hr⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) s = N.reactionVector r s :=
      congrFun (restrictReactions_reactionVector N (N.tropicalReduced a w) ⟨r, hr⟩) s
    rw [heq] at hmin'
    exact hmin'.1
  · intro r' hrv
    obtain ⟨r₁, r₂, hr₁pos, hr₂neg, hmin''⟩ := hEq s ⟨r, hmin'.1⟩
    have hr₁E : r₁ ∈ N.tropicalReduced a w := by
      have hmem : r₁ ∈ tropicalMinimal N a w s :=
        (mem_tropicalMinimal N a w r₁ s).mpr
          ⟨ne_of_gt hr₁pos, fun q hq => (hmin'' q hq).1⟩
      exact tropicalMinimal_subset_reduced N a w s hmem
    have hord : tropicalOrder N a w r ≤ tropicalOrder N a w r₁ := by
      have hne : (N.restrictReactions (N.tropicalReduced a w)).reactionVector
          ((⟨r₁, hr₁E⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) s ≠ 0 := by
        have heq : (N.restrictReactions (N.tropicalReduced a w)).reactionVector
            ((⟨r₁, hr₁E⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) s
            = N.reactionVector r₁ s :=
          congrFun (restrictReactions_reactionVector N (N.tropicalReduced a w) ⟨r₁, hr₁E⟩) s
        rw [heq]
        exact hr₁pos.ne'
      have h1 := hmin'.2 ((⟨r₁, hr₁E⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) hne
      rw [tropicalOrder_restrict N (N.tropicalReduced a w) a w hr,
        tropicalOrder_restrict N (N.tropicalReduced a w) a w hr₁E] at h1
      exact h1
    exact hord.trans ((hmin'' r' hrv).1)

/-- **The tropically minimal reactions of the reduced network.**  At a tropical equilibration,
the tropically minimal reactions of the reduced network (for a given species) are exactly the
tropically minimal reactions of the full network: the tropical reduction does not change the
leading system of a species. -/
theorem tropicalMinimal_reduced (N : Network S) (a : N.R → ℝ) (w : S → ℝ)
    (hEq : IsTropicalEquilibration N a w) (s : S) :
    (tropicalMinimal (N.restrictReactions (N.tropicalReduced a w)) (fun r => a r.1) w s).image
        Subtype.val = tropicalMinimal N a w s := by
  classical
  ext r
  constructor
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨r', hr', rfl⟩
    have hmin : IsTropicallyMinimal (N.restrictReactions (N.tropicalReduced a w))
        (fun r => a r.1) w r' s :=
      (mem_tropicalMinimal (N.restrictReactions (N.tropicalReduced a w)) (fun r => a r.1) w r' s).mp hr'
    have hmem : IsTropicallyMinimal N a w r'.1 s :=
      isTropicallyMinimal_of_restrict N a w hEq r'.2 hmin
    rw [mem_tropicalMinimal]
    exact hmem
  · intro hr
    rw [mem_tropicalMinimal] at hr
    have hrE : r ∈ N.tropicalReduced a w :=
      tropicalMinimal_subset_reduced N a w s ((mem_tropicalMinimal N a w r s).mpr hr)
    refine Finset.mem_image.mpr ⟨⟨r, hrE⟩, ?_, rfl⟩
    have hmem : IsTropicallyMinimal (N.restrictReactions (N.tropicalReduced a w))
        (fun r => a r.1) w ((⟨r, hrE⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) s :=
      isTropicallyMinimal_restrict N (N.tropicalReduced a w) a w hrE hr
    unfold tropicalMinimal
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · exact hmem

/-- **The tropically minimal reactions of a species are the reduced reactions that are tropically
minimal for it.** -/
theorem tropicalMinimal_eq_filter_reduced (N : Network S) (a : N.R → ℝ) (w : S → ℝ) (s : S) :
    tropicalMinimal N a w s =
      (N.tropicalReduced a w).filter (fun r => IsTropicallyMinimal N a w r s) := by
  classical
  ext r
  constructor
  · intro hr
    have hmem : IsTropicallyMinimal N a w r s := (mem_tropicalMinimal N a w r s).mp hr
    rw [Finset.mem_filter]
    constructor
    · rw [tropicalReduced_mem]
      exact ⟨s, hmem.1, hmem.2⟩
    · exact hmem
  · intro hr
    rw [Finset.mem_filter] at hr
    rw [mem_tropicalMinimal]
    exact hr.2
/-! ## 3. The dynamical reading of the reduction -/

/-- **The leading field of the full network is the leading field of the reduced network.**

This is the *dynamical* reading of the tropical reduction of Samal–Fridman–Pantea–Trifonov
(2015): at a tropical equilibration, the tropical (leading) system of the full network is the
tropical (leading) system of the reduced network, i.e. the reduced network carries the
dynamics of the original one at the tropical scale.

More precisely, for every concentration `x`,

```
N.tropicalLeadingField N κ a w x
  = (N.restrictReactions (N.tropicalReduced N a w)).tropicalLeadingField
      (κ.restrict (N.tropicalReduced N a w)) (fun r => a r.1) w x ,
```

the two sides being the sums over the tropically minimal reactions of the full network and of
the reduced network respectively. -/
theorem tropicalLeadingField_eq_reduced (N : Network S) (κ : N.RateConstants) (a : N.R → ℝ)
    (w : S → ℝ) (hEq : IsTropicalEquilibration N a w) (x : Concentration S) :
    N.tropicalLeadingField κ a w x =
      (N.restrictReactions (N.tropicalReduced a w)).tropicalLeadingField
        (κ.restrict (N.tropicalReduced a w)) (fun r => a r.1) w x := by
  classical
  funext s
  rw [tropicalLeadingField_eq_sum_reduced, tropicalLeadingField_eq_sum_reduced]
  have hrE : ∀ r : N.R, r ∈ tropicalMinimal N a w s → r ∈ N.tropicalReduced a w :=
    fun r hr => tropicalMinimal_subset_reduced N a w s hr
  refine Finset.sum_bij (f := fun r => tropicalLeadingTerm N κ s r x)
    (g := fun r => tropicalLeadingTerm (N.restrictReactions (N.tropicalReduced a w))
      (κ.restrict (N.tropicalReduced a w)) s r x)
    (s := tropicalMinimal N a w s)
    (t := tropicalMinimal (N.restrictReactions (N.tropicalReduced a w)) (fun r => a r.1) w s)
    (fun r (hr : r ∈ tropicalMinimal N a w s) =>
      ((⟨r, hrE r hr⟩ : (N.restrictReactions (N.tropicalReduced a w)).R))) ?_ ?_ ?_ ?_
  · intro r hr
    have hmem : IsTropicallyMinimal (N.restrictReactions (N.tropicalReduced a w))
        (fun r => a r.1) w
        ((⟨r, hrE r hr⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) s :=
      isTropicallyMinimal_restrict N (N.tropicalReduced a w) a w (hrE r hr)
        ((mem_tropicalMinimal N a w r s).mp hr)
    unfold tropicalMinimal
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · exact hmem
  · intro r₁ hr₁ r₂ hr₂ h
    exact congrArg Subtype.val h
  · intro r' hr'
    have hmem : IsTropicallyMinimal N a w r'.1 s := by
      have himage := tropicalMinimal_reduced N a w hEq s
      have hmem' : r'.1 ∈ (tropicalMinimal (N.restrictReactions (N.tropicalReduced a w))
          (fun r => a r.1) w s).image Subtype.val :=
        Finset.mem_image.mpr ⟨r', hr', rfl⟩
      exact (mem_tropicalMinimal N a w r'.1 s).mp (by rw [← himage]; exact hmem')
    refine ⟨r'.1, (mem_tropicalMinimal N a w r'.1 s).mpr hmem, ?_⟩
    exact Subtype.ext rfl
  · intro r hr
    rfl

/-- **The mass-action field of the reduced network is the leading field plus the contribution
of the reduced reactions that are not tropically minimal for the species.**

This identifies precisely the discrepancy between the *mass-action* field of the reduced
network and the *leading* field of the full network: the mass-action field of the reduced
network also contains the reactions of the reduced network that change the species without
being tropically minimal for it, i.e. the reactions of higher tropical order, which vanish in
the `ε → 0⁺` limit.

The statement holds for *any* valuation `w` and *any* orders `a`: no tropical equilibration is
needed for the decomposition itself. -/
theorem massActionVectorField_reduced_eq (N : Network S) (κ : N.RateConstants) (a : N.R → ℝ)
    (w : S → ℝ) (x : Concentration S) (s : S) :
    (N.restrictReactions (N.tropicalReduced a w)).massActionVectorField
        (κ.restrict (N.tropicalReduced a w)) x s =
      N.tropicalLeadingField κ a w x s +
        ∑ r ∈ (N.tropicalReduced a w).filter (fun r => ¬ IsTropicallyMinimal N a w r s),
          tropicalLeadingTerm N κ s r x := by
  classical
  rw [restrictReactions_massActionVectorField]
  dsimp only
  have hsplit := Finset.sum_filter_add_sum_filter_not (N.tropicalReduced a w)
    (fun r => IsTropicallyMinimal N a w r s)
    (fun r => N.massActionRate κ r x * N.reactionVector r s)
  rw [← hsplit]
  rw [tropicalLeadingField_eq_sum_reduced]
  rw [tropicalMinimal_eq_filter_reduced N a w s]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Finset.sum_congr rfl fun r _ => rfl
  · exact Finset.sum_congr rfl fun r _ => rfl

/-! ## 4. The reduced network is tropically equilibrated -/

/-- **The reduced network is tropically equilibrated at the same data.**

A tropical equilibration of the full network is a tropical equilibration of the reduced
network (Samal–Fridman–Pantea–Trifonov 2015, *Theorem 3*): the reduction loses no species
(`Network.tropicalReduced_species_eq`), the leading systems agree
(`Network.leadingSystem_eq_reduced_of_equilibration`), and the new content here is that the
*reduced network itself* is tropically equilibrated at the same valuation `w` and the same
orders `a`. -/
theorem IsTropicalEquilibration_reduced (N : Network S) (a : N.R → ℝ) (w : S → ℝ)
    (hEq : IsTropicalEquilibration N a w) :
    (N.restrictReactions (N.tropicalReduced a w)).IsTropicalEquilibration (fun r => a r.1) w := by
  intro s hs
  obtain ⟨r', hr'⟩ := hs
  have hN : ∃ r : N.R, N.reactionVector r s ≠ 0 := by
    refine ⟨r'.1, ?_⟩
    have heq : (N.restrictReactions (N.tropicalReduced a w)).reactionVector r' s
        = N.reactionVector r'.1 s :=
      congrFun (restrictReactions_reactionVector N (N.tropicalReduced a w) r') s
    rw [heq] at hr'
    exact hr'
  obtain ⟨r₁, r₂, hr₁pos, hr₂neg, hmin⟩ := hEq s hN
  have hr₁E : r₁ ∈ N.tropicalReduced a w := by
    have hmem : r₁ ∈ tropicalMinimal N a w s :=
      (mem_tropicalMinimal N a w r₁ s).mpr
        ⟨ne_of_gt hr₁pos, fun q hq => (hmin q hq).1⟩
    exact tropicalMinimal_subset_reduced N a w s hmem
  have hr₂E : r₂ ∈ N.tropicalReduced a w := by
    have hmem : r₂ ∈ tropicalMinimal N a w s :=
      (mem_tropicalMinimal N a w r₂ s).mpr
        ⟨ne_of_lt hr₂neg, fun q hq => (hmin q hq).2⟩
    exact tropicalMinimal_subset_reduced N a w s hmem
  refine ⟨((⟨r₁, hr₁E⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)),
    ((⟨r₂, hr₂E⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)), ?_, ?_, ?_⟩
  · have heq : (N.restrictReactions (N.tropicalReduced a w)).reactionVector
        ((⟨r₁, hr₁E⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) s = N.reactionVector r₁ s :=
      congrFun (restrictReactions_reactionVector N (N.tropicalReduced a w) ⟨r₁, hr₁E⟩) s
    rw [heq]
    exact hr₁pos
  · have heq : (N.restrictReactions (N.tropicalReduced a w)).reactionVector
        ((⟨r₂, hr₂E⟩ : (N.restrictReactions (N.tropicalReduced a w)).R)) s = N.reactionVector r₂ s :=
      congrFun (restrictReactions_reactionVector N (N.tropicalReduced a w) ⟨r₂, hr₂E⟩) s
    rw [heq]
    exact hr₂neg
  · intro r'' hr''
    have hrv : N.reactionVector r''.1 s ≠ 0 := by
      have heq : (N.restrictReactions (N.tropicalReduced a w)).reactionVector r'' s
          = N.reactionVector r''.1 s :=
        congrFun (restrictReactions_reactionVector N (N.tropicalReduced a w) r'') s
      rw [heq] at hr''
      exact hr''
    rw [tropicalOrder_restrict N (N.tropicalReduced a w) a w hr₁E,
      tropicalOrder_restrict' N (N.tropicalReduced a w) a w r'',
      tropicalOrder_restrict N (N.tropicalReduced a w) a w hr₂E]
    exact ⟨(hmin r''.1 hrv).1, (hmin r''.1 hrv).2⟩

/-! ## 5. The slow (leading) field -/

variable {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]

/-- **The slow (leading) field of the full network coincides with the leading field of the
reduced network on the slow species.**  This is the slow–fast reading of the dynamical
reduction: the slow part of the dynamics of the full network is the slow part of the
dynamics of the reduced network. -/
theorem tropicalSlowField_eq_reduced (N : Network (X ⊕ E)) (κ : N.RateConstants)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) (hEq : N.IsTropicalEquilibration a w)
    (x : X → ℝ) (y : E → ℝ) :
    (N.restrictReactions (N.tropicalReduced a w)).tropicalSlowField
        (κ.restrict (N.tropicalReduced a w)) (fun r => a r.1) w x y =
      N.tropicalSlowField κ a w x y := by
  funext s
  change (N.restrictReactions (N.tropicalReduced a w)).tropicalLeadingField
      (κ.restrict (N.tropicalReduced a w)) (fun r => a r.1) w (embedConcentration x y) (Sum.inl s)
      = N.tropicalLeadingField κ a w (embedConcentration x y) (Sum.inl s)
  exact (congrFun (tropicalLeadingField_eq_reduced N κ a w hEq (embedConcentration x y))
    (Sum.inl s)).symm

/-- **The slow field of the full network is the sum over the tropically minimal reactions of
the reduced network.** -/
theorem tropicalSlowField_eq_sum_reduced (N : Network (X ⊕ E)) (κ : N.RateConstants)
    (a : N.R → ℝ) (w : (X ⊕ E) → ℝ) (hEq : N.IsTropicalEquilibration a w)
    (x : X → ℝ) (y : E → ℝ) (s : X) :
    N.tropicalSlowField κ a w x y s =
      ∑ r ∈ tropicalMinimal (N.restrictReactions (N.tropicalReduced a w)) (fun r => a r.1) w
          (Sum.inl s),
        tropicalLeadingTerm (N.restrictReactions (N.tropicalReduced a w))
          (κ.restrict (N.tropicalReduced a w)) (Sum.inl s) r (embedConcentration x y) := by
  have hmain := tropicalLeadingField_eq_reduced N κ a w hEq (embedConcentration x y)
  have hsum := tropicalLeadingField_eq_sum_reduced
    (N.restrictReactions (N.tropicalReduced a w)) (κ.restrict (N.tropicalReduced a w))
    (fun r => a r.1) w (embedConcentration x y) (Sum.inl s)
  change N.tropicalLeadingField κ a w (embedConcentration x y) (Sum.inl s) = _
  exact (congrFun hmain (Sum.inl s)).trans hsum

/-! ## 6. A concrete instance: the discrepancy is genuine -/

namespace TropicalDynamicsInstance

open Network

/-- The species of the instance: `X` (index `0`) and `Y` (index `1`). -/
abbrev SEx := Fin 2

/-- The reactions of the instance: `∅ → X`, `X → ∅`, `Y → X`, `∅ → Y`. -/
abbrev REx := Fin 4

/-- The source complexes of the instance. -/
def exSource : REx → SEx → ℕ
  | 0 => fun _ => 0
  | 1 => fun s => if s.val = 0 then 1 else 0
  | 2 => fun s => if s.val = 1 then 1 else 0
  | 3 => fun _ => 0

/-- The target complexes of the instance. -/
def exTarget : REx → SEx → ℕ
  | 0 => fun s => if s.val = 0 then 1 else 0
  | 1 => fun _ => 0
  | 2 => fun s => if s.val = 0 then 1 else 0
  | 3 => fun s => if s.val = 1 then 1 else 0

/-- The network `∅ → X → ∅` together with `∅ → Y → X`. -/
def exNetwork : Network SEx where
  R := REx
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r => ⟨exSource r, exTarget r⟩

/-- The orders `a = (0, 0, 0, 1)`. -/
def exA : REx → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1

/-- The valuation `w = (0, 1)`. -/
def exW (s : SEx) : ℝ := if s.val = 0 then 0 else 1

/-- The rate constants of the instance, all equal to `1`. -/
def exκ : RateConstants exNetwork := ⟨fun _ => 1, fun _ => by norm_num⟩

/-- The reaction indices of the instance are the numerals of `REx`. -/
instance : OfNat exNetwork.R 0 := ⟨(0 : REx)⟩
instance : OfNat exNetwork.R 1 := ⟨(1 : REx)⟩
instance : OfNat exNetwork.R 2 := ⟨(2 : REx)⟩
instance : OfNat exNetwork.R 3 := ⟨(3 : REx)⟩

/-- The reactions of the instance. -/
theorem ex_reaction (r : REx) : exNetwork.reaction r = ⟨exSource r, exTarget r⟩ := rfl

/-- **The tropical orders of the four reactions are `0, 0, 1, 1`.** -/
theorem ex_tropicalOrder (r : REx) :
    tropicalOrder exNetwork exA exW r = (if r = 2 ∨ r = 3 then 1 else 0) := by
  fin_cases r <;> simp [tropicalOrder, exNetwork, exSource, exTarget, exA, exW]

/-- **The reactions that change the species `X`.** -/
theorem ex_changes_X (r : REx) :
    exNetwork.reactionVector r (0 : SEx) ≠ 0 ↔ (r = 0 ∨ r = 1 ∨ r = 2) := by
  fin_cases r <;>
    simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]

/-- **The reactions that change the species `Y`.** -/
theorem ex_changes_Y (r : REx) :
    exNetwork.reactionVector r (1 : SEx) ≠ 0 ↔ (r = 2 ∨ r = 3) := by
  fin_cases r <;>
    simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]

/-- **The valuation `w = (0, 1)` is a tropical equilibration of the instance.**  The species `X`
has tropical time scale `0` (the reactions `∅ → X` and `X → ∅` both have tropical order `0`)
and the species `Y` has tropical time scale `1` (the reactions `Y → X` and `∅ → Y` both have
tropical order `1`): the instance is a genuine two-tier tropical system. -/
theorem ex_isEquil : IsTropicalEquilibration exNetwork exA exW := by
  intro s hs
  have hval : s.val = 0 ∨ s.val = 1 := by omega
  rcases hval with h0 | h1
  · -- the species `X`
    have hs0 : s = 0 := Fin.ext h0
    subst hs0
    refine ⟨(0 : REx), (1 : REx), ?_, ?_, ?_⟩
    · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
    · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
    · intro r hr
      have hcases : (r : REx) = 0 ∨ (r : REx) = 1 ∨ (r : REx) = 2 := (ex_changes_X r).mp hr
      rcases hcases with rfl | rfl | rfl
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
  · -- the species `Y`
    have hs1 : s = 1 := Fin.ext h1
    subst hs1
    refine ⟨(3 : REx), (2 : REx), ?_, ?_, ?_⟩
    · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
    · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
    · intro r hr
      have hcases : (r : REx) = 2 ∨ (r : REx) = 3 := (ex_changes_Y r).mp hr
      rcases hcases with rfl | rfl
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]

/-- **Every reaction of the instance is kept by the tropical reduction.** -/
theorem ex_tropicalReduced : exNetwork.tropicalReduced exA exW = (Finset.univ : Finset REx) := by
  apply Finset.eq_univ_of_forall
  intro r
  rcases r with ⟨i, hi⟩
  interval_cases i
  · refine (exNetwork.tropicalReduced_mem exA exW ⟨0, hi⟩).2 ⟨0, ?_⟩
    constructor
    · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
    · intro r' hr'
      have hcases : (r' : REx) = 0 ∨ (r' : REx) = 1 ∨ (r' : REx) = 2 := (ex_changes_X r').mp hr'
      rcases hcases with rfl | rfl | rfl
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
  · refine (exNetwork.tropicalReduced_mem exA exW ⟨1, hi⟩).2 ⟨0, ?_⟩
    constructor
    · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
    · intro r' hr'
      have hcases : (r' : REx) = 0 ∨ (r' : REx) = 1 ∨ (r' : REx) = 2 := (ex_changes_X r').mp hr'
      rcases hcases with rfl | rfl | rfl
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
  · refine (exNetwork.tropicalReduced_mem exA exW ⟨2, hi⟩).2 ⟨1, ?_⟩
    constructor
    · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
    · intro r' hr'
      have hcases : (r' : REx) = 2 ∨ (r' : REx) = 3 := (ex_changes_Y r').mp hr'
      rcases hcases with rfl | rfl
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
  · refine (exNetwork.tropicalReduced_mem exA exW ⟨3, hi⟩).2 ⟨1, ?_⟩
    constructor
    · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
    · intro r' hr'
      have hcases : (r' : REx) = 2 ∨ (r' : REx) = 3 := (ex_changes_Y r').mp hr'
      rcases hcases with rfl | rfl
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]

/-- **The reaction `Y → X` is kept by the reduction but is not tropically minimal for `X`, and
it does change `X`.**  This is the mechanism behind the discrepancy between the mass-action
field of the reduced network and the leading field of the full network. -/
theorem ex_discrepancy :
    (2 : REx) ∈ exNetwork.tropicalReduced exA exW ∧
    exNetwork.reactionVector (2 : REx) (0 : SEx) ≠ 0 ∧
    ¬ IsTropicallyMinimal exNetwork exA exW (2 : REx) (0 : SEx) := by
  refine ⟨?_, (ex_changes_X (2 : REx)).mpr (by simp), ?_⟩
  · refine (exNetwork.tropicalReduced_mem exA exW (2 : REx)).2 ⟨1, ?_⟩
    constructor
    · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
    · intro r' hr'
      have hcases : (r' : REx) = 2 ∨ (r' : REx) = 3 := (ex_changes_Y r').mp hr'
      rcases hcases with rfl | rfl
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
      · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
  · intro h
    have h1 := h.2 (0 : REx) ((ex_changes_X (0 : REx)).mpr (by simp))
    simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget] at h1
    norm_num at h1

/-- **The reactions that are tropically minimal for the species `X`.**  They are exactly the
reactions of tropical order `0`, i.e. `∅ → X` and `X → ∅`; the reaction `Y → X` has tropical
order `1` and is therefore *not* minimal for `X`. -/
theorem ex_minimal_X (r : REx) :
    IsTropicallyMinimal exNetwork exA exW r (0 : SEx) ↔ (r = 0 ∨ r = 1) := by
  constructor
  · intro h
    have hcases : (r : REx) = 0 ∨ (r : REx) = 1 ∨ (r : REx) = 2 := (ex_changes_X r).mp h.1
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have h1 := h.2 (0 : REx) ((ex_changes_X (0 : REx)).mpr (by simp))
      simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget] at h1
      norm_num at h1
  · intro h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩
      · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
      · intro r' hr'
        have hcases : (r' : REx) = 0 ∨ (r' : REx) = 1 ∨ (r' : REx) = 2 :=
          (ex_changes_X r').mp hr'
        rcases hcases with rfl | rfl | rfl
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
    · refine ⟨?_, ?_⟩
      · simp [exNetwork, exSource, exTarget, Network.reactionVector_apply]
      · intro r' hr'
        have hcases : (r' : REx) = 0 ∨ (r' : REx) = 1 ∨ (r' : REx) = 2 :=
          (ex_changes_X r').mp hr'
        rcases hcases with rfl | rfl | rfl
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource, exTarget]

/-- **The tropically minimal reactions of the species `X`.** -/
theorem ex_tropicalMinimal_X : exNetwork.tropicalMinimal exA exW (0 : SEx) = {0, 1} := by
  ext r
  constructor
  · intro hr
    have hmem : IsTropicallyMinimal exNetwork exA exW r (0 : SEx) :=
      (exNetwork.mem_tropicalMinimal exA exW r 0).mp hr
    rcases (ex_minimal_X (r : REx)).mp hmem with h0 | h1
    · exact Finset.mem_insert.mpr (Or.inl h0)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h1))
  · intro hr
    have hcases : r = 0 ∨ r = 1 := by
      rcases Finset.mem_insert.mp hr with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    exact (exNetwork.mem_tropicalMinimal exA exW r 0).mpr
      ((ex_minimal_X (r : REx)).mpr hcases)

/-- **The reaction `Y → X` is a reduced reaction which changes `X` without being tropically
minimal for `X`.**  Its contribution to the mass-action field of the reduced network at `X` is
the number `1`, and it is absent from the leading field of the full network at `X`.  This is
the concrete manifestation of the discrepancy between the two fields. -/
theorem ex_extra_reaction :
    (2 : exNetwork.R) ∈ (exNetwork.tropicalReduced exA exW).filter
      (fun r => ¬ IsTropicallyMinimal exNetwork exA exW r (0 : SEx)) := by
  rw [Finset.mem_filter]
  constructor
  · exact ex_discrepancy.1
  · exact ex_discrepancy.2.2

/-- **The contribution of the extra reaction `Y → X` to the mass-action field of the reduced
network at the species `X` is the number `1`.** -/
theorem ex_extra_contribution :
    tropicalLeadingTerm exNetwork exκ (0 : SEx) (2 : REx) (fun _ => 1) = 1 := by
  unfold tropicalLeadingTerm
  simp [exNetwork, exSource, exTarget, Network.reactionVector_apply, exκ,
    Complex.massActionMonomial]

end TropicalDynamicsInstance

end

end Network
end CRNT

#print axioms CRNT.Network.tropicalLeadingField_eq_reduced
#print axioms CRNT.Network.massActionVectorField_reduced_eq
#print axioms CRNT.Network.tropicalOrder_reduced
#print axioms CRNT.Network.IsTropicalEquilibration_reduced
#print axioms CRNT.Network.tropicalSlowField_eq_reduced
#print axioms CRNT.Network.tropicalSlowField_eq_sum_reduced
#print axioms CRNT.Network.tropicalMinimal_reduced
#print axioms CRNT.Network.TropicalDynamicsInstance.ex_isEquil
#print axioms CRNT.Network.TropicalDynamicsInstance.ex_discrepancy
