import CRNT.Multistationarity.TrueChemistrySRCriterion
import CRNT.Open.Augmentation

/-!
# A witness for Hole B's `hsep` / `hflow` hypotheses

`stronglyConcordant_fullyOpen_of_trueSRCriterion` (`TrueChemistrySRCriterion.lean`,
residual `sorry`) assumes

* `hsep  : N.ReactantProductSeparated`,
* `hflow : N.ZeroComplexReactionsAreFlows`,
* `hSR   : N.TrueSRStrongCriterion`.

`adv-vacuity` (PR #16, `research/routes/vacuity-report.md` §R4; `research/DEAD-ENDS.md`
**B-26**) claimed that no network in the tree satisfies all three.  This module builds a
network satisfying the first two **non-vacuously**, and records precisely what it does and
does not establish about the third.

## The network

`cycle3Net` is the directed three-cycle `A → B → C → A` over `S = Fin 3` (species `0 = A`,
`1 = B`, `2 = C`), with reaction channels

| index | reaction     |
|-------|--------------|
| `0`   | `A → B`      |
| `1`   | `B → C`      |
| `2`   | `C → A`      |
| `3`   | `0 → A` (`inflowReaction 0`) |

Channel `3` exists solely to make `hflow` **non-vacuously** true: it is the only flow channel,
and it is literally `inflowReaction 0`, which is what `ZeroComplexReactionsAreFlows` demands.
(Without it, `ZeroComplexReactionsAreFlows` would hold vacuously, exactly as it does for
`netN` of `Examples/TrueSRNetCoeffCounterexample.lean`.)

## What is established here

* **`hsep`** — `cycle3Net_reactantProductSeparated`: no species occurs on both sides of any
  reaction.  Non-vacuous: `cycle3Net_sep_witness`.
* **`hflow`** — `cycle3Net_zeroComplexReactionsAreFlows`, together with
  `cycle3Net_not_flow` (channels `0`, `1`, `2` are not flow channels) and
  `cycle3Net_has_flow_channel` (so `hflow` is not vacuously true).
* **Hazard D2 (identity reactions), in both parts**, machine-checked:
  * `cycle3Net_no_identity_reaction`: the witness itself contains no identity reaction;
  * `identity_reaction_is_flowChannel_of_separated`: **in general**, under
    `ReactantProductSeparated` an identity reaction has the zero complex as *both* endpoints,
    and is therefore a flow channel;
  * `identity_reaction_excluded_of_bundle`: combined with `hflow`, no identity reaction can
    be nontrivial.  So the hazard D2 poses is closed for every network satisfying Hole B's
    `hsep` + `hflow` bundle.

## What is NOT established here — and why

The docstring of the earlier draft of this file also claimed `hSR`
(`TrueSRStrongCriterion`) and a theorem `cycle3Net_no_sToRIntersection`.  **Neither was ever
proved**: the draft ended in an unfinished `cycle_length_three` containing a literal `sorry`,
and `hSR` / `cycle3Net_no_sToRIntersection` do not appear anywhere in it.  Those claims have
been removed from this docstring rather than restated, because they are not discharged.

The gap is real and substantial.  Discharging `hSR` needs:

1. a classification of the true-SR edges of `cycle3Net` as the six hexagon edges
   `a —ρ_a— cycNext a`;
2. `every cycle has length exactly three` (`cycle_length_three`: a `TrueSRCycle n` injects
   `Fin n` into `Fin 3`, so `n ≤ 3`, and `n = 2` must be excluded — that exclusion needs the
   edge classification plus the fact that a degree-2 reaction vertex in the hexagon cannot
   exist);
3. `cycle3Net_no_sToRIntersection`: two cycles of `cycle3Net` share all six hexagon edges, so
   `covers_common` places all six into listed components, `components_separated` forces them
   into one component (consecutive hexagon edges share a vertex), and that component is a
   vertex-injective alternating path with six edges and hence seven vertices — impossible in
   `Fin 3`.

None of this is written.  In particular **B-26 is not refuted by this module**: the network
built here satisfies `hsep` and `hflow`, and whether it satisfies `hSR` remains open.

## A further restriction discovered here

`identity_reaction_is_flowChannel_of_separated` shows that under `ReactantProductSeparated`
every identity reaction is a flow channel.  Since `ZeroComplexReactionsAreFlows` forces every
flow channel to be a canonical `inflowReaction`/`outflowReaction`, any network satisfying
`hsep` + `hflow` has **no identity reaction at all** (whenever `S` is non-empty).  That is
recorded machine-checked by `identity_reaction_excluded_of_bundle`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### Primitive helpers -/

/-- A singleton complex is never the zero complex. -/
@[simp] theorem singleton_ne_zero {S : Type} [DecidableEq S] [Fintype S] (a : S) :
    ¬ (singletonComplex a = Complex.zero) := by
  intro h
  have h1 := congrFun h a
  simp only [singletonComplex, Pi.single_apply, Complex.zero_apply] at h1
  exact absurd h1 (by decide)

/-- An inflow channel is not an identity reaction. -/
theorem inflowReaction_source_ne_target (s : S) :
    (inflowReaction s).source ≠ (inflowReaction s).target := by
  intro h
  have h1 := congrFun h s
  simp only [inflowReaction, Complex.zero_apply, singletonComplex, Pi.single_apply] at h1
  exact absurd h1 (by decide)

/-- An outflow channel is not an identity reaction. -/
theorem outflowReaction_source_ne_target (s : S) :
    (outflowReaction s).source ≠ (outflowReaction s).target := by
  intro h
  have h1 := congrFun h s
  simp only [outflowReaction, Complex.zero_apply, singletonComplex, Pi.single_apply] at h1
  exact absurd h1 (by decide)

/-! ## The network

`abbrev`, not `def`: `cycle3Net.R` must reduce for typeclass synthesis of the `Fin 4`
numerals. -/
abbrev cycle3Net : Network (Fin 3) where
  R := Fin 4
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r =>
    if r = 0 then
      { source := singletonComplex (0 : Fin 3), target := singletonComplex (1 : Fin 3) }
    else if r = 1 then
      { source := singletonComplex (1 : Fin 3), target := singletonComplex (2 : Fin 3) }
    else if r = 2 then
      { source := singletonComplex (2 : Fin 3), target := singletonComplex (0 : Fin 3) }
    else inflowReaction (0 : Fin 3)

@[simp] theorem cycle3Net_r0_s0 : (cycle3Net.reaction (0:Fin 4)).source 0 = 1 := rfl
@[simp] theorem cycle3Net_r0_s1 : (cycle3Net.reaction (0:Fin 4)).source 1 = 0 := rfl
@[simp] theorem cycle3Net_r0_s2 : (cycle3Net.reaction (0:Fin 4)).source 2 = 0 := rfl
@[simp] theorem cycle3Net_r0_t0 : (cycle3Net.reaction (0:Fin 4)).target 0 = 0 := rfl
@[simp] theorem cycle3Net_r0_t1 : (cycle3Net.reaction (0:Fin 4)).target 1 = 1 := rfl
@[simp] theorem cycle3Net_r0_t2 : (cycle3Net.reaction (0:Fin 4)).target 2 = 0 := rfl
@[simp] theorem cycle3Net_r1_s0 : (cycle3Net.reaction (1:Fin 4)).source 0 = 0 := rfl
@[simp] theorem cycle3Net_r1_s1 : (cycle3Net.reaction (1:Fin 4)).source 1 = 1 := rfl
@[simp] theorem cycle3Net_r1_s2 : (cycle3Net.reaction (1:Fin 4)).source 2 = 0 := rfl
@[simp] theorem cycle3Net_r1_t0 : (cycle3Net.reaction (1:Fin 4)).target 0 = 0 := rfl
@[simp] theorem cycle3Net_r1_t1 : (cycle3Net.reaction (1:Fin 4)).target 1 = 0 := rfl
@[simp] theorem cycle3Net_r1_t2 : (cycle3Net.reaction (1:Fin 4)).target 2 = 1 := rfl
@[simp] theorem cycle3Net_r2_s0 : (cycle3Net.reaction (2:Fin 4)).source 0 = 0 := rfl
@[simp] theorem cycle3Net_r2_s1 : (cycle3Net.reaction (2:Fin 4)).source 1 = 0 := rfl
@[simp] theorem cycle3Net_r2_s2 : (cycle3Net.reaction (2:Fin 4)).source 2 = 1 := rfl
@[simp] theorem cycle3Net_r2_t0 : (cycle3Net.reaction (2:Fin 4)).target 0 = 1 := rfl
@[simp] theorem cycle3Net_r2_t1 : (cycle3Net.reaction (2:Fin 4)).target 1 = 0 := rfl
@[simp] theorem cycle3Net_r2_t2 : (cycle3Net.reaction (2:Fin 4)).target 2 = 0 := rfl
@[simp] theorem cycle3Net_r3_s0 : (cycle3Net.reaction (3:Fin 4)).source 0 = 0 := rfl
@[simp] theorem cycle3Net_r3_s1 : (cycle3Net.reaction (3:Fin 4)).source 1 = 0 := rfl
@[simp] theorem cycle3Net_r3_s2 : (cycle3Net.reaction (3:Fin 4)).source 2 = 0 := rfl
@[simp] theorem cycle3Net_r3_t0 : (cycle3Net.reaction (3:Fin 4)).target 0 = 1 := rfl
@[simp] theorem cycle3Net_r3_t1 : (cycle3Net.reaction (3:Fin 4)).target 1 = 0 := rfl
@[simp] theorem cycle3Net_r3_t2 : (cycle3Net.reaction (3:Fin 4)).target 2 = 0 := rfl

/-! ### The two index permutations of the triangle -/

/-- The successor permutation of the three-cycle: `A → B → C → A`. -/
def cycNext : Fin 3 → Fin 3 := fun | 0 => 1 | 1 => 2 | 2 => 0

/-- The predecessor permutation of the three-cycle. -/
def cycPrev : Fin 3 → Fin 3 := fun | 0 => 2 | 1 => 0 | 2 => 1

@[simp] theorem cycNext_0 : cycNext 0 = 1 := rfl
@[simp] theorem cycNext_1 : cycNext 1 = 2 := rfl
@[simp] theorem cycNext_2 : cycNext 2 = 0 := rfl
@[simp] theorem cycPrev_0 : cycPrev 0 = 2 := rfl
@[simp] theorem cycPrev_1 : cycPrev 1 = 0 := rfl
@[simp] theorem cycPrev_2 : cycPrev 2 = 1 := rfl

theorem cycNext_ne_self : ∀ a : Fin 3, cycNext a ≠ a := by decide
theorem cycPrev_ne_self : ∀ a : Fin 3, cycPrev a ≠ a := by decide
theorem cycNext_injective : Function.Injective cycNext := by decide
theorem cycPrev_injective : Function.Injective cycPrev := by decide

/-- `cycNext` and `cycPrev` are mutual inverses — the triangle really is one cycle. -/
theorem cycNext_cycPrev : ∀ a : Fin 3, cycNext (cycPrev a) = a := by decide
theorem cycPrev_cycNext : ∀ a : Fin 3, cycPrev (cycNext a) = a := by decide

/-! ## Hypothesis `hsep`: reactant/product separation -/

/-- **No species occurs on both sides of any reaction of `cycle3Net`.**

Each of `A → B`, `B → C`, `C → A` has singleton source and target at *different* species.
For the inflow channel the hypothesis `source s ≠ 0` is unsatisfiable, so the clause is
vacuous there. -/
theorem cycle3Net_reactantProductSeparated : cycle3Net.ReactantProductSeparated := by
  intro r s hs
  rcases r with _ | _ | _ | r
  · fin_cases s <;> simp_all
  · fin_cases s <;> simp_all
  · fin_cases s <;> simp_all
  · exact absurd (hs (by rfl)) (by simp)

/-- `hsep` is not vacuously satisfied: channel `0` really does have a nonzero source entry. -/
theorem cycle3Net_sep_witness : ∃ r s, (cycle3Net.reaction r).source s ≠ 0 :=
  ⟨0, 0, by decide⟩

/-! ## Hazard D2: identity reactions -/

/-- **No channel of `cycle3Net` is an identity reaction.** -/
theorem cycle3Net_no_identity_reaction :
    ∀ r : cycle3Net.R, (cycle3Net.reaction r).source ≠ (cycle3Net.reaction r).target := by
  intro r
  fin_cases r <;> decide

/-- **General principle (closes degeneracy entry D2).**  Under `ReactantProductSeparated`, an
identity reaction has the zero complex as *both* endpoints, hence is a flow channel.

Proof: if `source = target` and `source s ≠ 0` then `target s = source s ≠ 0`, contradicting
separation.  So the source vanishes everywhere. -/
theorem identity_reaction_is_flowChannel_of_separated {N : Network S}
    (hsep : N.ReactantProductSeparated) {r : N.R}
    (hid : (N.reaction r).source = (N.reaction r).target) : N.IsFlowChannel r := by
  show (N.reaction r).source = Complex.zero ∨ (N.reaction r).target = Complex.zero
  by_cases hex : ∃ s, (N.reaction r).source s ≠ 0
  · -- a nonzero source entry would contradict separation, since `hid` makes it a target
    -- entry too
    exfalso
    obtain ⟨s, hs⟩ := hex
    have hz : (N.reaction r).target s = 0 := hsep r s hs
    exact hs (hid.symm ▸ hz)
  · left
    show (N.reaction r).source = Complex.zero
    funext t
    simp only [Complex.zero_apply]
    by_contra hne
    exact hex ⟨t, hne⟩

/-- Consequently the identity-reaction hazard of `isCPair` cannot arise for **any** network
satisfying Hole B's `hsep` + `hflow` bundle: `hsep` turns an identity reaction into a flow
channel, and `hflow` confines flow channels to the canonical singleton inflow/outflow
pseudo-reactions, neither of which is an identity reaction. -/
theorem identity_reaction_excluded_of_bundle {N : Network S}
    (hsep : N.ReactantProductSeparated) (hflow : N.ZeroComplexReactionsAreFlows)
    {r : N.R} (hid : (N.reaction r).source = (N.reaction r).target)
    (hfin : (N.reaction r).Nontrivial) : False := by
  have hfc := identity_reaction_is_flowChannel_of_separated hsep hid
  rcases hflow r hfc with ⟨s, heq⟩ | ⟨s, heq⟩
  · have hcon : (inflowReaction s).source = (inflowReaction s).target := heq.symm ▸ hid
    exact (inflowReaction_source_ne_target s hcon).elim
  · have hcon : (outflowReaction s).source = (outflowReaction s).target := heq.symm ▸ hid
    exact (outflowReaction_source_ne_target s hcon).elim

/-! ## Hypothesis `hflow`: the zero complex occurs only in a canonical inflow channel -/

/-- Channels `0`, `1`, `2` are internal: both endpoints are nonzero singletons. -/
@[simp] theorem cycle3Net_not_flow (r : Fin 4) (h : r ≠ 3) : ¬ cycle3Net.IsFlowChannel r := by
  show ¬ ((cycle3Net.reaction r).source = Complex.zero ∨ (cycle3Net.reaction r).target = Complex.zero)
  intro hcon
  rcases hcon with hs | ht
  · exfalso
    have hd := congrArg (fun c : Complex (Fin 3) => c 0) hs
    simp only [Complex.zero_apply, cycle3Net, singletonComplex, Pi.single_apply,
      if_pos, if_neg (by decide : ¬ ((0 : Fin 4) = 1)),
      if_neg (by decide : ¬ ((0:Fin 4) = 2)),
      if_neg (by decide : ¬ ((0:Fin 4) = 3))] at hd
    fin_cases r <;> simp_all
  · exfalso
    have hd := congrArg (fun c : Complex (Fin 3) => c 1) ht
    simp only [Complex.zero_apply, cycle3Net, singletonComplex, Pi.single_apply,
      if_pos] at hd
    fin_cases r <;> simp_all

/-- **The only flow channel is the canonical inflow `0 → A`.**  This is what makes `hflow`
non-vacuous rather than an artefact of having no flow channel at all. -/
theorem cycle3Net_zeroComplexReactionsAreFlows : cycle3Net.ZeroComplexReactionsAreFlows := by
  intro r hr
  have h3 : r = 3 := by
    by_contra hne
    rcases hr with hs | ht
    · exact (cycle3Net_not_flow r hne) (Or.inl hs)
    · exact (cycle3Net_not_flow r hne) (Or.inr ht)
  subst h3
  exact Or.inl ⟨0, rfl⟩

/-- The inflow channel really is a flow channel: `hflow` is not vacuously true. -/
theorem cycle3Net_has_flow_channel : ∃ r, cycle3Net.IsFlowChannel r := ⟨3, Or.inl rfl⟩

end Network
end CRNT