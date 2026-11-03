import CRNT.Open.Boundary

/-!
# Boundary equilibria of the partial-open (CFSTR) extension

A continuous-flow stirred-tank reactor exchanges material with its surroundings through a
*chosen* set of species `O ⊆ S`: each species in `O` is synthesised (`0 → s`) and degraded
(`s → 0`), while the species outside `O` are closed. Adjoining these pseudo-reactions for the
open species only gives the **partial-open extension** `N(O)`, indexed by
`N.R ⊕ {s // s ∈ O} ⊕ {s // s ∈ O}` (original reactions, inflows, outflows).

Unlike the fully open extension — where every species has a strictly positive influx, so no
equilibrium can touch the boundary — a partial-open reactor *can* have boundary equilibria: a
closed species (one outside `O`) may legitimately sit at zero concentration. The sharp
statement is therefore a **characterization of which faces can carry an equilibrium**, not an
absence result. An *open* species, however, still experiences a strictly positive net influx
when absent (its original contributions are nonnegative, its outflow vanishes at zero, and its
inflow constant is strictly positive), so it cannot vanish at a steady state:

* `partialOpen_steadyState_pos_on_open`: at a nonnegative steady state every open species is
  strictly positive;
* `faceOf_partialOpen_steadyState_disjoint`: the face carrying an equilibrium is disjoint from
  the open set `O` — boundary equilibria live only on closed species;
* `not_boundarySteadyState_on_open`: no boundary steady state vanishes on an open species.

Depends on: `CRNT.Open.Boundary`.
-/

namespace CRNT

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

namespace Network

/-- **The partial-open (CFSTR) extension** of a network through the open set `O`: the original
reactions together with a synthesis `0 → s` and a degradation `s → 0` for every species in `O`.
Reactions are indexed by `N.R ⊕ {s // s ∈ O} ⊕ {s // s ∈ O}` — original, inflows, outflows. -/
def partialOpen (N : Network S) (O : Finset S) : Network S where
  R := N.R ⊕ {s // s ∈ O} ⊕ {s // s ∈ O}
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := Sum.elim N.reaction
    (Sum.elim (fun s => inflowReaction s.val) (fun s => outflowReaction s.val))

@[simp] theorem partialOpen_reaction_inl (N : Network S) (O : Finset S) (r : N.R) :
    (N.partialOpen O).reaction (Sum.inl r) = N.reaction r := rfl

@[simp] theorem partialOpen_reaction_inflow (N : Network S) (O : Finset S) (s : {s // s ∈ O}) :
    (N.partialOpen O).reaction (Sum.inr (Sum.inl s)) = inflowReaction s.val := rfl

@[simp] theorem partialOpen_reaction_outflow (N : Network S) (O : Finset S) (s : {s // s ∈ O}) :
    (N.partialOpen O).reaction (Sum.inr (Sum.inr s)) = outflowReaction s.val := rfl

/-- The inflow reaction's vector for an open species is the standard basis vector `e_s`. -/
theorem reactionVector_partialOpen_inflow (N : Network S) (O : Finset S) (s : {s // s ∈ O}) :
    (N.partialOpen O).reactionVector (Sum.inr (Sum.inl s)) = Pi.single s.val (1 : ℝ) := by
  funext s'
  simp only [reactionVector, partialOpen_reaction_inflow]
  simp only [inflowReaction, singletonComplex_apply, Complex.zero_apply, Pi.single_apply]
  split <;> simp_all

/-- The outflow reaction's vector for an open species is `-e_s`. -/
theorem reactionVector_partialOpen_outflow (N : Network S) (O : Finset S) (s : {s // s ∈ O}) :
    (N.partialOpen O).reactionVector (Sum.inr (Sum.inr s)) = -Pi.single s.val (1 : ℝ) := by
  funext s'
  simp only [reactionVector, partialOpen_reaction_outflow]
  simp only [outflowReaction, singletonComplex_apply, Complex.zero_apply, Pi.neg_apply,
    Pi.single_apply]
  split <;> simp_all

/-- **The mass-action field of the partial-open extension at an open species splits** into the
original reaction part, the constant inflow `κ(0 → s)`, and the linear outflow `−κ(s → 0)·x s`,
exactly as in the fully open case. -/
theorem massActionVectorField_partialOpen_apply_mem (N : Network S) (O : Finset S)
    (κ : RateConstants (N.partialOpen O)) (x : Concentration S) {s : S} (hsO : s ∈ O) :
    (N.partialOpen O).massActionVectorField κ x s =
      (∑ r : N.R, (N.partialOpen O).massActionRate κ (Sum.inl r) x * N.reactionVector r s)
        + κ.k (Sum.inr (Sum.inl ⟨s, hsO⟩)) - κ.k (Sum.inr (Sum.inr ⟨s, hsO⟩)) * x s := by
  rw [massActionVectorField_apply]
  -- Split the sum over `N.R ⊕ {s // s ∈ O} ⊕ {s // s ∈ O}` into its three blocks.
  have hsplit : (∑ r : (N.partialOpen O).R, (N.partialOpen O).massActionRate κ r x *
      (N.partialOpen O).reactionVector r s) =
      (∑ r : N.R, (N.partialOpen O).massActionRate κ (Sum.inl r) x *
        (N.partialOpen O).reactionVector (Sum.inl r) s)
      + ((∑ t : {s // s ∈ O}, (N.partialOpen O).massActionRate κ (Sum.inr (Sum.inl t)) x *
        (N.partialOpen O).reactionVector (Sum.inr (Sum.inl t)) s)
      + (∑ t : {s // s ∈ O}, (N.partialOpen O).massActionRate κ (Sum.inr (Sum.inr t)) x *
        (N.partialOpen O).reactionVector (Sum.inr (Sum.inr t)) s)) := by
    have h1 := Fintype.sum_sum_type (α₁ := N.R) (α₂ := {s // s ∈ O} ⊕ {s // s ∈ O})
          (fun r => (N.partialOpen O).massActionRate κ r x *
            (N.partialOpen O).reactionVector r s)
    have h2 := Fintype.sum_sum_type (α₁ := {s // s ∈ O}) (α₂ := {s // s ∈ O})
          (fun t => (N.partialOpen O).massActionRate κ (Sum.inr t) x *
            (N.partialOpen O).reactionVector (Sum.inr t) s)
    rw [h2] at h1
    exact h1
  rw [hsplit]
  -- The original block: the partial-open reaction vector at `Sum.inl r` is `N.reactionVector r`.
  have horig : (∑ r : N.R, (N.partialOpen O).massActionRate κ (Sum.inl r) x *
      (N.partialOpen O).reactionVector (Sum.inl r) s) =
      ∑ r : N.R, (N.partialOpen O).massActionRate κ (Sum.inl r) x * N.reactionVector r s := by
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [reactionVector, partialOpen_reaction_inl]
  -- The inflow block collapses to its diagonal `⟨s, hsO⟩` term.
  have hin : (∑ t : {s // s ∈ O}, (N.partialOpen O).massActionRate κ (Sum.inr (Sum.inl t)) x *
      (N.partialOpen O).reactionVector (Sum.inr (Sum.inl t)) s) =
      κ.k (Sum.inr (Sum.inl ⟨s, hsO⟩)) := by
    rw [Finset.sum_eq_single (⟨s, hsO⟩ : {s // s ∈ O})]
    · rw [reactionVector_partialOpen_inflow]
      simp only [Pi.single_eq_same, mul_one, massActionRate, partialOpen_reaction_inflow,
        inflowReaction, Complex.massActionMonomial_zero, mul_one]
    · intro t _ hts
      have hne : s ≠ t.val := fun h => hts (Subtype.ext h.symm)
      rw [reactionVector_partialOpen_inflow, Pi.single_eq_of_ne hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- The outflow block collapses to its diagonal `⟨s, hsO⟩` term.
  have hout : (∑ t : {s // s ∈ O}, (N.partialOpen O).massActionRate κ (Sum.inr (Sum.inr t)) x *
      (N.partialOpen O).reactionVector (Sum.inr (Sum.inr t)) s) =
      - (κ.k (Sum.inr (Sum.inr ⟨s, hsO⟩)) * x s) := by
    rw [Finset.sum_eq_single (⟨s, hsO⟩ : {s // s ∈ O})]
    · have hmono : (outflowReaction s : Reaction S).source.massActionMonomial x = x s := by
        rw [outflowReaction, Complex.massActionMonomial, Finset.prod_eq_single s]
        · show x s ^ (singletonComplex s s) = x s
          rw [singletonComplex, Pi.single_eq_same, pow_one]
        · intro t _ hts
          show x t ^ (singletonComplex s t) = 1
          rw [singletonComplex, Pi.single_eq_of_ne hts, pow_zero]
        · intro h; exact absurd (Finset.mem_univ s) h
      rw [reactionVector_partialOpen_outflow]
      simp only [Pi.neg_apply, Pi.single_eq_same, massActionRate, partialOpen_reaction_outflow,
        hmono, mul_neg, mul_one]
    · intro t _ hts
      have hne : s ≠ t.val := fun h => hts (Subtype.ext h.symm)
      rw [reactionVector_partialOpen_outflow, Pi.neg_apply, Pi.single_eq_of_ne hne,
        neg_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [horig, hin, hout]
  ring

/-- **Each original reaction contributes nonnegatively at an absent species** in the partial-open
extension. A reaction that consumes `s` cannot fire when `s` is absent (its rate vanishes), while
a reaction that produces or ignores `s` has a nonnegative coefficient there. -/
theorem partialOpen_originalRate_mul_reactionVector_nonneg_of_zero (N : Network S) (O : Finset S)
    (κ : RateConstants (N.partialOpen O)) {x : Concentration S} (hx : x.Nonnegative)
    {s : S} (hs : x s = 0) (r : N.R) :
    0 ≤ (N.partialOpen O).massActionRate κ (Sum.inl r) x * N.reactionVector r s := by
  rcases le_or_gt 0 (N.reactionVector r s) with hrv | hrv
  · exact mul_nonneg (massActionRate_nonneg (N.partialOpen O) κ (Sum.inl r) hx) hrv
  · -- The reaction vector is negative, so `s` is strictly consumed: the source needs `s`.
    have hsource : (N.reaction r).source s ≠ 0 := by
      rw [reactionVector_apply] at hrv
      intro h
      have hlt : ((N.reaction r).target s : ℝ) < ((N.reaction r).source s : ℝ) := by linarith
      rw [h, Nat.cast_zero] at hlt
      have hnn : (0 : ℝ) ≤ ((N.reaction r).target s : ℝ) := by positivity
      linarith
    -- Hence the source monomial vanishes at `x` (it contains the factor `(x s)^k = 0`).
    have hmono : ((N.partialOpen O).reaction (Sum.inl r)).source.massActionMonomial x = 0 := by
      rw [partialOpen_reaction_inl, Complex.massActionMonomial,
        Finset.prod_eq_zero (Finset.mem_univ s)]
      rw [hs, zero_pow hsource]
    have hmono' : (N.reaction r).source.massActionMonomial x = 0 := by
      simpa [partialOpen_reaction_inl] using hmono
    simp only [massActionRate, partialOpen_reaction_inl, hmono', mul_zero, zero_mul]
    exact le_rfl

/-- **A nonnegative steady state of the partial-open extension is strictly positive on every open
species.** At an absent open species the field reduces to a sum of nonnegative original
contributions, a zero outflow term, and the strictly positive inflow constant — so it cannot
vanish. Closed species (outside `O`) are *not* constrained, hence boundary equilibria can occur
on them. -/
theorem partialOpen_steadyState_pos_on_open (N : Network S) (O : Finset S)
    (κ : RateConstants (N.partialOpen O)) {x : Concentration S} (hx : x.Nonnegative)
    (hss : (N.partialOpen O).IsMassActionSteadyState κ x) {s : S} (hsO : s ∈ O) :
    0 < x s := by
  refine lt_of_le_of_ne (hx s) (fun hzero => ?_)
  have hs : x s = 0 := hzero.symm
  have hfield := (isMassActionSteadyState_iff (N.partialOpen O) κ x).mp hss s
  rw [← massActionVectorField_apply] at hfield
  rw [massActionVectorField_partialOpen_apply_mem N O κ x hsO] at hfield
  have horig : 0 ≤ ∑ r : N.R, (N.partialOpen O).massActionRate κ (Sum.inl r) x *
      N.reactionVector r s :=
    Finset.sum_nonneg fun r _ =>
      partialOpen_originalRate_mul_reactionVector_nonneg_of_zero N O κ hx hs r
  have hinflow : 0 < κ.k (Sum.inr (Sum.inl ⟨s, hsO⟩)) := κ.positive _
  rw [hs, mul_zero, sub_zero] at hfield
  linarith

/-- **The face of the orthant carrying an equilibrium of the partial-open extension is disjoint
from the open set.** A boundary steady state can only vanish on closed species; every open
species is strictly positive. -/
theorem faceOf_partialOpen_steadyState_disjoint (N : Network S) (O : Finset S)
    (κ : RateConstants (N.partialOpen O)) {x : Concentration S} (hx : x.Nonnegative)
    (hss : (N.partialOpen O).IsMassActionSteadyState κ x) :
    Disjoint (faceOf x) O := by
  rw [Finset.disjoint_left]
  intro s hsface hsO
  rw [mem_faceOf] at hsface
  exact absurd hsface (partialOpen_steadyState_pos_on_open N O κ hx hss hsO).ne'

/-- **No boundary steady state of the partial-open extension vanishes on an open species.** -/
theorem not_boundarySteadyState_on_open (N : Network S) (O : Finset S)
    (κ : RateConstants (N.partialOpen O)) {x : Concentration S}
    (hbss : (N.partialOpen O).BoundarySteadyState κ x) {s : S} (hsO : s ∈ O) :
    x s ≠ 0 :=
  (partialOpen_steadyState_pos_on_open N O κ hbss.1 hbss.2.2 hsO).ne'

end Network

end CRNT
