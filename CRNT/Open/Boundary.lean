import CRNT.Open.Augmentation
import CRNT.Equilibria.SteadyState

/-!
# Boundary equilibria of the fully open extension

A nonnegative concentration sits on the *boundary* of the orthant when some species is
absent. The faces of the orthant are indexed by the zero-set of a concentration, and a
**boundary steady state** is a nonnegative equilibrium lying on one of these faces.

For the fully open extension `N⁺` every species is synthesised at a strictly positive
constant inflow `0 → s`. A species held at zero concentration therefore experiences a
net positive influx: the original reactions can only add to its concentration (a reaction
that consumes `s` cannot fire when `s` is absent), the outflow term vanishes, and the
inflow constant is strictly positive. Hence the field cannot vanish on any face:

* `fullyOpen_steadyState_positive`: every nonnegative steady state of `N⁺` is strictly
  interior;
* `not_boundarySteadyState_fullyOpen`: `N⁺` has no boundary steady states;
* `faceOf_fullyOpen_steadyState_eq_empty`: the only face carrying an equilibrium is the
  interior face `∅`.

Depends on: `CRNT.Open.Augmentation`,
`CRNT.Equilibria.SteadyState`.
-/

namespace CRNT

open scoped BigOperators

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A concentration lies on the boundary of the nonnegative orthant when some species is
absent. -/
def IsBoundary (x : Concentration S) : Prop := ∃ s : S, x s = 0

/-- The face of the orthant carrying `x`: the set of absent species. The interior face is
`∅`. -/
noncomputable def faceOf (x : Concentration S) : Finset S :=
  Finset.univ.filter (fun s => x s = 0)

omit [DecidableEq S] in
@[simp] theorem mem_faceOf {x : Concentration S} {s : S} :
    s ∈ faceOf x ↔ x s = 0 := by
  simp [faceOf]

/-- A boundary steady state of a network: a nonnegative mass-action equilibrium that lies
on some face of the orthant. -/
def BoundarySteadyState (N : Network S) (κ : RateConstants N) (x : Concentration S) : Prop :=
  x.Nonnegative ∧ IsBoundary x ∧ N.IsMassActionSteadyState κ x

/-- **The mass-action field of the fully open extension splits** into the original
reaction part, the constant inflow `κ(0 → s)`, and the linear outflow `−κ(s → 0)·x s`. -/
@[simp] theorem massActionVectorField_fullyOpen_apply (N : Network S)
    (κ : RateConstants N.fullyOpen) (x : Concentration S) (s : S) :
    N.fullyOpen.massActionVectorField κ x s =
      (∑ r : N.R, N.fullyOpen.massActionRate κ (Sum.inl r) x * N.reactionVector r s)
        + κ.k (Sum.inr (Sum.inl s)) - κ.k (Sum.inr (Sum.inr s)) * x s := by
  rw [massActionVectorField_apply]
  -- Split the sum over `N.fullyOpen.R = N.R ⊕ S ⊕ S` into its three blocks.
  have hsplit : (∑ r : N.fullyOpen.R, N.fullyOpen.massActionRate κ r x *
      N.fullyOpen.reactionVector r s) =
      (∑ r : N.R, N.fullyOpen.massActionRate κ (Sum.inl r) x *
        N.fullyOpen.reactionVector (Sum.inl r) s)
      + ((∑ t : S, N.fullyOpen.massActionRate κ (Sum.inr (Sum.inl t)) x *
        N.fullyOpen.reactionVector (Sum.inr (Sum.inl t)) s)
      + (∑ t : S, N.fullyOpen.massActionRate κ (Sum.inr (Sum.inr t)) x *
        N.fullyOpen.reactionVector (Sum.inr (Sum.inr t)) s)) := by
    have h1 := Fintype.sum_sum_type (α₁ := N.R) (α₂ := S ⊕ S)
          (fun r => N.fullyOpen.massActionRate κ r x * N.fullyOpen.reactionVector r s)
    have h2 := Fintype.sum_sum_type (α₁ := S) (α₂ := S)
          (fun t => N.fullyOpen.massActionRate κ (Sum.inr t) x *
            N.fullyOpen.reactionVector (Sum.inr t) s)
    rw [h2] at h1
    exact h1
  rw [hsplit]
  -- The original block: the fully open reaction vector at `Sum.inl r` is `N.reactionVector r`.
  have horig : (∑ r : N.R, N.fullyOpen.massActionRate κ (Sum.inl r) x *
      N.fullyOpen.reactionVector (Sum.inl r) s) =
      ∑ r : N.R, N.fullyOpen.massActionRate κ (Sum.inl r) x * N.reactionVector r s := by
    refine Finset.sum_congr rfl fun r _ => ?_
    change N.fullyOpen.massActionRate κ (Sum.inl r) x *
        (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) = _
    rfl
  -- The inflow block collapses to its diagonal `s` term.
  have hin : (∑ t : S, N.fullyOpen.massActionRate κ (Sum.inr (Sum.inl t)) x *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inl t)) s) =
      κ.k (Sum.inr (Sum.inl s)) := by
    rw [Finset.sum_eq_single s]
    · rw [reactionVector_inflow, Pi.single_eq_same, mul_one]
      change κ.k (Sum.inr (Sum.inl s)) *
          (inflowReaction s).source.massActionMonomial x = _
      simp [inflowReaction, Complex.massActionMonomial_zero]
    · intro t _ hts
      rw [reactionVector_inflow, Pi.single_eq_of_ne (Ne.symm hts), mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  -- The outflow block collapses to its diagonal `s` term.
  have hout : (∑ t : S, N.fullyOpen.massActionRate κ (Sum.inr (Sum.inr t)) x *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inr t)) s) =
      - (κ.k (Sum.inr (Sum.inr s)) * x s) := by
    rw [Finset.sum_eq_single s]
    · have hmono : (outflowReaction s : Reaction S).source.massActionMonomial x = x s := by
        rw [outflowReaction, Complex.massActionMonomial, Finset.prod_eq_single s]
        · show x s ^ (singletonComplex s s) = x s
          rw [singletonComplex, Pi.single_eq_same, pow_one]
        · intro t _ hts
          show x t ^ (singletonComplex s t) = 1
          rw [singletonComplex, Pi.single_eq_of_ne hts, pow_zero]
        · intro h; exact absurd (Finset.mem_univ s) h
      rw [reactionVector_outflow, Pi.neg_apply, Pi.single_eq_same, mul_neg, mul_one]
      simp only [massActionRate, fullyOpen_reaction_outflow, hmono]
    · intro t _ hts
      rw [reactionVector_outflow, Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hts),
        neg_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [horig, hin, hout]
  ring

/-- **Each original reaction contributes nonnegatively at an absent species.** A reaction
that consumes `s` cannot fire when `s` is absent (its rate vanishes), while a reaction
that produces or ignores `s` has a nonnegative coefficient there. -/
theorem originalRate_mul_reactionVector_nonneg_of_zero (N : Network S)
    (κ : RateConstants N.fullyOpen) {x : Concentration S} (hx : x.Nonnegative)
    {s : S} (hs : x s = 0) (r : N.R) :
    0 ≤ N.fullyOpen.massActionRate κ (Sum.inl r) x * N.reactionVector r s := by
  rcases le_or_gt 0 (N.reactionVector r s) with hrv | hrv
  · exact mul_nonneg (massActionRate_nonneg N.fullyOpen κ (Sum.inl r) hx) hrv
  · -- The reaction vector is negative, so `s` is strictly consumed: the source needs `s`.
    have hsource : (N.reaction r).source s ≠ 0 := by
      rw [reactionVector_apply] at hrv
      intro h
      have hlt : ((N.reaction r).target s : ℝ) < ((N.reaction r).source s : ℝ) := by linarith
      rw [h, Nat.cast_zero] at hlt
      have hnn : (0 : ℝ) ≤ ((N.reaction r).target s : ℝ) := by positivity
      linarith
    -- Hence the source monomial vanishes at `x` (it contains the factor `(x s)^k = 0`).
    have hmono : (N.fullyOpen.reaction (Sum.inl r)).source.massActionMonomial x = 0 := by
      rw [fullyOpen_reaction_inl, Complex.massActionMonomial,
        Finset.prod_eq_zero (Finset.mem_univ s)]
      rw [hs, zero_pow hsource]
    simp only [massActionRate, hmono, zero_mul, mul_zero]
    exact le_rfl

/-- **A nonnegative steady state of the fully open extension is strictly interior.** At an
absent species the field reduces to a sum of nonnegative original contributions, a zero
outflow term, and the strictly positive inflow constant — so it cannot vanish. -/
theorem fullyOpen_steadyState_positive (N : Network S) (κ : RateConstants N.fullyOpen)
    {x : Concentration S} (hx : x.Nonnegative)
    (hss : N.fullyOpen.IsMassActionSteadyState κ x) : x.Positive := by
  intro s
  refine lt_of_le_of_ne (hx s) (fun hzero => ?_)
  have hs : x s = 0 := hzero.symm
  have hfield := (isMassActionSteadyState_iff N.fullyOpen κ x).mp hss s
  rw [← massActionVectorField_apply] at hfield
  rw [massActionVectorField_fullyOpen_apply] at hfield
  -- The original block is nonnegative, the outflow vanishes, the inflow is positive.
  have horig : 0 ≤ ∑ r : N.R, N.fullyOpen.massActionRate κ (Sum.inl r) x *
      N.reactionVector r s :=
    Finset.sum_nonneg fun r _ =>
      originalRate_mul_reactionVector_nonneg_of_zero N κ hx hs r
  have hinflow : 0 < κ.k (Sum.inr (Sum.inl s)) := κ.positive _
  rw [hs, mul_zero, sub_zero] at hfield
  linarith

/-- **The fully open extension has no boundary steady states.** -/
theorem not_boundarySteadyState_fullyOpen (N : Network S) (κ : RateConstants N.fullyOpen)
    (x : Concentration S) : ¬ N.fullyOpen.BoundarySteadyState κ x := by
  rintro ⟨hx, ⟨s, hs⟩, hss⟩
  exact absurd hs (fullyOpen_steadyState_positive N κ hx hss s).ne'

/-- **The only face of the orthant carrying an equilibrium of the fully open extension is
the interior face.** -/
theorem faceOf_fullyOpen_steadyState_eq_empty (N : Network S) (κ : RateConstants N.fullyOpen)
    {x : Concentration S} (hx : x.Nonnegative)
    (hss : N.fullyOpen.IsMassActionSteadyState κ x) : faceOf x = ∅ := by
  rw [faceOf, Finset.filter_eq_empty_iff]
  intro s _
  exact (fullyOpen_steadyState_positive N κ hx hss s).ne'

end Network

end CRNT
