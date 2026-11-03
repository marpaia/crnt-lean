import CRNT.Equilibria.DetailedBalanced
import CRNT.Graph.Reversibility
import CRNT.Deficiency.KernelDimension
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Reversible pairings and Wegscheider conditions

For a reversible CRN with possible parallel reaction channels, reversibility is represented by
an explicit involution pairing each reaction channel with a reverse channel.  This avoids
pretending that the reverse of a parallel edge is uniquely determined by the raw network.

Given such a pairing, the logarithmic equilibrium constant of reaction `r` is

`log K_r = log k_r - log k_rev(r)`.

The coordinate-free Wegscheider condition says precisely that the vector `log K` annihilates
the kernel of the stoichiometric map.  Equivalently, every stoichiometric cycle has zero
log-affinity.  This formulation contains the usual multiplicative cycle-product identities
without choosing a graph cycle basis.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A pairing of every reaction channel with a reverse channel.  Parallel reactions are
allowed, so the pairing is data rather than merely a proposition about endpoint existence. -/
structure ReversiblePairing (N : Network S) where
  rev : N.R → N.R
  involutive : Function.Involutive rev
  source_rev : ∀ r, (N.reaction (rev r)).source = (N.reaction r).target
  target_rev : ∀ r, (N.reaction (rev r)).target = (N.reaction r).source

namespace ReversiblePairing

variable {N : Network S}

/-- The reverse pairing as an equivalence of reaction channels. -/
def equiv (ρ : ReversiblePairing N) : N.R ≃ N.R where
  toFun := ρ.rev
  invFun := ρ.rev
  left_inv := ρ.involutive
  right_inv := ρ.involutive

@[simp] theorem rev_rev (ρ : ReversiblePairing N) (r : N.R) :
    ρ.rev (ρ.rev r) = r := ρ.involutive r

@[simp] theorem source_rev_apply (ρ : ReversiblePairing N) (r : N.R) :
    (N.reaction (ρ.rev r)).source = (N.reaction r).target := ρ.source_rev r

@[simp] theorem target_rev_apply (ρ : ReversiblePairing N) (r : N.R) :
    (N.reaction (ρ.rev r)).target = (N.reaction r).source := ρ.target_rev r

/-- Reversing a reaction negates its stoichiometric reaction vector. -/
theorem reactionVector_rev (ρ : ReversiblePairing N) (r : N.R) :
    N.reactionVector (ρ.rev r) = -N.reactionVector r := by
  funext s
  simp [Network.reactionVector_apply, ρ.source_rev r, ρ.target_rev r]

/-- A reverse-channel pairing witnesses ordinary reaction-network reversibility. -/
theorem reversible (ρ : ReversiblePairing N) : N.Reversible := by
  intro r
  exact ⟨ρ.rev r, ρ.source_rev r, ρ.target_rev r⟩

/-- A network admitting a reverse reaction channel for every reaction is weakly reversible. -/
theorem weaklyReversible (ρ : ReversiblePairing N) : N.WeaklyReversible :=
  ρ.reversible.weaklyReversible

end ReversiblePairing

/-- Reaction-channel detailed balance relative to a chosen reverse pairing. -/
def IsReactionwiseDetailedBalanced (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (x : Concentration S) : Prop :=
  ∀ r : N.R, N.massActionRate κ r x = N.massActionRate κ (ρ.rev r) x

/-- The equilibrium-constant ratio `k_r/k_rev(r)`. -/
noncomputable def equilibriumConstant (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (r : N.R) : ℝ :=
  κ.k r / κ.k (ρ.rev r)

/-- Every equilibrium constant is strictly positive. -/
theorem equilibriumConstant_pos (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (r : N.R) :
    0 < N.equilibriumConstant ρ κ r :=
  div_pos (κ.positive r) (κ.positive (ρ.rev r))

/-- Reversal inverts the equilibrium constant. -/
theorem equilibriumConstant_rev (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (r : N.R) :
    N.equilibriumConstant ρ κ (ρ.rev r) = (N.equilibriumConstant ρ κ r)⁻¹ := by
  simp only [equilibriumConstant, ρ.rev_rev]
  field_simp [ne_of_gt (κ.positive r), ne_of_gt (κ.positive (ρ.rev r))]

/-- Logarithmic equilibrium constant / reaction affinity determined by the rate constants. -/
noncomputable def logEquilibriumConstant (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (r : N.R) : ℝ :=
  Real.log (κ.k r) - Real.log (κ.k (ρ.rev r))

/-- Reversal negates the logarithmic equilibrium constant. -/
theorem logEquilibriumConstant_rev (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (r : N.R) :
    N.logEquilibriumConstant ρ κ (ρ.rev r) = -N.logEquilibriumConstant ρ κ r := by
  simp [logEquilibriumConstant, ρ.rev_rev]

/-- **Wegscheider condition, basis-free form.**  Every real stoichiometric cycle has zero
log-affinity.  Equivalently `log K` lies in the dot-product orthogonal complement of
`ker(stoichMap)`.  Integer graph-cycle product identities are contained as special cases. -/
def SatisfiesWegscheider (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) : Prop :=
  N.logEquilibriumConstant ρ κ ∈ orthSum (LinearMap.ker N.stoichMap)

/-- Expanded cycle form of the Wegscheider condition. -/
theorem satisfiesWegscheider_iff (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) :
    N.SatisfiesWegscheider ρ κ ↔
      ∀ z ∈ LinearMap.ker N.stoichMap,
        ∑ r : N.R, N.logEquilibriumConstant ρ κ r * z r = 0 := by
  rfl

/-- A thermodynamic log-potential realizes the rate affinities as stoichiometric
potential differences. -/
def HasWegscheiderPotential (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) : Prop :=
  ∃ μ : S → ℝ, ∀ r : N.R,
    N.logEquilibriumConstant ρ κ r =
      ∑ s : S, N.reactionVector r s * μ s

/-- **Potential form implies all Wegscheider cycle conditions.**  This is the linear
algebra behind the familiar statement that a potential difference sums to zero around
every closed stoichiometric cycle. -/
theorem satisfiesWegscheider_of_hasPotential (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (hpot : N.HasWegscheiderPotential ρ κ) :
    N.SatisfiesWegscheider ρ κ := by
  rcases hpot with ⟨μ, hμ⟩
  rw [N.satisfiesWegscheider_iff ρ κ]
  intro z hz
  have hstoich : N.stoichMap z = 0 := hz
  calc
    (∑ r : N.R, N.logEquilibriumConstant ρ κ r * z r)
        = ∑ r : N.R, (∑ s : S, N.reactionVector r s * μ s) * z r := by
            apply Finset.sum_congr rfl
            intro r _
            rw [hμ r]
    _ = ∑ r : N.R, ∑ s : S, (N.reactionVector r s * μ s) * z r := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_mul]
    _ = ∑ s : S, ∑ r : N.R, (N.reactionVector r s * μ s) * z r := by
          rw [Finset.sum_comm]
    _ = ∑ s : S, (∑ r : N.R, z r * N.reactionVector r s) * μ s := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = 0 := by
          have hs : ∀ s : S, (∑ r : N.R, z r * N.reactionVector r s) = 0 := by
            intro s
            have h := congrFun hstoich s
            rw [N.stoichMap_apply] at h
            exact h
          apply Finset.sum_eq_zero
          intro s _
          rw [hs s, zero_mul]


/-- Logarithm of a positive mass-action monomial.  This is the finite-dimensional
identity `log x^y = y · log x` used to pass between detailed-balance equations and
thermodynamic potentials. -/
theorem log_massActionMonomial_eq {x : Concentration S} (hx : x.Positive)
    (c : Complex S) :
    Real.log (c.massActionMonomial x) =
      ∑ s : S, (c s : ℝ) * Real.log (x s) := by
  rw [Complex.massActionMonomial,
    Real.log_prod (fun s _ => (pow_pos (hx s) _).ne')]
  exact Finset.sum_congr rfl fun s _ => Real.log_pow _ _

/-- Reactionwise detailed balance for an involutive reverse-channel pairing implies
aggregate detailed balance between complexes.  The proof reindexes the finite sum of
parallel channels by the reverse-channel equivalence, so it remains valid when several
reactions have the same source and target complexes. -/
theorem isDetailedBalanced_of_reactionwiseDetailedBalanced
    (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (x : Concentration S)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ x) :
    N.IsDetailedBalanced κ x := by
  intro c hc d hd
  unfold pairFlux
  apply Fintype.sum_equiv ρ.equiv
  intro r
  change
    (if (N.reaction r).source = c ∧ (N.reaction r).target = d then
      N.massActionRate κ r x else 0) =
      if (N.reaction (ρ.rev r)).source = d ∧
          (N.reaction (ρ.rev r)).target = c then
        N.massActionRate κ (ρ.rev r) x else 0
  by_cases hsrc : (N.reaction r).source = c
  · by_cases htgt : (N.reaction r).target = d
    · simp [ReversiblePairing.equiv, hsrc, htgt,
        ρ.source_rev r, ρ.target_rev r, hdb r]
    · simp [ReversiblePairing.equiv, hsrc, htgt,
        ρ.source_rev r, ρ.target_rev r]
  · simp [ReversiblePairing.equiv, hsrc, ρ.source_rev r, ρ.target_rev r]

/-- At a positive reactionwise detailed-balanced state, the logarithmic rate ratios are
stoichiometric potential differences.  The potential is simply `μ_s = log x_s`. -/
theorem hasWegscheiderPotential_of_reactionwiseDetailedBalanced
    (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) {x : Concentration S} (hx : x.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ x) :
    N.HasWegscheiderPotential ρ κ := by
  refine ⟨fun s => Real.log (x s), ?_⟩
  intro r
  have h := congrArg Real.log (hdb r)
  have hsrcpos := Complex.massActionMonomial_pos hx (N.reaction r).source
  have htgtpos := Complex.massActionMonomial_pos hx (N.reaction r).target
  rw [massActionRate, massActionRate, ρ.source_rev,
    Real.log_mul (κ.positive r).ne' hsrcpos.ne',
    Real.log_mul (κ.positive (ρ.rev r)).ne' htgtpos.ne',
    log_massActionMonomial_eq hx, log_massActionMonomial_eq hx] at h
  rw [logEquilibriumConstant]
  simp only [reactionVector_apply]
  calc
    Real.log (κ.k r) - Real.log (κ.k (ρ.rev r))
        = (∑ s : S, ((N.reaction r).target s : ℝ) * Real.log (x s))
          - (∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (x s)) := by
            linarith
    _ = ∑ s : S,
        (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) *
          Real.log (x s) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- Positive reactionwise detailed balance implies every Wegscheider cycle condition. -/
theorem satisfiesWegscheider_of_reactionwiseDetailedBalanced
    (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) {x : Concentration S} (hx : x.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ x) :
    N.SatisfiesWegscheider ρ κ :=
  N.satisfiesWegscheider_of_hasPotential ρ κ
    (N.hasWegscheiderPotential_of_reactionwiseDetailedBalanced ρ κ hx hdb)

/-- Conversely, a thermodynamic species potential constructs a positive reactionwise
 detailed-balanced concentration by exponentiation, `x_s = exp μ_s`. -/
theorem exists_positive_reactionwiseDetailedBalanced_of_hasWegscheiderPotential
    (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (hpot : N.HasWegscheiderPotential ρ κ) :
    ∃ x : Concentration S, x.Positive ∧
      N.IsReactionwiseDetailedBalanced ρ κ x := by
  rcases hpot with ⟨μ, hμ⟩
  let x : Concentration S := fun s => Real.exp (μ s)
  have hx : x.Positive := fun s => Real.exp_pos _
  refine ⟨x, hx, ?_⟩
  intro r
  have hrpos := N.massActionRate_pos κ r hx
  have hrevpos := N.massActionRate_pos κ (ρ.rev r) hx
  apply Real.log_injOn_pos hrpos hrevpos
  rw [massActionRate, massActionRate,
    Real.log_mul (κ.positive r).ne' (Complex.massActionMonomial_pos hx _).ne',
    Real.log_mul (κ.positive (ρ.rev r)).ne' (Complex.massActionMonomial_pos hx _).ne',
    log_massActionMonomial_eq hx, log_massActionMonomial_eq hx]
  rw [ρ.source_rev]
  simp only [x, Real.log_exp]
  have hp := hμ r
  rw [logEquilibriumConstant] at hp
  simp only [reactionVector_apply] at hp
  have hsum :
      (∑ s : S,
          (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) * μ s) =
        (∑ s : S, ((N.reaction r).target s : ℝ) * μ s) -
          (∑ s : S, ((N.reaction r).source s : ℝ) * μ s) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hpDiff := hp.trans hsum
  linarith

/-- The potential formulation is equivalent to existence of a positive reactionwise
 detailed-balanced concentration for the chosen reverse-channel pairing. -/
theorem hasWegscheiderPotential_iff_exists_positive_reactionwiseDetailedBalanced
    (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N) :
    N.HasWegscheiderPotential ρ κ ↔
      ∃ x : Concentration S, x.Positive ∧
        N.IsReactionwiseDetailedBalanced ρ κ x := by
  constructor
  · exact N.exists_positive_reactionwiseDetailedBalanced_of_hasWegscheiderPotential ρ κ
  · rintro ⟨x, hx, hdb⟩
    exact N.hasWegscheiderPotential_of_reactionwiseDetailedBalanced ρ κ hx hdb

/-- A Wegscheider potential therefore produces a positive aggregate detailed-balanced
state, hence also a positive complex-balanced steady state. -/
theorem exists_positiveDetailedBalanced_of_hasWegscheiderPotential
    (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (hpot : N.HasWegscheiderPotential ρ κ) :
    ∃ x : Concentration S, N.IsPositiveDetailedBalanced κ x := by
  obtain ⟨x, hx, hrdb⟩ :=
    N.exists_positive_reactionwiseDetailedBalanced_of_hasWegscheiderPotential ρ κ hpot
  exact ⟨x, hx,
    N.isDetailedBalanced_of_reactionwiseDetailedBalanced ρ κ x hrdb⟩

end Network
end CRNT
