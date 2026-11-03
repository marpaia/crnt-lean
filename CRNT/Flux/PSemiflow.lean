import CRNT.Dynamics.SiphonConservation
import CRNT.Equilibria.CompatibilityClass

/-!
# P-semiflows and conservative reaction networks

A P-semiflow is a nonnegative species vector in the left kernel of the stoichiometric
matrix.  A strictly positive P-semiflow makes the CRN conservative and bounds every
nonnegative stoichiometric compatibility class.  These are the species-side duals of the
T-invariants / stationary fluxes formalized in `CRNT.Flux.Cone`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Weighted total associated with a species vector. -/
def weightedTotal (w : S → ℝ) (x : Concentration S) : ℝ :=
  ∑ s : S, w s * x s

/-- A P-invariant is a linear conservation law. -/
def IsPInvariant (N : Network S) (w : S → ℝ) : Prop :=
  w ∈ orthSum N.stoichSubspace

/-- A P-semiflow is a nonzero nonnegative P-invariant. -/
def IsPSemiflow (N : Network S) (w : S → ℝ) : Prop :=
  N.IsPInvariant w ∧ (∀ s, 0 ≤ w s) ∧ w ≠ 0

/-- A strictly positive P-semiflow. -/
def IsStrictPSemiflow (N : Network S) (w : S → ℝ) : Prop :=
  N.IsPInvariant w ∧ ∀ s, 0 < w s

/-- A CRN is conservative when it admits a strictly positive P-semiflow. -/
def IsConservative (N : Network S) : Prop :=
  ∃ w : S → ℝ, N.IsStrictPSemiflow w

/-- Support of a species-side invariant. -/
noncomputable def speciesSupport (w : S → ℝ) : Finset S :=
  Finset.univ.filter fun s => w s ≠ 0

/-- Stoichiometrically compatible concentrations have the same value of every P-invariant. -/
theorem weightedTotal_eq_of_stoichCompatible (N : Network S)
    {w : S → ℝ} (hw : N.IsPInvariant w)
    {x y : Concentration S} (hxy : N.StoichCompatible x y) :
    weightedTotal w x = weightedTotal w y := by
  have horth := (mem_orthSum.mp hw) (y - x) hxy
  unfold weightedTotal
  have hzero : ∑ s : S, w s * (y s - x s) = 0 := by
    simpa [Pi.sub_apply] using horth
  simp only [mul_sub] at hzero
  rw [Finset.sum_sub_distrib] at hzero
  linarith

/-- A P-invariant is constant along mass-action trajectories (algebraic compatibility
version). -/
theorem pInvariant_constant_on_compatibilityClass (N : Network S)
    {w : S → ℝ} (hw : N.IsPInvariant w) (x₀ : Concentration S) :
    ∀ x ∈ N.compatibilityClass x₀, weightedTotal w x = weightedTotal w x₀ := by
  intro x hx
  exact (N.weightedTotal_eq_of_stoichCompatible hw hx).symm

/-- Every coordinate of a nonnegative state is bounded by a positive conserved total. -/
theorem coordinate_le_of_strictPSemiflow (N : Network S)
    {w : S → ℝ} (hw : N.IsStrictPSemiflow w)
    {x₀ x : Concentration S} (hx₀ : x₀.Nonnegative) (hx : x.Nonnegative)
    (hcomp : N.StoichCompatible x₀ x) (s : S) :
    x s ≤ weightedTotal w x₀ / w s := by
  have htot := N.weightedTotal_eq_of_stoichCompatible hw.1 hcomp
  have hterm : w s * x s ≤ weightedTotal w x := by
    unfold weightedTotal
    exact Finset.single_le_sum
      (fun t _ => mul_nonneg (hw.2 t).le (hx t)) (Finset.mem_univ s)
  rw [← htot] at hterm
  exact (le_div_iff₀ (hw.2 s)).2 (by simpa [mul_comm] using hterm)

/-- **Conservative-class boundedness.**  A strictly positive P-semiflow gives an explicit
coordinate box containing the entire nonnegative compatibility class. -/
theorem nonnegative_compatibilityClass_bounded_by_PSemiflow
    (N : Network S) {w : S → ℝ} (hw : N.IsStrictPSemiflow w)
    {x₀ : Concentration S} (hx₀ : x₀.Nonnegative) :
    ∀ x : Concentration S, x.Nonnegative → N.StoichCompatible x₀ x →
      ∀ s : S, x s ≤ weightedTotal w x₀ / w s := by
  intro x hx hcomp s
  exact N.coordinate_le_of_strictPSemiflow hw hx₀ hx hcomp s

/-- The support of a nonnegative conservation law is a siphon.  If a reaction produced
positive conserved mass in the support without consuming any supported species, its
weighted stoichiometric change would be strictly positive, contradicting conservation. -/
theorem support_isSiphon_of_PSemiflow (N : Network S)
    {w : S → ℝ} (hw : N.IsPSemiflow w) :
    N.IsSiphon (speciesSupport w) := by
  intro r hProd
  obtain ⟨s, hsP, hsProd⟩ := hProd
  by_contra hnoReactant
  push_neg at hnoReactant
  have hsourceZero : ∀ t : S, (N.reaction r).source t ≠ 0 → w t = 0 := by
    intro t ht
    by_contra hwt
    have htmem : t ∈ speciesSupport w := by simp [speciesSupport, hwt]
    exact hnoReactant t htmem ht
  have hcons : ∑ t : S, w t * N.reactionVector r t = 0 :=
    (N.conservationLaw_iff_mem_orthSum w).2 hw.1 r
  have hnonneg : ∀ t : S, 0 ≤ w t * N.reactionVector r t := by
    intro t
    by_cases hsrc : (N.reaction r).source t = 0
    · rw [Network.reactionVector_apply, hsrc]
      simp only [Nat.cast_zero, sub_zero]
      exact mul_nonneg (hw.2.1 t) (Nat.cast_nonneg _)
    · rw [hsourceZero t hsrc, zero_mul]
  have hsW : 0 < w s := by
    have hsSupp : s ∈ speciesSupport w := hsP
    have hne : w s ≠ 0 := by simpa [speciesSupport] using hsSupp
    exact lt_of_le_of_ne (hw.2.1 s) (Ne.symm hne)
  have hsSrc : (N.reaction r).source s = 0 := by
    by_contra hsrc
    exact hsW.ne' (hsourceZero s hsrc)
  have hsTerm : 0 < w s * N.reactionVector r s := by
    rw [Network.reactionVector_apply, hsSrc]
    simp only [Nat.cast_zero, sub_zero]
    exact mul_pos hsW (by exact_mod_cast Nat.pos_of_ne_zero hsProd)
  have hsumpos : 0 < ∑ t : S, w t * N.reactionVector r t := by
    exact Finset.sum_pos' (fun t _ => hnonneg t) ⟨s, Finset.mem_univ s, hsTerm⟩
  linarith

/-- A strict P-semiflow has full support, so a conservative network has the full species
set as a siphon. -/
theorem full_siphon_of_strictPSemiflow (N : Network S)
    [Nonempty S] {w : S → ℝ} (hw : N.IsStrictPSemiflow w) :
    N.IsSiphon Finset.univ := by
  have hp : N.IsPSemiflow w :=
    ⟨hw.1, fun s => (hw.2 s).le, fun hz => by
      have := hw.2 (Classical.arbitrary S)
      simp [hz] at this⟩
  simpa [speciesSupport, (hw.2 _).ne'] using N.support_isSiphon_of_PSemiflow hp

end Network
end CRNT
