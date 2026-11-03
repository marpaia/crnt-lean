import CRNT.Equilibria.CompatibilityClass
-- `nonnegativeCompatibilityClass` is declared here, verbatim identically; declaring it in
-- both modules made `import CRNT` fail outright.
import CRNT.Geometry.ConservativeCompatibility
import CRNT.Dynamics.SiphonConservation
import CRNT.Flux.PSemiflow

/-!
# Faces of stoichiometric compatibility classes

A nonnegative stoichiometric class is the polyhedron

  (x₀ + S) ∩ ℝ^S_{≥0}.

For a species set `P`, its coordinate face is cut out by `x_s = 0` for every
`s ∈ P`.  Conservation laws supported on `P` exclude that face from every
compatibility class containing a strictly positive point.  This is the geometric
content behind the distinction between critical and noncritical siphons.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Coordinate face of a nonnegative compatibility class specified by the coordinates
that vanish. -/
def compatibilityFace (N : Network S) (x₀ : Concentration S) (P : Finset S) :
    Set (Concentration S) :=
  {x | N.StoichCompatible x₀ x ∧ x.Nonnegative ∧ ∀ s ∈ P, x s = 0}

@[simp] theorem compatibilityFace_empty (N : Network S) (x₀ : Concentration S) :
    N.compatibilityFace x₀ ∅ = N.nonnegativeCompatibilityClass x₀ := by
  ext x
  simp [compatibilityFace, nonnegativeCompatibilityClass]

/-- More vanishing coordinates give a smaller face. -/
theorem compatibilityFace_antitone (N : Network S) (x₀ : Concentration S)
    {P Q : Finset S} (hPQ : P ⊆ Q) :
    N.compatibilityFace x₀ Q ⊆ N.compatibilityFace x₀ P := by
  rintro x ⟨hcomp, hnn, hzero⟩
  exact ⟨hcomp, hnn, fun s hs => hzero s (hPQ hs)⟩

/-- A face for a union is the intersection of the corresponding coordinate faces. -/
theorem compatibilityFace_union (N : Network S) (x₀ : Concentration S)
    (P Q : Finset S) :
    N.compatibilityFace x₀ (P ∪ Q) =
      N.compatibilityFace x₀ P ∩ N.compatibilityFace x₀ Q := by
  ext x
  simp only [compatibilityFace, Set.mem_setOf_eq, Set.mem_inter_iff,
    Finset.mem_union]
  constructor
  · rintro ⟨hc, hnn, hz⟩
    exact ⟨⟨hc, hnn, fun s hs => hz s (Or.inl hs)⟩,
      ⟨hc, hnn, fun s hs => hz s (Or.inr hs)⟩⟩
  · rintro ⟨⟨hc, hnn, hzP⟩, ⟨_, _, hzQ⟩⟩
    exact ⟨hc, hnn, fun s hs => hs.elim (hzP s) (hzQ s)⟩

/-- The exact support condition used in critical-siphon theory: a nonnegative
conservation law that is strictly positive precisely on `P`. -/
def CarriesPositiveConservationLaw (N : Network S) (P : Finset S) : Prop :=
  ∃ w : S → ℝ,
    w ∈ orthSum N.stoichSubspace ∧
    (∀ s, 0 ≤ w s) ∧
    (∀ s, 0 < w s ↔ s ∈ P)

/-- Critical siphons are exactly nonempty siphons that do not carry such a law. -/
theorem isCriticalSiphon_iff_not_carriesPositiveConservationLaw
    (N : Network S) (P : Finset S) :
    N.IsCriticalSiphon P ↔
      P.Nonempty ∧ N.IsSiphon P ∧ ¬ N.CarriesPositiveConservationLaw P := by
  rw [N.isCriticalSiphon_iff_mem_orthSum]
  constructor
  · rintro ⟨hne, hsi, hno⟩
    exact ⟨hne, hsi, fun h => hno (by obtain ⟨w, h1, h2, h3⟩ := h; exact ⟨w, h2, h3, h1⟩)⟩
  · rintro ⟨hne, hsi, hno⟩
    exact ⟨hne, hsi, fun h => hno (by obtain ⟨w, h2, h3, h1⟩ := h; exact ⟨w, h1, h2, h3⟩)⟩

/-- A positive conservation law supported on `P` has strictly positive total on every
strictly positive concentration whenever `P` is nonempty. -/
theorem weightedTotal_pos_of_supported_positive_conservation
    (N : Network S) {P : Finset S} (hP : P.Nonempty)
    {w : S → ℝ}
    (hnn : ∀ s, 0 ≤ w s)
    (hsupp : ∀ s, 0 < w s ↔ s ∈ P)
    {x : Concentration S} (hx : x.Positive) :
    0 < weightedTotal w x := by
  obtain ⟨s, hsP⟩ := hP
  have hws : 0 < w s := (hsupp s).2 hsP
  unfold weightedTotal
  exact Finset.sum_pos'
    (fun t _ => mul_nonneg (hnn t) (hx t).le)
    ⟨s, Finset.mem_univ s, mul_pos hws (hx s)⟩

/-- On the coordinate face `P`, a nonnegative law supported on `P` has zero total. -/
theorem weightedTotal_eq_zero_on_coordinateFace
    {P : Finset S} {w : S → ℝ}
    (hnn : ∀ s, 0 ≤ w s)
    (hsupp : ∀ s, 0 < w s ↔ s ∈ P)
    {x : Concentration S} (hzero : ∀ s ∈ P, x s = 0) :
    weightedTotal w x = 0 := by
  unfold weightedTotal
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : s ∈ P
  · rw [hzero s hs, mul_zero]
  · have hnotpos : ¬ 0 < w s := by simpa [hs] using not_congr (hsupp s)
    have hws : w s = 0 := le_antisymm (le_of_not_gt hnotpos) (hnn s)
    rw [hws, zero_mul]

/-- **Conservation exclusion of a coordinate face.** If a nonempty set `P` carries a
positive conservation law, then no stoichiometric class containing a strictly positive
point can meet the coordinate face where every species in `P` vanishes. -/
theorem compatibilityFace_empty_of_carriesPositiveConservationLaw
    (N : Network S) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {P : Finset S} (hP : P.Nonempty)
    (hcons : N.CarriesPositiveConservationLaw P) :
    N.compatibilityFace x₀ P = ∅ := by
  rcases hcons with ⟨w, hworth, hwnn, hwsupp⟩
  ext x
  constructor
  · rintro ⟨hcomp, hnn, hzero⟩
    have hsame := N.weightedTotal_eq_of_stoichCompatible hworth hcomp
    have hpos := N.weightedTotal_pos_of_supported_positive_conservation
      hP hwnn hwsupp hx₀
    have hz := weightedTotal_eq_zero_on_coordinateFace hwnn hwsupp hzero
    simp only [Set.mem_empty_iff_false]
    linarith
  · simp

/-- Every noncritical nonempty siphon has a conservation-law certificate excluding its
coordinate face from every positive compatibility class. -/
theorem compatibilityFace_empty_of_noncritical_siphon
    (N : Network S) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {P : Finset S} (hPne : P.Nonempty) (hPsiph : N.IsSiphon P)
    (hncrit : ¬ N.IsCriticalSiphon P) :
    N.compatibilityFace x₀ P = ∅ := by
  have hcarry : N.CarriesPositiveConservationLaw P := by
    rw [N.isCriticalSiphon_iff_not_carriesPositiveConservationLaw] at hncrit
    push_neg at hncrit
    exact hncrit hPne hPsiph
  exact N.compatibilityFace_empty_of_carriesPositiveConservationLaw hx₀ hPne hcarry

/-- Therefore any siphon coordinate face that actually intersects a positive
compatibility class must be critical. -/
theorem criticalSiphon_of_compatibilityFace_nonempty
    (N : Network S) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {P : Finset S} (hPne : P.Nonempty) (hPsiph : N.IsSiphon P)
    (hface : (N.compatibilityFace x₀ P).Nonempty) :
    N.IsCriticalSiphon P := by
  by_contra hn
  have hempty := N.compatibilityFace_empty_of_noncritical_siphon hx₀ hPne hPsiph hn
  rw [hempty] at hface
  exact Set.not_nonempty_empty hface

end Network
end CRNT
