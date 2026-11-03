import CRNT.Multistationarity.ConcordanceConverse

/-!
# Discordance and the converse concordance theorem

The definition of concordance is deliberately the negation of a finite sign witness.  The
forward theorem in `Concordance.lean` shows that absence of such a witness forces every
weakly monotonic kinetics to be injective.  The converse theorem of Shinar--Feinberg says
that this structural criterion is exact: a discordance witness can be realized by a
weakly monotonic kinetics and two distinct positive stoichiometrically compatible
compositions with equal species-formation rates.

The difficult part is constructive--building globally admissible rates from the sign
witness.  It is isolated in `exists_noninjective_weaklyMonotonic_of_witness`; the logical
consequences then make concordance an iff characterization of kinetics-independent
injectivity.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- A network is discordant iff it has a concordance witness. -/
def Discordant (N : Network S) : Prop := ¬ N.Concordant

/-- Unfold discordance into the explicit sign witness. -/
theorem discordant_iff_exists_witness (N : Network S) :
    N.Discordant ↔
      ∃ (α : N.R → ℝ) (σ : S → ℝ), N.ConcordanceWitness α σ := by
  simp [Discordant, Concordant]

/-- A discordance witness can be realized by two distinct positive compatible states and
an admissible weakly monotonic kinetics having the same species-formation rate there.
This is the constructive converse theorem of concordance theory. -/
theorem exists_noninjective_weaklyMonotonic_of_witness
    {α : N.R → ℝ} {σ : S → ℝ}
    (h : N.ConcordanceWitness α σ) :
    ∃ (K : Kinetics N) (x y : Concentration S),
      K.WeaklyMonotonic ∧
      x.Positive ∧ y.Positive ∧
      x ≠ y ∧
      y - x ∈ N.stoichSubspace ∧
      K.vectorField x = K.vectorField y := by
  obtain ⟨R⟩ := N.realize_concordanceWitness h
  obtain ⟨hne, hcomp, hfield⟩ := concordanceKineticsRealization_noninjective R
  refine ⟨R.kinetics, R.pair.x, R.pair.y, R.weaklyMonotonic,
    R.pair.x_pos, R.pair.y_pos, hne, ?_, hfield⟩
  exact hcomp

/-- Every discordant network admits a noninjective weakly monotonic kinetics. -/
theorem Discordant.exists_noninjective_weaklyMonotonic (hN : N.Discordant) :
    ∃ K : Kinetics N, K.WeaklyMonotonic ∧ ¬ K.Injective := by
  rw [discordant_iff_exists_witness] at hN
  obtain ⟨α, σ, hw⟩ := hN
  obtain ⟨K, x, y, hwm, hx, hy, hxy, hcompat, heq⟩ :=
    exists_noninjective_weaklyMonotonic_of_witness hw
  refine ⟨K, hwm, ?_⟩
  intro hinj
  have hxmem : x ∈ N.positiveCompatibilityClass x :=
    ⟨Network.StoichCompatible.refl N x, hx⟩
  have hymem : y ∈ N.positiveCompatibilityClass x := by
    refine ⟨?_, hy⟩
    show y - x ∈ N.stoichSubspace
    simpa [sub_eq_add_neg] using hcompat
  exact hxy ((hinj x) hxmem hymem heq)

/- The concordance characterization is provided by `ConcordanceConverse`. -/

/-- Equivalent existential formulation of discordance. -/
theorem discordant_iff_exists_noninjective_weaklyMonotonic (N : Network S) :
    N.Discordant ↔
      ∃ K : Kinetics N, K.WeaklyMonotonic ∧ ¬ K.Injective := by
  constructor
  · exact Discordant.exists_noninjective_weaklyMonotonic
  · rintro ⟨K, hwm, hnon⟩ hcon
    exact hnon (hcon.injective_of_weaklyMonotonic hwm)

/-- The structural dichotomy is exhaustive. -/
theorem concordant_or_discordant (N : Network S) : N.Concordant ∨ N.Discordant := by
  exact Classical.em _

end Network
end CRNT
