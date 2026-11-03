import CRNT.Translation.DynamicalEquivalence
import CRNT.Stoich.Subspace

/-!
# Reaction-vector-preserving network translation

A basic network translation moves the source and target of each reaction by the same
(nonnegative integer) complex.  Reaction vectors are therefore unchanged.  The translated
reaction graph can be very different, while the stoichiometric subspace and rank are
identical.

For kinetics, the translated structural network is naturally a generalized mass-action
network: the **stoichiometric complexes** are the translated complexes but the **kinetic
complex** attached to each reaction remains its original source.  With that convention the
translated generalized vector field is exactly the original mass-action vector field.

This is the theorem-level core of CRNT network translation; no search procedure for a
weakly reversible or deficiency-zero translation is included.
-/

namespace CRNT

namespace Reaction

variable {S : Type}

/-- Translate a reaction by adding the same complex to its source and target. -/
def translate (r : Reaction S) (τ : Complex S) : Reaction S where
  source := Complex.add r.source τ
  target := Complex.add r.target τ

@[simp] theorem translate_source (r : Reaction S) (τ : Complex S) :
    (r.translate τ).source = Complex.add r.source τ := rfl

@[simp] theorem translate_target (r : Reaction S) (τ : Complex S) :
    (r.translate τ).target = Complex.add r.target τ := rfl

/-- Translation preserves the stoichiometric reaction vector. -/
@[simp] theorem translate_vector (r : Reaction S) (τ : Complex S) :
    (r.translate τ).vector = r.vector := by
  funext s
  simp only [vector_apply, translate_source, translate_target, Complex.add_apply]
  push_cast
  ring

end Reaction

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Compatibility wrapper for the reaction-wise translation API.  A reaction translation is
just the current reaction-indexed shift function; downstream modules can use the namespace
projections below without reintroducing an obsolete structure. -/
abbrev ReactionTranslation (N : Network S) := N.R → Complex S

/-- Translate each reaction channel independently by a complex `τ r`.  The reaction index
set is definitionally unchanged. -/
def translate (N : Network S) (τ : N.R → Complex S) : Network S where
  R := N.R
  decEqR := N.decEqR
  fintypeR := N.fintypeR
  reaction := fun r => (N.reaction r).translate (τ r)

@[simp] theorem translate_reaction (N : Network S) (τ : N.R → Complex S) (r : N.R) :
    (N.translate τ).reaction r = (N.reaction r).translate (τ r) := rfl

@[simp] theorem translate_reactionVector (N : Network S) (τ : N.R → Complex S) (r : N.R) :
    (N.translate τ).reactionVector r = N.reactionVector r := by
  funext s
  change ((N.reaction r).translate (τ r)).vector s = (N.reaction r).vector s
  rw [Reaction.translate_vector]

/-- Translation preserves the set of stoichiometric reaction vectors exactly. -/
theorem translate_reactionVectors (N : Network S) (τ : N.R → Complex S) :
    (N.translate τ).reactionVectors = N.reactionVectors := by
  ext v
  constructor <;> intro hv
  · obtain ⟨r, hr⟩ := hv
    exact ⟨r, (N.translate_reactionVector τ r).symm.trans hr⟩
  · obtain ⟨r, hr⟩ := hv
    exact ⟨r, (N.translate_reactionVector τ r).trans hr⟩

/-- **Stoichiometric invariance of network translation.** -/
@[simp] theorem translate_stoichSubspace (N : Network S) (τ : N.R → Complex S) :
    (N.translate τ).stoichSubspace = N.stoichSubspace := by
  simp only [stoichSubspace, N.translate_reactionVectors τ]

/-- Network translation preserves stoichiometric rank. -/
@[simp] theorem translate_stoichRank (N : Network S) (τ : N.R → Complex S) :
    (N.translate τ).stoichRank = N.stoichRank := by
  unfold stoichRank
  rw [N.translate_stoichSubspace τ]

/-- The zero translation, which leaves every reaction unchanged. -/
def zeroTranslation (N : Network S) : N.R → Complex S := fun _ => Complex.zero

@[simp] theorem translate_zero_reaction (N : Network S) (r : N.R) :
    (N.translate N.zeroTranslation).reaction r = N.reaction r := by
  cases hr : N.reaction r with
  | mk source target =>
      simp only [translate, zeroTranslation, Reaction.translate, hr]
      constructor <;> funext s <;> simp [Complex.add, Complex.zero]

/-- A translation is **source coherent** when reaction channels with the same original
source complex receive the same translated source complex.  This is exactly what is needed
for the reaction-wise construction to descend to a map on source complexes. -/
def TranslationSourceCoherent (N : Network S) (τ : N.R → Complex S) : Prop :=
  ∀ r q : N.R, (N.reaction r).source = (N.reaction q).source →
    ((N.translate τ).reaction r).source = ((N.translate τ).reaction q).source

/-- A reaction-wise translation is **proper** when it preserves the partition of reaction
channels by source complex: two translated reactions have the same source exactly when the
original reactions did.  This packages both well-definedness of the source-complex map and
its injectivity, the defining feature of a proper CRNT translation. -/
def IsProperTranslation (N : Network S) (τ : N.R → Complex S) : Prop :=
  ∀ r q : N.R,
    ((N.translate τ).reaction r).source = ((N.translate τ).reaction q).source ↔
      (N.reaction r).source = (N.reaction q).source

namespace ReactionTranslation

/-- Structural network induced by a reaction-wise translation. -/
def network {N : Network S} (T : N.ReactionTranslation) : Network S := N.translate T

/-- Translated source complex of a reaction channel. -/
def source {N : Network S} (T : N.ReactionTranslation) (r : N.R) : Complex S :=
  ((N.translate T).reaction r).source

/-- Translated target complex of a reaction channel. -/
def target {N : Network S} (T : N.ReactionTranslation) (r : N.R) : Complex S :=
  ((N.translate T).reaction r).target

/-- Source coherence, exposed as a translation-level predicate. -/
abbrev SourceCoherent {N : Network S} (T : N.ReactionTranslation) : Prop :=
  N.TranslationSourceCoherent T

/-- Properness, exposed as a translation-level predicate. -/
abbrev Proper {N : Network S} (T : N.ReactionTranslation) : Prop :=
  N.IsProperTranslation T

end ReactionTranslation

/-- Proper translations are source coherent. -/
theorem IsProperTranslation.sourceCoherent (N : Network S) {τ : N.R → Complex S}
    (h : N.IsProperTranslation τ) : N.TranslationSourceCoherent τ := by
  intro r q hrs
  exact (h r q).2 hrs

/-- The zero translation is proper. -/
theorem zeroTranslation_isProper (N : Network S) :
    N.IsProperTranslation N.zeroTranslation := by
  intro r q
  simp only [translate_zero_reaction]

/-- Transport rate constants to a translated network.  This only reindexes along the
(definitionally identical) reaction-channel type. -/
def RateConstants.translate {N : Network S} (κ : RateConstants N)
    (τ : N.R → Complex S) : RateConstants (N.translate τ) where
  k := κ.k
  positive := κ.positive

@[simp] theorem RateConstants.translate_k {N : Network S} (κ : RateConstants N)
    (τ : N.R → Complex S) (r : N.R) :
    (κ.translate τ).k r = κ.k r := rfl

/-- Generalized mass-action rate on a translated network, using the **original source
complex** as kinetic complex.  This is the kinetic convention underlying network
translation theory. -/
def translatedGeneralizedRate (N : Network S) (τ : N.R → Complex S)
    (κ : RateConstants N) (r : N.R) (x : Concentration S) : ℝ :=
  κ.k r * (N.reaction r).source.massActionMonomial x

/-- Generalized mass-action vector field associated with a reaction-wise translation:
translated reaction vectors, but original source complexes as kinetic complexes. -/
def translatedGeneralizedVectorField (N : Network S) (τ : N.R → Complex S)
    (κ : RateConstants N) (x : Concentration S) : S → ℝ :=
  fun s => ∑ r : N.R, N.translatedGeneralizedRate τ κ r x *
    (N.translate τ).reactionVector r s

/-- **Dynamical equivalence theorem for network translation.**  Keeping the original
source complexes as kinetic complexes makes every reaction-wise translation exactly
dynamically equivalent to the original mass-action system. -/
theorem translatedGeneralizedVectorField_eq_massActionVectorField
    (N : Network S) (τ : N.R → Complex S) (κ : RateConstants N) :
    N.translatedGeneralizedVectorField τ κ = N.massActionVectorField κ := by
  funext x s
  simp only [translatedGeneralizedVectorField, translatedGeneralizedRate,
    massActionVectorField_apply, massActionRate]
  congr 1
  funext r
  rw [N.translate_reactionVector τ r]

end Network
end CRNT
