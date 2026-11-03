import CRNT.Oscillation.StructuralCore

/-!
# Search-friendly indexed child selections

`Network.ChildSelection` is the natural theorem-facing object: two finite subsets plus an explicit
bijection.  For exhaustive search on a finite CRN, however, it is simpler to enumerate an index set
`I` and two injective maps

`species : I -> S`, `reaction : I -> N.R`,

with the reactant condition checked pointwise.  This file supplies that representation and lifts the
same unstable/core/oscillatory predicates to its square stoichiometric matrix.

The intended executable search enumerates `I = Fin k` for `1 <= k <= min |S| |R|`; Lean then checks
or consumes proof-carrying witnesses without having to synthesize a finset equivalence first.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Search-friendly child selection indexed by an arbitrary finite type `I`. -/
structure IndexedChildSelection (N : Network S) (I : Type)
    [DecidableEq I] [Fintype I] where
  species : I → S
  reaction : I → N.R
  species_injective : Function.Injective species
  reaction_injective : Function.Injective reaction
  reactant : ∀ i : I, 0 < (N.reaction (reaction i)).source (species i)

namespace IndexedChildSelection

variable {N : Network S} {I : Type} [DecidableEq I] [Fintype I]

/-- Square stoichiometric matrix associated with an indexed child selection. -/
def matrix (C : N.IndexedChildSelection I) : Matrix I I ℝ :=
  fun i j => N.reactionVector (C.reaction j) (C.species i)

end IndexedChildSelection

variable {N : Network S}

/-! `ChildSelection.Idx` is already defined in `CRNT/Oscillation/StructuralCore.lean`; only the
instances it needs for `IndexedChildSelection` were missing. -/

instance (C : N.ChildSelection) : DecidableEq C.Idx :=
  fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm

instance (C : N.ChildSelection) : Fintype C.Idx := FinsetCoe.fintype C.species

/-- Every theorem-facing `ChildSelection` has a definitionally equivalent indexed presentation,
using its selected-species subtype as the index type.  This is the bridge from the existing
structural theory to the search-friendly API. -/
def ChildSelection.toIndexed (C : N.ChildSelection) :
    N.IndexedChildSelection C.Idx where
  species := fun i => i.1
  reaction := fun i => (C.pairing i).1
  species_injective := Subtype.val_injective
  reaction_injective := fun _ _ hij => C.pairing.injective (Subtype.ext hij)
  reactant := C.reactant

/-- Converting an existing child selection to the indexed representation does not change its
child-selection matrix. -/
@[simp] theorem ChildSelection.toIndexed_matrix (C : N.ChildSelection) :
    C.toIndexed.matrix = C.matrix := by
  rfl

namespace IndexedChildSelection

variable {I : Type} [DecidableEq I] [Fintype I]


/-- An indexed child selection cannot contain more selected species than the ambient CRN. -/
theorem card_le_species (C : N.IndexedChildSelection I) :
    Fintype.card I ≤ Fintype.card S :=
  Fintype.card_le_of_injective C.species C.species_injective

/-- An indexed child selection cannot contain more selected reactions than the ambient CRN. -/
theorem card_le_reactions (C : N.IndexedChildSelection I) :
    Fintype.card I ≤ Fintype.card N.R :=
  Fintype.card_le_of_injective C.reaction C.reaction_injective

/-- Hence exhaustive indexed-core search only needs sizes up to the smaller ambient cardinality. -/
theorem card_le_min (C : N.IndexedChildSelection I) :
    Fintype.card I ≤ min (Fintype.card S) (Fintype.card N.R) := by
  exact le_min C.card_le_species C.card_le_reactions

/-- Strict Hurwitz instability of the indexed child-selection matrix. -/
def IsUnstable (C : N.IndexedChildSelection I) : Prop :=
  C.matrix.HasUnstableEigenvalue

/-- Hurwitz stability. -/
def IsStable (C : N.IndexedChildSelection I) : Prop :=
  C.matrix.IsHurwitzReal

/-- Minimal unstable core. -/
def IsUnstableCore (C : N.IndexedChildSelection I) : Prop :=
  C.matrix.IsUnstableCore

/-- Exact class-I oscillatory core predicate. -/
def IsOscillatoryCoreClassI (C : N.IndexedChildSelection I) : Prop :=
  C.matrix.IsOscillatoryCoreClassI

/-- Exact class-II oscillatory core predicate. -/
def IsOscillatoryCoreClassII (C : N.IndexedChildSelection I) : Prop :=
  C.matrix.IsOscillatoryCoreClassII

/-- An indexed selection is an oscillatory core of either exact class. -/
def IsOscillatoryCore (C : N.IndexedChildSelection I) : Prop :=
  C.IsOscillatoryCoreClassI ∨ C.IsOscillatoryCoreClassII

/-- Reindexing an indexed child selection along an equivalence preserves all CRN semantics. -/
def reindex {J : Type} [DecidableEq J] [Fintype J]
    (C : N.IndexedChildSelection I) (e : J ≃ I) : N.IndexedChildSelection J where
  species := C.species ∘ e
  reaction := C.reaction ∘ e
  species_injective := C.species_injective.comp e.injective
  reaction_injective := C.reaction_injective.comp e.injective
  reactant := fun j => C.reactant (e j)

/-- Matrix under reindexing is the corresponding simultaneous row/column submatrix permutation. -/
theorem matrix_reindex {J : Type} [DecidableEq J] [Fintype J]
    (C : N.IndexedChildSelection I) (e : J ≃ I) :
    (C.reindex e).matrix = C.matrix.submatrix e e := by
  ext i j
  rfl

/-- Restrict an indexed child selection to a finite subset of its selected indices. -/
def restrict (C : N.IndexedChildSelection I) (J : Finset I) :
    N.IndexedChildSelection {i : I // i ∈ J} where
  species := fun i => C.species i.1
  reaction := fun i => C.reaction i.1
  species_injective := C.species_injective.comp Subtype.val_injective
  reaction_injective := C.reaction_injective.comp Subtype.val_injective
  reactant := fun i => C.reactant i.1

/-- Restriction gives exactly the corresponding principal child-selection matrix. -/
theorem matrix_restrict (C : N.IndexedChildSelection I) (J : Finset I) :
    (C.restrict J).matrix = C.matrix.principalSubmatrix J := by
  ext i j
  rfl

end IndexedChildSelection

/-- A finite-search witness for an exact class-I oscillatory core. -/
structure IndexedOscillatoryCoreClassICertificate (N : Network S) : Type where
  k : ℕ
  positiveSize : 0 < k
  selection : N.IndexedChildSelection (Fin k)
  isClassI : selection.IsOscillatoryCoreClassI

/-- A finite-search witness for an exact class-II oscillatory core. -/
structure IndexedOscillatoryCoreClassIICertificate (N : Network S) : Type where
  k : ℕ
  positiveSize : 0 < k
  selection : N.IndexedChildSelection (Fin k)
  isClassII : selection.IsOscillatoryCoreClassII

/-- Search-facing disjunction of the two exact structural core classes. -/
def HasIndexedOscillatoryCore (N : Network S) : Prop :=
  Nonempty (IndexedOscillatoryCoreClassICertificate N) ∨
    Nonempty (IndexedOscillatoryCoreClassIICertificate N)

/-- Class-I search witnesses automatically satisfy the finite exhaustive-search size bound. -/
theorem IndexedOscillatoryCoreClassICertificate.size_le
    {N : Network S} (C : IndexedOscillatoryCoreClassICertificate N) :
    C.k ≤ min (Fintype.card S) (Fintype.card N.R) := by
  simpa using C.selection.card_le_min

/-- Class-II search witnesses automatically satisfy the same finite exhaustive-search size bound. -/
theorem IndexedOscillatoryCoreClassIICertificate.size_le
    {N : Network S} (C : IndexedOscillatoryCoreClassIICertificate N) :
    C.k ≤ min (Fintype.card S) (Fintype.card N.R) := by
  simpa using C.selection.card_le_min

/-- Any theorem realizing indexed oscillatory cores under parameter-rich kinetics can be consumed
without first converting the search witness into the finset/equivalence representation. -/
def IndexedParameterRichOscillatoryCoreRealizationTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T)
    (F : N.SteadyStateParameterRichFamily),
    N.SupportsSmoothReactivityPaths F →
    N.IsConsistent → N.IsSymbolicallyNondegenerate →
    N.HasIndexedOscillatoryCore → N.ParameterRichOscillatoryCapacity F

/-- Consume an indexed class-I witness. -/
theorem IndexedOscillatoryCoreClassICertificate.parameterRichOscillatoryCapacity
    {N : Network S} (hRealize : IndexedParameterRichOscillatoryCoreRealizationTarget)
    (F : N.SteadyStateParameterRichFamily) (hpaths : N.SupportsSmoothReactivityPaths F)
    (hcons : N.IsConsistent) (hnd : N.IsSymbolicallyNondegenerate)
    (C : IndexedOscillatoryCoreClassICertificate N) :
    N.ParameterRichOscillatoryCapacity F :=
  hRealize N F hpaths hcons hnd (Or.inl ⟨C⟩)

/-- Consume an indexed class-II witness. -/
theorem IndexedOscillatoryCoreClassIICertificate.parameterRichOscillatoryCapacity
    {N : Network S} (hRealize : IndexedParameterRichOscillatoryCoreRealizationTarget)
    (F : N.SteadyStateParameterRichFamily) (hpaths : N.SupportsSmoothReactivityPaths F)
    (hcons : N.IsConsistent) (hnd : N.IsSymbolicallyNondegenerate)
    (C : IndexedOscillatoryCoreClassIICertificate N) :
    N.ParameterRichOscillatoryCapacity F :=
  hRealize N F hpaths hcons hnd (Or.inr ⟨C⟩)

end Network

end CRNT
