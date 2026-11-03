import CRNT.Deficiency.DeficiencyOne
import CRNT.Graph.WeakReversibility
import CRNT.Graph.Reversibility
import CRNT.Dynamics.Siphon
import Mathlib.LinearAlgebra.Dimension.Constructions
import CRNT.Decision.StrongLinkage

/-!
# Isomorphisms of chemical reaction networks

CRNT statements should not depend on the chosen names of species or reaction channels.
This module packages simultaneous renaming of species and reactions and records the main
structural invariants.

Parallel reaction channels are preserved because an isomorphism includes an equivalence
of reaction **indices**, not merely an equivalence of directed source/target pairs.
-/

namespace CRNT

namespace Complex

variable {S T : Type}

/-- Rename species coordinates along an equivalence. -/
def rename (e : S ≃ T) (y : Complex S) : Complex T :=
  fun t => y (e.symm t)

@[simp] theorem rename_apply (e : S ≃ T) (y : Complex S) (t : T) :
    rename e y t = y (e.symm t) := rfl

@[simp] theorem rename_refl (y : Complex S) : rename (Equiv.refl S) y = y := by
  rfl

@[simp] theorem rename_trans {U : Type} (e : S ≃ T) (f : T ≃ U) (y : Complex S) :
    rename f (rename e y) = rename (e.trans f) y := by
  rfl

/-- Species renaming is a bijection on complexes. -/
def renameEquiv (e : S ≃ T) : Complex S ≃ Complex T where
  toFun := rename e
  invFun := rename e.symm
  left_inv := by intro y; ext s; simp [rename]
  right_inv := by intro y; ext t; simp [rename]

end Complex

namespace Reaction

variable {S T : Type}

/-- Rename every species in a reaction. -/
def rename (e : S ≃ T) (r : Reaction S) : Reaction T where
  source := Complex.rename e r.source
  target := Complex.rename e r.target

@[simp] theorem rename_source (e : S ≃ T) (r : Reaction S) :
    (rename e r).source = Complex.rename e r.source := rfl

@[simp] theorem rename_target (e : S ≃ T) (r : Reaction S) :
    (rename e r).target = Complex.rename e r.target := rfl

end Reaction

namespace Network

variable {S T : Type} [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]

/-- Isomorphism of reaction networks: a bijection of species, a bijection of reaction
channels, and compatibility of each reaction with the species renaming. -/
structure Isomorphism (N : Network S) (M : Network T) where
  speciesEquiv : S ≃ T
  reactionEquiv : N.R ≃ M.R
  map_reaction : ∀ r : N.R,
    M.reaction (reactionEquiv r) = Reaction.rename speciesEquiv (N.reaction r)

namespace Isomorphism

variable {N : Network S} {M : Network T}

/-- Inverse network isomorphism. -/
def symm (F : N.Isomorphism M) : M.Isomorphism N where
  speciesEquiv := F.speciesEquiv.symm
  reactionEquiv := F.reactionEquiv.symm
  map_reaction := by
    intro q
    obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
    simp only [Equiv.symm_apply_apply]
    rw [F.map_reaction r]
    cases N.reaction r
    simp [Reaction.rename, Complex.rename]

/-- Composition of network isomorphisms. -/
def trans {U : Type} [DecidableEq U] [Fintype U]
    {L : Network U} (F : N.Isomorphism M) (G : M.Isomorphism L) :
    N.Isomorphism L where
  speciesEquiv := F.speciesEquiv.trans G.speciesEquiv
  reactionEquiv := F.reactionEquiv.trans G.reactionEquiv
  map_reaction := by
    intro r
    simp only [Equiv.trans_apply]
    rw [G.map_reaction, F.map_reaction]
    simp [Reaction.rename, Complex.rename]

/-- Coordinate renaming on real species vectors. -/
noncomputable def speciesLinearEquiv (F : N.Isomorphism M) :
    (S → ℝ) ≃ₗ[ℝ] (T → ℝ) where
  toFun := fun x t => x (F.speciesEquiv.symm t)
  invFun := fun y s => y (F.speciesEquiv s)
  left_inv := by intro x; ext s; simp
  right_inv := by intro y; ext t; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Reaction vectors commute with network isomorphism. -/
theorem map_reactionVector (F : N.Isomorphism M) (r : N.R) :
    F.speciesLinearEquiv (N.reactionVector r) =
      M.reactionVector (F.reactionEquiv r) := by
  funext t
  rw [reactionVector_apply, F.map_reaction]
  rfl

/-- The stoichiometric subspaces correspond exactly. -/
theorem map_stoichSubspace (F : N.Isomorphism M) :
    N.stoichSubspace.map F.speciesLinearEquiv.toLinearMap = M.stoichSubspace := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    intro v hv
    rcases hv with ⟨r, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    simpa [F.map_reactionVector r] using
      M.reactionVector_mem_stoichSubspace (F.reactionEquiv r)
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with ⟨q, rfl⟩
    obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
    exact ⟨N.reactionVector r, N.reactionVector_mem_stoichSubspace r,
      F.map_reactionVector r⟩

/-- Stoichiometric rank is an isomorphism invariant. -/
theorem stoichRank_eq (F : N.Isomorphism M) : N.stoichRank = M.stoichRank := by
  rw [Network.stoichRank, Network.stoichRank, ← F.map_stoichSubspace]
  exact (LinearEquiv.finrank_map_eq F.speciesLinearEquiv N.stoichSubspace).symm

/-- Species renaming maps the network complex set bijectively. -/
theorem complex_mem_iff (F : N.Isomorphism M) (y : Complex S) :
    y ∈ N.complexes ↔ Complex.rename F.speciesEquiv y ∈ M.complexes := by
  constructor <;> intro h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_image.mp h with ⟨r, _, rfl⟩
      have hs : Complex.rename F.speciesEquiv (N.reaction r).source
          = (M.reaction (F.reactionEquiv r)).source := by
        rw [F.map_reaction r]
        rfl
      rw [hs]
      exact M.source_mem_complexes (F.reactionEquiv r)
    · rcases Finset.mem_image.mp h with ⟨r, _, rfl⟩
      have ht : Complex.rename F.speciesEquiv (N.reaction r).target
          = (M.reaction (F.reactionEquiv r)).target := by
        rw [F.map_reaction r]
        rfl
      rw [ht]
      exact M.target_mem_complexes (F.reactionEquiv r)
  · -- The old proof invoked `complex_mem_iff` on `F.symm`, i.e. itself; that is circular.
    -- Argue directly instead, using injectivity of `Complex.renameEquiv`.
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_image.mp h with ⟨q, _, hq⟩
      obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
      have hs : Complex.rename F.speciesEquiv (N.reaction r).source
          = (M.reaction (F.reactionEquiv r)).source := by
        rw [F.map_reaction r]
        rfl
      have heq : Complex.rename F.speciesEquiv (N.reaction r).source
          = Complex.rename F.speciesEquiv y := by rw [hs, hq]
      have hy : (N.reaction r).source = y :=
        (Complex.renameEquiv F.speciesEquiv).injective heq
      exact hy ▸ N.source_mem_complexes r
    · rcases Finset.mem_image.mp h with ⟨q, _, hq⟩
      obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
      have ht : Complex.rename F.speciesEquiv (N.reaction r).target
          = (M.reaction (F.reactionEquiv r)).target := by
        rw [F.map_reaction r]
        rfl
      have heq : Complex.rename F.speciesEquiv (N.reaction r).target
          = Complex.rename F.speciesEquiv y := by rw [ht, hq]
      have hy : (N.reaction r).target = y :=
        (Complex.renameEquiv F.speciesEquiv).injective heq
      exact hy ▸ N.target_mem_complexes r

/-- Number of complexes is invariant. -/
theorem numComplexes_eq (F : N.Isomorphism M) : N.numComplexes = M.numComplexes := by
  unfold Network.numComplexes
  exact Finset.card_bijective (Complex.rename F.speciesEquiv)
    (Complex.renameEquiv F.speciesEquiv).bijective
    (fun y => F.complex_mem_iff y)

/-- Number of reaction channels is invariant. -/
theorem numReactions_eq (F : N.Isomorphism M) : N.numReactions = M.numReactions := by
  exact Fintype.card_congr F.reactionEquiv

/-- Directed reaction adjacency is preserved by renaming. -/
theorem directlyReacts_iff (F : N.Isomorphism M) (y z : Complex S) :
    N.DirectlyReacts y z ↔
      M.DirectlyReacts (Complex.rename F.speciesEquiv y)
        (Complex.rename F.speciesEquiv z) := by
  constructor
  · rintro ⟨r, hs, ht⟩
    refine ⟨F.reactionEquiv r, ?_, ?_⟩
    -- after rewriting, the goal is about the *source/target complex* of the renamed
    -- reaction, which is definitionally the renamed complex; `congrArg` bridges it.
    · rw [F.map_reaction]
      exact congrArg (Complex.rename F.speciesEquiv) hs
    · rw [F.map_reaction]
      exact congrArg (Complex.rename F.speciesEquiv) ht
  · rintro ⟨q, hs, ht⟩
    obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
    refine ⟨r, ?_, ?_⟩
    · have := hs
      rw [F.map_reaction] at this
      exact (Complex.renameEquiv F.speciesEquiv).injective this
    · have := ht
      rw [F.map_reaction] at this
      exact (Complex.renameEquiv F.speciesEquiv).injective this

/-- Reachability is preserved by network isomorphism. -/
theorem reaches_iff (F : N.Isomorphism M) (y z : Complex S) :
    N.Reaches y z ↔
      M.Reaches (Complex.rename F.speciesEquiv y)
        (Complex.rename F.speciesEquiv z) := by
  have forward : ∀ {a b : Complex S}, N.Reaches a b →
      M.Reaches (Complex.rename F.speciesEquiv a) (Complex.rename F.speciesEquiv b) := by
    intro a b h
    induction h with
    | refl => exact Network.Reaches.refl M _
    | tail hreach hstep ih =>
        exact Relation.ReflTransGen.tail ih ((F.directlyReacts_iff _ _).mp hstep)
  have backward : ∀ {a b : Complex T}, M.Reaches a b →
      N.Reaches (Complex.rename F.speciesEquiv.symm a)
        (Complex.rename F.speciesEquiv.symm b) := by
    intro a b h
    induction h with
    | refl => exact Network.Reaches.refl N _
    | @tail b c hreach hstep ih =>
        have hstep' : N.DirectlyReacts
            (Complex.rename F.speciesEquiv.symm b)
            (Complex.rename F.speciesEquiv.symm c) := by
          apply (F.directlyReacts_iff _ _).mpr
          simpa [Complex.rename] using hstep
        exact Relation.ReflTransGen.tail ih hstep'
  constructor
  · exact forward
  · intro h
    simpa [Complex.rename] using backward h

/-- Undirected linkage is preserved. -/
theorem linked_iff (F : N.Isomorphism M) (y z : Complex S) :
    N.Linked y z ↔
      M.Linked (Complex.rename F.speciesEquiv y)
        (Complex.rename F.speciesEquiv z) := by
  have edge_forward : ∀ {a b : Complex S}, N.UndirectedEdge a b →
      M.UndirectedEdge (Complex.rename F.speciesEquiv a)
        (Complex.rename F.speciesEquiv b) := by
    intro a b h
    rcases h with h | h
    · exact Or.inl ((F.directlyReacts_iff _ _).mp h)
    · exact Or.inr ((F.directlyReacts_iff _ _).mp h)
  have edge_backward : ∀ {a b : Complex T}, M.UndirectedEdge a b →
      N.UndirectedEdge (Complex.rename F.speciesEquiv.symm a)
        (Complex.rename F.speciesEquiv.symm b) := by
    intro a b h
    rcases h with h | h
    · left
      apply (F.directlyReacts_iff _ _).mpr
      simpa [Complex.rename] using h
    · right
      apply (F.directlyReacts_iff _ _).mpr
      simpa [Complex.rename] using h
  have forward : ∀ {a b : Complex S}, N.Linked a b →
      M.Linked (Complex.rename F.speciesEquiv a)
        (Complex.rename F.speciesEquiv b) := by
    intro a b h
    induction h with
    | refl => exact Network.Linked.refl M _
    | tail hreach hstep ih =>
        exact Relation.ReflTransGen.tail ih (edge_forward hstep)
  have backward : ∀ {a b : Complex T}, M.Linked a b →
      N.Linked (Complex.rename F.speciesEquiv.symm a)
        (Complex.rename F.speciesEquiv.symm b) := by
    intro a b h
    induction h with
    | refl => exact Network.Linked.refl N _
    | tail hreach hstep ih =>
        exact Relation.ReflTransGen.tail ih (edge_backward hstep)
  constructor
  · exact forward
  · intro h
    simpa [Complex.rename] using backward h

/-- Strong linkage is preserved. -/
theorem stronglyLinked_iff (F : N.Isomorphism M) (y z : Complex S) :
    N.StronglyLinked y z ↔
      M.StronglyLinked (Complex.rename F.speciesEquiv y)
        (Complex.rename F.speciesEquiv z) := by
  simp [StronglyLinked, F.reaches_iff]

/-- Linkage-class count is an isomorphism invariant. -/
theorem numLinkageClasses_eq (F : N.Isomorphism M) :
    N.numLinkageClasses = M.numLinkageClasses := by
  let E : {c : Complex S // c ∈ N.complexes} ≃ {c : Complex T // c ∈ M.complexes} := {
    toFun := fun c => ⟨Complex.rename F.speciesEquiv c.1,
      (F.complex_mem_iff c.1).mp c.2⟩
    invFun := fun c => ⟨Complex.rename F.speciesEquiv.symm c.1, by
      have hm : Complex.rename F.speciesEquiv
          (Complex.rename F.speciesEquiv.symm c.1) ∈ M.complexes := by
        simpa [Complex.rename] using c.2
      exact (F.complex_mem_iff _).mpr hm⟩
    left_inv := by intro c; apply Subtype.ext; simp [Complex.rename]
    right_inv := by intro c; apply Subtype.ext; simp [Complex.rename] }
  let f : Quotient N.linkedSetoid → Quotient M.linkedSetoid :=
    Quotient.map E (by
      intro a b hab
      exact (F.linked_iff a.1 b.1).mp hab)
  let g : Quotient M.linkedSetoid → Quotient N.linkedSetoid :=
    Quotient.map E.symm (by
      intro a b hab
      change M.Linked a.1 b.1 at hab
      have h := (F.linked_iff (E.symm a).1 (E.symm b).1).mpr ?_
      · exact h
      · simpa [E, Complex.rename] using hab)
  have hfg : Function.LeftInverse g f := by
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    apply Quotient.sound
    change N.Linked (E.symm (E a)).1 a.1
    simpa [E, Complex.rename] using Network.Linked.refl N a.1
  have hgf : Function.RightInverse g f := by
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    apply Quotient.sound
    change M.Linked (E (E.symm a)).1 a.1
    simpa [E, Complex.rename] using Network.Linked.refl M a.1
  unfold Network.numLinkageClasses
  exact Nat.card_congr { toFun := f, invFun := g, left_inv := hfg, right_inv := hgf }

/-- Deficiency is invariant under network isomorphism. -/
theorem deficiency_eq (F : N.Isomorphism M) : N.deficiency = M.deficiency := by
  have hn := F.numComplexes_eq
  have hl := F.numLinkageClasses_eq
  have hs := F.stoichRank_eq
  have hN := N.numComplexes_eq_add
  have hM := M.numComplexes_eq_add
  omega

/-- Deficiency zero is invariant. -/
theorem deficiencyZero_iff (F : N.Isomorphism M) :
    N.DeficiencyZero ↔ M.DeficiencyZero := by
  rw [N.deficiencyZero_iff_deficiency_eq_zero,
    M.deficiencyZero_iff_deficiency_eq_zero, F.deficiency_eq]

/-- Weak reversibility is invariant. -/
theorem weaklyReversible_iff (F : N.Isomorphism M) :
    N.WeaklyReversible ↔ M.WeaklyReversible := by
  constructor
  · intro h q
    obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
    have hr := (F.reaches_iff (N.reaction r).target (N.reaction r).source).mp (h r)
    rw [F.map_reaction r]
    exact hr
  · intro h r
    have hr := h (F.reactionEquiv r)
    rw [F.map_reaction r] at hr
    exact (F.reaches_iff (N.reaction r).target (N.reaction r).source).mpr hr

/-- Reversibility is invariant. -/
theorem reversible_iff (F : N.Isomorphism M) :
    N.Reversible ↔ M.Reversible := by
  rw [N.reversible_iff_directlyReacts_symm, M.reversible_iff_directlyReacts_symm]
  constructor
  · intro h c d hcd
    let c' := Complex.rename F.speciesEquiv.symm c
    let d' := Complex.rename F.speciesEquiv.symm d
    have hcd' : N.DirectlyReacts c' d' := by
      apply (F.directlyReacts_iff c' d').mpr
      simpa [c', d', Complex.rename] using hcd
    have hdc' := h hcd'
    have := (F.directlyReacts_iff d' c').mp hdc'
    simpa [c', d', Complex.rename] using this
  · intro h c d hcd
    have hm := (F.directlyReacts_iff c d).mp hcd
    have hrev := h hm
    exact (F.directlyReacts_iff d c).mpr hrev

end Isomorphism

end Network
end CRNT
