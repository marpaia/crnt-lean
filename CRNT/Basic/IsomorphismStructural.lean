import CRNT.Basic.IsomorphismKinetics
import CRNT.Dynamics.Trap
import CRNT.Flux.PSemiflow
import CRNT.Flux.Cone
import CRNT.Multistationarity.Normality
import CRNT.Multistationarity.WeakNormality
import CRNT.Multistationarity.StrongConcordance

/-!
# Structural CRNT invariants under network isomorphism

Species/reaction names carry no mathematics.  This file transports several
higher-level structural notions across `Network.Isomorphism`: siphons and traps,
conservation laws and conservativity, consistency, normality/weak normality, and
concordance/strong concordance.
-/

namespace CRNT
namespace Network
namespace Isomorphism

variable {S T : Type} [DecidableEq S] [Fintype S]
  [DecidableEq T] [Fintype T]
variable {N : Network S} {M : Network T}

/-- Rename a finite species set. -/
def mapSpeciesFinset (F : N.Isomorphism M) (P : Finset S) : Finset T :=
  P.map F.speciesEquiv.toEmbedding

@[simp] theorem mem_mapSpeciesFinset (F : N.Isomorphism M)
    (P : Finset S) (t : T) :
    t ∈ F.mapSpeciesFinset P ↔ F.speciesEquiv.symm t ∈ P := by
  simp [mapSpeciesFinset]

/-- Reactant incidence is preserved. -/
theorem isReactant_iff (F : N.Isomorphism M) (r : N.R) (s : S) :
    N.IsReactant r s ↔ M.IsReactant (F.reactionEquiv r) (F.speciesEquiv s) := by
  rw [IsReactant, IsReactant, F.map_reaction]
  simp [Reaction.rename, Complex.rename]

/-- Product incidence is preserved. -/
theorem isProduct_iff (F : N.Isomorphism M) (r : N.R) (s : S) :
    N.IsProduct r s ↔ M.IsProduct (F.reactionEquiv r) (F.speciesEquiv s) := by
  rw [IsProduct, IsProduct, F.map_reaction]
  simp [Reaction.rename, Complex.rename]

/-- Renaming a species lands in the renamed set exactly when the original was in it. -/
@[simp] theorem mem_mapSpeciesFinset_apply (F : N.Isomorphism M) (P : Finset S) (s : S) :
    F.speciesEquiv s ∈ F.mapSpeciesFinset P ↔ s ∈ P := by
  simp [mapSpeciesFinset]

/-- The inverse isomorphism undoes the species-set renaming. -/
@[simp] theorem symm_mapSpeciesFinset (F : N.Isomorphism M) (P : Finset S) :
    F.symm.mapSpeciesFinset (F.mapSpeciesFinset P) = P := by
  ext s
  simp [mapSpeciesFinset, Isomorphism.symm]

/-- One direction of siphon invariance.  The `iff` then follows by applying this to
`F.symm`, which halves the work and keeps both directions in step. -/
theorem isSiphon_map (F : N.Isomorphism M) {P : Finset S} (h : N.IsSiphon P) :
    M.IsSiphon (F.mapSpeciesFinset P) := by
  intro q hq
  obtain ⟨t, ht, hprod⟩ := hq
  obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
  obtain ⟨s, rfl⟩ := F.speciesEquiv.surjective t
  rw [mem_mapSpeciesFinset_apply] at ht
  obtain ⟨s', hs', hreact⟩ := h r ⟨s, ht, (F.isProduct_iff r s).2 hprod⟩
  exact ⟨F.speciesEquiv s', by simpa using hs', (F.isReactant_iff r s').1 hreact⟩

/-- Siphons are invariant under relabeling. -/
theorem isSiphon_iff (F : N.Isomorphism M) (P : Finset S) :
    N.IsSiphon P ↔ M.IsSiphon (F.mapSpeciesFinset P) :=
  ⟨fun h => F.isSiphon_map h, fun h => by simpa using F.symm.isSiphon_map h⟩

/-- One direction of trap invariance. -/
theorem isTrap_map (F : N.Isomorphism M) {P : Finset S} (h : N.IsTrap P) :
    M.IsTrap (F.mapSpeciesFinset P) := by
  intro q hq
  obtain ⟨t, ht, hreact⟩ := hq
  obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
  obtain ⟨s, rfl⟩ := F.speciesEquiv.surjective t
  rw [mem_mapSpeciesFinset_apply] at ht
  obtain ⟨s', hs', hprod⟩ := h r ⟨s, ht, (F.isReactant_iff r s).2 hreact⟩
  exact ⟨F.speciesEquiv s', by simpa using hs', (F.isProduct_iff r s').1 hprod⟩

/-- Traps are invariant under relabeling. -/
theorem isTrap_iff (F : N.Isomorphism M) (P : Finset S) :
    N.IsTrap P ↔ M.IsTrap (F.mapSpeciesFinset P) :=
  ⟨fun h => F.isTrap_map h, fun h => by simpa using F.symm.isTrap_map h⟩

/-- The species-set renaming is monotone and injective, and `F.symm` inverts it. -/
@[simp] theorem mapSpeciesFinset_subset (F : N.Isomorphism M) (P Q : Finset S) :
    F.mapSpeciesFinset P ⊆ F.mapSpeciesFinset Q ↔ P ⊆ Q := by
  simp only [mapSpeciesFinset, Finset.subset_iff, Finset.mem_map]
  constructor
  · intro h s hs
    obtain ⟨s', hs', he⟩ := h ⟨s, hs, rfl⟩
    exact (F.speciesEquiv.injective he) ▸ hs'
  · rintro h t ⟨s, hs, rfl⟩
    exact ⟨s, h hs, rfl⟩

@[simp] theorem mapSpeciesFinset_nonempty (F : N.Isomorphism M) (P : Finset S) :
    (F.mapSpeciesFinset P).Nonempty ↔ P.Nonempty := by
  simp [mapSpeciesFinset, Finset.map_nonempty]

@[simp] theorem mapSpeciesFinset_inj (F : N.Isomorphism M) (P Q : Finset S) :
    F.mapSpeciesFinset P = F.mapSpeciesFinset Q ↔ P = Q := by
  simp [mapSpeciesFinset, Finset.map_inj]

/-- One direction of minimal-siphon invariance.  Every candidate strict subset of the
renamed set is the renaming of a candidate strict subset upstairs. -/
theorem isMinimalSiphon_map (F : N.Isomorphism M) {P : Finset S}
    (h : N.IsMinimalSiphon P) : M.IsMinimalSiphon (F.mapSpeciesFinset P) := by
  obtain ⟨hne, hsi, hmin⟩ := h
  refine ⟨by simpa using hne, F.isSiphon_map hsi, ?_⟩
  intro Q hQ hQne hQne'
  rw [Finset.mem_powerset] at hQ
  -- pull `Q` back along `F.symm`
  set Q' := F.symm.mapSpeciesFinset Q with hQ'
  have hback : F.mapSpeciesFinset Q' = Q := by
    ext t; simp [hQ', mapSpeciesFinset, Isomorphism.symm]
  have hsub : Q' ⊆ P := by
    rw [← F.mapSpeciesFinset_subset Q' P, hback]; exact hQ
  have hne2 : Q'.Nonempty := by
    rw [← F.mapSpeciesFinset_nonempty Q', hback]; exact hQne
  have hne3 : Q' ≠ P := by
    intro hEq
    exact hQne' (by rw [← hback, hEq])
  intro hMQ
  exact hmin Q' (Finset.mem_powerset.mpr hsub) hne2 hne3
    ((F.isSiphon_iff Q').2 (by rw [hback]; exact hMQ))

/-- Minimal siphons transport to minimal siphons. -/
theorem isMinimalSiphon_iff (F : N.Isomorphism M) (P : Finset S) :
    N.IsMinimalSiphon P ↔ M.IsMinimalSiphon (F.mapSpeciesFinset P) :=
  ⟨fun h => F.isMinimalSiphon_map h, fun h => by simpa using F.symm.isMinimalSiphon_map h⟩

/-- Conservation-law vectors transport contragrediently with species renaming. -/
noncomputable def mapSpeciesCovector (F : N.Isomorphism M) (w : S → ℝ) : T → ℝ :=
  fun t => w (F.speciesEquiv.symm t)

/-- `mapSpeciesCovector` is exactly the action of `speciesLinearEquiv`. -/
theorem mapSpeciesCovector_eq (F : N.Isomorphism M) (w : S → ℝ) :
    F.mapSpeciesCovector w = F.speciesLinearEquiv w := rfl

/-- The inverse isomorphism undoes the covector renaming. -/
@[simp] theorem symm_mapSpeciesCovector (F : N.Isomorphism M) (w : S → ℝ) :
    F.symm.mapSpeciesCovector (F.mapSpeciesCovector w) = w := by
  funext s
  simp [mapSpeciesCovector, Isomorphism.symm]

/-- One direction of conservation-law invariance. -/
theorem conservationLaw_map (F : N.Isomorphism M) {w : S → ℝ}
    (h : ∀ r : N.R, ∑ s : S, w s * N.reactionVector r s = 0) :
    ∀ q : M.R, ∑ t : T, F.mapSpeciesCovector w t * M.reactionVector q t = 0 := by
  intro q
  obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
  rw [← F.map_reactionVector r]
  have hsum : ∑ t : T, F.mapSpeciesCovector w t *
      F.speciesLinearEquiv (N.reactionVector r) t
      = ∑ s : S, w s * N.reactionVector r s := by
    rw [← F.speciesEquiv.sum_comp (fun t => F.mapSpeciesCovector w t *
      F.speciesLinearEquiv (N.reactionVector r) t)]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [mapSpeciesCovector, speciesLinearEquiv]
  rw [hsum, h r]

/-- Orthogonality to every reaction vector is invariant. -/
theorem conservationLaw_iff (F : N.Isomorphism M) (w : S → ℝ) :
    (∀ r : N.R, ∑ s : S, w s * N.reactionVector r s = 0) ↔
    (∀ q : M.R, ∑ t : T, F.mapSpeciesCovector w t * M.reactionVector q t = 0) :=
  ⟨fun h => F.conservationLaw_map h,
   fun h => by simpa using F.symm.conservationLaw_map h⟩

/-- P-invariance transports: a renamed covector still annihilates the renamed
stoichiometric subspace. -/
theorem isPInvariant_map (F : N.Isomorphism M) {w : S → ℝ} (h : N.IsPInvariant w) :
    M.IsPInvariant (F.mapSpeciesCovector w) := by
  rw [IsPInvariant, mem_orthSum]
  intro v hv
  -- every stoichiometric vector downstairs is the renaming of one upstairs
  rw [← F.map_stoichSubspace] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  have : ∑ t : T, F.mapSpeciesCovector w t * F.speciesLinearEquiv.toLinearMap u t
      = ∑ s : S, w s * u s := by
    rw [← F.speciesEquiv.sum_comp (fun t => F.mapSpeciesCovector w t *
      F.speciesLinearEquiv.toLinearMap u t)]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [mapSpeciesCovector, speciesLinearEquiv]
  rw [this]
  exact (mem_orthSum.mp h) u hu

/-- One direction of conservativity invariance. -/
theorem isConservative_map (F : N.Isomorphism M) (h : N.IsConservative) :
    M.IsConservative := by
  obtain ⟨w, hinv, hpos⟩ := h
  refine ⟨F.mapSpeciesCovector w, F.isPInvariant_map hinv, fun t => ?_⟩
  obtain ⟨s, rfl⟩ := F.speciesEquiv.surjective t
  simpa [mapSpeciesCovector] using hpos s

/-- Strict conservativity is invariant. -/
theorem conservative_iff (F : N.Isomorphism M) :
    N.IsConservative ↔ M.IsConservative :=
  ⟨F.isConservative_map, F.symm.isConservative_map⟩

/-- One direction of consistency invariance: push a strictly positive flux forward along
`reactionEquiv`, using that `speciesLinearEquiv` is linear and carries reaction vectors to
reaction vectors. -/
theorem isConsistent_map (F : N.Isomorphism M) (h : N.IsConsistent) : M.IsConsistent := by
  obtain ⟨α, hpos, hsum⟩ := h
  refine ⟨fun q => α (F.reactionEquiv.symm q), fun q => hpos _, ?_⟩
  have : ∑ q : M.R, α (F.reactionEquiv.symm q) • M.reactionVector q
      = ∑ r : N.R, α r • M.reactionVector (F.reactionEquiv r) := by
    exact (F.reactionEquiv.sum_comp
      (fun q => α (F.reactionEquiv.symm q) • M.reactionVector q)).symm.trans
      (by refine Finset.sum_congr rfl fun r _ => ?_; simp)
  rw [this]
  have hmap : ∑ r : N.R, α r • M.reactionVector (F.reactionEquiv r)
      = F.speciesLinearEquiv (∑ r : N.R, α r • N.reactionVector r) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, F.map_reactionVector r]
  rw [hmap, hsum, map_zero]

/-- Stationary-flux consistency is invariant. -/
theorem consistent_iff (F : N.Isomorphism M) :
    N.IsConsistent ↔ M.IsConsistent :=
  ⟨F.isConsistent_map, F.symm.isConsistent_map⟩

/-- Kernel membership of a flux vector transports along `reactionEquiv`. -/
theorem inKerL_map (F : N.Isomorphism M) {α : N.R → ℝ} (h : N.InKerL α) :
    M.InKerL (fun q => α (F.reactionEquiv.symm q)) := by
  have hre : ∑ q : M.R, α (F.reactionEquiv.symm q) • M.reactionVector q
      = ∑ r : N.R, α r • M.reactionVector (F.reactionEquiv r) := by
    exact (F.reactionEquiv.sum_comp
      (fun q => α (F.reactionEquiv.symm q) • M.reactionVector q)).symm.trans
      (by refine Finset.sum_congr rfl fun r _ => ?_; simp)
  have hmap : ∑ r : N.R, α r • M.reactionVector (F.reactionEquiv r)
      = F.speciesLinearEquiv (∑ r : N.R, α r • N.reactionVector r) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, F.map_reactionVector r]
  rw [InKerL, hre, hmap, h, map_zero]

/-- A stoichiometric vector renames to a stoichiometric vector. -/
theorem mem_stoichSubspace_map (F : N.Isomorphism M) {σ : S → ℝ}
    (h : σ ∈ N.stoichSubspace) : F.mapSpeciesCovector σ ∈ M.stoichSubspace := by
  rw [← F.map_stoichSubspace]
  exact Submodule.mem_map_of_mem h

/-- Renaming a nonzero covector gives a nonzero covector. -/
theorem mapSpeciesCovector_ne_zero (F : N.Isomorphism M) {σ : S → ℝ} (h : σ ≠ 0) :
    F.mapSpeciesCovector σ ≠ 0 := by
  intro hz
  apply h
  funext s
  have := congrFun hz (F.speciesEquiv s)
  simpa [mapSpeciesCovector] using this

@[simp] theorem mapSpeciesCovector_apply (F : N.Isomorphism M) (σ : S → ℝ) (s : S) :
    F.mapSpeciesCovector σ (F.speciesEquiv s) = σ s := by
  simp [mapSpeciesCovector]

/-- A concordance witness renames to a concordance witness. -/
theorem concordanceWitness_map (F : N.Isomorphism M) {α : N.R → ℝ} {σ : S → ℝ}
    (h : N.ConcordanceWitness α σ) :
    M.ConcordanceWitness (fun q => α (F.reactionEquiv.symm q)) (F.mapSpeciesCovector σ) where
  mem_kerL := F.inKerL_map h.mem_kerL
  mem_stoich := F.mem_stoichSubspace_map h.mem_stoich
  sigma_ne := F.mapSpeciesCovector_ne_zero h.sigma_ne
  sign_match := by
    intro q hq
    obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
    simp only [Equiv.symm_apply_apply] at hq
    obtain ⟨s, hs, hsign⟩ := h.sign_match r hq
    exact ⟨F.speciesEquiv s, (F.isReactant_iff r s).1 hs, by simpa using hsign⟩
  sign_balance := by
    intro q hq
    obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
    simp only [Equiv.symm_apply_apply] at hq
    rcases h.sign_balance r hq with hzero | ⟨s, s', hs, hs', hneg, hpos⟩
    · refine Or.inl fun t ht => ?_
      obtain ⟨u, rfl⟩ := F.speciesEquiv.surjective t
      simpa using hzero u ((F.isReactant_iff r u).2 ht)
    · exact Or.inr ⟨F.speciesEquiv s, F.speciesEquiv s',
        (F.isReactant_iff r s).1 hs, (F.isReactant_iff r s').1 hs',
        by simpa using hneg, by simpa using hpos⟩

/-- Renamed positive species weights. -/
def mapSpeciesWeights (F : N.Isomorphism M) (q : PositiveSpeciesWeights S) :
    PositiveSpeciesWeights T where
  weight := fun t => q.weight (F.speciesEquiv.symm t)
  positive := fun t => q.positive _

/-- Renamed positive reaction weights. -/
def mapReactionWeights (F : N.Isomorphism M) (η : PositiveReactionWeights N) :
    PositiveReactionWeights M where
  weight := fun q => η.weight (F.reactionEquiv.symm q)
  positive := fun q => η.positive _

/-- A stoichiometric vector downstairs pulls back to one upstairs. -/
theorem symm_mem_stoichSubspace (F : N.Isomorphism M) {v : T → ℝ}
    (h : v ∈ M.stoichSubspace) : F.speciesLinearEquiv.symm v ∈ N.stoichSubspace := by
  rw [← F.map_stoichSubspace] at h
  obtain ⟨u, hu, rfl⟩ := h
  simpa using hu

/-- The weighted complex pairing is a renaming invariant. -/
theorem weightedComplexPairing_map (F : N.Isomorphism M) (q : PositiveSpeciesWeights S)
    (r : N.R) (σ : S → ℝ) :
    weightedComplexPairing (F.mapSpeciesWeights q)
        (M.reaction (F.reactionEquiv r)).source (F.mapSpeciesCovector σ)
      = weightedComplexPairing q (N.reaction r).source σ := by
  simp only [weightedComplexPairing]
  rw [← F.speciesEquiv.sum_comp (fun t => (F.mapSpeciesWeights q).weight t *
    ((M.reaction (F.reactionEquiv r)).source t : ℝ) * F.mapSpeciesCovector σ t)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [mapSpeciesWeights, mapSpeciesCovector, F.map_reaction, Reaction.rename,
    Complex.rename]

/-- **Conjugation identity for the normality operator.**  Renaming the weights and
renaming the input agree: `F ∘ T_N = T_M ∘ F`.  This is what makes injectivity transport. -/
theorem normalityOperator_map (F : N.Isomorphism M) (q : PositiveSpeciesWeights S)
    (η : PositiveReactionWeights N) (σ : S → ℝ) :
    M.normalityOperator (F.mapSpeciesWeights q) (F.mapReactionWeights η)
        (F.mapSpeciesCovector σ)
      = F.speciesLinearEquiv (N.normalityOperator q η σ) := by
  show ∑ p : M.R, ((F.mapReactionWeights η).weight p *
      weightedComplexPairing (F.mapSpeciesWeights q) (M.reaction p).source
        (F.mapSpeciesCovector σ)) • M.reactionVector p
    = F.speciesLinearEquiv (∑ r : N.R,
        (η.weight r * weightedComplexPairing q (N.reaction r).source σ) •
          N.reactionVector r)
  rw [map_sum]
  rw [← F.reactionEquiv.sum_comp (fun p => ((F.mapReactionWeights η).weight p *
    weightedComplexPairing (F.mapSpeciesWeights q) (M.reaction p).source
      (F.mapSpeciesCovector σ)) • M.reactionVector p)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, F.map_reactionVector r, F.weightedComplexPairing_map q r σ]
  simp [mapReactionWeights]

/-- A normality witness renames to a normality witness. -/
noncomputable def normalWitness_map (F : N.Isomorphism M) (W : N.NormalWitness) :
    M.NormalWitness where
  speciesWeights := F.mapSpeciesWeights W.speciesWeights
  reactionWeights := F.mapReactionWeights W.reactionWeights
  nonsingular := by
    intro x y hxy
    have hx := F.symm_mem_stoichSubspace x.2
    have hy := F.symm_mem_stoichSubspace y.2
    -- read `hxy` as an ambient equality, then conjugate it back to `N`
    have hamb : M.normalityOperator (F.mapSpeciesWeights W.speciesWeights)
          (F.mapReactionWeights W.reactionWeights) (x : T → ℝ)
        = M.normalityOperator (F.mapSpeciesWeights W.speciesWeights)
          (F.mapReactionWeights W.reactionWeights) (y : T → ℝ) :=
      congrArg Subtype.val hxy
    have hxv : (x : T → ℝ) = F.mapSpeciesCovector (F.speciesLinearEquiv.symm x) := by
      funext t; simp [mapSpeciesCovector, speciesLinearEquiv]
    have hyv : (y : T → ℝ) = F.mapSpeciesCovector (F.speciesLinearEquiv.symm y) := by
      funext t; simp [mapSpeciesCovector, speciesLinearEquiv]
    rw [hxv, hyv, F.normalityOperator_map, F.normalityOperator_map] at hamb
    have hN := W.nonsingular (a₁ := ⟨F.speciesLinearEquiv.symm x, hx⟩)
      (a₂ := ⟨F.speciesLinearEquiv.symm y, hy⟩)
      (Subtype.ext (F.speciesLinearEquiv.injective hamb))
    exact Subtype.ext (F.speciesLinearEquiv.symm.injective (congrArg Subtype.val hN))

/-- Normality is invariant under species/reaction relabeling. -/
theorem normal_iff (F : N.Isomorphism M) : N.Normal ↔ M.Normal :=
  ⟨fun ⟨W⟩ => ⟨F.normalWitness_map W⟩, fun ⟨W⟩ => ⟨F.symm.normalWitness_map W⟩⟩

/-- Concordance is invariant. -/
theorem concordant_iff (F : N.Isomorphism M) :
    N.Concordant ↔ M.Concordant := by
  constructor
  · intro hN ⟨α, σ, hw⟩
    exact hN ⟨_, _, F.symm.concordanceWitness_map hw⟩
  · intro hM ⟨α, σ, hw⟩
    exact hM ⟨_, _, F.concordanceWitness_map hw⟩

/-- The reaction direction sign is a renaming invariant. -/
@[simp] theorem reactionDirectionSign_map (F : N.Isomorphism M) (r : N.R) (s : S) :
    M.reactionDirectionSign (F.reactionEquiv r) (F.speciesEquiv s)
      = N.reactionDirectionSign r s := by
  simp [reactionDirectionSign, F.map_reaction, Reaction.rename, Complex.rename]

/-- `Promotes` is a renaming invariant. -/
theorem promotes_map (F : N.Isomorphism M) {r : N.R} {σ : S → ℝ} {s : S}
    (h : N.Promotes r σ s) :
    M.Promotes (F.reactionEquiv r) (F.mapSpeciesCovector σ) (F.speciesEquiv s) := by
  obtain ⟨hsign, hne⟩ := h
  exact ⟨by simpa [mapSpeciesCovector] using hsign, by simpa using hne⟩

/-- `Opposes` is a renaming invariant. -/
theorem opposes_map (F : N.Isomorphism M) {r : N.R} {σ : S → ℝ} {s : S}
    (h : N.Opposes r σ s) :
    M.Opposes (F.reactionEquiv r) (F.mapSpeciesCovector σ) (F.speciesEquiv s) := by
  obtain ⟨hsign, hne⟩ := h
  exact ⟨by simpa [mapSpeciesCovector] using hsign, by simpa using hne⟩

/-- A strong-concordance witness renames to a strong-concordance witness. -/
theorem strongConcordanceWitness_map (F : N.Isomorphism M) {α : N.R → ℝ} {σ : S → ℝ}
    (h : N.StrongConcordanceWitness α σ) :
    M.StrongConcordanceWitness (fun q => α (F.reactionEquiv.symm q))
      (F.mapSpeciesCovector σ) where
  mem_kerL := F.inKerL_map h.mem_kerL
  mem_stoich := F.mem_stoichSubspace_map h.mem_stoich
  sigma_ne := F.mapSpeciesCovector_ne_zero h.sigma_ne
  positive_reaction := by
    intro q hq
    obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
    simp only [Equiv.symm_apply_apply] at hq
    obtain ⟨s, hs⟩ := h.positive_reaction r hq
    exact ⟨F.speciesEquiv s, F.promotes_map hs⟩
  negative_reaction := by
    intro q hq
    obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
    simp only [Equiv.symm_apply_apply] at hq
    obtain ⟨s, hs⟩ := h.negative_reaction r hq
    exact ⟨F.speciesEquiv s, F.opposes_map hs⟩
  zero_reaction := by
    intro q hq
    obtain ⟨r, rfl⟩ := F.reactionEquiv.surjective q
    simp only [Equiv.symm_apply_apply] at hq
    rcases h.zero_reaction r hq with hzero | ⟨s, t, hs, ht⟩
    · refine Or.inl fun u hu => ?_
      obtain ⟨v, rfl⟩ := F.speciesEquiv.surjective u
      simpa [mapSpeciesCovector] using hzero v ((F.isReactant_iff r v).2 hu)
    · exact Or.inr ⟨F.speciesEquiv s, F.speciesEquiv t,
        F.promotes_map hs, F.opposes_map ht⟩

/-- Strong concordance is invariant. -/
theorem stronglyConcordant_iff (F : N.Isomorphism M) :
    N.StronglyConcordant ↔ M.StronglyConcordant := by
  constructor
  · intro hN ⟨α, σ, hw⟩
    exact hN ⟨_, _, F.symm.strongConcordanceWitness_map hw⟩
  · intro hM ⟨α, σ, hw⟩
    exact hM ⟨_, _, F.strongConcordanceWitness_map hw⟩

/-- Renamed source-influence family.  The `pos_iff_source` clause survives because the
renamed reaction's source is the renamed source complex. -/
noncomputable def mapSourceInfluenceFamily (F : N.Isomorphism M)
    (P : N.SourceInfluenceFamily) : M.SourceInfluenceFamily where
  influence := fun q =>
    { vec := fun t => (P.influence (F.reactionEquiv.symm q)).vec (F.speciesEquiv.symm t)
      nonneg := fun t => (P.influence _).nonneg _
      pos_iff_source := fun t => by
        have hr : M.reaction q
            = Reaction.rename F.speciesEquiv (N.reaction (F.reactionEquiv.symm q)) := by
          simpa using F.map_reaction (F.reactionEquiv.symm q)
        rw [hr]
        simpa [Reaction.rename, Complex.rename] using
          (P.influence (F.reactionEquiv.symm q)).pos_iff_source (F.speciesEquiv.symm t) }

/-- The renamed influence vector at a renamed species is the original. -/
@[simp] theorem mapSourceInfluenceFamily_vec (F : N.Isomorphism M)
    (P : N.SourceInfluenceFamily) (r : N.R) (s : S) :
    ((F.mapSourceInfluenceFamily P).influence (F.reactionEquiv r)).vec
        (F.speciesEquiv s) = (P.influence r).vec s := by
  -- `simp` cannot rewrite `reactionEquiv.symm (reactionEquiv r)` here: the *type* of
  -- `P.influence r` depends on `r`.  The result type is `ℝ`, so `congrArg` does it.
  have hs : F.speciesEquiv.symm (F.speciesEquiv s) = s := F.speciesEquiv.symm_apply_apply s
  have hr : F.reactionEquiv.symm (F.reactionEquiv r) = r :=
    F.reactionEquiv.symm_apply_apply r
  show (P.influence (F.reactionEquiv.symm (F.reactionEquiv r))).vec
      (F.speciesEquiv.symm (F.speciesEquiv s)) = (P.influence r).vec s
  rw [hs]
  exact congrArg (fun r' => (P.influence r').vec s) hr

/-- Conjugation identity for the weak-normality operator. -/
theorem weakNormalityOperator_map (F : N.Isomorphism M) (P : N.SourceInfluenceFamily)
    (σ : S → ℝ) :
    M.weakNormalityOperator (F.mapSourceInfluenceFamily P) (F.mapSpeciesCovector σ)
      = F.speciesLinearEquiv (N.weakNormalityOperator P σ) := by
  show ∑ p : M.R, (∑ t : T, ((F.mapSourceInfluenceFamily P).influence p).vec t *
      F.mapSpeciesCovector σ t) • M.reactionVector p
    = F.speciesLinearEquiv (∑ r : N.R,
        (∑ s : S, (P.influence r).vec s * σ s) • N.reactionVector r)
  rw [map_sum]
  rw [← F.reactionEquiv.sum_comp (fun p =>
    (∑ t : T, ((F.mapSourceInfluenceFamily P).influence p).vec t *
      F.mapSpeciesCovector σ t) • M.reactionVector p)]
  refine Finset.sum_congr rfl fun r _ => ?_
  -- compute the scalar coefficient first; `congr 1` would leave it as a stray goal
  have hscal : ∑ t : T,
      ((F.mapSourceInfluenceFamily P).influence (F.reactionEquiv r)).vec t *
        F.mapSpeciesCovector σ t
      = ∑ s : S, (P.influence r).vec s * σ s := by
    rw [← F.speciesEquiv.sum_comp (fun t =>
      ((F.mapSourceInfluenceFamily P).influence (F.reactionEquiv r)).vec t *
        F.mapSpeciesCovector σ t)]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [F.mapSourceInfluenceFamily_vec P r s, mapSpeciesCovector]
  rw [map_smul, F.map_reactionVector r, hscal]

/-- A weak-normality witness renames to a weak-normality witness. -/
noncomputable def weakNormalWitness_map (F : N.Isomorphism M) (W : N.WeakNormalWitness) :
    M.WeakNormalWitness where
  influences := F.mapSourceInfluenceFamily W.influences
  nonsingular := by
    intro x y hxy
    have hx := F.symm_mem_stoichSubspace x.2
    have hy := F.symm_mem_stoichSubspace y.2
    have hamb : M.weakNormalityOperator (F.mapSourceInfluenceFamily W.influences)
          (x : T → ℝ)
        = M.weakNormalityOperator (F.mapSourceInfluenceFamily W.influences)
          (y : T → ℝ) := congrArg Subtype.val hxy
    have hxv : (x : T → ℝ) = F.mapSpeciesCovector (F.speciesLinearEquiv.symm x) := by
      funext t; simp [mapSpeciesCovector, speciesLinearEquiv]
    have hyv : (y : T → ℝ) = F.mapSpeciesCovector (F.speciesLinearEquiv.symm y) := by
      funext t; simp [mapSpeciesCovector, speciesLinearEquiv]
    rw [hxv, hyv, F.weakNormalityOperator_map, F.weakNormalityOperator_map] at hamb
    have hN := W.nonsingular (a₁ := ⟨F.speciesLinearEquiv.symm x, hx⟩)
      (a₂ := ⟨F.speciesLinearEquiv.symm y, hy⟩)
      (Subtype.ext (F.speciesLinearEquiv.injective hamb))
    exact Subtype.ext (F.speciesLinearEquiv.symm.injective (congrArg Subtype.val hN))

/-- Weak normality is invariant. -/
theorem weaklyNormal_iff (F : N.Isomorphism M) : N.WeaklyNormal ↔ M.WeaklyNormal :=
  ⟨fun ⟨W⟩ => ⟨F.weakNormalWitness_map W⟩, fun ⟨W⟩ => ⟨F.symm.weakNormalWitness_map W⟩⟩


end Isomorphism
end Network
end CRNT
