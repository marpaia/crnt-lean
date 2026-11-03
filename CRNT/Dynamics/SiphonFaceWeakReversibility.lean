import CRNT.Dynamics.Siphon
import CRNT.Dynamics.MassActionAlgebra
import CRNT.Dynamics.Persistence
import CRNT.Dynamics.PersistenceTheorem
import CRNT.Dynamics.ConfinedInvariance
import CRNT.Equilibria.ComplexBalanced
import CRNT.Graph.WeakReversibility
import CRNT.Subnetwork.ReactionRestriction
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Theorems.DeficiencyZero.Stability

/-!
# Weakly reversible reaction subnetworks on siphon faces

A siphon separates the reaction graph across the coordinate face where its species vanish.
In a weakly reversible network, a reaction cannot cross this separation in either direction:
if one endpoint complex avoids the siphon species, then so does the other. Consequently the
reactions whose source complexes avoid the siphon form a weakly reversible reaction-restricted
subnetwork. This is the structural reduction needed to analyze the dynamics tangent to a
boundary siphon face.
-/

namespace CRNT
namespace Network

open scoped Topology
open Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A complex avoids the species in `P`. -/
def ComplexAvoids (P : Finset S) (c : Complex S) : Prop :=
  ∀ s ∈ P, c s = 0

instance decidableComplexAvoids (P : Finset S) (c : Complex S) :
    Decidable (ComplexAvoids P c) := by
  unfold ComplexAvoids
  infer_instance

/-- The reactions whose source complexes avoid a fixed species set. -/
def avoidingSiphonReactions (N : Network S) (P : Finset S) : Finset N.R :=
  Finset.univ.filter (fun r => ComplexAvoids P (N.reaction r).source)

/-- Fill the zero coordinates of a siphon-face point with the corresponding coordinates of a
reference concentration. -/
def fillSiphonFace (P : Finset S) (xstar x : Concentration S) : Concentration S :=
  fun s => if s ∈ P then xstar s else x s

/-- If the source avoids a siphon, then so does the target. -/
theorem complexAvoids_target_of_source_avoids_siphon (N : Network S) {P : Finset S}
    (hP : N.IsSiphon P) {r : N.R}
    (hsrc : ComplexAvoids P (N.reaction r).source) :
    ComplexAvoids P (N.reaction r).target := by
  intro s hs
  by_contra hzero
  obtain ⟨t, htP, hreact⟩ := hP r ⟨s, hs, hzero⟩
  exact hreact (hsrc t htP)

/-- Avoidance of a siphon propagates along every directed reaction path. -/
theorem complexAvoids_of_reaches (N : Network S) {P : Finset S}
    (hP : N.IsSiphon P) {c d : Complex S} (hcd : N.Reaches c d)
    (hc : ComplexAvoids P c) : ComplexAvoids P d := by
  induction hcd with
  | refl => exact hc
  | @tail b d _ hbd ih =>
      rcases hbd with ⟨r, hrs, hrt⟩
      have hb : ComplexAvoids P b := ih
      have hs : ComplexAvoids P (N.reaction r).source := by
        simpa [hrs] using hb
      have ht := N.complexAvoids_target_of_source_avoids_siphon hP hs
      simpa [hrt] using ht

/-- Under weak reversibility, avoidance of a siphon is constant across every reaction edge. -/
theorem complexAvoids_source_iff_target_of_siphon_weaklyReversible
    (N : Network S) {P : Finset S} (hP : N.IsSiphon P)
    (hwr : N.WeaklyReversible) (r : N.R) :
    ComplexAvoids P (N.reaction r).source ↔
      ComplexAvoids P (N.reaction r).target := by
  constructor
  · exact N.complexAvoids_target_of_source_avoids_siphon hP
  · intro ht
    exact N.complexAvoids_of_reaches hP (hwr r) ht

/-- Restricting to reactions whose source avoids a siphon preserves any path that starts at an
avoiding complex. -/
theorem reaches_restrictReactions_avoiding_siphon
    (N : Network S) {P : Finset S} (hP : N.IsSiphon P)
    (E : Finset N.R) (hE : ∀ r : N.R,
      ComplexAvoids P (N.reaction r).source → r ∈ E)
    {c d : Complex S} (hcd : N.Reaches c d) (hc : ComplexAvoids P c) :
    (N.restrictReactions E).Reaches c d := by
  induction hcd with
  | refl => exact Network.Reaches.refl _ c
  | @tail b d hab hbd ih =>
      rcases hbd with ⟨r, hrs, hrt⟩
      have hb : ComplexAvoids P b := N.complexAvoids_of_reaches hP hab hc
      have hs : ComplexAvoids P (N.reaction r).source := by
        simpa [hrs] using hb
      have hEr : r ∈ E := hE r hs
      have hstep : (N.restrictReactions E).DirectlyReacts b d := by
        refine ⟨⟨r, hEr⟩, ?_, ?_⟩
        · change (N.reaction r).source = b
          exact hrs
        · change (N.reaction r).target = d
          exact hrt
      exact Network.Reaches.tail ih hstep

/-- The reaction-restricted subnetwork whose source complexes avoid a siphon is weakly
reversible whenever the parent network is weakly reversible. -/
theorem restrictReactions_avoiding_siphon_weaklyReversible
    (N : Network S) {P : Finset S} (hP : N.IsSiphon P) (hwr : N.WeaklyReversible) :
    (N.restrictReactions (N.avoidingSiphonReactions P)).WeaklyReversible := by
  classical
  let E := N.avoidingSiphonReactions P
  change (N.restrictReactions E).WeaklyReversible
  intro r
  have hsrc : ComplexAvoids P (N.reaction r.1).source := by
    exact (Finset.mem_filter.mp r.2).2
  have htgt : ComplexAvoids P (N.reaction r.1).target :=
    (N.complexAvoids_source_iff_target_of_siphon_weaklyReversible hP hwr r.1).mp hsrc
  have hback : N.Reaches (N.reaction r.1).target (N.reaction r.1).source := hwr r.1
  have hback' : (N.restrictReactions E).Reaches
      (N.reaction r.1).target (N.reaction r.1).source :=
    N.reaches_restrictReactions_avoiding_siphon hP E
      (fun q hq => Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩) hback htgt
  simpa using hback'

/-- **A critical siphon has a transverse stoichiometric direction.** If every stoichiometric
vector vanished on `P`, the indicator of `P` would be a nonnegative conservation law supported
exactly there, contradicting criticality. Thus some stoichiometric displacement changes a siphon
coordinate. This is the directional content behind the rank drop of the avoiding-face network. -/
theorem exists_stoichVector_nonzero_on_criticalSiphon
    (N : Network S) {P : Finset S} (hcrit : N.IsCriticalSiphon P) :
    ∃ v : S → ℝ, v ∈ N.stoichSubspace ∧ ∃ s ∈ P, v s ≠ 0 := by
  classical
  let K : Submodule ℝ (S → ℝ) := {
    carrier := {v | ∀ s ∈ P, v s = 0}
    zero_mem' := by intro s hs; rfl
    add_mem' := by intro v w hv hw s hs; simp [hv s hs, hw s hs]
    smul_mem' := by intro a v hv s hs; simp [hv s hs]
  }
  have hnot : ¬ N.stoichSubspace ≤ K := by
    intro hparent
    let w : S → ℝ := fun s => if s ∈ P then 1 else 0
    have hwnn : ∀ s, 0 ≤ w s := by
      intro s
      by_cases hs : s ∈ P <;> simp [w, hs]
    have hwpos : ∀ s, 0 < w s ↔ s ∈ P := by
      intro s
      by_cases hs : s ∈ P <;> simp [w, hs]
    have hwcons : ∀ r : N.R, ∑ s, w s * N.reactionVector r s = 0 := by
      intro r
      have hr : N.reactionVector r ∈ N.stoichSubspace :=
        N.reactionVector_mem_stoichSubspace r
      have hz : ∀ s ∈ P, N.reactionVector r s = 0 := hparent hr
      apply Finset.sum_eq_zero
      intro s _
      by_cases hs : s ∈ P
      · have hz' : ((N.reaction r).target s : ℝ) -
            ((N.reaction r).source s : ℝ) = 0 := by
          simpa [Network.reactionVector_apply] using hz s hs
        simp [w, hs, hz']
      · simp [w, hs]
    exact hcrit.2.2 ⟨w, hwnn, hwpos, hwcons⟩
  have hv : ∃ v : S → ℝ, v ∈ N.stoichSubspace ∧ v ∉ K := by
    by_contra h
    apply hnot
    intro v hvS
    by_contra hvK
    exact h ⟨v, hvS, hvK⟩
  obtain ⟨v, hvS, hvK⟩ := hv
  have hs : ∃ s ∈ P, v s ≠ 0 := by
    by_contra h
    apply hvK
    intro s hsP
    by_contra hvs
    exact h ⟨s, hsP, hvs⟩
  exact ⟨v, hvS, hs⟩

/-- A critical siphon forces a strict stoichiometric rank drop on its avoiding face.  Every
reaction vector retained on the face vanishes on the siphon coordinates.  If the full
stoichiometric space also vanished there, the indicator of the siphon would be a positive
conservation law supported exactly on it, contradicting criticality. -/
theorem restrictReactions_avoiding_siphon_stoichRank_lt
    (N : Network S) {P : Finset S} (hcrit : N.IsCriticalSiphon P) :
    (N.restrictReactions (N.avoidingSiphonReactions P)).stoichRank < N.stoichRank := by
  classical
  let E := N.avoidingSiphonReactions P
  let Nf := N.restrictReactions E
  let K : Submodule ℝ (S → ℝ) := {
    carrier := {v | ∀ s ∈ P, v s = 0}
    zero_mem' := by
      intro s hs
      rfl
    add_mem' := by
      intro v w hv hw s hs
      simp [hv s hs, hw s hs]
    smul_mem' := by
      intro a v hv s hs
      simp [hv s hs]
  }
  have hfaceK : Nf.stoichSubspace ≤ K := by
    apply Submodule.span_le.mpr
    rintro v ⟨r, rfl⟩
    intro s hs
    have hsrc : ComplexAvoids P (N.reaction r.1).source := by
      simpa [E, avoidingSiphonReactions] using r.2
    have htgt : ComplexAvoids P (N.reaction r.1).target :=
      N.complexAvoids_target_of_source_avoids_siphon hcrit.2.1 hsrc
    change ((N.reaction r.1).target s : ℝ) -
      ((N.reaction r.1).source s : ℝ) = 0
    rw [htgt s hs, hsrc s hs]
    norm_num
  obtain ⟨v, hvS, s, hsP, hvs⟩ := N.exists_stoichVector_nonzero_on_criticalSiphon hcrit
  have hparent_not_le : ¬ N.stoichSubspace ≤ K := by
    intro hparent
    exact hvs (hparent hvS s hsP)
  have hle : Nf.stoichSubspace ≤ N.stoichSubspace := by
    simpa [Nf, E] using N.restrictReactions_stoichSubspace_le E
  have hne : Nf.stoichSubspace ≠ N.stoichSubspace := by
    intro heq
    apply hparent_not_le
    rw [← heq]
    exact hfaceK
  have hlt : Nf.stoichSubspace < N.stoichSubspace := lt_of_le_of_ne hle hne
  exact Submodule.finrank_lt_finrank_of_lt hlt

/-- Complex balance restricts to the weakly reversible subnetwork on the complement of a siphon.
The siphon condition and weak reversibility ensure no reaction edge crosses between the two
complex sets, so every inflow and outflow at a retained complex is unchanged by restriction. -/
theorem restrictReactions_avoiding_siphon_complexBalanced
    (N : Network S) (κ : N.RateConstants) {P : Finset S}
    (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {x : Concentration S} (hcb : N.IsComplexBalanced κ x) :
    (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced
      (κ.restrict (N.avoidingSiphonReactions P)) x := by
  classical
  let E := N.avoidingSiphonReactions P
  let Nf := N.restrictReactions E
  let κf := κ.restrict E
  have hsrcAvoid (r : N.R) (hr : r ∈ E) :
      ComplexAvoids P (N.reaction r).source := by
    simpa [E, avoidingSiphonReactions] using hr
  have htgtAvoid (r : N.R) (hr : r ∈ E) :
      ComplexAvoids P (N.reaction r).target :=
    N.complexAvoids_target_of_source_avoids_siphon hP (hsrcAvoid r hr)
  have hcAvoid {c : Complex S} (hc : c ∈ Nf.complexes) : ComplexAvoids P c := by
    rcases Finset.mem_union.mp hc with hsource | htarget
    · rcases Finset.mem_image.mp hsource with ⟨r, _, hr⟩
      have h := hsrcAvoid r.1 r.2
      change (N.reaction r.1).source = c at hr
      rw [← hr]
      exact h
    · rcases Finset.mem_image.mp htarget with ⟨r, _, hr⟩
      have h := htgtAvoid r.1 r.2
      change (N.reaction r.1).target = c at hr
      rw [← hr]
      exact h
  have hparentComplex {c : Complex S} (hc : c ∈ Nf.complexes) : c ∈ N.complexes :=
    N.restrictReactions_complexes_subset E hc
  have hinflow (c : Complex S) (hc : c ∈ Nf.complexes) :
      Nf.inflow κf x c = N.inflow κ x c := by
    change (∑ r : {r : N.R // r ∈ E},
      if (N.reaction r.1).target = c then N.massActionRate κ r.1 x else 0) = _
    rw [Finset.sum_coe_sort E
      (fun r => if (N.reaction r).target = c then N.massActionRate κ r x else 0)]
    apply Finset.sum_subset (Finset.subset_univ E)
    intro r _ hrnot
    by_cases htarget : (N.reaction r).target = c
    · have havoid := hcAvoid hc
      have hsrc : ComplexAvoids P (N.reaction r).source :=
        (N.complexAvoids_source_iff_target_of_siphon_weaklyReversible hP hwr r).mpr
          (by simpa [htarget] using havoid)
      have hrE : r ∈ E := by
        simpa [E, avoidingSiphonReactions] using
          (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hsrc⟩ : r ∈ N.avoidingSiphonReactions P)
      exact (hrnot hrE).elim
    · simp [htarget]
  have houtflow (c : Complex S) (hc : c ∈ Nf.complexes) :
      Nf.outflow κf x c = N.outflow κ x c := by
    change (∑ r : {r : N.R // r ∈ E},
      if (N.reaction r.1).source = c then N.massActionRate κ r.1 x else 0) = _
    rw [Finset.sum_coe_sort E
      (fun r => if (N.reaction r).source = c then N.massActionRate κ r x else 0)]
    apply Finset.sum_subset (Finset.subset_univ E)
    intro r _ hrnot
    by_cases hsource : (N.reaction r).source = c
    · have hsrcAvoid := hcAvoid hc
      have hrE : r ∈ E := by
        simpa [E, avoidingSiphonReactions] using
          (Finset.mem_filter.mpr ⟨Finset.mem_univ r, by simpa [hsource] using hsrcAvoid⟩ :
            r ∈ N.avoidingSiphonReactions P)
      exact (hrnot hrE).elim
    · simp [hsource]
  intro c hc
  rw [hinflow c hc, houtflow c hc]
  exact hcb c (hparentComplex hc)

/-- On a siphon face, the full mass-action vector field equals that of the restricted network
whose reactions have source complexes avoiding the absent species. The missing reactions have
zero rate, and filling the absent coordinates does not change any retained reaction rate. -/
theorem massActionVectorField_eq_restrict_avoiding_siphon
    (N : Network S) (κ : N.RateConstants) {P : Finset S}
    {xstar x : Concentration S}
    (hxzero : ∀ s ∈ P, x s = 0) :
    N.massActionVectorField κ x =
      (N.restrictReactions (N.avoidingSiphonReactions P)).massActionVectorField
        (κ.restrict (N.avoidingSiphonReactions P)) (fillSiphonFace P xstar x) := by
  classical
  let E := N.avoidingSiphonReactions P
  have hsrcAvoid (r : N.R) (hr : r ∈ E) :
      ComplexAvoids P (N.reaction r).source := by
    simpa [E, avoidingSiphonReactions] using hr
  have hrate_eq (r : N.R) (hr : r ∈ E) :
      N.massActionRate κ r (fillSiphonFace P xstar x) = N.massActionRate κ r x := by
    unfold massActionRate
    congr 1
    unfold Complex.massActionMonomial
    apply Finset.prod_congr rfl
    intro s _
    by_cases hs : s ∈ P
    · have hsource : (N.reaction r).source s = 0 := hsrcAvoid r hr s hs
      simp [fillSiphonFace, hs, hsource]
    · simp [fillSiphonFace, hs]
  funext s
  rw [N.restrictReactions_massActionVectorField]
  change (∑ r : N.R, N.massActionRate κ r x * N.reactionVector r s) =
    ∑ r ∈ E,
      N.massActionRate κ r (fillSiphonFace P xstar x) * N.reactionVector r s
  have hsum :
      (∑ r ∈ E, N.massActionRate κ r x * N.reactionVector r s) =
        ∑ r : N.R, N.massActionRate κ r x * N.reactionVector r s := by
    apply Finset.sum_subset (Finset.subset_univ E)
    intro r _ hrnot
    have hnotAvoid : ¬ ComplexAvoids P (N.reaction r).source := by
      intro havoid
      have hrE : r ∈ E := by
        simpa [E, avoidingSiphonReactions] using
          (Finset.mem_filter.mpr ⟨Finset.mem_univ r, havoid⟩ :
            r ∈ N.avoidingSiphonReactions P)
      exact hrnot hrE
    change ¬ ∀ s, s ∈ P → (N.reaction r).source s = 0 at hnotAvoid
    push Not at hnotAvoid
    obtain ⟨s₀, hs₀P, hs₀source⟩ := hnotAvoid
    rw [N.massActionRate_eq_zero_of_reactant_zero κ (hxzero s₀ hs₀P) hs₀source, zero_mul]
  calc
    (∑ r : N.R, N.massActionRate κ r x * N.reactionVector r s) =
        ∑ r ∈ E, N.massActionRate κ r x * N.reactionVector r s := hsum.symm
    _ = ∑ r ∈ E,
        N.massActionRate κ r (fillSiphonFace P xstar x) * N.reactionVector r s := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [hrate_eq r hr]

/-- If the derivative of relative entropy along a siphon face vanishes, then the state is an
equilibrium. The face derivative is the ordinary relative-entropy dissipation of the closed
complex-balanced subnetwork obtained by deleting reactions that require an absent species. -/
theorem massActionVectorField_eq_zero_of_faceDissipation_eq_zero
    (N : Network S) (κ : N.RateConstants) {P : Finset S}
    (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar x : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hxzero : ∀ s ∈ P, x s = 0)
    (hxpos : ∀ s, s ∉ P → 0 < x s)
    (hfaceDiss : (∑ s, if s ∈ P then 0 else
      (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s) = 0) :
    N.massActionVectorField κ x = 0 := by
  let E := N.avoidingSiphonReactions P
  let Nf := N.restrictReactions E
  let κf := κ.restrict E
  let xf := fillSiphonFace P xstar x
  have hxfpos : xf.Positive := by
    intro s
    by_cases hs : s ∈ P
    · simpa [xf, fillSiphonFace, hs] using hxs s
    · simpa [xf, fillSiphonFace, hs] using hxpos s hs
  have hcbf : Nf.IsComplexBalanced κf xstar := by
    exact N.restrictReactions_avoiding_siphon_complexBalanced κ hP hwr hcb
  have hfields : N.massActionVectorField κ x =
      Nf.massActionVectorField κf xf := by
    exact N.massActionVectorField_eq_restrict_avoiding_siphon κ hxzero
  have hfaceDiss' :
      (∑ s, (Real.log (xf s) - Real.log (xstar s)) *
        Nf.massActionVectorField κf xf s) = 0 := by
    calc
      (∑ s, (Real.log (xf s) - Real.log (xstar s)) *
          Nf.massActionVectorField κf xf s) =
          ∑ s, if s ∈ P then 0 else
            (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s := by
              apply Finset.sum_congr rfl
              intro s _
              by_cases hs : s ∈ P
              · simp [xf, fillSiphonFace, hs]
              · simp only [xf, fillSiphonFace, if_neg hs]
                rw [← congrFun hfields s]
      _ = 0 := hfaceDiss
  have hcbx : Nf.IsComplexBalanced κf xf :=
    Nf.complexBalanced_of_dissipation_eq_zero κf hxfpos hxs hcbf hfaceDiss'
  have hsteady := hcbx.isMassActionSteadyState Nf κf
  funext s
  calc
    N.massActionVectorField κ x s = Nf.massActionVectorField κf xf s :=
      congrFun hfields s
    _ = 0 := hsteady s

/-- Filling the zero coordinates of a siphon-face point with the reference concentration removes
exactly their constant entropy contributions. -/
theorem relEntropy_fillSiphonFace
    {P : Finset S} {xstar x : Concentration S} (hxs : xstar.Positive)
    (hxzero : ∀ s ∈ P, x s = 0) :
    relEntropy xstar (fillSiphonFace P xstar x) =
      relEntropy xstar x - ∑ s ∈ P, xstar s := by
  classical
  unfold relEntropy
  have hsumP : ∑ s ∈ P, xstar s = ∑ s, if s ∈ P then xstar s else 0 := by
    simp
  rw [hsumP, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsp : s ∈ P
  · simp [fillSiphonFace, hsp, hxzero s hsp, (hxs s).ne']
  · simp [fillSiphonFace, hsp]

/-- A boundary orbit that stays in a siphon face and has constant relative entropy can only
accumulate at an equilibrium of the full vector field. Filling the absent coordinates turns the
face orbit into a positive trajectory of the weakly reversible face subnetwork; the constant
entropy forces its restricted dissipation to vanish. The theorem returns both the resulting
complex balance of the filled face state and stationarity of the original state. -/
theorem complexBalanced_and_massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit
    (N : Network S) (κ : N.RateConstants) {P : Finset S}
    (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar x : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} (hγ0 : γ 0 = x)
    (hface : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P)
    (hpositive : ∀ s, s ∉ P → 0 < γ 0 s)
    (hderiv : ∀ t, 0 ≤ t →
      HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {c : ℝ} (hconstantEntropy : ∀ t, 0 ≤ t → relEntropy xstar (γ t) = c) :
    (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced
        (κ.restrict (N.avoidingSiphonReactions P))
        (fillSiphonFace P xstar (γ 0)) ∧
      N.massActionVectorField κ x = 0 := by
  classical
  let E := N.avoidingSiphonReactions P
  let Nf := N.restrictReactions E
  let κf := κ.restrict E
  let η : ℝ → Concentration S := fun t => fillSiphonFace P xstar (γ t)
  have hxface : x ∈ N.SiphonFace P := by
    simpa [hγ0] using hface 0 le_rfl
  have hxfaceProps := (mem_siphonFace_iff N).mp hxface
  have hxzero : ∀ s ∈ P, x s = 0 :=
    (faceSum_eq_zero_iff hxfaceProps.1).mp hxfaceProps.2
  have hγzero : ∀ s ∈ P, γ 0 s = 0 := by
    intro s hs
    rw [hγ0]
    exact hxzero s hs
  have hfields0 : N.massActionVectorField κ x =
      Nf.massActionVectorField κf (η 0) := by
    calc
      N.massActionVectorField κ x = N.massActionVectorField κ (γ 0) := by rw [hγ0]
      _ = Nf.massActionVectorField κf (η 0) :=
        N.massActionVectorField_eq_restrict_avoiding_siphon κ hγzero
  have hηpos : (η 0).Positive := by
    intro s
    by_cases hs : s ∈ P
    · simpa [η, fillSiphonFace, hs] using hxs s
    · simpa [η, fillSiphonFace, hs] using hpositive s hs
  have hηderiv : HasDerivAt η (Nf.massActionVectorField κf (η 0)) 0 := by
    apply hasDerivAt_pi.mpr
    intro s
    by_cases hs : s ∈ P
    · have hfieldzero : Nf.massActionVectorField κf (η 0) s = 0 :=
        (congrFun hfields0 s).symm.trans
          (N.massActionVectorField_eq_zero_on_siphonFace κ hP hxface hs)
      have hconst : HasDerivAt (fun _ : ℝ => xstar s) 0 0 :=
        hasDerivAt_const 0 (xstar s)
      have hconst' : HasDerivAt (fun _ : ℝ => xstar s)
          (Nf.massActionVectorField κf (η 0) s) 0 :=
        hconst.congr_deriv hfieldzero.symm
      simpa [η, fillSiphonFace, hs] using hconst'
    · have hγcoord : HasDerivAt (fun t => γ t s)
          (N.massActionVectorField κ (γ 0) s) 0 :=
        (hasDerivAt_pi.mp (hderiv 0 le_rfl)) s
      have hfieldeq : N.massActionVectorField κ (γ 0) s =
          Nf.massActionVectorField κf (η 0) s := by
        rw [hγ0]
        exact congrFun hfields0 s
      have hγcoord' := hγcoord.congr_deriv hfieldeq
      simpa [η, fillSiphonFace, hs] using hγcoord'
  have hηconstant : ∀ t, 0 ≤ t →
      relEntropy xstar (η t) = c - ∑ s ∈ P, xstar s := by
    intro t ht
    have hfaceProps := (mem_siphonFace_iff N).mp (hface t ht)
    have hzero_t : ∀ s ∈ P, γ t s = 0 :=
      (faceSum_eq_zero_iff hfaceProps.1).mp hfaceProps.2
    rw [relEntropy_fillSiphonFace hxs
      hzero_t]
    exact congrArg (fun z => z - ∑ s ∈ P, xstar s) (hconstantEntropy t ht)
  have hchain := relEntropy_hasDerivAt hxs hηpos
    (fun s => (hasDerivAt_pi.mp hηderiv) s)
  let rightNhds : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hconstantSlope :
      (fun t => t⁻¹ •
        (relEntropy xstar (η (0 + t)) - relEntropy xstar (η 0))) =ᶠ[rightNhds]
        fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [hηconstant t ht.le, hηconstant 0 le_rfl]
  have hslopeZero : Tendsto
      (fun t => t⁻¹ •
        (relEntropy xstar (η (0 + t)) - relEntropy xstar (η 0)))
      rightNhds (𝓝 0) :=
    Filter.Tendsto.congr' hconstantSlope.symm tendsto_const_nhds
  have hfaceDiss :
      (∑ s, (Real.log (η 0 s) - Real.log (xstar s)) *
        Nf.massActionVectorField κf (η 0) s) = 0 := by
    exact tendsto_nhds_unique hchain.tendsto_slope_zero_right hslopeZero
  have hcbf : Nf.IsComplexBalanced κf xstar := by
    exact N.restrictReactions_avoiding_siphon_complexBalanced κ hP hwr hcb
  have hcbη : Nf.IsComplexBalanced κf (η 0) :=
    Nf.complexBalanced_of_dissipation_eq_zero κf hηpos hxs hcbf hfaceDiss
  refine ⟨hcbη, ?_⟩
  have hsteady := hcbη.isMassActionSteadyState Nf κf
  funext s
  calc
    N.massActionVectorField κ x s = Nf.massActionVectorField κf (η 0) s :=
      congrFun hfields0 s
    _ = 0 := hsteady s

/-- A boundary orbit that stays in a siphon face and has constant relative entropy can only
accumulate at an equilibrium of the full vector field. Filling the absent coordinates turns the
face orbit into a positive trajectory of the weakly reversible face subnetwork; the constant
entropy forces its restricted dissipation to vanish. This projection preserves the original
stationarity interface while the stronger paired theorem also exposes complex balance of the
filled face state. -/
theorem massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit
    (N : Network S) (κ : N.RateConstants) {P : Finset S}
    (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar x : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} (hγ0 : γ 0 = x)
    (hface : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P)
    (hpositive : ∀ s, s ∉ P → 0 < γ 0 s)
    (hderiv : ∀ t, 0 ≤ t →
      HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {c : ℝ} (hconstantEntropy : ∀ t, 0 ≤ t → relEntropy xstar (γ t) = c) :
    N.massActionVectorField κ x = 0 :=
  (N.complexBalanced_and_massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit
    κ hP hwr hxs hcb hγ0 hface hpositive hderiv hconstantEntropy).2

/-- Entropy confinement supplies forward invariance of the siphon face. The initial point may be
on the boundary; positivity is required only in the coordinates complementary to that face. -/
theorem massActionVectorField_eq_zero_of_confined_constantEntropy_siphonFaceOrbit
    (N : Network S) (κ : N.RateConstants) {P : Finset S}
    (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar x : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    {γ : ℝ → Concentration S} (hγ0 : γ 0 = x)
    (h0 : γ 0 ∈ N.SiphonFace P)
    (hnonneg : ∀ t, 0 ≤ t → (γ t).Nonnegative)
    (hpositive : ∀ s, s ∉ P → 0 < γ 0 s)
    (hderiv : ∀ t, 0 ≤ t →
      HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {c : ℝ} (hconstantEntropy : ∀ t, 0 ≤ t → relEntropy xstar (γ t) = c) :
    N.massActionVectorField κ x = 0 := by
  have hface : ∀ t, 0 ≤ t → γ t ∈ N.SiphonFace P :=
    N.siphonFace_forwardInvariant_of_relEntropy_le_forward κ hP hxs hderiv hnonneg
      (fun t ht => (hconstantEntropy t ht).le) h0
  exact N.massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit
    κ hP hwr hxs hcb hγ0 hface hpositive hderiv hconstantEntropy

end Network
end CRNT
