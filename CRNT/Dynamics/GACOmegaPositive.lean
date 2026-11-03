import CRNT.Dynamics.GlobalStability
import CRNT.Dynamics.BoundaryOmegaSiphon
import CRNT.Dynamics.CriticalSiphonOmega
import CRNT.Dynamics.SiphonFaceWeakReversibility

/-!
# A single positive ω-limit point forces global convergence

The sharpest *general* reduction of the global attractor conjecture available from the
relative-entropy Lyapunov stack: for a weakly reversible complex-balanced mass-action semiflow,
if the ω-limit set of a trajectory contains **even one strictly positive point**, then the whole
ω-limit set is the equilibrium `{x*}`. No structural hypothesis (no siphon condition) is needed.

The mechanism. LaSalle pins the relative entropy to a constant `c` on the ω-limit set. A positive
ω-point `p` has a strictly positive forward orbit (still inside ω), along which the relative
entropy is constant; vanishing dissipation then makes `p` complex-balanced, so `p = x*` by
deficiency-zero uniqueness. Hence `x* ∈ ω` and `c = relEntropy x* x* = 0`. Positive-definiteness
of the relative entropy (`relEntropy_eq_zero_iff`) then forces **every** ω-point — boundary points
included — to equal `x*`.

Consequence: global convergence holds for *any* complex-balanced trajectory whose ω-limit set
meets the open positive orthant. The full conjecture is thereby reduced precisely to excluding
ω-limit sets contained entirely in the boundary — which is exactly the persistence question that
remains open in general. This subsumes the no-critical-siphon theorem (there every ω-point is
positive, so in particular one is).

The hypotheses are the standard mass-action semiflow facts a LaSalle construction supplies
(`hgenω` ω-orbits solve the genuine field, `hωc` constancy of the relative entropy on ω, `hωaff`
affine invariance, `hposorbit` positivity of orbits from positive ω-points).

Depends on: `CRNT.Dynamics.GlobalStability`.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Boundary omega-points induce complex-balanced face equilibria.** If the zero set of a
boundary omega-point is a siphon, constant relative entropy and forward invariance force its
filled state to be complex-balanced for the weakly reversible subnetwork that avoids the absent
species. The original boundary point is also stationary for the full network. -/
theorem complexBalanced_and_massActionVectorField_eq_zero_of_mem_boundaryOmega_siphon
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : N.IsSiphon P)
    (hzeroSet : ∀ s, s ∈ P ↔ w s = 0) :
    (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced
        (κ.restrict (N.avoidingSiphonReactions P)) (fillSiphonFace P xstar w) ∧
      N.massActionVectorField κ w = 0 := by
  have hwposOutside : ∀ s, s ∉ P → 0 < w s := by
    intro s hs
    have hnotzero : w s ≠ 0 := by
      intro hz
      exact hs ((hzeroSet s).2 hz)
    exact lt_of_le_of_ne (hωnn w hw s) (Ne.symm hnotzero)
  have hface0 : γ w 0 ∈ N.SiphonFace P := by
    have hwface : w ∈ N.SiphonFace P := by
      apply (mem_siphonFace_iff N).mpr
      have hwnn := hωnn w hw
      exact ⟨hwnn, (faceSum_eq_zero_iff hwnn).2 (fun s hs => (hzeroSet s).1 hs)⟩
    simpa [hγ0] using hwface
  have hyωt : ∀ t : ℝ, 0 ≤ t → γ w t ∈ omegaLimit atTop ϕ {x₀} := by
    intro t ht
    have hflow := (Flow.isInvariant_omegaLimit atTop ϕ {x₀}
      (fun s => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) ⟨t, ht⟩) hw
    exact (hϕγ w ⟨t, ht⟩) ▸ hflow
  have hnonneg : ∀ t, 0 ≤ t → (γ w t).Nonnegative :=
    fun t ht => hωnn (γ w t) (hyωt t ht)
  have hpositive : ∀ s, s ∉ P → 0 < γ w 0 s := by
    intro s hs
    simpa [hγ0] using hwposOutside s hs
  have hconstant : ∀ t, 0 ≤ t → relEntropy xstar (γ w t) = c :=
    fun t ht => hωc (γ w t) (hyωt t ht)
  have hface : ∀ t, 0 ≤ t → γ w t ∈ N.SiphonFace P :=
    N.siphonFace_forwardInvariant_of_relEntropy_le_forward κ hP hxs (hgenω w hw) hnonneg
      (fun t ht => (hconstant t ht).le) hface0
  have hpair := N.complexBalanced_and_massActionVectorField_eq_zero_of_constantEntropy_siphonFaceOrbit
    κ hP hwr hxs hcb (hγ0 w) hface hpositive (hgenω w hw) hconstant
  constructor
  · simpa [hγ0] using hpair.1
  · simpa [hγ0] using hpair.2

/-- A boundary omega point with a nonempty zero set exposes a lower-rank complex-balanced face.
The zero set is critical by affine conservation, the avoiding-face restriction is complex-balanced
at the filled state, and criticality forces its stoichiometric rank to be strictly smaller than the
parent rank. This packages the structural data needed by a rank-induction boundary argument. -/
theorem criticalBoundaryOmegaFace_lowerRank
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hzeroSet : ∀ s, s ∈ P ↔ w s = 0) (hPne : P.Nonempty) :
    N.IsCriticalSiphon P ∧
      (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced
        (κ.restrict (N.avoidingSiphonReactions P)) (fillSiphonFace P xstar w) ∧
      (N.restrictReactions (N.avoidingSiphonReactions P)).stoichRank < N.stoichRank ∧
      N.massActionVectorField κ w = 0 := by
  have hcrit : N.IsCriticalSiphon P :=
    N.isCriticalSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hωaff hx₀
      hw hzeroSet hPne
  have hface := N.complexBalanced_and_massActionVectorField_eq_zero_of_mem_boundaryOmega_siphon
    hwr κ hxs hcb hγ0 hϕγ hgenω hωnn hωc hw hcrit.2.1 hzeroSet
  exact ⟨hcrit, hface.1, N.restrictReactions_avoiding_siphon_stoichRank_lt hcrit, hface.2⟩


/-- A finite species set lets us choose a boundary omega point whose zero set is maximal by
cardinality. Every omega point on that same zero face then has exactly the same zero set, and —
exported as the final component — no omega point of `Ω` has a zero set of larger cardinality
than `P'`. -/
theorem exists_maximal_zeroSet_omegaPoint
    {Ω : Set (Concentration S)}
    {w : Concentration S} (hw : w ∈ Ω)
    {P : Finset S} (hPne : P.Nonempty)
    (hzeroSet : ∀ s, s ∈ P ↔ w s = 0) :
    ∃ w' ∈ Ω, ∃ P' : Finset S, P'.Nonempty ∧
      (∀ s, s ∈ P' ↔ w' s = 0) ∧
      (∀ z ∈ Ω, (∀ s ∈ P', z s = 0) → ∀ s, z s = 0 ↔ s ∈ P') ∧
      ∀ z ∈ Ω, (Finset.univ.filter (fun s => z s = 0)).card ≤ P'.card := by
  classical
  let candidates : Finset (Finset S) :=
    Finset.univ.powerset.filter fun Q => ∃ z ∈ Ω, ∀ s, s ∈ Q ↔ z s = 0
  have hPmem : P ∈ candidates := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr (Finset.subset_univ P)
    · exact ⟨w, hw, hzeroSet⟩
  have hcandidates : candidates.Nonempty := ⟨P, hPmem⟩
  obtain ⟨Pmax, hPmaxmem, hPmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  obtain ⟨wmax, hwmax, hzeroMax⟩ := (Finset.mem_filter.mp hPmaxmem).2
  have hPmaxNonempty : Pmax.Nonempty := by
    apply Finset.card_pos.mp
    exact lt_of_lt_of_le (Finset.card_pos.mpr hPne) (hPmax P hPmem)
  have hmaxExact : ∀ z ∈ Ω, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax := by
    intro z hz hzero s
    let Qz : Finset S := Finset.univ.filter fun i => z i = 0
    have hQexact : ∀ i, i ∈ Qz ↔ z i = 0 := by
      intro i
      simp [Qz]
    have hQmem : Qz ∈ candidates := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_powerset.mpr (Finset.subset_univ Qz)
      · exact ⟨z, hz, hQexact⟩
    have hsubset : Pmax ⊆ Qz := by
      intro i hi
      exact (hQexact i).2 (hzero i hi)
    have hcard : Qz.card ≤ Pmax.card := hPmax Qz hQmem
    have hEq : Pmax = Qz := Finset.eq_of_subset_of_card_le hsubset hcard
    rw [hEq]
    exact (hQexact s).symm
  have hzcard : ∀ z ∈ Ω, (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card := by
    intro z hz
    let Qz : Finset S := Finset.univ.filter fun i => z i = 0
    have hQexact : ∀ i, i ∈ Qz ↔ z i = 0 := by
      intro i
      simp [Qz]
    have hQmem : Qz ∈ candidates := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_powerset.mpr (Finset.subset_univ Qz)
      · exact ⟨z, hz, hQexact⟩
    exact hPmax Qz hQmem
  exact ⟨wmax, hwmax, Pmax, hPmaxNonempty, hzeroMax, hmaxExact, hzcard⟩

/-- **Exact output of a boundary-face rank reduction.** A compact forward orbit either already
has a positive omega-point, or it has a boundary omega-point whose zero set is a nonempty critical
siphon and whose avoiding-face network has strictly smaller stoichiometric rank and a positive
complex-balanced face equilibrium. This is the structural alternative supplied by the existing
face analysis; it does not transfer that face equilibrium back into the parent orbit's omega-limit
set. -/
theorem positiveOmega_or_lowerRankCriticalBoundaryFace
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀},
      (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c) :
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
      ∃ w ∈ omegaLimit atTop ϕ {x₀}, ∃ P : Finset S,
        P.Nonempty ∧ (∀ s, s ∈ P ↔ w s = 0) ∧ N.IsCriticalSiphon P ∧
        (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced
          (κ.restrict (N.avoidingSiphonReactions P)) (fillSiphonFace P xstar w) ∧
        (N.restrictReactions (N.avoidingSiphonReactions P)).stoichRank < N.stoichRank ∧
        N.massActionVectorField κ w = 0 := by
  classical
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0),
      closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem,
      (IsClosed.closure_subset_iff hK.isClosed).mpr hsubK⟩
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs
      (Set.singleton_nonempty x₀)
  by_cases hall : ∀ w ∈ omegaLimit atTop ϕ {x₀}, w.Positive
  · exact Or.inl ⟨p, hp, hall p hp⟩
  · push Not at hall
    obtain ⟨w, hw, hwnp⟩ := hall
    obtain ⟨s, hs⟩ : ∃ s, ¬ 0 < w s := not_forall.mp hwnp
    have hs0 : w s = 0 := le_antisymm (not_lt.mp hs) (hωnn w hw s)
    let P : Finset S := Finset.univ.filter (fun s => w s = 0)
    have hzeroSet : ∀ s, s ∈ P ↔ w s = 0 := by
      intro s
      simp [P]
    have hPne : P.Nonempty := ⟨s, (hzeroSet s).2 hs0⟩
    obtain ⟨hPcrit, hfacecb, hrank, hsteady⟩ :=
      N.criticalBoundaryOmegaFace_lowerRank hwr κ hxs hcb hγ0 hϕγ hK hmaps
        hgenω hωnn hωaff hx₀ hωc hw hzeroSet hPne
    exact Or.inr ⟨w, hw, P, hPne, hzeroSet, hPcrit, hfacecb, hrank, hsteady⟩

/-- Complex balance of a filled siphon-face state places its log-ratio to the reference in the
orthogonal complement of the face subnetwork's stoichiometric subspace. This is the toric
constraint on boundary omega equilibria after restricting to reactions that avoid the siphon. -/
theorem logRatio_fillSiphonFace_mem_orthogonalFaceStoich
    (N : Network S) (κ : N.RateConstants) {P : Finset S}
    (hP : N.IsSiphon P) (hwr : N.WeaklyReversible)
    {xstar x : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hxoutside : ∀ s, s ∉ P → 0 < x s)
    (hcbface :
      (N.restrictReactions (N.avoidingSiphonReactions P)).IsComplexBalanced
        (κ.restrict (N.avoidingSiphonReactions P)) (fillSiphonFace P xstar x)) :
    (fun s => Real.log (fillSiphonFace P xstar x s) - Real.log (xstar s)) ∈
      orthSum (N.restrictReactions (N.avoidingSiphonReactions P)).stoichSubspace := by
  let Nf := N.restrictReactions (N.avoidingSiphonReactions P)
  let κf := κ.restrict (N.avoidingSiphonReactions P)
  have hfillpos : (fillSiphonFace P xstar x).Positive := by
    intro s
    by_cases hs : s ∈ P
    · simpa [fillSiphonFace, hs] using hxs s
    · simpa [fillSiphonFace, hs] using hxoutside s hs
  have hwrf : Nf.WeaklyReversible :=
    N.restrictReactions_avoiding_siphon_weaklyReversible hP hwr
  have hcbstar : Nf.IsComplexBalanced κf xstar :=
    N.restrictReactions_avoiding_siphon_complexBalanced κ hP hwr hcb
  exact Nf.logRatio_orthogonal_of_complexBalanced hwrf κf hfillpos hxs hcbface hcbstar

/-- A boundary omega point whose zero set is a siphon carries the face subnetwork's toric
constraint: after filling its zero coordinates from the positive reference, the log-ratio is
orthogonal to every face-subnetwork reaction direction. -/
theorem logRatio_fillSiphonFace_mem_orthogonalFaceStoich_of_mem_boundaryOmega_siphon
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : N.IsSiphon P)
    (hzeroSet : ∀ s, s ∈ P ↔ w s = 0) :
    (fun s => Real.log (fillSiphonFace P xstar w s) - Real.log (xstar s)) ∈
      orthSum (N.restrictReactions (N.avoidingSiphonReactions P)).stoichSubspace := by
  have hfacePair := N.complexBalanced_and_massActionVectorField_eq_zero_of_mem_boundaryOmega_siphon
    hwr κ hxs hcb hγ0 hϕγ hgenω hωnn hωc hw hP hzeroSet
  have hwposOutside : ∀ s, s ∉ P → 0 < w s := by
    intro s hs
    have hnotzero : w s ≠ 0 := by
      intro hz
      exact hs ((hzeroSet s).2 hz)
    exact lt_of_le_of_ne (hωnn w hw s) (Ne.symm hnotzero)
  exact N.logRatio_fillSiphonFace_mem_orthogonalFaceStoich κ hP hwr hxs hcb
    hwposOutside hfacePair.1

/-- **Boundary omega-points are face equilibria.** Every point whose zero set is a siphon is
stationary for the full network. This is the stationarity projection of
`complexBalanced_and_massActionVectorField_eq_zero_of_mem_boundaryOmega_siphon`, which also
returns complex balance of the filled face state. -/
theorem massActionVectorField_eq_zero_of_mem_boundaryOmega_siphon
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hP : N.IsSiphon P)
    (hzeroSet : ∀ s, s ∈ P ↔ w s = 0) :
    N.massActionVectorField κ w = 0 :=
  (N.complexBalanced_and_massActionVectorField_eq_zero_of_mem_boundaryOmega_siphon
    hwr κ hxs hcb hγ0 hϕγ hgenω hωnn hωc hw hP hzeroSet).2

/-- Compactness makes the zero set of any boundary omega point a siphon, so every such point is a
stationary point of the full complex-balanced vector field. -/
theorem massActionVectorField_eq_zero_of_mem_boundaryOmega
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    {P : Finset S} (hzeroSet : ∀ s, s ∈ P ↔ w s = 0) :
    N.massActionVectorField κ w = 0 := by
  have hP : N.IsSiphon P :=
    N.isSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hw hzeroSet
  exact N.massActionVectorField_eq_zero_of_mem_boundaryOmega_siphon hwr κ hxs hcb hγ0 hϕγ
    hgenω hωnn hωc hw hP hzeroSet

/-- Every point in the omega-limit set is stationary once relative entropy is constant there.
The zero set may be empty: the face argument also covers positive omega-points by taking
`P = ∅`. -/
theorem massActionVectorField_eq_zero_on_omegaLimit
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K)
    (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c) :
    ∀ w ∈ omegaLimit atTop ϕ {x₀}, N.massActionVectorField κ w = 0 := by
  classical
  intro w hw
  let P : Finset S := Finset.univ.filter (fun s => w s = 0)
  have hzeroSet : ∀ s, s ∈ P ↔ w s = 0 := by
    intro s
    simp [P]
  exact N.massActionVectorField_eq_zero_of_mem_boundaryOmega hwr κ hxs hcb hγ0 hϕγ
    hK hmaps hgenω hωnn hωc hw hzeroSet

/-- **One positive ω-limit point ⇒ `ω = {x*}`.** For a weakly reversible network with a positive
complex-balanced reference `x*` and a positive start `x₀` in its class, suppose the mass-action
semiflow `ϕ` (curves `γ`) satisfies the standard LaSalle facts: ω-orbits solve the genuine field
(`hgenω`), the relative entropy is the constant `c` on the ω-limit set (`hωc`), ω-points are
nonnegative (`hωnn`) and affinely invariant (`hωaff`), and orbits from positive ω-points stay
positive (`hposorbit`). If the ω-limit set contains a single strictly positive point, it is
exactly `{x*}`. -/
theorem omegaLimit_eq_singleton_of_mem_positive
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0compat : N.StoichCompatible x₀ xstar)
    (hγ0 : ∀ x, γ x 0 = x) (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    {c : ℝ} (hωc : ∀ z ∈ omegaLimit atTop ϕ {x₀}, relEntropy xstar z = c)
    (hposorbit : ∀ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p →
      ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t))
    (hex : ∃ p ∈ omegaLimit atTop ϕ {x₀}, Concentration.Positive p) :
    omegaLimit atTop ϕ {x₀} = {xstar} := by
  obtain ⟨p, hpω, hppos⟩ := hex
  -- forward invariance of the ω-limit set, transported to the curves `γ`
  have hyωt : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      γ y t ∈ omegaLimit atTop ϕ {x₀} := by
    intro y hy t ht
    have := (Flow.isInvariant_omegaLimit atTop ϕ {x₀}
      (fun s => tendsto_atTop_mono (fun _ => le_add_self) tendsto_id) ⟨t, ht⟩) hy
    exact (hϕγ y ⟨t, ht⟩) ▸ this
  have hxstarmem : xstar ∈ N.positiveCompatibilityClass x₀ := ⟨hx0compat, hxs⟩
  -- the positive ω-point equals x*
  have hposyt : ∀ t : ℝ, 0 ≤ t → Concentration.Positive (γ p t) := hposorbit p hpω hppos
  have hyaff : p - x₀ ∈ N.stoichSubspace := hωaff p hpω
  have hyt_eq : ∀ t₀ : ℝ, 0 < t₀ → γ p t₀ = xstar := by
    intro t₀ ht₀
    have hposy : Concentration.Positive (γ p t₀) := hposyt t₀ ht₀.le
    have hydt : HasDerivAt (γ p) (N.massActionVectorField κ (γ p t₀)) t₀ := hgenω p hpω t₀ ht₀.le
    have hconst : ∀ t : ℝ, 0 ≤ t → relEntropy xstar (γ p t) = c :=
      fun t ht => hωc _ (hyωt p hpω t ht)
    have hchain := relEntropy_hasDerivAt hxs hposy (fun s => (hasDerivAt_pi.mp hydt) s)
    have heqc : (fun τ => relEntropy xstar (γ p τ)) =ᶠ[𝓝 t₀] (fun _ => c) := by
      filter_upwards [Ioi_mem_nhds ht₀] with τ hτ; exact hconst τ (le_of_lt hτ)
    have hd0 : HasDerivAt (fun τ => relEntropy xstar (γ p τ)) 0 t₀ :=
      (heqc.hasDerivAt_iff).mpr (hasDerivAt_const t₀ c)
    have hdiss : (∑ s, (Real.log (γ p t₀ s) - Real.log (xstar s))
        * N.massActionVectorField κ (γ p t₀) s) = 0 := hchain.unique hd0
    have hCB : N.IsComplexBalanced κ (γ p t₀) :=
      complexBalanced_of_dissipation_eq_zero N κ hposy hxs hcb hdiss
    have hmem : γ p t₀ ∈ N.positiveCompatibilityClass x₀ := by
      refine ⟨?_, hposy⟩
      show γ p t₀ - x₀ ∈ N.stoichSubspace
      have h1 : γ p t₀ - p ∈ N.stoichSubspace := by
        have hsoly : ∀ τ ∈ Set.Icc (0:ℝ) t₀,
            HasDerivAt (γ p) (N.massActionVectorField κ (γ p τ)) τ :=
          fun τ hτ => hgenω p hpω τ hτ.1
        have := sub_mem_stoichSubspace_of_solution N κ ht₀.le hsoly
        rwa [hγ0] at this
      have heq : γ p t₀ - x₀ = (γ p t₀ - p) + (p - x₀) := by ring
      rw [heq]; exact N.stoichSubspace.add_mem h1 hyaff
    exact N.isComplexBalanced_unique_in_positiveClass hwr κ hmem hxstarmem hCB hcb
  have hcont0 : ContinuousAt (γ p) 0 := (hgenω p hpω 0 le_rfl).continuousAt
  have htend1 : Tendsto (γ p) (𝓝[>] (0:ℝ)) (𝓝 p) := by
    have h1 : Tendsto (γ p) (𝓝[>] (0:ℝ)) (𝓝 (γ p 0)) :=
      hcont0.tendsto.mono_left nhdsWithin_le_nhds
    rwa [hγ0] at h1
  have htend2 : Tendsto (γ p) (𝓝[>] (0:ℝ)) (𝓝 xstar) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (hyt_eq τ hτ).symm
  have hpx : p = xstar := tendsto_nhds_unique htend1 htend2
  -- hence x* ∈ ω, the LaSalle constant is 0, and every ω-point equals x*
  have hxω : xstar ∈ omegaLimit atTop ϕ {x₀} := hpx ▸ hpω
  have hc0 : c = 0 := by
    have h := hωc xstar hxω
    rw [(relEntropy_eq_zero_iff (fun i => (hxs i).le) hxs).mpr rfl] at h
    exact h.symm
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hxω, fun w hw => ?_⟩
  have hw0 : relEntropy xstar w = 0 := by rw [hωc w hw, hc0]
  exact (relEntropy_eq_zero_iff (hωnn w hw) hxs).mp hw0

end Network

end CRNT
