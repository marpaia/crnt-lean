import CRNT.Deficiency.BorosLinkageProjection
import CRNT.Analysis.BorosPathEstimate
import CRNT.Kinetics.GeneralizedBirchSelector
import CRNT.Deficiency.LogMonomialRatio
import CRNT.Deficiency.SteadyStateKernel
import CRNT.Equilibria.CompatibilityClass
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The Boros Birch graph for a network

The parameter space is the incidence projection of the complex-transpose row space.  A moving
reference concentration, followed by the generalized Birch selector, gives a continuous lift of
each parameter to the requested positive stoichiometric class.
-/

namespace CRNT
namespace Network

open scoped InnerProductSpace

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A single finite path-length bound for all reachable ordered pairs of network complexes. -/
noncomputable def borosUniformReactionPathLength (N : Network S) : ℕ :=
  Analysis.borosUniformReachabilityPathLength
    (fun a b : N.ComplexIdx => N.DirectlyReacts a.val b.val)

private theorem exists_subtype_reach_of_reaches (N : Network S)
    {a c : Complex S} (ha : a ∈ N.complexes) (hreach : N.Reaches a c) :
    ∃ ci : N.ComplexIdx, ci.val = c ∧
      Relation.ReflTransGen (fun u v : N.ComplexIdx =>
        N.DirectlyReacts u.val v.val) ⟨a, ha⟩ ci := by
  induction hreach with
  | refl => exact ⟨⟨a, ha⟩, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c hprev hbc ih =>
      obtain ⟨bi, hbi, hpath⟩ := ih
      rcases hbc with ⟨r, hs, ht⟩
      have hc : c ∈ N.complexes := by
        rw [← ht]
        exact N.target_mem_complexes r
      let ci : N.ComplexIdx := ⟨c, hc⟩
      have hedge : N.DirectlyReacts bi.val ci.val := by
        rw [hbi]
        exact ⟨r, hs, ht⟩
      exact ⟨ci, rfl, hpath.tail hedge⟩

private theorem network_reaches_of_complexIdx_path (N : Network S)
    {a c : N.ComplexIdx}
    (h : Relation.ReflTransGen (fun u v : N.ComplexIdx =>
      N.DirectlyReacts u.val v.val) a c) : N.Reaches a.val c.val := by
  induction h with
  | refl => exact Reaches.refl N a.val
  | @tail b c hab hbc ih => exact ih.trans (Reaches.single hbc)

/-- Weak reversibility plus a large endpoint gap forces a large weighted increment on a reaction
edge in that linkage class. The path threshold is uniform over all complex pairs of the network. -/
theorem WeaklyReversible.exists_reaction_edge_weightedIncrement_gt
    (N : Network S) (hwr : N.WeaklyReversible) (b : ℝ) (hb : 0 ≤ b)
    (a c : N.ComplexIdx) (hclass : N.classOf a = N.classOf c)
    (gap : N.ComplexIdx → ℝ) (ha : gap a = 0)
    (hend : Analysis.borosWeightedPathBound b N.borosUniformReactionPathLength < gap c) :
    ∃ u v : N.ComplexIdx,
      N.DirectlyReacts u.val v.val ∧ b < Real.exp (-gap u) * gap v := by
  have hreach : N.Reaches a.val c.val :=
    hwr.reaches_of_linked (Quotient.exact hclass)
  obtain ⟨ci, hci, hreachIdx⟩ :=
    exists_subtype_reach_of_reaches N a.property hreach
  have hciEq : ci = c := Subtype.ext hci
  rw [hciEq] at hreachIdx
  exact Analysis.exists_reachable_edge_weightedIncrement_gt b hb gap hreachIdx ha
    (by simpa [borosUniformReactionPathLength] using hend)

/-- The large edge can be chosen inside the endpoint's linkage class. The path prefix places its
source in that class, while the direct reaction keeps its target there as well. -/
theorem WeaklyReversible.exists_reaction_edge_weightedIncrement_gt_with_context
    (N : Network S) (hwr : N.WeaklyReversible) (b : ℝ) (hb : 0 ≤ b)
    (a c : N.ComplexIdx) (hclass : N.classOf a = N.classOf c)
    (gap : N.ComplexIdx → ℝ) (ha : gap a = 0)
    (hend : Analysis.borosWeightedPathBound b N.borosUniformReactionPathLength < gap c) :
    ∃ r : N.R, N.classOf (N.sourceIdx r) = N.classOf a ∧
      b < Real.exp (-gap (N.sourceIdx r)) * gap (N.targetIdx r) := by
  have hreach : N.Reaches a.val c.val :=
    hwr.reaches_of_linked (Quotient.exact hclass)
  obtain ⟨ci, hci, hreachIdx⟩ :=
    exists_subtype_reach_of_reaches N a.property hreach
  have hciEq : ci = c := Subtype.ext hci
  rw [hciEq] at hreachIdx
  obtain ⟨u, v, huv, hau, hvc, hlarge⟩ :=
    Analysis.exists_reachable_edge_weightedIncrement_gt_with_context b hb gap
      hreachIdx ha (by simpa [borosUniformReactionPathLength] using hend)
  have hreachAU := network_reaches_of_complexIdx_path N hau
  have hclassAU : N.classOf a = N.classOf u :=
    Quotient.sound (Network.Linked.of_reaches hreachAU)
  rcases huv with ⟨r, hrs, hrt⟩
  have hsource : N.sourceIdx r = u := by
    apply Subtype.ext
    exact hrs
  have htarget : N.targetIdx r = v := by
    apply Subtype.ext
    exact hrt
  refine ⟨r, ?_, ?_⟩
  · rw [hsource]
    exact hclassAU.symm
  · simpa [hsource, htarget] using hlarge

/-- The incidence subspace represented in Euclidean complex coordinates. -/
noncomputable def borosIncidenceEuclidMap (N : Network S) :
    (N.R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ N.ComplexIdx :=
  (toEuclid (ι := N.ComplexIdx)).toLinearMap.comp N.incidenceMap

noncomputable def borosIncidenceEuclidSpace (N : Network S) :
    Submodule ℝ (EuclideanSpace ℝ N.ComplexIdx) :=
  LinearMap.range N.borosIncidenceEuclidMap

/-- A vector orthogonal to the incidence space is constant on each linkage class. Orthogonality
annihilates every reaction increment, and linkage is generated by those reaction edges. -/
theorem borosIncidenceOrthogonal_eq_on_linkageClass (N : Network S)
    {w : N.ComplexIdx → ℝ}
    (hw : toEuclid w ∈ N.borosIncidenceEuclidSpace.orthogonal)
    {c d : N.ComplexIdx} (hcd : N.classOf c = N.classOf d) :
    w c = w d := by
  have hedge : ∀ r : N.R, w (N.targetIdx r) = w (N.sourceIdx r) := by
    intro r
    let q : N.R → ℝ := Pi.single r 1
    have hdot :
        (∑ c : N.ComplexIdx, w c * N.incidenceMap q c) = 0 := by
      have h := (N.borosIncidenceEuclidSpace.mem_orthogonal' (toEuclid w)).mp hw
        (toEuclid (N.incidenceMap q)) ⟨q, rfl⟩
      rw [inner_toEuclid] at h
      exact h
    have hdot' :
        (∑ c : N.ComplexIdx, w c * N.incidenceMap (Pi.single r 1) c) = 0 := by
      simpa [q] using hdot
    rw [N.sum_mul_incidenceMap_single_eq_edgeIncrement] at hdot'
    linarith
  have hlink : N.Linked c.val d.val := Quotient.exact hcd
  simpa only [Subtype.coe_eta] using
    N.linked_imp_eq_of_edge_const hedge c.val c.property d.val hlink d.property

/-- Projection of the complex-transpose row space onto the incidence subspace. -/
noncomputable def borosBirchParameterMap (N : Network S) :
    (S → ℝ) →ₗ[ℝ] EuclideanSpace ℝ N.ComplexIdx :=
  N.borosIncidenceEuclidSpace.starProjection.toLinearMap.comp
    ((toEuclid (ι := N.ComplexIdx)).toLinearMap.comp N.complexTransposeMap)

/-- Boros's Birch parameter space `Π_I(range Yᵀ)`. -/
noncomputable def borosBirchParameterSpace (N : Network S) :
    Submodule ℝ (EuclideanSpace ℝ N.ComplexIdx) :=
  LinearMap.range N.borosBirchParameterMap

/-- A linear choice of species potentials realizing each point of the Boros parameter space. -/
noncomputable def borosBirchSection (N : Network S) :
    N.borosBirchParameterSpace →ₗ[ℝ] (S → ℝ) := by
  classical
  exact Classical.choose
    (N.borosBirchParameterMap.rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_rangeRestrict N.borosBirchParameterMap))

theorem borosBirchSection_spec (N : Network S)
    (z : N.borosBirchParameterSpace) :
    N.borosBirchParameterMap (N.borosBirchSection z) = z.1 := by
  classical
  have h := Classical.choose_spec
    (N.borosBirchParameterMap.rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_rangeRestrict N.borosBirchParameterMap))
  have hz := LinearMap.congr_fun h z
  exact congrArg Subtype.val hz

private theorem complexTranspose_inner_complexMap (N : Network S)
    (p : S → ℝ) (v : N.ComplexIdx → ℝ) :
    ⟪toEuclid (N.complexTransposeMap p), toEuclid v⟫_ℝ =
      ⟪toEuclid p, toEuclid (N.complexMap v)⟫_ℝ := by
  rw [inner_toEuclid, inner_toEuclid]
  change (∑ c : N.ComplexIdx, (∑ s : S, (c.val s : ℝ) * p s) * v c) =
    ∑ s : S, p s * (∑ c : N.ComplexIdx, v c * (c.val s : ℝ))
  calc
    (∑ c : N.ComplexIdx, (∑ s : S, (c.val s : ℝ) * p s) * v c) =
        ∑ c, ∑ s, ((c.val s : ℝ) * p s) * v c := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_mul]
    _ = ∑ s : S, ∑ c : N.ComplexIdx, ((c.val s : ℝ) * p s) * v c :=
      Finset.sum_comm
    _ = ∑ s : S, p s * (∑ c : N.ComplexIdx, v c * (c.val s : ℝ)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring

/-- A positive mass-action monomial is the exponential of the corresponding complex-transpose
log-concentration coordinate. -/
theorem complexMonomialVector_eq_exp_complexTranspose_log (N : Network S)
    {x : Concentration S} (hx : x.Positive) :
    N.complexMonomialVector x =
      fun c => Real.exp (N.complexTransposeMap (fun s => Real.log (x s)) c) := by
  funext c
  have hpos : 0 < N.complexMonomialVector x c := by
    rw [N.complexMonomialVector_apply]
    exact Complex.massActionMonomial_pos hx c.val
  rw [← Real.exp_log hpos, N.log_complexMonomialVector hx c]
  simp [complexTransposeMap]

/-- Pairing an incidence vector with an incidence-projected transpose row is the usual
transpose pairing. -/
private theorem inner_borosBirchParameterMap (N : Network S)
    {v : N.ComplexIdx → ℝ}
    (hv : toEuclid v ∈ N.borosIncidenceEuclidSpace) (p : S → ℝ) :
    ⟪toEuclid v, N.borosBirchParameterMap p⟫_ℝ =
      ⟪toEuclid p, toEuclid (N.complexMap v)⟫_ℝ := by
  change ⟪toEuclid v,
      N.borosIncidenceEuclidSpace.starProjection
        (toEuclid (N.complexTransposeMap p))⟫_ℝ = _
  calc
    _ = ⟪N.borosIncidenceEuclidSpace.starProjection (toEuclid v),
        toEuclid (N.complexTransposeMap p)⟫_ℝ := by
          rw [← N.borosIncidenceEuclidSpace.inner_starProjection_left_eq_right]
    _ = ⟪toEuclid v, toEuclid (N.complexTransposeMap p)⟫_ℝ := by
          rw [N.borosIncidenceEuclidSpace.starProjection_eq_self_iff.mpr hv]
    _ = ⟪toEuclid (N.complexTransposeMap p), toEuclid v⟫_ℝ := real_inner_comm _ _
    _ = ⟪toEuclid p, toEuclid (N.complexMap v)⟫_ℝ :=
          complexTranspose_inner_complexMap N p v

/-- If the Boros parameter projection of an incidence vector vanishes, then that vector is in
`ker Y`. -/
theorem complexMap_eq_zero_of_borosBirchProjection_eq_zero (N : Network S)
    {v : N.ComplexIdx → ℝ}
    (hv : toEuclid v ∈ N.borosIncidenceEuclidSpace)
    (hproj : N.borosBirchParameterSpace.starProjection (toEuclid v) = 0) :
    N.complexMap v = 0 := by
  have horth : toEuclid v ∈ N.borosBirchParameterSpace.orthogonal := by
    exact (N.borosBirchParameterSpace.starProjection_apply_eq_zero_iff).mp hproj
  have hpair (p : S → ℝ) :
      ⟪toEuclid v, N.borosBirchParameterMap p⟫_ℝ = 0 := by
    exact (N.borosBirchParameterSpace.mem_orthogonal' (toEuclid v)).mp horth _
      (LinearMap.mem_range.mpr ⟨p, rfl⟩)
  have hnorm :
      ⟪toEuclid (N.complexMap v), toEuclid (N.complexMap v)⟫_ℝ = 0 := by
    have h := hpair (N.complexMap v)
    rw [inner_borosBirchParameterMap N hv] at h
    exact h
  apply toEuclid.injective
  exact inner_self_eq_zero.mp hnorm

/-- A concentration whose mass-action kinetic vector has zero Boros projection is a steady
state. The kinetic vector lies in the incidence space, so the projected orthogonality condition
is exactly `Y(Aκ x^Y)=0`. -/
theorem isMassActionSteadyState_of_borosBirchProjection_eq_zero (N : Network S)
    (κ : N.RateConstants) (x : Concentration S)
    (hproj : N.borosBirchParameterSpace.starProjection
      (toEuclid (N.kineticMap κ (N.complexMonomialVector x))) = 0) :
    N.IsMassActionSteadyState κ x := by
  have hv : toEuclid (N.kineticMap κ (N.complexMonomialVector x)) ∈
      N.borosIncidenceEuclidSpace := by
    rcases N.kineticMap_mem_range_incidenceMap κ _ with ⟨r, hr⟩
    exact ⟨r, by change toEuclid (N.incidenceMap r) = _; rw [hr]⟩
  have hker := N.complexMap_eq_zero_of_borosBirchProjection_eq_zero hv hproj
  intro s
  rw [N.massActionVectorField_eq κ x, hker]
  rfl

/-- The generalized Birch selector continuously parametrizes the positive part of a requested
stoichiometric class by the incidence projection of the complex-transpose row space. The
complementary complex-log coordinate is continuous and lies in the orthogonal complement of the
incidence subspace, exactly the graph form used in the Boros reduction. -/
theorem exists_continuous_borosBirchGraph
    (N : Network S) (x₀ : Concentration S) (hx₀ : x₀.Positive) :
    ∃ x : N.borosBirchParameterSpace → Concentration S,
      Continuous x ∧
      (∀ z s, 0 < x z s) ∧
      (∀ z, x z - x₀ ∈ N.stoichSubspace) ∧
      Continuous (fun z =>
        toEuclid (N.complexTransposeMap (fun s => Real.log (x z s))) - z.1) ∧
      (∀ z, toEuclid (N.complexTransposeMap (fun s => Real.log (x z s))) - z.1 ∈
        N.borosIncidenceEuclidSpace.orthogonal) := by
  classical
  letI : TopologicalSpace S := ⊥
  let E := N.borosBirchParameterSpace
  let sectionCLM : E →L[ℝ] (S → ℝ) :=
    ⟨N.borosBirchSection, LinearMap.continuous_of_finiteDimensional _⟩
  let xstar : E → (S → ℝ) := fun z s => Real.exp (sectionCLM z s)
  have hxstar : ContDiff ℝ 1 xstar := by
    apply contDiff_pi.mpr
    intro s
    exact (Real.contDiff_exp (n := 1)).comp
      ((contDiff_apply ℝ ℝ s).comp sectionCLM.contDiff)
  have hxstarpos : ∀ z s, 0 < xstar z s := fun _ _ => Real.exp_pos _
  let c : E → (S → ℝ) := fun _ => x₀
  have hc : ContDiff ℝ 1 c := contDiff_const
  have hcpos : ∀ z s, 0 < c z s := fun _ s => hx₀ s
  have hclosure : GeneralizedClosureCondition N.stoichSubspace N.stoichSubspace :=
    ⟨rfl, Set.Subset.rfl⟩
  obtain ⟨x, hxcont, hxpos, hxsel⟩ :=
    exists_continuous_generalizedBirchSelector_varyingReference
      N.stoichSubspace N.stoichSubspace hclosure xstar hxstar hxstarpos c hc hcpos
  have hlogcont : Continuous (fun z : E => fun s => Real.log (x z s)) := by
    apply continuous_pi
    intro s
    exact Real.continuousOn_log.comp_continuous
      ((continuous_apply s).comp hxcont) (fun z => ne_of_gt (hxpos z s))
  have hrowcont : Continuous (fun z : E =>
      toEuclid (N.complexTransposeMap (fun s => Real.log (x z s)))) := by
    exact (LinearMap.continuous_of_finiteDimensional
      (((toEuclid (ι := N.ComplexIdx)).toLinearMap.comp N.complexTransposeMap))).comp hlogcont
  have hgraphcont : Continuous (fun z : E =>
      toEuclid (N.complexTransposeMap (fun s => Real.log (x z s))) - z.1) := by
    exact hrowcont.sub (continuous_subtype_val.comp continuous_id)
  have hgraphmem : ∀ z : E,
      toEuclid (N.complexTransposeMap (fun s => Real.log (x z s))) - z.1 ∈
        N.borosIncidenceEuclidSpace.orthogonal := by
    intro z
    rcases hxsel z with ⟨hxclass, hbirch⟩
    let d : S → ℝ := fun s => Real.log (x z s) - sectionCLM z s
    have hbirch' : toEuclid d ∈ (N.stoichSubspace.map toEuclid.toLinearMap).orthogonal := by
      have h := hbirch
      have hlogstar : ∀ s, Real.log (xstar z s) = sectionCLM z s := by
        intro s
        change Real.log (Real.exp (sectionCLM z s)) = _
        rw [Real.log_exp]
      have hd : d = (fun s => Real.log (x z s) - Real.log (xstar z s)) := by
        funext s
        dsimp [d]
        rw [← hlogstar s]
      have h' : d ∈ orthSum N.stoichSubspace := by
        rw [hd]
        exact h
      rw [orthSum_eq] at h'
      exact h'
    have hYd : toEuclid (N.complexTransposeMap d) ∈
        N.borosIncidenceEuclidSpace.orthogonal := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      rcases LinearMap.mem_range.mp hw with ⟨r, rfl⟩
      have hstoich : N.complexMap (N.incidenceMap r) ∈ N.stoichSubspace := by
        have heq : N.complexMap (N.incidenceMap r) = N.stoichMap r := by
          rw [← LinearMap.comp_apply, N.complexMap_comp_incidenceMap]
        rw [heq, ← N.range_stoichMap]
        exact ⟨r, rfl⟩
      have hstoich' : toEuclid (N.complexMap (N.incidenceMap r)) ∈
          N.stoichSubspace.map toEuclid.toLinearMap :=
        ⟨N.complexMap (N.incidenceMap r), hstoich, rfl⟩
      change ⟪toEuclid (N.incidenceMap r),
        toEuclid (N.complexTransposeMap d)⟫_ℝ = 0
      calc
        ⟪toEuclid (N.incidenceMap r), toEuclid (N.complexTransposeMap d)⟫_ℝ =
            ⟪toEuclid (N.complexTransposeMap d), toEuclid (N.incidenceMap r)⟫_ℝ :=
          real_inner_comm _ _
        _ = ⟪toEuclid d, toEuclid (N.complexMap (N.incidenceMap r))⟫_ℝ :=
          complexTranspose_inner_complexMap N d (N.incidenceMap r)
        _ = 0 := by
          rw [real_inner_comm]
          exact Submodule.inner_right_of_mem_orthogonal hstoich' hbirch'
    have hres : toEuclid (N.complexTransposeMap (sectionCLM z)) - z.1 ∈
        N.borosIncidenceEuclidSpace.orthogonal := by
      have hz := N.borosBirchSection_spec z
      change N.borosIncidenceEuclidSpace.starProjection
        (toEuclid (N.complexTransposeMap (N.borosBirchSection z))) = z.1 at hz
      have hz' : toEuclid (N.complexTransposeMap (sectionCLM z)) -
          N.borosIncidenceEuclidSpace.starProjection
            (toEuclid (N.complexTransposeMap (sectionCLM z))) ∈
              N.borosIncidenceEuclidSpace.orthogonal :=
        N.borosIncidenceEuclidSpace.sub_starProjection_mem_orthogonal _
      simpa [sectionCLM, hz] using hz'
    have hsum : toEuclid (N.complexTransposeMap d) +
        (toEuclid (N.complexTransposeMap (sectionCLM z)) - z.1) ∈
          N.borosIncidenceEuclidSpace.orthogonal :=
      N.borosIncidenceEuclidSpace.orthogonal.add_mem hYd hres
    have heq : toEuclid (N.complexTransposeMap (fun s => Real.log (x z s))) - z.1 =
        toEuclid (N.complexTransposeMap d) +
          (toEuclid (N.complexTransposeMap (sectionCLM z)) - z.1) := by
      have hlogsplit : (fun s => Real.log (x z s)) = d + sectionCLM z := by
        funext s
        dsimp [d]
        ring
      rw [hlogsplit, map_add, map_add]
      abel
    rw [heq]
    exact hsum
  refine ⟨x, hxcont, hxpos, ?_, hgraphcont, hgraphmem⟩
  intro z
  simpa [c] using (hxsel z).1

/-- The negative projection of the mass-action kinetic vector onto Boros's parameter space.
Its zero is equivalent, for the Birch selector's positive concentrations, to a steady state. -/
noncomputable def borosBirchKineticProjectionField (N : Network S)
    (κ : N.RateConstants)
    (x : N.borosBirchParameterSpace → Concentration S)
    (z : N.borosBirchParameterSpace) : N.borosBirchParameterSpace :=
  -N.borosBirchParameterSpace.orthogonalProjectionOnto
    (toEuclid (N.kineticMap κ (N.complexMonomialVector (x z))))

/-- The projected kinetic field varies continuously with a continuous positive concentration
selector. -/
theorem continuous_borosBirchKineticProjectionField (N : Network S)
    (κ : N.RateConstants)
    {x : N.borosBirchParameterSpace → Concentration S}
    (hxcont : Continuous x) (hxpos : ∀ z s, 0 < x z s) :
    Continuous (N.borosBirchKineticProjectionField κ x) := by
  classical
  letI : TopologicalSpace S := ⊥
  have hlogcont : Continuous (fun z : N.borosBirchParameterSpace =>
      fun s => Real.log (x z s)) := by
    apply continuous_pi
    intro s
    exact Real.continuousOn_log.comp_continuous
      ((continuous_apply s).comp hxcont) (fun z => ne_of_gt (hxpos z s))
  have hrowcont : Continuous (fun z : N.borosBirchParameterSpace =>
      toEuclid (N.complexTransposeMap (fun s => Real.log (x z s)))) := by
    exact (LinearMap.continuous_of_finiteDimensional
      (((toEuclid (ι := N.ComplexIdx)).toLinearMap.comp N.complexTransposeMap))).comp
        hlogcont
  have hrowrawcont : Continuous (fun z : N.borosBirchParameterSpace =>
      N.complexTransposeMap (fun s => Real.log (x z s))) := by
    exact (LinearMap.continuous_of_finiteDimensional N.complexTransposeMap).comp hlogcont
  have hmonocont : Continuous (fun z : N.borosBirchParameterSpace =>
      N.complexMonomialVector (x z)) := by
    have hexp : Continuous (fun z : N.borosBirchParameterSpace =>
        fun c => Real.exp (N.complexTransposeMap
          (fun s => Real.log (x z s)) c)) := by
      apply continuous_pi
      intro c
      exact Real.continuous_exp.comp ((continuous_apply c).comp hrowrawcont)
    have heq : (fun z : N.borosBirchParameterSpace => N.complexMonomialVector (x z)) =
        fun z => fun c => Real.exp (N.complexTransposeMap
          (fun s => Real.log (x z s)) c) := by
      funext z
      exact N.complexMonomialVector_eq_exp_complexTranspose_log (hxpos z)
    rw [heq]
    exact hexp
  let kineticEuclid : (N.ComplexIdx → ℝ) →ₗ[ℝ]
      EuclideanSpace ℝ N.ComplexIdx :=
    (toEuclid (ι := N.ComplexIdx)).toLinearMap.comp (N.kineticMap κ)
  have hflowcont : Continuous (fun z : N.borosBirchParameterSpace =>
      toEuclid (N.kineticMap κ (N.complexMonomialVector (x z)))) := by
    exact (LinearMap.continuous_of_finiteDimensional kineticEuclid).comp hmonocont
  have hprojcont :=
    N.borosBirchParameterSpace.orthogonalProjectionOnto.continuous.comp hflowcont
  change Continuous (fun z : N.borosBirchParameterSpace =>
    -N.borosBirchParameterSpace.orthogonalProjectionOnto
      (toEuclid (N.kineticMap κ (N.complexMonomialVector (x z)))))
  exact continuous_neg.comp hprojcont

/-- A zero of the Birch-selector kinetic field is a steady state in its selected concentration.
The selector itself supplies positivity and membership in the requested class. -/
theorem isMassActionSteadyState_of_borosBirchKineticProjectionField_eq_zero
    (N : Network S) (κ : N.RateConstants)
    (x : N.borosBirchParameterSpace → Concentration S)
    (z : N.borosBirchParameterSpace)
    (hzero : N.borosBirchKineticProjectionField κ x z = 0) :
    N.IsMassActionSteadyState κ (x z) := by
  have hproj : N.borosBirchParameterSpace.starProjection
      (toEuclid (N.kineticMap κ (N.complexMonomialVector (x z)))) = 0 := by
    change -N.borosBirchParameterSpace.orthogonalProjectionOnto
      (toEuclid (N.kineticMap κ (N.complexMonomialVector (x z)))) = 0 at hzero
    have h' := neg_eq_zero.mp hzero
    have horth := (N.borosBirchParameterSpace.orthogonalProjectionOnto_eq_zero_iff).mp h'
    exact (N.borosBirchParameterSpace.starProjection_apply_eq_zero_iff).mpr horth
  exact N.isMassActionSteadyState_of_borosBirchProjection_eq_zero κ (x z) hproj

/-- The full Boros reduction after its rate-dependent boundary estimate: a continuous Birch
selector and strict inward pairing on every active nested face yield a positive steady state in
the requested class. -/
theorem exists_borosBirchSteadyState_of_activeInward
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    [Nonempty (Quotient N.linkedSetoid)] (κ : N.RateConstants)
    {x₀ : Concentration S}
    (x : N.borosBirchParameterSpace → Concentration S)
    (hxcont : Continuous x) (hxpos : ∀ z s, 0 < x z s)
    (hxclass : ∀ z, x z ∈ N.positiveCompatibilityClass x₀)
    (r : ℕ → ℝ)
    (hinward : ∀ z ∈ Analysis.borosWithinSubspaceNestedDomain
          N.borosLinkageProjectionSystem N.borosBirchParameterSpace r,
      ∀ Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid),
        ‖Analysis.borosWithinSubspaceProjectionFamily
            N.borosLinkageProjectionSystem N.borosBirchParameterSpace Q z‖ =
          Analysis.borosProjectionRadius r Q →
        0 < inner ℝ (N.borosBirchKineticProjectionField κ x z)
          (Analysis.borosWithinSubspaceProjectionFamily
            N.borosLinkageProjectionSystem N.borosBirchParameterSpace Q z)) :
    ∃ y : Concentration S,
      y ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ y := by
  let P := N.borosLinkageProjectionSystem
  let D := Analysis.borosWithinSubspaceNestedDomain P N.borosBirchParameterSpace r
  have hfield : Continuous (N.borosBirchKineticProjectionField κ x) :=
    N.continuous_borosBirchKineticProjectionField κ hxcont hxpos
  obtain ⟨z, hzD, hzfield⟩ :=
    Analysis.borosWithinSubspaceNestedDomain_exists_zero_of_strict_inward
      P N.borosBirchParameterSpace r (N.borosBirchKineticProjectionField κ x)
      hfield.continuousOn (by simpa [P, D] using hinward)
  exact ⟨x z, hxclass z,
    N.isMassActionSteadyState_of_borosBirchKineticProjectionField_eq_zero κ x z hzfield⟩

end Network
end CRNT
