import CRNT.Graph.PositiveCirculation
import CRNT.Flux.Elementary
import CRNT.Deficiency.CycleExactSequence
import CRNT.LinearAlgebra.ConformalDecomposition

/-!
# Directed-cycle decomposition of graph circulations

Nonnegative graph circulations form an s-cone `ker ∂ ∩ ℝ_{≥0}^R`.  Its extreme rays
are the directed-cycle flows.  Consequently every nonnegative graph circulation is a
finite nonnegative sum of directed-cycle flows, and a strictly positive circulation is
exactly a positive cycle cover of all reaction channels.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Nonnegative graph circulation. -/
def IsNonnegativeGraphCirculation (N : Network S) (v : N.R → ℝ) : Prop :=
  (∀ r, 0 ≤ v r) ∧ N.incidenceMap v = 0

/-- A reaction edge carrying strictly positive weight in a flux vector. -/
def PositiveFluxEdge (N : Network S) (v : N.R → ℝ)
    (c d : N.ComplexIdx) : Prop :=
  ∃ r : N.R, N.sourceIdx r = c ∧ N.targetIdx r = d ∧ 0 < v r

/-- A finite list of reactions forming a directed path whose every edge has positive flux. -/
def IsPositiveFluxPath (N : Network S) (v : N.R → ℝ) :
    List N.R → N.ComplexIdx → N.ComplexIdx → Prop
  | [], c, d => c = d
  | r :: rs, c, d =>
      N.sourceIdx r = c ∧ 0 < v r ∧ IsPositiveFluxPath N v rs (N.targetIdx r) d

/-- The reaction-count flux of a finite reaction list, counting repeated reactions with
multiplicity. -/
def unitReactionFlux (N : Network S) (r : N.R) : N.R → ℝ := Pi.single r 1

def reactionListFlux (N : Network S) : List N.R → (N.R → ℝ)
  | [] => 0
  | r :: rs => unitReactionFlux N r + reactionListFlux N rs

/-- Reaction-count fluxes are pointwise nonnegative. -/
theorem reactionListFlux_nonneg (N : Network S) (rs : List N.R) :
    ∀ r, 0 ≤ reactionListFlux N rs r := by
  induction rs with
  | nil => intro r; simp [reactionListFlux]
  | cons e es ih =>
      intro r
      simp only [reactionListFlux, Pi.add_apply]
      have hsingle : 0 ≤ unitReactionFlux N e r := by
        by_cases h : r = e <;> simp [unitReactionFlux, h]
      exact add_nonneg hsingle (ih r)

/-- Pairing a reaction-count flux with any scalar reaction weight sums that weight once per
occurrence in the concrete reaction list. -/
theorem reactionListFlux_weighted_sum (N : Network S) (rs : List N.R)
    (f : N.R → ℝ) :
    (∑ r, reactionListFlux N rs r * f r) = (rs.map f).sum := by
  induction rs with
  | nil => simp [reactionListFlux]
  | cons e es ih =>
      calc
        (∑ r, reactionListFlux N (e :: es) r * f r) =
            (∑ r, unitReactionFlux N e r * f r) +
              ∑ r, reactionListFlux N es r * f r := by
                simp only [reactionListFlux, Pi.add_apply]
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro r _
                ring
        _ = f e + (es.map f).sum := by
              rw [ih]
              simp [unitReactionFlux, Pi.single_apply]
        _ = ((e :: es).map f).sum := by simp

/-- Every reaction occurring with positive multiplicity in a positive-flux path itself has
positive flux in the path's support vector. -/
theorem IsPositiveFluxPath.reactionListFlux_pos_supportedBy (N : Network S)
    {v : N.R → ℝ} {rs : List N.R} {a b : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs a b) {r : N.R}
    (hr : 0 < reactionListFlux N rs r) : 0 < v r := by
  induction rs generalizing a b with
  | nil => simp [reactionListFlux] at hr
  | cons e es ih =>
      rcases hp with ⟨_, hepos, hp'⟩
      by_cases hre : r = e
      · simpa [hre] using hepos
      · have htail : 0 < reactionListFlux N es r := by
          have heq : unitReactionFlux N e r = 0 := by
            simp [unitReactionFlux, hre]
          change 0 < unitReactionFlux N e r + reactionListFlux N es r at hr
          rw [heq, zero_add] at hr
          exact hr
        exact ih hp' htail

/-- The incidence image of a unit reaction flux is its target unit vector minus its source unit
vector. -/
theorem incidenceMap_single (N : Network S) (r : N.R) :
    N.incidenceMap (Pi.single r (1 : ℝ)) =
      Pi.single (N.targetIdx r) 1 - Pi.single (N.sourceIdx r) 1 := by
  funext c
  rw [N.incidenceMap_apply, Finset.sum_eq_single r]
  · simp [Pi.single_apply, eq_comm]
  · intro r' _ hne
    simp [hne]
  · intro h
    exact False.elim (h (Finset.mem_univ r))

/-- The incidence of a positive-flux path is the endpoint difference, by telescoping the unit
reaction boundaries along its concrete reaction list. -/
theorem IsPositiveFluxPath.incidenceMap_reactionListFlux (N : Network S)
    {v : N.R → ℝ} {rs : List N.R} {a b : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs a b) :
    N.incidenceMap (reactionListFlux N rs) =
      Pi.single b 1 - Pi.single a 1 := by
  induction rs generalizing a with
  | nil =>
      change a = b at hp
      subst b
      simp [reactionListFlux]
  | cons r rs ih =>
      rcases hp with ⟨hs, _hr, hp'⟩
      change N.incidenceMap (Pi.single r 1 + reactionListFlux N rs) = _
      rw [map_add, N.incidenceMap_single, ih hp', hs]
      abel

/-- Appending a positive-flow reaction extends the endpoint of a positive-flux path. -/
theorem IsPositiveFluxPath.append_edge (N : Network S) {v : N.R → ℝ}
    {rs : List N.R} {a b : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs a b) {r : N.R} {c : N.ComplexIdx}
    (hs : N.sourceIdx r = b) (ht : N.targetIdx r = c) (hr : 0 < v r) :
    N.IsPositiveFluxPath v (rs ++ [r]) a c := by
  induction rs generalizing a with
  | nil =>
      change a = b at hp
      simp only [List.nil_append, IsPositiveFluxPath]
      exact ⟨hs.trans hp.symm, hr, ht⟩
  | cons r' rs ih =>
      rcases hp with ⟨hs', hr', hp'⟩
      simp only [List.cons_append, IsPositiveFluxPath]
      exact ⟨hs', hr', ih hp'⟩

/-- Along a positive-flux path, the multiset of targets together with its start vertex equals
the multiset of sources together with its end vertex. This is the finite path analogue of
telescoping incidence balance, retaining the concrete edge order. -/
theorem IsPositiveFluxPath.targetList_append_start_perm_sourceList_append_end
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {a b : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs a b) :
    List.Perm (rs.map N.targetIdx ++ [a]) (rs.map N.sourceIdx ++ [b]) := by
  induction rs generalizing a with
  | nil =>
      change a = b at hp
      simp [hp]
  | cons r rs ih =>
      rcases hp with ⟨hs, _hr, htail⟩
      have h₁ : List.Perm
          (N.targetIdx r :: rs.map N.targetIdx ++ [a])
          ((rs.map N.targetIdx ++ [N.targetIdx r]) ++ [a]) := by
        have hcomm : List.Perm ([N.targetIdx r] ++ rs.map N.targetIdx)
            (rs.map N.targetIdx ++ [N.targetIdx r]) := by
          simpa using (List.perm_append_comm :
            ([N.targetIdx r] ++ rs.map N.targetIdx).Perm
              (rs.map N.targetIdx ++ [N.targetIdx r]))
        simpa [List.append_assoc] using hcomm.append_right [a]
      have h₂ : List.Perm
          ((rs.map N.targetIdx ++ [N.targetIdx r]) ++ [a])
          ((rs.map N.sourceIdx ++ [b]) ++ [a]) := (ih htail).append_right [a]
      have h₃ : List.Perm
          ((rs.map N.sourceIdx ++ [b]) ++ [a])
          ([a] ++ (rs.map N.sourceIdx ++ [b])) :=
        (List.perm_append_comm :
          ((rs.map N.sourceIdx ++ [b]) ++ [a]).Perm
            ([a] ++ (rs.map N.sourceIdx ++ [b])))
      have h := h₁.trans (h₂.trans h₃)
      simpa [List.map_cons, List.cons_append, List.append_assoc, hs] using h

/-- A closed positive-flux path has the same multiset of source and target complexes, so its
source and target lists determine a permutation of reaction positions even when complexes repeat. -/
theorem IsPositiveFluxPath.targetList_perm_sourceList
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {a : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs a a) :
    List.Perm (rs.map N.targetIdx) (rs.map N.sourceIdx) := by
  have h := IsPositiveFluxPath.targetList_append_start_perm_sourceList_append_end N hp
  have hcount : ∀ c : N.ComplexIdx,
      List.count c (rs.map N.targetIdx) = List.count c (rs.map N.sourceIdx) := by
    intro c
    have hle := h.subperm.count_le c
    have hge := h.symm.subperm.count_le c
    simp only [List.count_append, List.count_singleton] at hle hge
    omega
  exact List.perm_iff_count.mpr hcount

/-- Reflexive-transitive reachability by positive-flux edges is equivalent to a concrete finite
reaction list carrying positive flux on every edge. -/
theorem positiveFluxPath_iff_reflTransGen (N : Network S) {v : N.R → ℝ}
    {a b : N.ComplexIdx} :
    Relation.ReflTransGen (N.PositiveFluxEdge v) a b ↔
      ∃ rs : List N.R, N.IsPositiveFluxPath v rs a b := by
  constructor
  · intro hab
    induction hab with
    | refl => exact ⟨[], rfl⟩
    | @tail b c hab hbc ih =>
        rcases ih with ⟨rs, hrs⟩
        rcases hbc with ⟨r, hs, ht, hr⟩
        exact ⟨rs ++ [r], IsPositiveFluxPath.append_edge N hrs hs ht hr⟩
  · rintro ⟨rs, hrs⟩
    induction rs generalizing a with
    | nil =>
        change a = b at hrs
        subst b
        exact Relation.ReflTransGen.refl
    | cons r rs ih =>
        rcases hrs with ⟨hs, hr, hrs'⟩
        have hstep : N.PositiveFluxEdge v a (N.targetIdx r) :=
          ⟨r, hs, rfl, hr⟩
        exact Relation.ReflTransGen.head hstep (ih hrs')

/-- Every positive edge in a nonnegative graph circulation has a return path consisting only of
positive-flow edges. The proof takes the vertices reachable from the edge's target; if its source
were outside, the edge would carry positive flux into that set while no positive edge could leave,
contradicting circulation balance across the cut. -/
theorem IsNonnegativeGraphCirculation.positiveEdge_has_returnPath
    (N : Network S) {v : N.R → ℝ} (hv : N.IsNonnegativeGraphCirculation v)
    {r₀ : N.R} (hr₀ : 0 < v r₀) :
    Relation.ReflTransGen (N.PositiveFluxEdge v)
      (N.targetIdx r₀) (N.sourceIdx r₀) := by
  classical
  by_contra hret
  let U : Finset N.ComplexIdx :=
    Finset.univ.filter (fun c => Relation.ReflTransGen (N.PositiveFluxEdge v)
      (N.targetIdx r₀) c)
  have hmem : ∀ c : N.ComplexIdx,
      c ∈ U ↔ Relation.ReflTransGen (N.PositiveFluxEdge v) (N.targetIdx r₀) c := by
    intro c
    simp [U]
  have htgt : N.targetIdx r₀ ∈ U :=
    (hmem _).2 Relation.ReflTransGen.refl
  have hsrc : N.sourceIdx r₀ ∉ U := by
    intro hs
    exact hret ((hmem _).1 hs)
  have hclosed : ∀ r : N.R, N.sourceIdx r ∈ U → 0 < v r → N.targetIdx r ∈ U := by
    intro r hs hr
    rw [hmem] at hs ⊢
    exact hs.trans (Relation.ReflTransGen.single ⟨r, rfl, rfl, hr⟩)
  have hvertex : ∀ c : N.ComplexIdx,
      excessVertex N.sourceIdx N.targetIdx v c = 0 := by
    intro c
    have hc := congrFun hv.2 c
    rw [N.incidenceMap_apply] at hc
    have hedge : ∀ e : N.R,
        (if N.sourceIdx e = c then v e else 0) -
            (if N.targetIdx e = c then v e else 0) =
          -(v e * ((if N.targetIdx e = c then 1 else 0) -
            (if N.sourceIdx e = c then 1 else 0))) := by
      intro e
      by_cases hs : N.sourceIdx e = c <;>
        by_cases ht : N.targetIdx e = c <;> simp [hs, ht]
    rw [excessVertex, ← Finset.sum_sub_distrib]
    calc
      (∑ e : N.R,
          ((if N.sourceIdx e = c then v e else 0) -
            (if N.targetIdx e = c then v e else 0)))
          = ∑ e : N.R, -(v e * ((if N.targetIdx e = c then 1 else 0) -
              (if N.sourceIdx e = c then 1 else 0))) := by
                exact Finset.sum_congr rfl (fun e _ => hedge e)
      _ = -(∑ e : N.R, v e * ((if N.targetIdx e = c then 1 else 0) -
              (if N.sourceIdx e = c then 1 else 0))) := by
                rw [Finset.sum_neg_distrib]
      _ = 0 := by rw [hc]; simp
  have hset0 : excessSet N.sourceIdx N.targetIdx v U = 0 := by
    rw [excessSet_eq_sum_excessVertex]
    simp [hvertex]
  have hout :
      (∑ r, if N.sourceIdx r ∈ U ∧ N.targetIdx r ∉ U then v r else 0) = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases h : N.sourceIdx r ∈ U ∧ N.targetIdx r ∉ U
    · have hnpos : ¬ 0 < v r := fun hp => h.2 (hclosed r h.1 hp)
      have hz : v r = 0 := le_antisymm (le_of_not_gt hnpos) (hv.1 r)
      simp [h, hz]
    · simp [h]
  have hinpos :
      0 < ∑ r, if N.sourceIdx r ∉ U ∧ N.targetIdx r ∈ U then v r else 0 := by
    refine Finset.sum_pos' (fun r _ => ?_) ⟨r₀, Finset.mem_univ r₀, ?_⟩
    · by_cases h : N.sourceIdx r ∉ U ∧ N.targetIdx r ∈ U
      · rw [if_pos h]
        exact hv.1 r
      · rw [if_neg h]
    · rw [if_pos ⟨hsrc, htgt⟩]
      exact hr₀
  have hneg : excessSet N.sourceIdx N.targetIdx v U < 0 := by
    rw [excessSet, hout, zero_sub]
    exact neg_neg_of_pos hinpos
  rw [hset0] at hneg
  exact (lt_irrefl 0) hneg

/-- Every positive edge in a nonnegative graph circulation lies on a concrete closed walk whose
return path uses only positive-flow reactions. -/
theorem IsNonnegativeGraphCirculation.positiveEdge_has_returnPathList
    (N : Network S) {v : N.R → ℝ} (hv : N.IsNonnegativeGraphCirculation v)
    {r₀ : N.R} (hr₀ : 0 < v r₀) :
    ∃ rs : List N.R,
      N.IsPositiveFluxPath v rs (N.targetIdx r₀) (N.sourceIdx r₀) := by
  exact (N.positiveFluxPath_iff_reflTransGen).mp
    (hv.positiveEdge_has_returnPath N hr₀)

/-- Every positive-flow reaction in a nonnegative circulation starts a concrete closed walk whose
reaction list begins with that edge and whose entire walk stays in the positive support. -/
theorem IsNonnegativeGraphCirculation.positiveEdge_has_closedWalk
    (N : Network S) {v : N.R → ℝ} (hv : N.IsNonnegativeGraphCirculation v)
    {r₀ : N.R} (hr₀ : 0 < v r₀) :
    ∃ rs : List N.R,
      N.IsPositiveFluxPath v (r₀ :: rs) (N.sourceIdx r₀) (N.sourceIdx r₀) := by
  obtain ⟨rs, hrs⟩ := hv.positiveEdge_has_returnPathList N hr₀
  refine ⟨rs, ?_⟩
  change N.sourceIdx r₀ = N.sourceIdx r₀ ∧ 0 < v r₀ ∧
    N.IsPositiveFluxPath v rs (N.targetIdx r₀) (N.sourceIdx r₀)
  exact ⟨rfl, hr₀, hrs⟩

/-- Support-minimal nonzero nonnegative graph circulation: algebraic directed cycle flow. -/
def IsDirectedCycleFlow (N : Network S) (v : N.R → ℝ) : Prop :=
  N.IsNonnegativeGraphCirculation v ∧ v ≠ 0 ∧
    ∀ w : N.R → ℝ,
      N.IsNonnegativeGraphCirculation w → w ≠ 0 →
      N.fluxSupport w ⊆ N.fluxSupport v →
      N.fluxSupport v ⊆ N.fluxSupport w

/-- A support-minimal graph circulation is supported exactly on the reaction-count flux of a
positive closed walk through any chosen support edge. This converts the abstract support
minimality used by the linear-algebra decomposition into concrete graph-cycle data. -/
theorem IsDirectedCycleFlow.exists_closedWalk_flux_of_mem_support
    (N : Network S) {v : N.R → ℝ} (hv : N.IsDirectedCycleFlow v)
    {r₀ : N.R} (hr₀ : r₀ ∈ N.fluxSupport v) :
    ∃ rs : List N.R,
      N.IsPositiveFluxPath v (r₀ :: rs) (N.sourceIdx r₀) (N.sourceIdx r₀) ∧
      ∃ w : N.R → ℝ, w = reactionListFlux N (r₀ :: rs) ∧
        N.IsNonnegativeGraphCirculation w ∧ 0 < w r₀ ∧
          N.fluxSupport w ⊆ N.fluxSupport v ∧ N.fluxSupport w = N.fluxSupport v := by
  have hv₀ : 0 < v r₀ := by
    have hne := (N.mem_fluxSupport_iff v r₀).1 hr₀
    exact lt_of_le_of_ne (hv.1.1 r₀) (Ne.symm hne)
  obtain ⟨rs, hwalk⟩ := hv.1.positiveEdge_has_closedWalk N hv₀
  let w : N.R → ℝ := reactionListFlux N (r₀ :: rs)
  have hwnn : ∀ r, 0 ≤ w r := by
    intro r
    exact reactionListFlux_nonneg N (r₀ :: rs) r
  have hwinc : N.incidenceMap w = 0 := by
    dsimp [w]
    rw [IsPositiveFluxPath.incidenceMap_reactionListFlux N hwalk]
    simp
  have hwr₀ : 0 < w r₀ := by
    have htailnn := reactionListFlux_nonneg N rs r₀
    change 0 < unitReactionFlux N r₀ r₀ + reactionListFlux N rs r₀
    have hunit : unitReactionFlux N r₀ r₀ = 1 := by
      simp [unitReactionFlux]
    rw [hunit]
    linarith
  have hw0 : w ≠ 0 := by
    intro hz
    have hz₀ := congrFun hz r₀
    rw [hz₀] at hwr₀
    exact (lt_irrefl 0) hwr₀
  have hsub : N.fluxSupport w ⊆ N.fluxSupport v := by
    intro r hr
    have hwne := (N.mem_fluxSupport_iff w r).1 hr
    have hwpos : 0 < w r := lt_of_le_of_ne (hwnn r) (Ne.symm hwne)
    have hvpos := IsPositiveFluxPath.reactionListFlux_pos_supportedBy N hwalk hwpos
    exact (N.mem_fluxSupport_iff v r).2 hvpos.ne'
  have hrev := hv.2.2 w ⟨hwnn, hwinc⟩ hw0 hsub
  exact ⟨rs, hwalk, w, rfl, ⟨hwnn, hwinc⟩, hwr₀, hsub,
    Finset.Subset.antisymm hsub hrev⟩

private theorem nonnegElementary_incidence_iff_cycle (N : Network S) (v : N.R → ℝ) :
    CRNT.NonnegElementary (LinearMap.ker N.incidenceMap) v ↔ N.IsDirectedCycleFlow v := by
  constructor
  · rintro ⟨hvker, hv0, hvnn, hmin⟩
    refine ⟨⟨hvnn, hvker⟩, hv0, ?_⟩
    intro w hw hw0 hsub
    have hsub' : CRNT.support w ⊆ CRNT.support v := by
      simpa [CRNT.support, Network.fluxSupport] using hsub
    have hrev := hmin w hw.2 hw0 hw.1 hsub'
    simpa [CRNT.support, Network.fluxSupport] using hrev
  · rintro ⟨hv, hv0, hmin⟩
    refine ⟨hv.2, hv0, hv.1, ?_⟩
    intro w hwker hw0 hwnn hsub
    have hw : N.IsNonnegativeGraphCirculation w := ⟨hwnn, hwker⟩
    have hsub' : N.fluxSupport w ⊆ N.fluxSupport v := by
      simpa [CRNT.support, Network.fluxSupport] using hsub
    have hrev := hmin w hw hw0 hsub'
    simpa [CRNT.support, Network.fluxSupport] using hrev

/-- A support-minimal graph circulation is a positive scalar multiple of the reaction-count flux
of a closed walk through each chosen support edge. The result follows from nonnegative
elementarity once the cut argument has produced a supported closed walk. -/
theorem IsDirectedCycleFlow.exists_pos_smul_closedWalkFlux
    (N : Network S) {v : N.R → ℝ} (hv : N.IsDirectedCycleFlow v)
    {r₀ : N.R} (hr₀ : r₀ ∈ N.fluxSupport v) :
    ∃ rs : List N.R,
      N.IsPositiveFluxPath v (r₀ :: rs) (N.sourceIdx r₀) (N.sourceIdx r₀) ∧
      ∃ t : ℝ, 0 < t ∧ v = t • reactionListFlux N (r₀ :: rs) := by
  obtain ⟨rs, hwalk, w, hwdef, hw, hwpos, _hwsub, hsupp⟩ :=
    IsDirectedCycleFlow.exists_closedWalk_flux_of_mem_support N hv hr₀
  have hw0 : w ≠ 0 := by
    intro hz
    have hz₀ := congrFun hz r₀
    rw [hz₀] at hwpos
    exact (lt_irrefl 0) hwpos
  have he : CRNT.NonnegElementary (LinearMap.ker N.incidenceMap) v :=
    (nonnegElementary_incidence_iff_cycle N v).2 hv
  have hwker : w ∈ LinearMap.ker N.incidenceMap := by
    rw [LinearMap.mem_ker]
    exact hw.2
  have hsub : CRNT.support w ⊆ CRNT.support v := by
    simpa [CRNT.support, Network.fluxSupport] using _hwsub
  obtain ⟨t, ht, hmul⟩ :=
    he.eq_pos_smul_of_support_subset hwker hw0 hw.1 hsub
  rw [hwdef] at hmul
  exact ⟨rs, hwalk, t, ht, hmul⟩

/-- At deficiency zero, every directed-cycle flow is also an elementary stoichiometric
flux mode.  The deficiency-zero hypothesis is necessary in general: without it a graph-cycle
support can contain a smaller stoichiometrically stationary support that is not a graph
circulation. -/
theorem directedCycleFlow_isElementaryFluxMode (N : Network S) (hδ : N.DeficiencyZero)
    {v : N.R → ℝ} (hv : N.IsDirectedCycleFlow v) :
    N.IsElementaryFluxMode v := by
  refine ⟨?_, hv.2.1, ?_⟩
  · exact ⟨hv.1.1, by
      have hfac := congrArg (fun f => f v) N.complexMap_comp_incidenceMap
      simpa [IsStationaryFlux, hv.1.2] using hfac.symm⟩
  · intro w hw hw0 hsub
    have hcycle : N.IsNonnegativeGraphCirculation w := by
      refine ⟨hw.1, ?_⟩
      exact (N.deficiencyZero_iff_stoichCycle_is_graphCycle.mp hδ) w hw.2
    exact hv.2.2 w hcycle hw0 hsub

/-- Every nonnegative graph circulation is a finite sum of directed-cycle flows. -/
theorem graphCirculation_decomposes_into_cycles (N : Network S)
    {v : N.R → ℝ} (hv : N.IsNonnegativeGraphCirculation v) :
    ∃ (m : ℕ) (c : Fin m → (N.R → ℝ)) (a : Fin m → ℝ),
      (∀ i, N.IsDirectedCycleFlow (c i)) ∧
      (∀ i, 0 ≤ a i) ∧
      v = ∑ i, a i • c i := by
  by_cases hv0 : v = 0
  · subst v
    exact ⟨0, Fin.elim0, Fin.elim0, (fun i => Fin.elim0 i),
      (fun i => Fin.elim0 i), by simp⟩
  · obtain ⟨L, hsum, hL⟩ :=
      CRNT.exists_nonnegElementarySum (S := LinearMap.ker N.incidenceMap) hv.2 hv0 hv.1
    let c : Fin L.length → (N.R → ℝ) := fun i => L.get i
    let a : Fin L.length → ℝ := fun _ => 1
    refine ⟨L.length, c, a, ?_, ?_, ?_⟩
    · intro i
      exact (nonnegElementary_incidence_iff_cycle N (c i)).1
        (hL (c i) (List.get_mem L i)).1
    · intro i; exact zero_le_one
    · calc
        v = L.sum := hsum.symm
        _ = ∑ i : Fin L.length, L.get i := (CRNT.sum_get_eq_list_sum L).symm
        _ = ∑ i : Fin L.length, a i • c i := by simp [a, c]

/-- Every nonnegative graph circulation is a finite nonnegative sum of concrete closed-walk
reaction-count fluxes. This strengthens `graphCirculation_decomposes_into_cycles` by retaining a
finite reaction-list witness for each elementary cycle mode, which is needed to apply the toric
cycle estimate to the actual directed edges. -/
theorem graphCirculation_decomposes_into_closedWalkFluxes (N : Network S)
    {v : N.R → ℝ} (hv : N.IsNonnegativeGraphCirculation v) :
    ∃ (m : ℕ) (rs : Fin m → List N.R) (a : Fin m → ℝ),
      (∀ i, 0 ≤ a i) ∧
      (∀ i, ∃ c : N.R → ℝ, ∃ b : N.ComplexIdx,
        N.IsDirectedCycleFlow c ∧ N.IsPositiveFluxPath c (rs i) b b) ∧
      v = ∑ i, a i • reactionListFlux N (rs i) := by
  obtain ⟨m, c, α, hc, hα, hsum⟩ := N.graphCirculation_decomposes_into_cycles hv
  classical
  have hpositive (i : Fin m) : ∃ r : N.R, 0 < c i r := by
    by_contra hn
    push Not at hn
    have hz : ∀ r : N.R, c i r = 0 := by
      intro r
      exact le_antisymm (hn r) ((hc i).1.1 r)
    apply (hc i).2.1
    funext r
    exact hz r
  let r₀ : Fin m → N.R := fun i => Classical.choose (hpositive i)
  have hr₀ (i : Fin m) : 0 < c i (r₀ i) := Classical.choose_spec (hpositive i)
  have hr₀supp (i : Fin m) : r₀ i ∈ N.fluxSupport (c i) :=
    (N.mem_fluxSupport_iff (c i) (r₀ i)).2 (hr₀ i).ne'
  have hwalk (i : Fin m) : ∃ rs : List N.R,
      N.IsPositiveFluxPath (c i) (r₀ i :: rs) (N.sourceIdx (r₀ i)) (N.sourceIdx (r₀ i)) ∧
      ∃ t : ℝ, 0 < t ∧ c i = t • reactionListFlux N (r₀ i :: rs) :=
    (hc i).exists_pos_smul_closedWalkFlux N (hr₀supp i)
  let walks (i : Fin m) : List N.R := r₀ i :: Classical.choose (hwalk i)
  have hwalk_spec (i : Fin m) :
      N.IsPositiveFluxPath (c i) (walks i) (N.sourceIdx (r₀ i)) (N.sourceIdx (r₀ i)) ∧
      ∃ t : ℝ, 0 < t ∧ c i = t • reactionListFlux N (walks i) := by
    simpa [walks] using Classical.choose_spec (hwalk i)
  let t (i : Fin m) : ℝ := Classical.choose (hwalk_spec i).2
  have ht (i : Fin m) : 0 < t i ∧ c i = t i • reactionListFlux N (walks i) :=
    Classical.choose_spec (hwalk_spec i).2
  let β (i : Fin m) : ℝ := α i * t i
  refine ⟨m, walks, β, ?_, ?_, ?_⟩
  · intro i
    exact mul_nonneg (hα i) (le_of_lt (ht i).1)
  · intro i
    exact ⟨c i, N.sourceIdx (r₀ i), hc i, (hwalk_spec i).1⟩
  · calc
      v = ∑ i, α i • c i := hsum
      _ = ∑ i, β i • reactionListFlux N (walks i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(ht i).2]
        simp [β, smul_smul]

/-- Pairing a nonnegative circulation with any scalar reaction weight can be computed by summing
that weight along a finite closed-walk decomposition. This is the scalar form of the mass-action
velocity assembly: choose `f r` to be the source-dependent reaction rate times a projected edge
increment. -/
theorem weighted_sum_eq_closedWalkSums_of_decomposition (N : Network S)
    {v : N.R → ℝ} {m : ℕ} (rs : Fin m → List N.R) (a : Fin m → ℝ)
    (hdecomp : v = ∑ i, a i • reactionListFlux N (rs i)) (f : N.R → ℝ) :
    (∑ r, v r * f r) = ∑ i, a i * ((rs i).map f).sum := by
  have hcoord (r : N.R) : v r = ∑ i, a i * reactionListFlux N (rs i) r := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hdecomp r
  calc
    (∑ r, v r * f r) =
        ∑ r, (∑ i, a i * reactionListFlux N (rs i) r) * f r := by
          apply Finset.sum_congr rfl
          intro r _
          rw [hcoord]
    _ = ∑ r, ∑ i, (a i * reactionListFlux N (rs i) r) * f r := by
          apply Finset.sum_congr rfl
          intro r _
          exact Finset.sum_mul Finset.univ
            (fun i : Fin m => a i * reactionListFlux N (rs i) r) (f r)
    _ = ∑ i, ∑ r, (a i * reactionListFlux N (rs i) r) * f r := by
          rw [Finset.sum_comm]
    _ = ∑ i, a i * (∑ r, reactionListFlux N (rs i) r * f r) := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            (∑ r, (a i * reactionListFlux N (rs i) r) * f r) =
                ∑ r, a i * (reactionListFlux N (rs i) r * f r) := by
                  apply Finset.sum_congr rfl
                  intro r _
                  ring
            _ = a i * (∑ r, reactionListFlux N (rs i) r * f r) := by
                  symm
                  exact Finset.mul_sum Finset.univ
                    (fun r => reactionListFlux N (rs i) r * f r) (a i)
    _ = ∑ i, a i * ((rs i).map f).sum := by
          apply Finset.sum_congr rfl
          intro i _
          rw [reactionListFlux_weighted_sum]

/-- Pairing a nonnegative circulation with any scalar reaction weight can be computed by summing
that weight along a finite closed-walk decomposition. This is the scalar form of the mass-action
velocity assembly: choose `f r` to be the source-dependent reaction rate times a projected edge
increment. -/
theorem graphCirculation_weighted_sum_eq_closedWalkSums (N : Network S)
    {v : N.R → ℝ} (hv : N.IsNonnegativeGraphCirculation v) (f : N.R → ℝ) :
    ∃ (m : ℕ) (rs : Fin m → List N.R) (a : Fin m → ℝ),
      (∀ i, 0 ≤ a i) ∧
      (∀ i, ∃ c : N.R → ℝ, ∃ b : N.ComplexIdx,
        N.IsDirectedCycleFlow c ∧ N.IsPositiveFluxPath c (rs i) b b) ∧
      (∑ r, v r * f r) = ∑ i, a i * ((rs i).map f).sum := by
  obtain ⟨m, rs, a, ha, hwalks, hdecomp⟩ :=
    N.graphCirculation_decomposes_into_closedWalkFluxes hv
  exact ⟨m, rs, a, ha, hwalks,
    N.weighted_sum_eq_closedWalkSums_of_decomposition rs a hdecomp f⟩

/-- Weak reversibility is equivalent to existence of a directed-cycle-flow cover of all
reaction channels. -/
theorem weaklyReversible_iff_cycleFlow_cover (N : Network S) :
    N.WeaklyReversible ↔
      ∀ r : N.R, ∃ c : N.R → ℝ,
        N.IsDirectedCycleFlow c ∧ c r > 0 := by
  constructor
  · intro hwr r
    obtain ⟨v, hv⟩ := N.exists_positiveGraphCirculation_of_weaklyReversible hwr
    obtain ⟨m, c, a, hc, ha, hsum⟩ :=
      N.graphCirculation_decomposes_into_cycles ⟨fun q => (hv.1 q).le, hv.2⟩
    have hcoord := congrFun hsum r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    have hex : ∃ i : Fin m, 0 < c i r := by
      by_contra hnone
      push Not at hnone
      have hz : ∀ i : Fin m, c i r = 0 := by
        intro i
        exact le_antisymm (hnone i) ((hc i).1.1 r)
      have hsum0 : (∑ i : Fin m, a i * c i r) = 0 := by simp [hz]
      rw [hsum0] at hcoord
      exact (hv.1 r).ne' hcoord
    obtain ⟨i, hi⟩ := hex
    exact ⟨c i, hc i, hi⟩
  · intro hcover
    classical
    choose c hc hcr using hcover
    let v : N.R → ℝ := ∑ q : N.R, c q
    exact N.weaklyReversible_of_positiveGraphCirculation (α := v) ⟨by
      intro r
      simp only [v, Finset.sum_apply]
      apply Finset.sum_pos'
      · intro q _
        exact (hc q).1.1 r
      · exact ⟨r, Finset.mem_univ r, hcr r⟩, by
      simp only [v, map_sum]
      apply Finset.sum_eq_zero
      intro q _
      exact (hc q).1.2⟩

end Network
end CRNT
