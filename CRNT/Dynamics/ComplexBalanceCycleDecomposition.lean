import CRNT.Graph.CirculationDecomposition
import CRNT.Equilibria.ComplexBalanceLinearStability
import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Dynamics.ToricEmbeddingOrder
import CRNT.Geometry.ConeFace
import CRNT.Geometry.ToricFan

namespace CRNT.Network
open scoped BigOperators InnerProductSpace
variable {S : Type} [DecidableEq S] [Fintype S]

/-- For a concrete closed reaction walk, the exponential source weights give a nonpositive
projected velocity in the same direction used in the exponent. This is the finite entropy
dissipation inequality for each cycle in a complex-balance decomposition. -/
theorem closedWalk_expProjectedVelocity_nonpos
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {c : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs c c) (z : S → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    (∑ i : Fin rs.length,
      (q * Real.exp (⟪toEuclid z,
        toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ)) *
        ⟪toEuclid z,
          toEuclid (CRNT.exponentVector (N.targetIdx (rs.get i)).val) -
            toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ) ≤ 0 := by
  let source := rs.map N.sourceIdx
  let target := rs.map N.targetIdx
  let f : N.ComplexIdx → EuclideanSpace ℝ S :=
    fun c => toEuclid (CRNT.exponentVector c.val)
  have hperm : List.Perm target source := by
    exact IsPositiveFluxPath.targetList_perm_sourceList N hp
  have hcycle := CRNT.cyclicProjectedVelocity_nonpos_of_permutedList
    target source hperm f (toEuclid z) q hq
  have hsourceLen : source.length = rs.length := by simp [source]
  let e : Fin rs.length ≃ Fin source.length := finCongr hsourceLen.symm
  have hsum :
      (∑ i : Fin rs.length,
        (q * Real.exp (⟪toEuclid z, f (N.sourceIdx (rs.get i))⟫_ℝ)) *
          ⟪toEuclid z, f (N.targetIdx (rs.get i)) - f (N.sourceIdx (rs.get i))⟫_ℝ) =
      ∑ i : Fin source.length,
        (q * Real.exp (⟪toEuclid z, f (source.get i)⟫_ℝ)) *
          ⟪toEuclid z, f (target.get (finCongr hperm.length_eq.symm i)) -
            f (source.get i)⟫_ℝ := by
    apply Fintype.sum_equiv e
    intro i
    have hi : finCongr hperm.length_eq.symm (e i) =
        finCongr (by simp [target]) (i) := by
      apply Fin.ext
      simp [e, hsourceLen, target]
    simp [source, target, f, e, hi]
  rw [hsum]
  exact hcycle

/-- The same closed-walk sign bound in reaction-list coordinates. The reaction vector is the
target exponent minus the source exponent, so this is the projected entropy-dissipation term
that appears after expanding the full mass-action field. -/
theorem closedWalk_reactionListEntropy_nonpos
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {c : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs c c) (z : S → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    q * (rs.map (fun r =>
      Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * z s) *
        (∑ s, z s * N.reactionVector r s))).sum ≤ 0 := by
  let f : N.ComplexIdx → EuclideanSpace ℝ S :=
    fun c => toEuclid (CRNT.exponentVector c.val)
  let g : N.R → ℝ := fun r =>
    Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * z s) *
      (∑ s, z s * N.reactionVector r s)
  have hsource (r : N.R) :
      ⟪toEuclid z, f (N.sourceIdx r)⟫_ℝ =
        ∑ s, ((N.sourceIdx r).val s : ℝ) * z s := by
    change ⟪toEuclid z,
      toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ = _
    rw [inner_toEuclid]
    apply Finset.sum_congr rfl
    intro s _
    simp [CRNT.exponentVector, mul_comm]
  have hvector (r : N.R) :
      f (N.targetIdx r) - f (N.sourceIdx r) = toEuclid (N.reactionVector r) := by
    ext s
    simp [f, CRNT.exponentVector, Network.sourceIdx, Network.targetIdx]
  have hinc (r : N.R) :
      ⟪toEuclid z, f (N.targetIdx r) - f (N.sourceIdx r)⟫_ℝ =
        ∑ s, z s * N.reactionVector r s := by
    rw [hvector, inner_toEuclid]
  have hcycle := N.closedWalk_expProjectedVelocity_nonpos hp z q hq
  have hsum :
      (∑ i : Fin rs.length,
        (q * Real.exp (⟪toEuclid z,
          f (N.sourceIdx (rs.get i))⟫_ℝ)) *
          ⟪toEuclid z,
            f (N.targetIdx (rs.get i)) - f (N.sourceIdx (rs.get i))⟫_ℝ) =
      q * (rs.map g).sum := by
    calc
      _ = ∑ i : Fin rs.length, q * g (rs.get i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hsource, hinc]
        ring
      _ = q * (rs.map g).sum := by
        rw [← Finset.mul_sum]
        rw [← List.sum_ofFn]
        have hlist :
            List.ofFn (fun i : Fin rs.length => g (rs.get i)) = rs.map g := by
          simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map rs g)
        exact congrArg (fun L : List ℝ => q * L.sum) hlist
  rw [hsum] at hcycle
  exact hcycle


theorem equilibriumReactionFlux_isPositiveGraphCirculation
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    N.IsPositiveGraphCirculation (N.equilibriumReactionFlux κ xstar) := by
  constructor
  · intro r
    exact N.massActionRate_pos κ r hxs
  · have hk := (N.isComplexBalanced_iff_kineticMap κ xstar).1 hcb
    have heq := N.kineticMap_eq_incidenceMap κ (N.complexMonomialVector xstar)
    rw [hk] at heq
    have hfun : N.equilibriumReactionFlux κ xstar =
        (fun r => κ.k r * N.complexMonomialVector xstar (N.sourceIdx r)) := by
      funext r
      exact N.massActionRate_eq κ r xstar
    rw [hfun]
    exact heq.symm

theorem equilibriumReactionFlux_decomposes_into_cycles
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    ∃ (m : ℕ) (c : Fin m → (N.R → ℝ)) (a : Fin m → ℝ),
      (∀ i, N.IsDirectedCycleFlow (c i)) ∧
      (∀ i, 0 ≤ a i) ∧
      N.equilibriumReactionFlux κ xstar = ∑ i, a i • c i := by
  have hp := N.equilibriumReactionFlux_isPositiveGraphCirculation κ hxs hcb
  exact N.graphCirculation_decomposes_into_cycles ⟨fun r => (hp.1 r).le, hp.2⟩

/-- A positive complex-balanced equilibrium flux decomposes into a finite family of concrete
closed reaction walks with nonnegative weights. This retains the edge order and multiplicities
needed by the toric projected-velocity estimate. -/
theorem equilibriumReactionFlux_decomposes_into_closedWalks
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    ∃ (m : ℕ) (rs : Fin m → List N.R) (a : Fin m → ℝ),
      (∀ i, 0 ≤ a i) ∧
      (∀ i, ∃ c : N.R → ℝ, ∃ b : N.ComplexIdx,
        N.IsDirectedCycleFlow c ∧ N.IsPositiveFluxPath c (rs i) b b) ∧
      N.equilibriumReactionFlux κ xstar =
        ∑ i, a i • reactionListFlux N (rs i) := by
  have hp := N.equilibriumReactionFlux_isPositiveGraphCirculation κ hxs hcb
  exact N.graphCirculation_decomposes_into_closedWalkFluxes
    ⟨fun r => (hp.1 r).le, hp.2⟩

theorem massActionRate_eq_equilibriumFlux_mul_exp_logRatio
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (r : N.R) :
    N.massActionRate κ r x = N.equilibriumReactionFlux κ xstar r *
      Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) *
        (Real.log (x s) - Real.log (xstar s))) := by
  rw [N.massActionRate_eq κ r x]
  simp only [equilibriumReactionFlux]
  rw [N.massActionRate_eq κ r xstar]
  rw [N.complexMonomialVector_eq_mul_exp hx hxs (N.sourceIdx r)]
  ring


theorem massActionVectorField_eq_equilibriumFlux_exp_sum
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) :
    N.massActionVectorField κ x =
      ∑ r : N.R, (N.equilibriumReactionFlux κ xstar r *
        Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) *
          (Real.log (x s) - Real.log (xstar s)))) • N.reactionVector r := by
  funext s
  simp only [massActionVectorField_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [N.massActionRate_eq_equilibriumFlux_mul_exp_logRatio κ hx hxs r]


theorem massActionVectorField_eq_cycleFlow_exp_sum
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive)
    {m : ℕ} {c : Fin m → (N.R → ℝ)} {a : Fin m → ℝ}
    (hdecomp : N.equilibriumReactionFlux κ xstar = ∑ i, a i • c i) :
    N.massActionVectorField κ x =
      ∑ i : Fin m, a i •
        (∑ r : N.R, (c i r *
          Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) *
            (Real.log (x s) - Real.log (xstar s)))) • N.reactionVector r) := by
  rw [N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs]
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  have hr := congrFun hdecomp r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hr
  rw [hr, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- For a positive complex-balanced reference, every coordinate of the mass-action vector field
is a nonnegative weighted sum over the concrete closed walks in one fixed decomposition of the
equilibrium flux. Each list entry contributes its source monomial and reaction increment, with
repeated reactions retained according to their multiplicity. -/
theorem massActionVectorField_coord_eq_closedWalk_exp_sum
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    ∃ (m : ℕ) (rs : Fin m → List N.R) (a : Fin m → ℝ),
      (∀ i, 0 ≤ a i) ∧
      (∀ i, ∃ c : N.R → ℝ, ∃ b : N.ComplexIdx,
        N.IsDirectedCycleFlow c ∧ N.IsPositiveFluxPath c (rs i) b b) ∧
      ∀ s, N.massActionVectorField κ x s =
        ∑ i, a i * ((rs i).map (fun r =>
          Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
            (Real.log (x t) - Real.log (xstar t))) * N.reactionVector r s)).sum := by
  obtain ⟨m, rs, a, ha, hwalks, hdecomp⟩ :=
    N.equilibriumReactionFlux_decomposes_into_closedWalks κ hxs hcb
  have hfield := N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs
  refine ⟨m, rs, a, ha, hwalks, ?_⟩
  intro s
  have hweight := N.weighted_sum_eq_closedWalkSums_of_decomposition rs a hdecomp
    (fun r => Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
      (Real.log (x t) - Real.log (xstar t))) * N.reactionVector r s)
  have hcoord := congrFun hfield s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  calc
    N.massActionVectorField κ x s =
        ∑ r, (N.equilibriumReactionFlux κ xstar r *
          Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
            (Real.log (x t) - Real.log (xstar t)))) * N.reactionVector r s := hcoord
    _ = ∑ r, N.equilibriumReactionFlux κ xstar r *
          (Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
            (Real.log (x t) - Real.log (xstar t))) * N.reactionVector r s) := by
          apply Finset.sum_congr rfl
          intro r _
          ring
    _ = ∑ i, a i * ((rs i).map (fun r =>
          Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
            (Real.log (x t) - Real.log (xstar t))) * N.reactionVector r s)).sum := hweight

/-- Reproves the complex-balanced relative-entropy dissipation inequality by first decomposing
the positive equilibrium reaction flux into closed walks, then applying the projected sign bound
to each walk separately. -/
theorem dissipation_nonpos_via_closedWalkDecomposition
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    (∑ s, (Real.log (x s) - Real.log (xstar s)) *
      N.massActionVectorField κ x s) ≤ 0 := by
  let z : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let f : N.R → ℝ := fun r =>
    Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t) *
      (∑ s, z s * N.reactionVector r s)
  have hflux : N.IsPositiveGraphCirculation (N.equilibriumReactionFlux κ xstar) := by
    constructor
    · intro r
      exact N.massActionRate_pos κ r hxs
    · have hk := (N.isComplexBalanced_iff_kineticMap κ xstar).1 hcb
      have heq := N.kineticMap_eq_incidenceMap κ (N.complexMonomialVector xstar)
      rw [hk] at heq
      have hfun : N.equilibriumReactionFlux κ xstar =
          (fun r => κ.k r * N.complexMonomialVector xstar (N.sourceIdx r)) := by
        funext r
        exact N.massActionRate_eq κ r xstar
      rw [hfun]
      exact heq.symm
  obtain ⟨m, rs, a, ha, hwalks, hdecomp⟩ :=
    N.graphCirculation_decomposes_into_closedWalkFluxes
      ⟨fun r => (hflux.1 r).le, hflux.2⟩
  have hcoord (s : S) :
      N.massActionVectorField κ x s =
        ∑ r, (N.equilibriumReactionFlux κ xstar r *
          Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
          N.reactionVector r s := by
    have hfield := congrFun (N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs) s
    simpa [z, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hfield
  have hpair :
      (∑ s, z s * N.massActionVectorField κ x s) =
        ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
    calc
      (∑ s, z s * N.massActionVectorField κ x s) =
          ∑ s, z s * ∑ r,
            (N.equilibriumReactionFlux κ xstar r *
              Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
              N.reactionVector r s := by
                apply Finset.sum_congr rfl
                intro s _
                rw [hcoord s]
      _ = ∑ s, ∑ r,
            z s * ((N.equilibriumReactionFlux κ xstar r *
              Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
              N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro s _
                rw [Finset.mul_sum]
      _ = ∑ r, ∑ s,
            (N.equilibriumReactionFlux κ xstar r *
              Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
              (z s * N.reactionVector r s) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro r _
                apply Finset.sum_congr rfl
                intro s _
                ring
      _ = ∑ r, (N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) * z t)) *
            (∑ s, z s * N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro r _
                rw [Finset.mul_sum]
      _ = ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
                apply Finset.sum_congr rfl
                intro r _
                simp only [f]
                ring
  have hweighted := N.weighted_sum_eq_closedWalkSums_of_decomposition
    rs a hdecomp f
  rw [hpair, hweighted]
  apply Finset.sum_nonpos
  intro i _
  obtain ⟨cycleFlow, base, hcycleFlow, hp⟩ := hwalks i
  exact N.closedWalk_reactionListEntropy_nonpos hp z (a i) (ha i)

/-- **Projected closed-walk estimate with perturbed monomial weights.** For a positive closed
reaction walk, let `p i` be the source-complex projection in a reference direction, and let `k i`
be a positive prefactor accounting for fixed equilibrium-rate factors. If the prefactors are
uniformly bounded, the reference gaps dominate their ratio, and every strict ordering in the test
direction agrees with the reference ordering, then the rate-weighted reaction vectors have
nonpositive projection. This is the closed-walk estimate used away from toric uncertainty walls. -/
theorem closedWalk_reactionList_projected_nonpos_of_rateSeparation
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {c : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs c c)
    (z₀ z : EuclideanSpace ℝ S) (k p : Fin rs.length → ℝ)
    {kmin kmax δ : ℝ}
    (hkmin : 0 ≤ kmin) (hscale : kmax ≤ kmin * Real.exp δ)
    (hk : ∀ i, kmin ≤ k i ∧ k i ≤ kmax)
    (hgap : ∀ i j, p i < p j → p i + δ ≤ p j)
    (hpSource : ∀ i, p i =
      ⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ)
    (horder : ∀ i j,
      ⟪z, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ <
        ⟪z, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get j)).val)⟫_ℝ → p i < p j) :
    (∑ i : Fin rs.length,
      (k i * Real.exp (p i)) *
        ⟪z, toEuclid (N.reactionVector (rs.get i))⟫_ℝ) ≤ 0 := by
  let f : N.ComplexIdx → EuclideanSpace ℝ S :=
    fun c => toEuclid (CRNT.exponentVector c.val)
  let source := rs.map N.sourceIdx
  let target := rs.map N.targetIdx
  let eSource : Fin rs.length ≃ Fin source.length := finCongr (by simp [source])
  have hperm : List.Perm target source :=
    IsPositiveFluxPath.targetList_perm_sourceList N hp
  have hsource (i : Fin source.length) :
      source.get i = N.sourceIdx (rs.get (eSource.symm i)) := by
    simp [source, eSource]
  have hindex (i : Fin source.length) :
      finCongr hperm.length_eq.symm i = finCongr (by simp [target]) (eSource.symm i) := by
    apply Fin.ext
    simp [eSource, source, target]
  have htarget (i : Fin source.length) :
      target.get (finCongr hperm.length_eq.symm i) =
        N.targetIdx (rs.get (eSource.symm i)) := by
    rw [hindex i]
    simp [target, eSource]
  let k' : Fin source.length → ℝ := fun i => k (eSource.symm i)
  let p' : Fin source.length → ℝ := fun i => p (eSource.symm i)
  have hp' : ∀ i : Fin source.length, p' i = ⟪z₀, f (source.get i)⟫_ℝ := by
    intro i
    change p (eSource.symm i) = ⟪z₀, f (source.get i)⟫_ℝ
    rw [hsource i]
    exact hpSource (eSource.symm i)
  have hvec (r : N.R) : f (N.targetIdx r) - f (N.sourceIdx r) =
      toEuclid (N.reactionVector r) := by
    ext s
    simp [f, CRNT.exponentVector, Network.sourceIdx, Network.targetIdx]
  have htransport :
      (∑ i : Fin rs.length,
        (k i * Real.exp (p i)) *
          ⟪z, toEuclid (N.reactionVector (rs.get i))⟫_ℝ) =
      ∑ i : Fin source.length,
        (k (eSource.symm i) * Real.exp (p (eSource.symm i))) *
          ⟪z, toEuclid (N.reactionVector (rs.get (eSource.symm i)))⟫_ℝ := by
    exact Fintype.sum_equiv eSource
      (fun i => (k i * Real.exp (p i)) *
        ⟪z, toEuclid (N.reactionVector (rs.get i))⟫_ℝ)
      (fun i => (k (eSource.symm i) * Real.exp (p (eSource.symm i))) *
        ⟪z, toEuclid (N.reactionVector (rs.get (eSource.symm i)))⟫_ℝ)
      (fun _ => rfl)
  have hwalk := cyclicProjectedVelocity_nonpos_of_permutedList_rateSeparation
    target source hperm f k' p' z₀ z hkmin hscale
    (fun i => hk (eSource.symm i))
    (fun i j hij => hgap (eSource.symm i) (eSource.symm j) hij)
    hp' (by
      intro i j hij
      change p (eSource.symm i) < p (eSource.symm j)
      apply horder (eSource.symm i) (eSource.symm j)
      rw [hsource i, hsource j] at hij
      change _ < _ at hij
      exact hij)
  rw [htransport]
  apply le_of_eq_of_le ?_ hwalk
  apply Finset.sum_congr rfl
  intro i _
  rw [htarget i, hsource i, ← hvec (rs.get (eSource.symm i))]

/-- **Closed-walk projection under a pure exponential source order.** When a cycle's edge
coefficients are a common nonnegative cycle-flow weight times the exponential of source levels,
no gap estimate is needed: strict order preservation alone makes the coefficients monotone. -/
theorem closedWalk_reactionList_projected_nonpos_of_order
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {c : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs c c)
    (z₀ z : EuclideanSpace ℝ S)
    (horder : ∀ i j,
      ⟪z, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ <
        ⟪z, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get j)).val)⟫_ℝ →
      ⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ <
        ⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get j)).val)⟫_ℝ) :
    (∑ i : Fin rs.length,
      Real.exp (⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ) *
        ⟪z, toEuclid (N.reactionVector (rs.get i))⟫_ℝ) ≤ 0 := by
  have h := N.closedWalk_reactionList_projected_nonpos_of_rateSeparation
    hp z₀ z (fun _ => 1)
    (fun i => ⟪z₀, toEuclid (CRNT.exponentVector (N.sourceIdx (rs.get i)).val)⟫_ℝ)
    (kmin := 1) (kmax := 1) (δ := 0)
    (by norm_num) (by norm_num)
    (fun _ => by constructor <;> norm_num)
    (by intro i j hij; simpa using hij.le)
    (fun _ => rfl) horder
  simpa only [one_mul] using h

/-- The source-complex pairing with a logarithmic direction. -/
def sourceLogProjection (N : Network S) (w : S → ℝ) (r : N.R) : ℝ :=
  ∑ s, ((N.sourceIdx r).val s : ℝ) * w s

/-- Source-log projection is the Euclidean pairing with the source exponent vector. -/
theorem sourceLogProjection_eq_inner_toEuclid (N : Network S) (w : S → ℝ)
    (r : N.R) :
    N.sourceLogProjection w r =
      ⟪toEuclid (CRNT.exponentVector (N.sourceIdx r).val), toEuclid w⟫_ℝ := by
  rw [CRNT.inner_toEuclid]
  simp [sourceLogProjection, CRNT.exponentVector]

/-- A reaction vector is the difference of its target and source exponent vectors. -/
theorem reactionVector_eq_exponentVector_target_sub_source
    (N : Network S) (r : N.R) :
    N.reactionVector r =
      CRNT.exponentVector (N.reaction r).target -
        CRNT.exponentVector (N.reaction r).source := by
  funext s
  simp [CRNT.exponentVector, reactionVector_apply]

/-- The Euclidean image of the stoichiometric subspace. -/
noncomputable def euclideanStoichSubspace (N : Network S) :
    Submodule ℝ (EuclideanSpace ℝ S) :=
  Submodule.map CRNT.toEuclid.toLinearMap N.stoichSubspace

/-- The orthogonal projection of a logarithmic direction onto the stoichiometric subspace. -/
noncomputable def relativeLogStoichProjection (N : Network S) (u : S → ℝ) : S → ℝ :=
  CRNT.toEuclid.symm
    (N.euclideanStoichSubspace.starProjection (CRNT.toEuclid u))

theorem relativeLogStoichProjection_mem (N : Network S) (u : S → ℝ) :
    N.relativeLogStoichProjection u ∈ N.stoichSubspace := by
  have hp := N.euclideanStoichSubspace.starProjection_apply_mem (CRNT.toEuclid u)
  rw [euclideanStoichSubspace, Submodule.mem_map] at hp
  rcases hp with ⟨v, hv, hvp⟩
  change CRNT.toEuclid.symm
    ((Submodule.map CRNT.toEuclid.toLinearMap N.stoichSubspace).starProjection
      (CRNT.toEuclid u)) ∈ N.stoichSubspace
  rw [← hvp]
  simpa using hv

/-- Any two linked complexes differ by a vector in the stoichiometric subspace. The proof
telescopes the reaction vectors along the undirected path, allowing a negative reaction vector
when a path edge is traversed against its orientation. -/
theorem exponentVector_sub_mem_stoichSubspace_of_linked
    (N : Network S) {c d : Complex S} (hcd : N.Linked c d) :
    CRNT.exponentVector d - CRNT.exponentVector c ∈ N.stoichSubspace := by
  induction hcd with
  | refl => simp
  | @tail a d _ had ih =>
      have hstep : CRNT.exponentVector d - CRNT.exponentVector a ∈
          N.stoichSubspace := by
        rcases had with hforward | hbackward
        · obtain ⟨r, hs, ht⟩ := hforward
          have hvec : CRNT.exponentVector d - CRNT.exponentVector a =
              N.reactionVector r := by
            rw [← ht, ← hs, N.reactionVector_eq_exponentVector_target_sub_source]
          rw [hvec]
          exact N.reactionVector_mem_stoichSubspace r
        · obtain ⟨r, hs, ht⟩ := hbackward
          have hvec : CRNT.exponentVector d - CRNT.exponentVector a =
              -N.reactionVector r := by
            rw [← hs, ← ht, N.reactionVector_eq_exponentVector_target_sub_source]
            abel
          rw [hvec]
          exact N.stoichSubspace.neg_mem (N.reactionVector_mem_stoichSubspace r)
      have hsum : CRNT.exponentVector d - CRNT.exponentVector c =
          (CRNT.exponentVector a - CRNT.exponentVector c) +
            (CRNT.exponentVector d - CRNT.exponentVector a) := by
        ext s
        simp
      rw [hsum]
      exact N.stoichSubspace.add_mem ih hstep

/-- The difference of source projections depends only on a stoichiometric projection of its
direction when the two source complexes are linked. -/
theorem sourceLogProjection_sub_eq_of_linked_orthogonal
    (N : Network S) {u w : S → ℝ}
    (horth : CRNT.toEuclid (u - w) ∈ N.euclideanStoichSubspaceᗮ)
    (r q : N.R) (hlinked : N.Linked (N.sourceIdx r).val (N.sourceIdx q).val) :
    N.sourceLogProjection u r - N.sourceLogProjection u q =
      N.sourceLogProjection w r - N.sourceLogProjection w q := by
  have hdiff := N.exponentVector_sub_mem_stoichSubspace_of_linked hlinked.symm
  have hinner :
      ⟪CRNT.toEuclid (u - w),
        CRNT.toEuclid (CRNT.exponentVector (N.sourceIdx r).val -
          CRNT.exponentVector (N.sourceIdx q).val)⟫_ℝ = 0 := by
    have hdiffE :
        CRNT.toEuclid (CRNT.exponentVector (N.sourceIdx r).val -
          CRNT.exponentVector (N.sourceIdx q).val) ∈ N.euclideanStoichSubspace := by
      rw [euclideanStoichSubspace, Submodule.mem_map]
      refine ⟨CRNT.exponentVector (N.sourceIdx r).val -
        CRNT.exponentVector (N.sourceIdx q).val, hdiff, ?_⟩
      rfl
    have hzero := Submodule.inner_right_of_mem_orthogonal hdiffE horth
    simpa [real_inner_comm] using hzero
  have hproj (v : S → ℝ) :
    N.sourceLogProjection v r - N.sourceLogProjection v q =
        ⟪CRNT.toEuclid (CRNT.exponentVector (N.sourceIdx r).val -
          CRNT.exponentVector (N.sourceIdx q).val),
          CRNT.toEuclid v⟫_ℝ := by
    rw [N.sourceLogProjection_eq_inner_toEuclid, N.sourceLogProjection_eq_inner_toEuclid]
    rw [← inner_sub_left]
    rfl
  rw [hproj u, hproj w]
  have hinner' :
      ⟪CRNT.toEuclid (CRNT.exponentVector (N.sourceIdx r).val -
          CRNT.exponentVector (N.sourceIdx q).val),
        CRNT.toEuclid (u - w)⟫_ℝ = 0 := by
    simpa only [real_inner_comm] using hinner
  have hsplit : u - w + w = u := sub_add_cancel u w
  rw [← hsplit, CRNT.toEuclid.map_add, inner_add_right, hinner']
  simp

/-- Every reaction source appearing along a positive-flux path is linked to the path's initial
complex. This lets cycle estimates use only source-order comparisons within one linkage class. -/
theorem positiveFluxPath_source_linked
    (N : Network S) {v : N.R → ℝ} {rs : List N.R} {a b : N.ComplexIdx}
    (hp : N.IsPositiveFluxPath v rs a b) {r : N.R} (hr : r ∈ rs) :
    N.Linked a.val (N.sourceIdx r).val := by
  induction rs generalizing a with
  | nil => simp at hr
  | cons e rs ih =>
      rcases hp with ⟨hsource, _, htail⟩
      simp only [List.mem_cons] at hr
      rcases hr with hre | hr
      · subst r
        simpa [hsource] using Linked.refl N (N.sourceIdx e).val
      · have hEdge : N.Linked a.val (N.targetIdx e).val := by
          rw [← hsource]
          exact N.linked_of_reaction e
        exact Linked.trans hEdge (ih htail hr)

theorem sourceLogProjection_sub_eq_relativeLogStoichProjection_of_linked
    (N : Network S) (u : S → ℝ) (r q : N.R)
    (hlinked : N.Linked (N.sourceIdx r).val (N.sourceIdx q).val) :
    N.sourceLogProjection u r - N.sourceLogProjection u q =
      N.sourceLogProjection (N.relativeLogStoichProjection u) r -
        N.sourceLogProjection (N.relativeLogStoichProjection u) q := by
  have horth : CRNT.toEuclid (u - N.relativeLogStoichProjection u) ∈
      N.euclideanStoichSubspaceᗮ := by
    change CRNT.toEuclid u -
        N.euclideanStoichSubspace.starProjection (CRNT.toEuclid u) ∈
      N.euclideanStoichSubspaceᗮ
    exact N.euclideanStoichSubspace.sub_starProjection_mem_orthogonal _
  exact N.sourceLogProjection_sub_eq_of_linked_orthogonal horth r q hlinked

/-- The sum of source-exponent differences for the ordering constraints imposed by `w₂` but
absent from `w₁`. It is a supporting normal for the intersection of their order cones. -/
noncomputable def relativeSourceOrderIntersectionNormal (N : Network S)
    (w₁ w₂ : S → ℝ) : EuclideanSpace ℝ S := by
  classical
  exact ∑ p : N.R × N.R,
    if ¬ N.sourceLogProjection w₁ p.1 ≤ N.sourceLogProjection w₁ p.2 ∧
        N.sourceLogProjection w₂ p.1 ≤ N.sourceLogProjection w₂ p.2 then
      toEuclid (CRNT.exponentVector (N.sourceIdx p.1).val) -
        toEuclid (CRNT.exponentVector (N.sourceIdx p.2).val)
    else 0

/-- Pairing with the intersection normal sums the projection gaps for comparisons imposed by
`w₂` that are absent from `w₁`. -/
theorem inner_relativeSourceOrderIntersectionNormal_eq (N : Network S)
    (w₁ w₂ : S → ℝ) (z : EuclideanSpace ℝ S) :
    ⟪N.relativeSourceOrderIntersectionNormal w₁ w₂, z⟫_ℝ =
      ∑ p : N.R × N.R,
        if ¬ N.sourceLogProjection w₁ p.1 ≤ N.sourceLogProjection w₁ p.2 ∧
            N.sourceLogProjection w₂ p.1 ≤ N.sourceLogProjection w₂ p.2 then
          N.sourceLogProjection (CRNT.toEuclid.symm z) p.1 -
            N.sourceLogProjection (CRNT.toEuclid.symm z) p.2
        else 0 := by
  classical
  have hproj (r : N.R) :
      N.sourceLogProjection (CRNT.toEuclid.symm z) r =
        ⟪toEuclid (CRNT.exponentVector (N.sourceIdx r).val), z⟫_ℝ := by
    rw [N.sourceLogProjection_eq_inner_toEuclid]
    rw [CRNT.toEuclid.apply_symm_apply z]
  unfold relativeSourceOrderIntersectionNormal
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro p _
  rcases p with ⟨r, q⟩
  by_cases h :
      ¬ N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q ∧
        N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q
  · rw [if_pos h, if_pos h, inner_sub_left, ← hproj q, ← hproj r]
  · rw [if_neg h, if_neg h]
    simp

/-- The fixed equilibrium factor attached to one reaction source monomial. -/
noncomputable def equilibriumSourceFactor (N : Network S) (xstar : Concentration S) (r : N.R) : ℝ :=
  Real.exp (-(N.sourceLogProjection (fun s => Real.log (xstar s)) r))

/-- **Complex-balanced velocity points into a separated source-order chamber.** Suppose source
monomial prefactors induced by the positive complex-balanced reference are bounded by one common
exponential gap. If the test direction respects the source ordering selected by `log x`, and all
strict source gaps in that ordering exceed the gap margin, then the mass-action velocity has
nonpositive projection in the test direction.

The proof decomposes the positive equilibrium flux into concrete closed walks. The rate-separation
estimate proved above handles each walk, and nonnegative cycle weights preserve the sign. The
hypotheses describe a chamber away from its uncertainty walls; the remaining GAC step is to build
forward-invariant zero-separating surfaces from these chamberwise signs. -/
theorem massActionVectorField_projected_nonpos_of_rateSeparatedSourceOrder
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (z : S → ℝ) {kmin kmax δ : ℝ}
    (hkmin : 0 ≤ kmin) (hscale : kmax ≤ kmin * Real.exp δ)
    (hk : ∀ r, kmin ≤ N.equilibriumSourceFactor xstar r ∧
      N.equilibriumSourceFactor xstar r ≤ kmax)
    (hgap : ∀ r q,
      N.sourceLogProjection (fun s => Real.log (x s)) r <
        N.sourceLogProjection (fun s => Real.log (x s)) q →
      N.sourceLogProjection (fun s => Real.log (x s)) r + δ ≤
        N.sourceLogProjection (fun s => Real.log (x s)) q)
    (horder : ∀ r q,
      N.sourceLogProjection z r < N.sourceLogProjection z q →
        N.sourceLogProjection (fun s => Real.log (x s)) r <
          N.sourceLogProjection (fun s => Real.log (x s)) q) :
    (∑ s, z s * N.massActionVectorField κ x s) ≤ 0 := by
  let logx : S → ℝ := fun s => Real.log (x s)
  let logstar : S → ℝ := fun s => Real.log (xstar s)
  let p : N.R → ℝ := fun r => N.sourceLogProjection logx r
  let k : N.R → ℝ := fun r => N.equilibriumSourceFactor xstar r
  let f : N.R → ℝ := fun r =>
    Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) *
      (∑ s, z s * N.reactionVector r s)
  have hprojection (w : S → ℝ) (r : N.R) :
      ⟪toEuclid w, toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ =
        N.sourceLogProjection w r := by
    rw [inner_toEuclid]
    apply Finset.sum_congr rfl
    intro s _
    simp [CRNT.exponentVector, mul_comm]
  have hreactionProjection (r : N.R) :
      ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ =
        ∑ s, z s * N.reactionVector r s := by
    rw [inner_toEuclid]
  have hsumExponent (r : N.R) :
      (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) =
        -(N.sourceLogProjection logstar r) + N.sourceLogProjection logx r := by
    dsimp [sourceLogProjection]
    calc
      (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) =
          ∑ s, (((N.sourceIdx r).val s : ℝ) * logx s -
            ((N.sourceIdx r).val s : ℝ) * logstar s) := by
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = (∑ s, ((N.sourceIdx r).val s : ℝ) * logx s) -
          ∑ s, ((N.sourceIdx r).val s : ℝ) * logstar s := by
            rw [Finset.sum_sub_distrib]
      _ = -(∑ s, ((N.sourceIdx r).val s : ℝ) * logstar s) +
          ∑ s, ((N.sourceIdx r).val s : ℝ) * logx s := by ring
  have hexpFactor (r : N.R) :
      Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) =
        k r * Real.exp (p r) := by
    dsimp [k, p, equilibriumSourceFactor]
    calc
      Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) =
          Real.exp (-(N.sourceLogProjection logstar r) +
            N.sourceLogProjection logx r) := by rw [hsumExponent]
      _ = Real.exp (-(N.sourceLogProjection logstar r)) *
          Real.exp (N.sourceLogProjection logx r) := Real.exp_add _ _
  have hterm (r : N.R) : f r = (k r * Real.exp (p r)) *
      ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ := by
    change Real.exp (∑ s, ((N.sourceIdx r).val s : ℝ) * (logx s - logstar s)) *
        (∑ s, z s * N.reactionVector r s) = _
    rw [hexpFactor r, ← hreactionProjection r]
  have hfield := N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs
  have hcoord (s : S) : N.massActionVectorField κ x s =
      ∑ r, (N.equilibriumReactionFlux κ xstar r *
        Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
          (Real.log (x t) - Real.log (xstar t)))) * N.reactionVector r s := by
    have h := congrFun hfield s
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  have hpair :
      (∑ s, z s * N.massActionVectorField κ x s) =
        ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
    calc
      (∑ s, z s * N.massActionVectorField κ x s) =
          ∑ s, z s * ∑ r, (N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
              (Real.log (x t) - Real.log (xstar t)))) * N.reactionVector r s := by
                apply Finset.sum_congr rfl
                intro s _
                rw [hcoord s]
      _ = ∑ s, ∑ r, z s * ((N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
              (Real.log (x t) - Real.log (xstar t)))) * N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro s _
                rw [Finset.mul_sum]
      _ = ∑ r, ∑ s, (N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
              (Real.log (x t) - Real.log (xstar t)))) *
            (z s * N.reactionVector r s) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro r _
                apply Finset.sum_congr rfl
                intro s _
                ring
      _ = ∑ r, (N.equilibriumReactionFlux κ xstar r *
            Real.exp (∑ t, ((N.sourceIdx r).val t : ℝ) *
              (Real.log (x t) - Real.log (xstar t)))) *
            (∑ s, z s * N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro r _
                rw [Finset.mul_sum]
      _ = ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
                apply Finset.sum_congr rfl
                intro r _
                simp only [f]
                ring
  obtain ⟨m, rs, a, ha, hwalks, hdecomp⟩ :=
    N.equilibriumReactionFlux_decomposes_into_closedWalks κ hxs hcb
  have hweighted := N.weighted_sum_eq_closedWalkSums_of_decomposition rs a hdecomp f
  have hlistSum (L : List N.R) :
      (L.map f).sum = ∑ j : Fin L.length, f (L.get j) := by
    rw [← List.sum_ofFn]
    have hlist : List.ofFn (fun j : Fin L.length => f (L.get j)) = L.map f := by
      simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map L f)
    rw [hlist]
  rw [hpair, hweighted]
  apply Finset.sum_nonpos
  intro i _
  obtain ⟨cycleFlow, base, hcycleFlow, hpath⟩ := hwalks i
  have hcycle := N.closedWalk_reactionList_projected_nonpos_of_rateSeparation
    hpath (toEuclid logx) (toEuclid z)
    (fun j => k ((rs i).get j)) (fun j => p ((rs i).get j))
    hkmin hscale
    (fun j => hk ((rs i).get j))
    (fun j l hjl => hgap ((rs i).get j) ((rs i).get l) hjl)
    (fun j => (hprojection logx ((rs i).get j)).symm)
    (by
      intro j l hjl
      exact horder ((rs i).get j) ((rs i).get l) (by
        rw [← hprojection z ((rs i).get j), ← hprojection z ((rs i).get l)]
        exact hjl))
  have hcycleSum : ((rs i).map f).sum ≤ 0 := by
    calc
      ((rs i).map f).sum = ∑ j : Fin (rs i).length, f ((rs i).get j) := hlistSum (rs i)
      _ = ∑ j : Fin (rs i).length,
          (k ((rs i).get j) * Real.exp (p ((rs i).get j))) *
            ⟪toEuclid z,
              toEuclid (N.reactionVector ((rs i).get j))⟫_ℝ := by
            apply Finset.sum_congr rfl
            intro j _
            exact hterm ((rs i).get j)
      _ ≤ 0 := hcycle
  exact mul_nonpos_of_nonneg_of_nonpos (ha i) hcycleSum

/-- The equilibrium source factors of a finite nonempty reaction family admit a positive common
lower bound, a common upper bound, and one exponential separation margin. This discharges the
scalar prefactor bounds in `massActionVectorField_projected_nonpos_of_rateSeparatedSourceOrder`;
the remaining assumptions there are the geometric chamber-order conditions. -/
theorem exists_uniform_equilibriumSourceFactor_bounds
    (N : Network S) (xstar : Concentration S) [Nonempty N.R] :
    ∃ kmin kmax δ : ℝ, 0 < kmin ∧
      (∀ r, kmin ≤ N.equilibriumSourceFactor xstar r ∧
        N.equilibriumSourceFactor xstar r ≤ kmax) ∧
      kmax ≤ kmin * Real.exp δ := by
  apply exists_uniform_exp_prefactor_separation
    (fun r : N.R => N.equilibriumSourceFactor xstar r)
  intro r
  exact Real.exp_pos _

/-- **Relative-source-order dissipation for the full complex-balanced field.** Let
`w = log(x / xstar)` be the relative logarithmic state. If a test direction `z` preserves the
strict ordering of linked source complexes induced by `w`, then the full mass-action vector field
has nonpositive projection onto `z`.

The proof decomposes the positive equilibrium flux into closed walks. On each walk the coefficient
is a common nonnegative cycle-flow weight times the exact exponential `exp(source · w)`, so strict
order preservation alone makes coefficients monotone; no uncertain prefactor or gap condition is
needed. This is the finite toric differential-inclusion sign at the point `x`. -/
theorem massActionVectorField_projected_nonpos_of_relativeSourceOrder
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (z : S → ℝ)
    (horder : ∀ r q, N.Linked (N.sourceIdx r).val (N.sourceIdx q).val →
      N.sourceLogProjection z r < N.sourceLogProjection z q →
        N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r <
          N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) q) :
    (∑ s, z s * N.massActionVectorField κ x s) ≤ 0 := by
  let logrel : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let phase : N.R → ℝ := fun r => N.sourceLogProjection logrel r
  let f : N.R → ℝ := fun r =>
    Real.exp (phase r) * (∑ s, z s * N.reactionVector r s)
  have hprojection (w : S → ℝ) (r : N.R) :
      ⟪toEuclid w, toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ =
        N.sourceLogProjection w r := by
    rw [inner_toEuclid]
    apply Finset.sum_congr rfl
    intro s _
    simp [CRNT.exponentVector, mul_comm]
  have hreactionProjection (r : N.R) :
      ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ =
        ∑ s, z s * N.reactionVector r s := by
    rw [inner_toEuclid]
  have hterm (r : N.R) : f r =
      Real.exp (⟪toEuclid logrel,
        toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ) *
        ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ := by
    calc
      f r = Real.exp (N.sourceLogProjection logrel r) *
          (∑ s, z s * N.reactionVector r s) := rfl
      _ = Real.exp (⟪toEuclid logrel,
            toEuclid (CRNT.exponentVector (N.sourceIdx r).val)⟫_ℝ) *
          ⟪toEuclid z, toEuclid (N.reactionVector r)⟫_ℝ := by
            rw [← hprojection logrel r, ← hreactionProjection r]
  have hfield := N.massActionVectorField_eq_equilibriumFlux_exp_sum κ hx hxs
  have hcoord (s : S) : N.massActionVectorField κ x s =
      ∑ r, (N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
        N.reactionVector r s := by
    have h := congrFun hfield s
    simpa [phase, logrel, sourceLogProjection, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using h
  have hpair :
      (∑ s, z s * N.massActionVectorField κ x s) =
        ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
    calc
      (∑ s, z s * N.massActionVectorField κ x s) =
          ∑ s, z s * ∑ r,
            (N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
              N.reactionVector r s := by
                apply Finset.sum_congr rfl
                intro s _
                rw [hcoord s]
      _ = ∑ s, ∑ r, z s *
            ((N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
              N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro s _
                rw [Finset.mul_sum]
      _ = ∑ r, ∑ s,
            (N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
              (z s * N.reactionVector r s) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro r _
                apply Finset.sum_congr rfl
                intro s _
                ring
      _ = ∑ r, (N.equilibriumReactionFlux κ xstar r * Real.exp (phase r)) *
            (∑ s, z s * N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro r _
                rw [Finset.mul_sum]
      _ = ∑ r, N.equilibriumReactionFlux κ xstar r * f r := by
                apply Finset.sum_congr rfl
                intro r _
                simp only [f]
                ring
  obtain ⟨m, rs, a, ha, hwalks, hdecomp⟩ :=
    N.equilibriumReactionFlux_decomposes_into_closedWalks κ hxs hcb
  have hweighted := N.weighted_sum_eq_closedWalkSums_of_decomposition rs a hdecomp f
  have hlistSum (L : List N.R) :
      (L.map f).sum = ∑ j : Fin L.length, f (L.get j) := by
    rw [← List.sum_ofFn]
    have hlist : List.ofFn (fun j : Fin L.length => f (L.get j)) = L.map f := by
      simpa only [List.get_eq_getElem] using (List.ofFn_getElem_eq_map L f)
    rw [hlist]
  rw [hpair, hweighted]
  apply Finset.sum_nonpos
  intro i _
  obtain ⟨cycleFlow, base, hcycleFlow, hpath⟩ := hwalks i
  have hsourceLinked (j : Fin (rs i).length) :
      N.Linked base.val (N.sourceIdx ((rs i).get j)).val :=
    N.positiveFluxPath_source_linked hpath (List.get_mem (rs i) j)
  have hlinked (j l : Fin (rs i).length) :
      N.Linked (N.sourceIdx ((rs i).get j)).val
        (N.sourceIdx ((rs i).get l)).val :=
    Linked.trans (hsourceLinked j).symm (hsourceLinked l)
  have hcycle := N.closedWalk_reactionList_projected_nonpos_of_order
    hpath (toEuclid logrel) (toEuclid z)
    (by
      intro j l hjl
      have hz : N.sourceLogProjection z ((rs i).get j) <
          N.sourceLogProjection z ((rs i).get l) := by
        rw [← hprojection z ((rs i).get j), ← hprojection z ((rs i).get l)]
        exact hjl
      have hrel := horder ((rs i).get j) ((rs i).get l)
        (hlinked j l) hz
      rw [hprojection logrel ((rs i).get j), hprojection logrel ((rs i).get l)]
      exact hrel)
  have hcycleSum : ((rs i).map f).sum ≤ 0 := by
    calc
      ((rs i).map f).sum = ∑ j : Fin (rs i).length, f ((rs i).get j) := hlistSum (rs i)
      _ = ∑ j : Fin (rs i).length,
          Real.exp (⟪toEuclid logrel,
            toEuclid (CRNT.exponentVector (N.sourceIdx ((rs i).get j)).val)⟫_ℝ) *
              ⟪toEuclid z, toEuclid (N.reactionVector ((rs i).get j))⟫_ℝ := by
            apply Finset.sum_congr rfl
            intro j _
            exact hterm ((rs i).get j)
      _ ≤ 0 := hcycle
  exact mul_nonpos_of_nonneg_of_nonpos (ha i) hcycleSum

/-- The closed cone of test directions whose source-complex projections preserve the weak order
of a reference direction `w`. Its inequalities are the non-strict closure of the corresponding
source-order chamber. -/
noncomputable def relativeSourceOrderCone (N : Network S) (w : S → ℝ) :
    PointedCone ℝ (EuclideanSpace ℝ S) where
  carrier :=
    {z | ∀ r q, N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
      N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
        N.sourceLogProjection (CRNT.toEuclid.symm z) q}
  add_mem' := by
    intro z z' hz hz' r q hp
    simp only [Set.mem_setOf_eq] at hz hz' ⊢
    have hsum (i : N.R) (v v' : S → ℝ) :
        N.sourceLogProjection (v + v') i =
          N.sourceLogProjection v i + N.sourceLogProjection v' i := by
      unfold sourceLogProjection
      calc
        (∑ s, ((N.sourceIdx i).val s : ℝ) * (v s + v' s)) =
            ∑ s, (((N.sourceIdx i).val s : ℝ) * v s +
              ((N.sourceIdx i).val s : ℝ) * v' s) := by
                apply Finset.sum_congr rfl
                intro s _
                ring
        _ = (∑ s, ((N.sourceIdx i).val s : ℝ) * v s) +
              ∑ s, ((N.sourceIdx i).val s : ℝ) * v' s := Finset.sum_add_distrib
    change N.sourceLogProjection (CRNT.toEuclid.symm (z + z')) r ≤
      N.sourceLogProjection (CRNT.toEuclid.symm (z + z')) q
    rw [LinearEquiv.map_add]
    rw [hsum r _ _, hsum q _ _]
    exact add_le_add (hz r q hp) (hz' r q hp)
  zero_mem' := by
    intro r q _
    simp [sourceLogProjection]
  smul_mem' := by
    intro c z hz r q hp
    simp only [Set.mem_setOf_eq] at hz ⊢
    have hproj (i : N.R) :
        N.sourceLogProjection (CRNT.toEuclid.symm (c • z)) i =
          (c : ℝ) * N.sourceLogProjection (CRNT.toEuclid.symm z) i := by
      rw [show c • z = (c : ℝ) • z from rfl, LinearEquiv.map_smul]
      unfold sourceLogProjection
      calc
        (∑ s, ((N.sourceIdx i).val s : ℝ) *
            ((c : ℝ) * (CRNT.toEuclid.symm z) s)) =
            ∑ s, (c : ℝ) *
              (((N.sourceIdx i).val s : ℝ) * (CRNT.toEuclid.symm z) s) := by
                apply Finset.sum_congr rfl
                intro s _
                ring
        _ = (c : ℝ) * ∑ s,
              ((N.sourceIdx i).val s : ℝ) * (CRNT.toEuclid.symm z) s := by
                rw [Finset.mul_sum]
    rw [hproj r, hproj q]
    exact mul_le_mul_of_nonneg_left (hz r q hp) c.2

/-- Each source projection, transported to Euclidean coordinates, is a continuous linear
functional. -/
theorem continuous_sourceLogProjection_toEuclid_symm (N : Network S) (r : N.R) :
    Continuous (fun z : EuclideanSpace ℝ S =>
      N.sourceLogProjection (CRNT.toEuclid.symm z) r) := by
  have hrepr : (fun z : EuclideanSpace ℝ S =>
      N.sourceLogProjection (CRNT.toEuclid.symm z) r) =
      fun z => ∑ s, CRNT.exponentVector (N.sourceIdx r).val s * z s := by
    funext z
    have hz : ∀ s, (CRNT.toEuclid.symm z) s = z s := by
      intro s
      have h := congrArg (fun v : EuclideanSpace ℝ S => v s)
        (CRNT.toEuclid.apply_symm_apply z)
      simpa only [CRNT.toEuclid_apply] using h
    simp [sourceLogProjection, CRNT.exponentVector, hz]
  rw [hrepr]
  exact continuous_finsetSum Finset.univ fun s _ =>
    continuous_const.mul (EuclideanSpace.proj s).continuous

/-- A relative source-order cone is an intersection of finitely many closed half-spaces,
one for each ordered source pair selected by its reference direction. -/
theorem isClosed_relativeSourceOrderCone (N : Network S) (w : S → ℝ) :
    IsClosed (N.relativeSourceOrderCone w : Set (EuclideanSpace ℝ S)) := by
  classical
  change IsClosed {z : EuclideanSpace ℝ S | ∀ r q,
    N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
      N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
        N.sourceLogProjection (CRNT.toEuclid.symm z) q}
  let I := {p : N.R × N.R //
    N.sourceLogProjection w p.1 ≤ N.sourceLogProjection w p.2}
  have hEq :
      {z : EuclideanSpace ℝ S | ∀ r q,
        N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
          N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
            N.sourceLogProjection (CRNT.toEuclid.symm z) q} =
      ⋂ p : I, {z : EuclideanSpace ℝ S |
        N.sourceLogProjection (CRNT.toEuclid.symm z) p.1.1 ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) p.1.2} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hz p
      exact hz p.1.1 p.1.2 p.2
    · intro hz r q hp
      exact hz ⟨(r, q), hp⟩
  rw [hEq]
  apply isClosed_iInter
  intro p
  exact isClosed_le
    (N.continuous_sourceLogProjection_toEuclid_symm p.1.1)
    (N.continuous_sourceLogProjection_toEuclid_symm p.1.2)

/-- In a weakly reversible network, every reaction target is also a reaction source. The
length-zero return path is handled by the original reaction; otherwise the first edge of the
return path starts at the target. -/
theorem exists_sourceIdx_eq_targetIdx_of_weaklyReversible
    (N : Network S) (hwr : N.WeaklyReversible) (r : N.R) :
    ∃ q : N.R, N.sourceIdx q = N.targetIdx r := by
  have hback : N.Reaches (N.reaction r).target (N.reaction r).source := hwr r
  have hfirst {c d : Complex S} (h : N.Reaches c d) (hne : c ≠ d) :
      ∃ q : N.R, (N.reaction q).source = c := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact False.elim (hne rfl)
    | @head a b hab _ ih =>
        obtain ⟨q, hsource, _⟩ := hab
        exact ⟨q, hsource⟩
  by_cases heq : (N.reaction r).target = (N.reaction r).source
  · refine ⟨r, ?_⟩
    apply Subtype.ext
    exact heq.symm
  · obtain ⟨q, hsource⟩ := hfirst hback heq
    refine ⟨q, ?_⟩
    apply Subtype.ext
    exact hsource

/-- **The relative source-order chamber has no line in the stoichiometric directions.**
If both a test direction and its negative preserve the source order selected by `w`, then
all source-complex projections of that direction agree. Weak reversibility makes every
reaction target a source, so the direction annihilates every reaction vector. A vector in
the stoichiometric subspace that annihilates all reaction vectors must therefore vanish.

This is the required reduction before treating the finite source-order chambers as a fan in
the stoichiometric subspace: conservation directions have been removed, and the restricted
order cone is salient. -/
theorem relativeSourceOrderCone_lineality_eq_zero
    (N : Network S) (w : S → ℝ) {z : EuclideanSpace ℝ S}
    (hz : z ∈ N.relativeSourceOrderCone w)
    (hnegz : -z ∈ N.relativeSourceOrderCone w)
    (hstoich : CRNT.toEuclid.symm z ∈ N.stoichSubspace)
    (hwr : N.WeaklyReversible) :
    z = 0 := by
  let u : S → ℝ := CRNT.toEuclid.symm z
  let p : N.R → ℝ := fun r => N.sourceLogProjection u r
  have hproj : ∀ r q : N.R, p r = p q := by
    intro r q
    change (∀ r q,
      N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q) at hz
    change (∀ r q,
      N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
        N.sourceLogProjection (CRNT.toEuclid.symm (-z)) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm (-z)) q) at hnegz
    have hnegproj (i : N.R) :
        N.sourceLogProjection (CRNT.toEuclid.symm (-z)) i = -p i := by
      simp [p, u, sourceLogProjection, Finset.sum_neg_distrib]
    rcases le_total (N.sourceLogProjection w r) (N.sourceLogProjection w q) with hrq | hqr
    · have h₁ := hz r q hrq
      have h₂ := hnegz r q hrq
      rw [hnegproj r, hnegproj q] at h₂
      change p r ≤ p q at h₁
      linarith
    · have h₁ := hz q r hqr
      have h₂ := hnegz q r hqr
      rw [hnegproj q, hnegproj r] at h₂
      change p q ≤ p r at h₁
      linarith
  have hreact : ∀ r : N.R, ∑ s, u s * N.reactionVector r s = 0 := by
    intro r
    obtain ⟨q, hq⟩ := N.exists_sourceIdx_eq_targetIdx_of_weaklyReversible hwr r
    have hqval := congrArg Subtype.val hq
    have hp :
        (∑ s, ((N.targetIdx r).val s : ℝ) * u s) =
          ∑ s, ((N.sourceIdx r).val s : ℝ) * u s := by
      simpa [p, sourceLogProjection, hqval, u] using hproj q r
    calc
      (∑ s, u s * N.reactionVector r s) =
          ∑ s, u s * (((N.reaction r).target s : ℝ) -
            ((N.reaction r).source s : ℝ)) := by
              apply Finset.sum_congr rfl
              intro s _
              rw [reactionVector_apply]
      _ = (∑ s, ((N.reaction r).target s : ℝ) * u s) -
            ∑ s, ((N.reaction r).source s : ℝ) * u s := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = 0 := by
            simpa [sourceIdx, targetIdx] using sub_eq_zero.mpr hp
  have huorth : ∀ v ∈ N.stoichSubspace, ∑ s, u s * v s = 0 := by
    intro v hv
    rw [stoichSubspace] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨r, rfl⟩ := hv
        exact hreact r
    | zero => simp
    | add v₁ v₂ _ _ ih₁ ih₂ =>
        calc
          (∑ s, u s * (v₁ + v₂) s) =
              ∑ s, (u s * v₁ s + u s * v₂ s) := by
                apply Finset.sum_congr rfl
                intro s _
                simp only [Pi.add_apply]
                ring
          _ = 0 := by rw [Finset.sum_add_distrib, ih₁, ih₂, add_zero]
    | smul a v _ ih =>
        calc
          (∑ s, u s * (a • v) s) = ∑ s, a * (u s * v s) := by
            apply Finset.sum_congr rfl
            intro s _
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
          _ = 0 := by rw [← Finset.mul_sum, ih, mul_zero]
  have hnorm : ∑ s, u s * u s = 0 := huorth u hstoich
  have hterms : ∀ s, u s * u s = 0 := by
    intro s
    have hnonneg : ∀ t ∈ (Finset.univ : Finset S), 0 ≤ u t * u t :=
      fun t _ => mul_self_nonneg (u t)
    have hs := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hnorm
    exact hs s (Finset.mem_univ s)
  have hu : u = 0 := by
    funext s
    exact mul_self_eq_zero.mp (hterms s)
  calc
    z = CRNT.toEuclid (CRNT.toEuclid.symm z) :=
      (CRNT.toEuclid.apply_symm_apply z).symm
    _ = 0 := by simp [u, hu]

/-- Restrict a relative source-order cone to the Euclidean image of the stoichiometric
subspace. -/
noncomputable def relativeSourceOrderStoichCone (N : Network S) (w : S → ℝ) :
    PointedCone ℝ (EuclideanSpace ℝ S) :=
  N.relativeSourceOrderCone w ⊓
    PointedCone.ofSubmodule
      (Submodule.map (σ₁₂ := RingHom.id ℝ) CRNT.toEuclid.toLinearMap
        N.stoichSubspace)

@[simp] theorem mem_relativeSourceOrderStoichCone (N : Network S) (w : S → ℝ)
    {z : EuclideanSpace ℝ S} :
    z ∈ N.relativeSourceOrderStoichCone w ↔
      z ∈ N.relativeSourceOrderCone w ∧
        CRNT.toEuclid.symm z ∈ N.stoichSubspace := by
  simp only [relativeSourceOrderStoichCone, Submodule.mem_inf,
    PointedCone.mem_ofSubmodule_iff, Submodule.mem_map]
  constructor
  · rintro ⟨hcone, u, hu, huz⟩
    refine ⟨hcone, ?_⟩
    rw [← huz]
    simpa using hu
  · rintro ⟨hcone, hu⟩
    refine ⟨hcone, CRNT.toEuclid.symm z, hu, ?_⟩
    exact CRNT.toEuclid.apply_symm_apply z

/-- The stoichiometrically restricted source-order cone is closed. Its first factor is a
finite intersection of closed half-spaces; its second factor is a finite-dimensional
subspace. -/
theorem isClosed_relativeSourceOrderStoichCone (N : Network S) (w : S → ℝ) :
    IsClosed (N.relativeSourceOrderStoichCone w : Set (EuclideanSpace ℝ S)) := by
  rw [relativeSourceOrderStoichCone, Submodule.coe_inf, PointedCone.coe_ofSubmodule]
  exact (N.isClosed_relativeSourceOrderCone w).inter
    (Submodule.closed_of_finiteDimensional
      (Submodule.map (σ₁₂ := RingHom.id ℝ) CRNT.toEuclid.toLinearMap
        N.stoichSubspace))

/-- The restricted source-order cone, packaged as a closed cone for use by the toric-fan
interfaces. -/
noncomputable def relativeSourceOrderStoichProperCone (N : Network S) (w : S → ℝ) :
    ProperCone ℝ (EuclideanSpace ℝ S) := by
  exact ⟨N.relativeSourceOrderStoichCone w,
    N.isClosed_relativeSourceOrderStoichCone w⟩

/-- Weak reversibility makes each stoichiometrically restricted source-order cone salient:
the cone and its negative intersect only at zero. -/
theorem relativeSourceOrderStoichCone_lineality_eq_zero
    (N : Network S) (w : S → ℝ) (hwr : N.WeaklyReversible)
    {z : EuclideanSpace ℝ S} (hz : z ∈ N.relativeSourceOrderStoichCone w)
    (hnegz : -z ∈ N.relativeSourceOrderStoichCone w) : z = 0 := by
  have hz' := (N.mem_relativeSourceOrderStoichCone w).mp hz
  have hnegz' := (N.mem_relativeSourceOrderStoichCone w).mp hnegz
  exact N.relativeSourceOrderCone_lineality_eq_zero w hz'.1 hnegz'.1 hz'.2 hwr

/-- The intersection normal has nonnegative pairing on its first source-order cone. -/
theorem inner_relativeSourceOrderIntersectionNormal_nonneg
    (N : Network S) (w₁ w₂ : S → ℝ) {z : EuclideanSpace ℝ S}
    (hz : z ∈ N.relativeSourceOrderCone w₁) :
    0 ≤ ⟪N.relativeSourceOrderIntersectionNormal w₁ w₂, z⟫_ℝ := by
  classical
  rw [N.inner_relativeSourceOrderIntersectionNormal_eq]
  have horder : ∀ r q : N.R,
      N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q := by
    change (∀ r q, _ ≤ _ → _ ≤ _) at hz
    exact hz
  apply Finset.sum_nonneg
  intro p _
  rcases p with ⟨r, q⟩
  by_cases h :
      ¬ N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q ∧
        N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q
  · rw [if_pos h]
    exact sub_nonneg.mpr (horder q r (le_of_not_ge h.1))
  · rw [if_neg h]

/-- If the intersection normal pairs to zero with a vector in its first cone, every new
source-order comparison imposed by the second reference has zero projection gap. -/
theorem sourceOrderIntersectionGap_eq_zero_of_inner_eq_zero
    (N : Network S) (w₁ w₂ : S → ℝ) {z : EuclideanSpace ℝ S}
    (hz : z ∈ N.relativeSourceOrderCone w₁)
    (hzero : ⟪N.relativeSourceOrderIntersectionNormal w₁ w₂, z⟫_ℝ = 0)
    {r q : N.R}
    (hinv : ¬ N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q ∧
      N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q) :
    N.sourceLogProjection (CRNT.toEuclid.symm z) q =
      N.sourceLogProjection (CRNT.toEuclid.symm z) r := by
  classical
  have horder : ∀ a b : N.R,
      N.sourceLogProjection w₁ a ≤ N.sourceLogProjection w₁ b →
        N.sourceLogProjection (CRNT.toEuclid.symm z) a ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) b := by
    change (∀ a b, _ ≤ _ → _ ≤ _) at hz
    exact hz
  have hnonneg : ∀ p ∈ (Finset.univ : Finset (N.R × N.R)),
      0 ≤ if ¬ N.sourceLogProjection w₁ p.1 ≤ N.sourceLogProjection w₁ p.2 ∧
          N.sourceLogProjection w₂ p.1 ≤ N.sourceLogProjection w₂ p.2 then
        N.sourceLogProjection (CRNT.toEuclid.symm z) p.1 -
          N.sourceLogProjection (CRNT.toEuclid.symm z) p.2
      else 0 := by
    intro p _
    rcases p with ⟨a, b⟩
    by_cases h :
        ¬ N.sourceLogProjection w₁ a ≤ N.sourceLogProjection w₁ b ∧
          N.sourceLogProjection w₂ a ≤ N.sourceLogProjection w₂ b
    · rw [if_pos h]
      exact sub_nonneg.mpr (horder b a (le_of_not_ge h.1))
    · rw [if_neg h]
  have hsum := N.inner_relativeSourceOrderIntersectionNormal_eq w₁ w₂ z
  rw [hzero] at hsum
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum.symm
  have hterm := hterms (r, q) (Finset.mem_univ _)
  have hgap := by simpa [hinv.1, hinv.2] using hterm
  linarith

/-- The intersection normal has nonpositive pairing on the second source-order cone. -/
theorem inner_relativeSourceOrderIntersectionNormal_nonpos
    (N : Network S) (w₁ w₂ : S → ℝ) {z : EuclideanSpace ℝ S}
    (hz : z ∈ N.relativeSourceOrderCone w₂) :
    ⟪N.relativeSourceOrderIntersectionNormal w₁ w₂, z⟫_ℝ ≤ 0 := by
  classical
  rw [N.inner_relativeSourceOrderIntersectionNormal_eq]
  have horder : ∀ r q : N.R,
      N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q := by
    change (∀ r q, _ ≤ _ → _ ≤ _) at hz
    exact hz
  apply Finset.sum_nonpos
  intro p _
  rcases p with ⟨r, q⟩
  by_cases h :
      ¬ N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q ∧
        N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q
  · rw [if_pos h]
    exact sub_nonpos.mpr (horder r q h.2)
  · rw [if_neg h]

/-- The intersection of two stoichiometrically restricted source-order cones is an exposed
face of the first cone. The supporting normal is the sum of the inequalities present in the
second order and absent in the first. -/
theorem relativeSourceOrderStoichCone_inf_eq_exposedFace
    (N : Network S) (w₁ w₂ : S → ℝ) :
    N.relativeSourceOrderStoichCone w₁ ⊓ N.relativeSourceOrderStoichCone w₂ =
      CRNT.exposedFace (N.relativeSourceOrderStoichCone w₁)
        (N.relativeSourceOrderIntersectionNormal w₁ w₂) := by
  ext z
  rw [Submodule.mem_inf, CRNT.mem_exposedFace]
  constructor
  · rintro ⟨hz₁, hz₂⟩
    have hcone₁ : z ∈ N.relativeSourceOrderCone w₁ :=
      (N.mem_relativeSourceOrderStoichCone w₁).mp hz₁ |>.1
    have hcone₂ : z ∈ N.relativeSourceOrderCone w₂ :=
      (N.mem_relativeSourceOrderStoichCone w₂).mp hz₂ |>.1
    refine ⟨hz₁, ?_⟩
    exact le_antisymm
      (N.inner_relativeSourceOrderIntersectionNormal_nonpos w₁ w₂ hcone₂)
      (N.inner_relativeSourceOrderIntersectionNormal_nonneg w₁ w₂ hcone₁)
  · rintro ⟨hz₁, hzero⟩
    have hz₁' := (N.mem_relativeSourceOrderStoichCone w₁).mp hz₁
    have hcone₁ := hz₁'.1
    have horder₁ : ∀ r q : N.R,
        N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q →
          N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
            N.sourceLogProjection (CRNT.toEuclid.symm z) q := by
      change (∀ r q, _ ≤ _ → _ ≤ _) at hcone₁
      exact hcone₁
    have hcone₂ : z ∈ N.relativeSourceOrderCone w₂ := by
      change (∀ r q,
        N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q →
          N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
            N.sourceLogProjection (CRNT.toEuclid.symm z) q)
      intro r q hw₂
      by_cases hw₁ : N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q
      · exact horder₁ r q hw₁
      · have hgap := N.sourceOrderIntersectionGap_eq_zero_of_inner_eq_zero
          w₁ w₂ hcone₁ hzero ⟨hw₁, hw₂⟩
        rw [hgap]
    exact ⟨hz₁, (N.mem_relativeSourceOrderStoichCone w₂).2 ⟨hcone₂, hz₁'.2⟩⟩

/-- The supporting normal for two restricted source-order cones belongs to the dual of the
first cone. -/
theorem relativeSourceOrderIntersectionNormal_mem_coneDual
    (N : Network S) (w₁ w₂ : S → ℝ) :
    N.relativeSourceOrderIntersectionNormal w₁ w₂ ∈
      CRNT.coneDual
        (N.relativeSourceOrderStoichProperCone w₁ : Set (EuclideanSpace ℝ S)) := by
  rw [CRNT.mem_coneDual]
  intro z hz
  rw [real_inner_comm]
  exact N.inner_relativeSourceOrderIntersectionNormal_nonneg w₁ w₂
    ((N.mem_relativeSourceOrderStoichCone w₁).mp hz).1

/-- Pairwise intersections in the finite restricted source-order family are exposed faces of
each participating cone, with a possibly different supporting normal for each side. -/
theorem relativeSourceOrderStoichProperCone_inter_isExposedFaceOf
    (N : Network S) (w₁ w₂ : S → ℝ) :
    CRNT.IsExposedFaceOf
      (N.relativeSourceOrderStoichProperCone w₁ ⊓
        N.relativeSourceOrderStoichProperCone w₂)
      (N.relativeSourceOrderStoichProperCone w₁) := by
  refine ⟨N.relativeSourceOrderIntersectionNormal w₁ w₂,
    N.relativeSourceOrderIntersectionNormal_mem_coneDual w₁ w₂, ?_⟩
  ext z
  have hface := congrArg (fun C : PointedCone ℝ (EuclideanSpace ℝ S) => z ∈ C)
    (N.relativeSourceOrderStoichCone_inf_eq_exposedFace w₁ w₂)
  simpa only [relativeSourceOrderStoichProperCone, ProperCone.toPointedCone,
    ClosedSubmodule.toSubmodule_inf, SetLike.mem_coe, Submodule.mem_inf] using
    Iff.of_eq hface

/-- The same intersection is an exposed face of its second participating cone. -/
theorem relativeSourceOrderStoichProperCone_inter_isExposedFaceOf_right
    (N : Network S) (w₁ w₂ : S → ℝ) :
    CRNT.IsExposedFaceOf
      (N.relativeSourceOrderStoichProperCone w₁ ⊓
        N.relativeSourceOrderStoichProperCone w₂)
      (N.relativeSourceOrderStoichProperCone w₂) := by
  simpa only [inf_comm] using
    (N.relativeSourceOrderStoichProperCone_inter_isExposedFaceOf w₂ w₁)

/-- The nonnegative projection gap for the source ordering chosen by `w`. For any point of its
relative source-order cone, the selected comparison is respected; this gap records its slack. -/
noncomputable def relativeSourceOrderIntersectionGap (N : Network S) (w : S → ℝ)
    (z : EuclideanSpace ℝ S) (r q : N.R) : ℝ :=
  if N.sourceLogProjection w r ≤ N.sourceLogProjection w q then
    N.sourceLogProjection (CRNT.toEuclid.symm z) q -
      N.sourceLogProjection (CRNT.toEuclid.symm z) r
  else
    N.sourceLogProjection (CRNT.toEuclid.symm z) r -
      N.sourceLogProjection (CRNT.toEuclid.symm z) q

/-- The selected projection gap is nonnegative throughout its source-order cone. -/
theorem relativeSourceOrderIntersectionGap_nonneg (N : Network S) (w : S → ℝ)
    {z : EuclideanSpace ℝ S} (hz : z ∈ N.relativeSourceOrderStoichCone w)
    (r q : N.R) :
    0 ≤ N.relativeSourceOrderIntersectionGap w z r q := by
  have horder := (N.mem_relativeSourceOrderStoichCone w).mp hz |>.1
  by_cases hw : N.sourceLogProjection w r ≤ N.sourceLogProjection w q
  · simp only [relativeSourceOrderIntersectionGap, if_pos hw]
    exact sub_nonneg.mpr (horder r q hw)
  · have hrev : N.sourceLogProjection w q ≤ N.sourceLogProjection w r :=
      le_of_lt (not_le.mp hw)
    simp only [relativeSourceOrderIntersectionGap, if_neg hw]
    exact sub_nonneg.mpr (horder q r hrev)

/-- A point in the intersection of two source-order cones that has positive slack for a
comparison. -/
noncomputable def relativeSourceOrderIntersectionWitness (N : Network S)
    (w₁ w₂ : S → ℝ) (r q : N.R) : EuclideanSpace ℝ S := by
  classical
  exact if h : ∃ z : EuclideanSpace ℝ S,
      z ∈ N.relativeSourceOrderStoichCone w₁ ⊓ N.relativeSourceOrderStoichCone w₂ ∧
      0 < N.relativeSourceOrderIntersectionGap w₁ z r q then
    Classical.choose h
  else 0

/-- Each selected witness lies in both source-order cones. If no point has positive slack, the
zero vector is the witness. -/
theorem relativeSourceOrderIntersectionWitness_mem (N : Network S)
    (w₁ w₂ : S → ℝ) (r q : N.R) :
    N.relativeSourceOrderIntersectionWitness w₁ w₂ r q ∈
      N.relativeSourceOrderStoichCone w₁ ⊓ N.relativeSourceOrderStoichCone w₂ := by
  classical
  unfold relativeSourceOrderIntersectionWitness
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact zero_mem _

/-- When positive slack exists in the intersection, its chosen witness has positive slack. -/
theorem relativeSourceOrderIntersectionWitness_gap_pos (N : Network S)
    (w₁ w₂ : S → ℝ) (r q : N.R)
    (h : ∃ z : EuclideanSpace ℝ S,
      z ∈ N.relativeSourceOrderStoichCone w₁ ⊓ N.relativeSourceOrderStoichCone w₂ ∧
        0 < N.relativeSourceOrderIntersectionGap w₁ z r q) :
    0 < N.relativeSourceOrderIntersectionGap w₁
      (N.relativeSourceOrderIntersectionWitness w₁ w₂ r q) r q := by
  classical
  unfold relativeSourceOrderIntersectionWitness
  have h' : ∃ z : EuclideanSpace ℝ S,
      z ∈ N.relativeSourceOrderStoichCone w₁ ⊓ N.relativeSourceOrderStoichCone w₂ ∧
        0 < N.relativeSourceOrderIntersectionGap w₁ z r q := h
  simp only [dif_pos h']
  exact (Classical.choose_spec h').2

/-- Additivity of source projections after transporting a finite sum from Euclidean coordinates. -/
private theorem sourceLogProjection_symm_sum (N : Network S) {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ S) (r : N.R) :
    N.sourceLogProjection (CRNT.toEuclid.symm (∑ i, v i)) r =
      ∑ i, N.sourceLogProjection (CRNT.toEuclid.symm (v i)) r := by
  rw [N.sourceLogProjection_eq_inner_toEuclid, CRNT.toEuclid.apply_symm_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [N.sourceLogProjection_eq_inner_toEuclid]
  rw [CRNT.toEuclid.apply_symm_apply]

/-- The gap of the finite sum of all comparison witnesses is the sum of their gaps. -/
theorem relativeSourceOrderIntersectionGap_point_eq_sum (N : Network S)
    (w₁ w₂ : S → ℝ) (r q : N.R) :
    N.relativeSourceOrderIntersectionGap w₁
        (∑ p : N.R × N.R, N.relativeSourceOrderIntersectionWitness w₁ w₂ p.1 p.2) r q =
      ∑ p : N.R × N.R,
        N.relativeSourceOrderIntersectionGap w₁
          (N.relativeSourceOrderIntersectionWitness w₁ w₂ p.1 p.2) r q := by
  classical
  unfold relativeSourceOrderIntersectionGap
  by_cases hw : N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q
  · simp only [if_pos hw]
    rw [sourceLogProjection_symm_sum, sourceLogProjection_symm_sum,
      ← Finset.sum_sub_distrib]
  · simp only [if_neg hw]
    rw [sourceLogProjection_symm_sum, sourceLogProjection_symm_sum,
      ← Finset.sum_sub_distrib]

/-- The point made by summing all comparison witnesses lies in the intersection cone. -/
theorem relativeSourceOrderIntersectionPoint_mem (N : Network S) (w₁ w₂ : S → ℝ) :
    (∑ p : N.R × N.R, N.relativeSourceOrderIntersectionWitness w₁ w₂ p.1 p.2) ∈
      N.relativeSourceOrderStoichCone w₁ ⊓ N.relativeSourceOrderStoichCone w₂ := by
  apply Submodule.sum_mem _
  intro p _
  exact N.relativeSourceOrderIntersectionWitness_mem w₁ w₂ p.1 p.2

/-- If a comparison has positive slack anywhere in the intersection, it has positive slack at the
point formed by summing all witnesses. All other witness gaps are nonnegative. -/
theorem relativeSourceOrderIntersectionPoint_gap_pos (N : Network S)
    (w₁ w₂ : S → ℝ) {z : EuclideanSpace ℝ S} {r q : N.R}
    (hz : z ∈ N.relativeSourceOrderStoichCone w₁ ⊓ N.relativeSourceOrderStoichCone w₂)
    (hgap : 0 < N.relativeSourceOrderIntersectionGap w₁ z r q) :
    0 < N.relativeSourceOrderIntersectionGap w₁
      (∑ p : N.R × N.R, N.relativeSourceOrderIntersectionWitness w₁ w₂ p.1 p.2) r q := by
  classical
  have hchosen := N.relativeSourceOrderIntersectionWitness_gap_pos w₁ w₂ r q ⟨z, hz, hgap⟩
  rw [N.relativeSourceOrderIntersectionGap_point_eq_sum]
  apply Finset.sum_pos'
  · intro p _
    have hp := (N.relativeSourceOrderIntersectionWitness_mem w₁ w₂ p.1 p.2).1
    exact N.relativeSourceOrderIntersectionGap_nonneg w₁ hp r q
  · exact ⟨(r, q), Finset.mem_univ _, hchosen⟩

/-- If the summed witness point has zero slack for a comparison, every point in the intersection
has zero slack for that comparison. -/
theorem relativeSourceOrderIntersectionGap_eq_zero_of_point_eq_zero (N : Network S)
    (w₁ w₂ : S → ℝ) {z : EuclideanSpace ℝ S} {r q : N.R}
    (hz : z ∈ N.relativeSourceOrderStoichCone w₁ ⊓ N.relativeSourceOrderStoichCone w₂)
    (hpoint : N.relativeSourceOrderIntersectionGap w₁
        (∑ p : N.R × N.R, N.relativeSourceOrderIntersectionWitness w₁ w₂ p.1 p.2) r q = 0) :
    N.relativeSourceOrderIntersectionGap w₁ z r q = 0 := by
  have hnonneg := N.relativeSourceOrderIntersectionGap_nonneg w₁ hz.1 r q
  by_contra hne
  have hpos : 0 < N.relativeSourceOrderIntersectionGap w₁ z r q :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hsumpos := N.relativeSourceOrderIntersectionPoint_gap_pos w₁ w₂ hz hpos
  rw [hpoint] at hsumpos
  exact (lt_irrefl 0 hsumpos)

/-- The intersection of two stoichiometrically restricted source-order cones is another cone in
the same family. The finite sum of witnesses for all reaction-pair comparisons selects a point
whose weak source order describes exactly the common refinement. This is the closure step needed
to turn the finite source-order cover into fan data. -/
theorem relativeSourceOrderStoichCone_inf_eq_intersectionPointCone
    (N : Network S) (w₁ w₂ : S → ℝ) :
    N.relativeSourceOrderStoichCone w₁ ⊓ N.relativeSourceOrderStoichCone w₂ =
      N.relativeSourceOrderStoichCone
        (CRNT.toEuclid.symm
          (∑ p : N.R × N.R, N.relativeSourceOrderIntersectionWitness w₁ w₂ p.1 p.2)) := by
  classical
  let z₀ : EuclideanSpace ℝ S :=
    ∑ p : N.R × N.R, N.relativeSourceOrderIntersectionWitness w₁ w₂ p.1 p.2
  let w₀ : S → ℝ := CRNT.toEuclid.symm z₀
  have hz₀ : z₀ ∈ N.relativeSourceOrderStoichCone w₁ ⊓
      N.relativeSourceOrderStoichCone w₂ := by
    simpa [z₀] using N.relativeSourceOrderIntersectionPoint_mem w₁ w₂
  apply PointedCone.ext
  intro z
  change (z ∈ N.relativeSourceOrderStoichCone w₁ ∧
      z ∈ N.relativeSourceOrderStoichCone w₂) ↔
    z ∈ N.relativeSourceOrderStoichCone w₀
  rw [N.mem_relativeSourceOrderStoichCone, N.mem_relativeSourceOrderStoichCone,
    N.mem_relativeSourceOrderStoichCone]
  constructor
  · rintro ⟨⟨hz₁, hS⟩, ⟨hz₂, _⟩⟩
    refine ⟨?_, hS⟩
    change ∀ r q,
      N.sourceLogProjection w₀ r ≤ N.sourceLogProjection w₀ q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q
    intro r q h₀
    by_cases hw₁ : N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q
    · exact hz₁ r q hw₁
    · have hrev : N.sourceLogProjection w₁ q ≤ N.sourceLogProjection w₁ r :=
        le_of_lt (not_le.mp hw₁)
      have h₀rev :=
        ((N.mem_relativeSourceOrderStoichCone w₁).mp hz₀.1).1 q r hrev
      have h₀eq : N.sourceLogProjection w₀ r = N.sourceLogProjection w₀ q := by
        exact le_antisymm h₀ h₀rev
      have hgap₀ : N.relativeSourceOrderIntersectionGap w₁ z₀ r q = 0 := by
        simp only [relativeSourceOrderIntersectionGap, if_neg hw₁]
        change N.sourceLogProjection w₀ r - N.sourceLogProjection w₀ q = 0
        exact sub_eq_zero.mpr h₀eq
      have hz₁stoich : z ∈ N.relativeSourceOrderStoichCone w₁ :=
        (N.mem_relativeSourceOrderStoichCone w₁).2 ⟨hz₁, hS⟩
      have hz₂stoich : z ∈ N.relativeSourceOrderStoichCone w₂ :=
        (N.mem_relativeSourceOrderStoichCone w₂).2 ⟨hz₂, hS⟩
      have hzinter : z ∈ N.relativeSourceOrderStoichCone w₁ ⊓
          N.relativeSourceOrderStoichCone w₂ := by
        exact ⟨hz₁stoich, hz₂stoich⟩
      have hgapz :=
        N.relativeSourceOrderIntersectionGap_eq_zero_of_point_eq_zero w₁ w₂
          hzinter
          (by simpa [z₀] using hgap₀)
      have hzEq : N.sourceLogProjection (CRNT.toEuclid.symm z) r =
          N.sourceLogProjection (CRNT.toEuclid.symm z) q := by
        exact sub_eq_zero.mp (by simpa [relativeSourceOrderIntersectionGap, hw₁] using hgapz)
      exact le_of_eq hzEq
  · rintro ⟨hz₀order, hS⟩
    refine ⟨⟨?_, hS⟩, ⟨?_, hS⟩⟩
    · change ∀ r q,
        N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q →
          N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
            N.sourceLogProjection (CRNT.toEuclid.symm z) q
      intro r q hw
      have h₀order := ((N.mem_relativeSourceOrderStoichCone w₁).mp hz₀.1).1 r q hw
      simpa [w₀, z₀] using hz₀order r q h₀order
    · change ∀ r q,
        N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q →
          N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
            N.sourceLogProjection (CRNT.toEuclid.symm z) q
      intro r q hw
      have h₀order := ((N.mem_relativeSourceOrderStoichCone w₂).mp hz₀.2).1 r q hw
      simpa [w₀, z₀] using hz₀order r q h₀order

/-- In the packaged proper-cone family, every pairwise intersection is represented by another
member. This is the closure property required by the finite fan construction. -/
theorem relativeSourceOrderStoichProperCone_inf_eq_member
    (N : Network S) (w₁ w₂ : S → ℝ) :
    ∃ w : S → ℝ,
      N.relativeSourceOrderStoichProperCone w =
        N.relativeSourceOrderStoichProperCone w₁ ⊓
          N.relativeSourceOrderStoichProperCone w₂ := by
  let z₀ : EuclideanSpace ℝ S :=
    ∑ p : N.R × N.R, N.relativeSourceOrderIntersectionWitness w₁ w₂ p.1 p.2
  let w₀ : S → ℝ := CRNT.toEuclid.symm z₀
  refine ⟨w₀, ?_⟩
  apply ProperCone.ext
  intro z
  change z ∈ N.relativeSourceOrderStoichCone w₀ ↔
    z ∈ N.relativeSourceOrderStoichCone w₁ ⊓
      N.relativeSourceOrderStoichCone w₂
  exact Iff.of_eq ((congrArg (fun C : PointedCone ℝ (EuclideanSpace ℝ S) => z ∈ C)
    (N.relativeSourceOrderStoichCone_inf_eq_intersectionPointCone w₁ w₂)).symm)

/-- The finite weak-order signature of the reaction-source projections selected by `w`. -/
noncomputable def relativeSourceOrderSignature (N : Network S) (w : S → ℝ) :
    N.R → N.R → Bool :=
  fun r q => decide (N.sourceLogProjection w r ≤ N.sourceLogProjection w q)

theorem relativeSourceOrderSignature_le_iff (N : Network S) (w : S → ℝ)
    (r q : N.R) :
    N.relativeSourceOrderSignature w r q = true ↔
      N.sourceLogProjection w r ≤ N.sourceLogProjection w q := by
  simp [relativeSourceOrderSignature]

/-- Any realized finite weak-order signature has a representative direction. The chosen
representative is only used to index the finite family; its chamber is independent of the
choice by `relativeSourceOrderCone_eq_of_sameSourceOrder`. -/
noncomputable def relativeSourceOrderWitness (N : Network S)
    (σ : N.R → N.R → Bool) : S → ℝ :=
  by
    classical
    exact if h : ∃ w, N.relativeSourceOrderSignature w = σ then
      Classical.choose h else 0

theorem relativeSourceOrderSignature_witness_eq (N : Network S)
    {σ : N.R → N.R → Bool}
    (h : ∃ w, N.relativeSourceOrderSignature w = σ) :
    N.relativeSourceOrderSignature (N.relativeSourceOrderWitness σ) = σ := by
  classical
  unfold relativeSourceOrderWitness
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- A chamber is determined by its weak ordering of source projections, including ties. -/
theorem relativeSourceOrderCone_eq_of_sameSourceOrder (N : Network S)
    {w₁ w₂ : S → ℝ}
    (h : ∀ r q : N.R,
      (N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q) ↔
        (N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q)) :
    N.relativeSourceOrderCone w₁ = N.relativeSourceOrderCone w₂ := by
  ext z
  change (∀ r q,
      N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q) ↔
    (∀ r q,
      N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q)
  constructor
  · intro hz r q horder
    exact hz r q ((h r q).2 horder)
  · intro hz r q horder
    exact hz r q ((h r q).1 horder)

/-- There are only finitely many relative source-order chambers: a chamber depends only on a
Boolean weak-order signature on the finite reaction-index type, and each realized signature
has a representative direction. This establishes finiteness of the candidate chamber family;
the face-intersection and covering axioms still need to be proved before it is a fan. -/
theorem finite_relativeSourceOrderCone_range (N : Network S) :
    (Set.range (N.relativeSourceOrderCone)).Finite := by
  classical
  let f : (N.R → N.R → Bool) → PointedCone ℝ (EuclideanSpace ℝ S) :=
    fun σ => N.relativeSourceOrderCone (N.relativeSourceOrderWitness σ)
  have hfinite : (Set.range f).Finite := by
    simpa [Set.range] using
      (Set.toFinite (Set.univ : Set (N.R → N.R → Bool))).image f
  have hsub : Set.range (N.relativeSourceOrderCone) ⊆ Set.range f := by
    rintro C ⟨w, rfl⟩
    let σ := N.relativeSourceOrderSignature w
    have hreal : ∃ v, N.relativeSourceOrderSignature v = σ := ⟨w, rfl⟩
    have hsig := N.relativeSourceOrderSignature_witness_eq hreal
    have horder : ∀ r q : N.R,
        (N.sourceLogProjection (N.relativeSourceOrderWitness σ) r ≤
          N.sourceLogProjection (N.relativeSourceOrderWitness σ) q) ↔
        (N.sourceLogProjection w r ≤ N.sourceLogProjection w q) := by
      intro r q
      rw [← N.relativeSourceOrderSignature_le_iff
          (N.relativeSourceOrderWitness σ) r q, hsig,
        N.relativeSourceOrderSignature_le_iff w r q]
    refine ⟨σ, ?_⟩
    change N.relativeSourceOrderCone (N.relativeSourceOrderWitness σ) =
      N.relativeSourceOrderCone w
    exact N.relativeSourceOrderCone_eq_of_sameSourceOrder horder
  exact hfinite.subset hsub

/-- Restricting two identical source-order chambers to the same stoichiometric subspace
preserves their equality. -/
theorem relativeSourceOrderStoichProperCone_eq_of_sameSourceOrder (N : Network S)
    {w₁ w₂ : S → ℝ}
    (horder : ∀ r q : N.R,
      (N.sourceLogProjection w₁ r ≤ N.sourceLogProjection w₁ q) ↔
        (N.sourceLogProjection w₂ r ≤ N.sourceLogProjection w₂ q)) :
    N.relativeSourceOrderStoichProperCone w₁ =
      N.relativeSourceOrderStoichProperCone w₂ := by
  apply ProperCone.ext
  intro z
  change z ∈ N.relativeSourceOrderStoichCone w₁ ↔
    z ∈ N.relativeSourceOrderStoichCone w₂
  rw [N.mem_relativeSourceOrderStoichCone, N.mem_relativeSourceOrderStoichCone]
  rw [N.relativeSourceOrderCone_eq_of_sameSourceOrder horder]

/-- There are only finitely many closed source-order cones after restriction to the
stoichiometric subspace. -/
theorem finite_relativeSourceOrderStoichProperCone_range (N : Network S) :
    (Set.range (N.relativeSourceOrderStoichProperCone)).Finite := by
  classical
  let f : (N.R → N.R → Bool) → ProperCone ℝ (EuclideanSpace ℝ S) :=
    fun σ => N.relativeSourceOrderStoichProperCone (N.relativeSourceOrderWitness σ)
  have hfinite : (Set.range f).Finite := by
    simpa [Set.range] using
      (Set.toFinite (Set.univ : Set (N.R → N.R → Bool))).image f
  have hsub : Set.range (N.relativeSourceOrderStoichProperCone) ⊆ Set.range f := by
    rintro C ⟨w, rfl⟩
    let σ := N.relativeSourceOrderSignature w
    have hreal : ∃ v, N.relativeSourceOrderSignature v = σ := ⟨w, rfl⟩
    have hsig := N.relativeSourceOrderSignature_witness_eq hreal
    have horder : ∀ r q : N.R,
        (N.sourceLogProjection (N.relativeSourceOrderWitness σ) r ≤
          N.sourceLogProjection (N.relativeSourceOrderWitness σ) q) ↔
        (N.sourceLogProjection w r ≤ N.sourceLogProjection w q) := by
      intro r q
      rw [← N.relativeSourceOrderSignature_le_iff
          (N.relativeSourceOrderWitness σ) r q, hsig,
        N.relativeSourceOrderSignature_le_iff w r q]
    refine ⟨σ, ?_⟩
    change N.relativeSourceOrderStoichProperCone
        (N.relativeSourceOrderWitness σ) =
      N.relativeSourceOrderStoichProperCone w
    exact N.relativeSourceOrderStoichProperCone_eq_of_sameSourceOrder horder
  exact hfinite.subset hsub

/-- The exact finite family of stoichiometrically restricted source-order cones, packaged as
the cone data consumed by the toric differential-inclusion layer. -/
noncomputable def relativeSourceOrderStoichConeFamily (N : Network S) :
    Finset (ProperCone ℝ (EuclideanSpace ℝ S)) := by
  classical
  exact (N.finite_relativeSourceOrderStoichProperCone_range).toFinset

@[simp] theorem mem_relativeSourceOrderStoichConeFamily
    (N : Network S) {C : ProperCone ℝ (EuclideanSpace ℝ S)} :
    C ∈ N.relativeSourceOrderStoichConeFamily ↔
      C ∈ Set.range (N.relativeSourceOrderStoichProperCone) := by
  classical
  change C ∈ (N.finite_relativeSourceOrderStoichProperCone_range).toFinset ↔ _
  exact N.finite_relativeSourceOrderStoichProperCone_range.mem_toFinset

/-- The finite family is closed under pairwise intersections: each intersection is represented
by the finite sum of comparison witnesses and therefore remains one of its cones. -/
theorem relativeSourceOrderStoichConeFamily_inter_mem
    (N : Network S) {C₁ C₂ : ProperCone ℝ (EuclideanSpace ℝ S)}
    (h₁ : C₁ ∈ N.relativeSourceOrderStoichConeFamily)
    (h₂ : C₂ ∈ N.relativeSourceOrderStoichConeFamily) :
    C₁ ⊓ C₂ ∈ N.relativeSourceOrderStoichConeFamily := by
  rw [N.mem_relativeSourceOrderStoichConeFamily] at h₁ h₂ ⊢
  rcases h₁ with ⟨w₁, rfl⟩
  rcases h₂ with ⟨w₂, rfl⟩
  obtain ⟨w, hw⟩ := N.relativeSourceOrderStoichProperCone_inf_eq_member w₁ w₂
  exact ⟨w, hw⟩

/-- Pairwise intersections in the finite family are common exposed faces of both cones. Combined
with intersection closure, this supplies the polyhedral-complex intersection law. -/
theorem relativeSourceOrderStoichConeFamily_inter_commonExposedFace
    (N : Network S) {C₁ C₂ : ProperCone ℝ (EuclideanSpace ℝ S)}
    (h₁ : C₁ ∈ N.relativeSourceOrderStoichConeFamily)
    (h₂ : C₂ ∈ N.relativeSourceOrderStoichConeFamily) :
    CRNT.IsExposedFaceOf (C₁ ⊓ C₂) C₁ ∧
      CRNT.IsExposedFaceOf (C₁ ⊓ C₂) C₂ := by
  rw [N.mem_relativeSourceOrderStoichConeFamily] at h₁ h₂
  rcases h₁ with ⟨w₁, rfl⟩
  rcases h₂ with ⟨w₂, rfl⟩
  exact ⟨N.relativeSourceOrderStoichProperCone_inter_isExposedFaceOf w₁ w₂,
    N.relativeSourceOrderStoichProperCone_inter_isExposedFaceOf_right w₁ w₂⟩

/-- Every face of a stoichiometrically restricted source-order cone contains a point
whose weak source order records exactly the comparisons that can be strict on that face. This is
the finite-arrangement interior-point construction: sum one face witness for each comparison that
is not identically an equality on the face. -/
private theorem exists_relativeSourceOrderFace_orderPoint
    (N : Network S) (w : S → ℝ) {D : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hD : PointedCone.IsFaceOf (D : PointedCone ℝ (EuclideanSpace ℝ S))
      (N.relativeSourceOrderStoichProperCone w : PointedCone ℝ (EuclideanSpace ℝ S))) :
    ∃ z ∈ D, ∀ r q : N.R,
      N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
        (0 < N.sourceLogProjection (CRNT.toEuclid.symm z) q -
            N.sourceLogProjection (CRNT.toEuclid.symm z) r ↔
          ∃ y ∈ D, 0 < N.sourceLogProjection (CRNT.toEuclid.symm y) q -
            N.sourceLogProjection (CRNT.toEuclid.symm y) r) := by
  classical
  have hDsubset : ∀ z, z ∈ D → z ∈ N.relativeSourceOrderStoichProperCone w := by
    intro z hz
    exact hD.le hz
  let gap : EuclideanSpace ℝ S → N.R × N.R → ℝ := fun z p =>
    N.sourceLogProjection (CRNT.toEuclid.symm z) p.2 -
      N.sourceLogProjection (CRNT.toEuclid.symm z) p.1
  let strict : N.R × N.R → Prop := fun p =>
    N.sourceLogProjection w p.1 ≤ N.sourceLogProjection w p.2 ∧
      ∃ z ∈ D, 0 < gap z p
  let witness : N.R × N.R → EuclideanSpace ℝ S := fun p =>
    if h : strict p then Classical.choose h.2 else 0
  let z : EuclideanSpace ℝ S := ∑ p : N.R × N.R, witness p
  have hwitness_mem : ∀ p : N.R × N.R, witness p ∈ D := by
    intro p
    by_cases h : strict p
    · dsimp [witness]
      rw [dif_pos h]
      exact (Classical.choose_spec h.2).1
    · simp [witness, h]
  have hzD : z ∈ D := by
    change z ∈ (D : PointedCone ℝ (EuclideanSpace ℝ S))
    dsimp [z]
    exact Submodule.sum_mem _ (fun p _ => hwitness_mem p)
  have hgap_sum (p : N.R × N.R) : gap z p = ∑ q : N.R × N.R, gap (witness q) p := by
    dsimp [gap, z]
    rw [N.sourceLogProjection_symm_sum, N.sourceLogProjection_symm_sum,
      ← Finset.sum_sub_distrib]
  have hw_order_on_D {y : EuclideanSpace ℝ S} (hy : y ∈ D)
      {r q : N.R} (horder : N.sourceLogProjection w r ≤ N.sourceLogProjection w q) :
      N.sourceLogProjection (CRNT.toEuclid.symm y) r ≤
        N.sourceLogProjection (CRNT.toEuclid.symm y) q := by
    have hyC := hDsubset y hy
    change y ∈ N.relativeSourceOrderStoichCone w at hyC
    exact (N.mem_relativeSourceOrderStoichCone w).mp hyC |>.1 r q horder
  have hterm_nonneg (p : N.R × N.R) (q : N.R) (r : N.R)
      (horder : N.sourceLogProjection w r ≤ N.sourceLogProjection w q) :
      0 ≤ gap (witness p) (r, q) := by
    dsimp [gap]
    have hproj := hw_order_on_D (hwitness_mem p) horder
    linarith
  have hgap_nonneg (r q : N.R)
      (horder : N.sourceLogProjection w r ≤ N.sourceLogProjection w q) :
      0 ≤ gap z (r, q) := by
    rw [hgap_sum]
    exact Finset.sum_nonneg fun p _ => hterm_nonneg p q r horder
  have hgap_pos_of_strict (p : N.R × N.R) (h : strict p) : 0 < gap z p := by
    have hterm_pos : 0 < gap (witness p) p := by
      dsimp [witness]
      rw [dif_pos h]
      exact (Classical.choose_spec h.2).2
    rw [hgap_sum]
    exact Finset.sum_pos' (fun q _ => hterm_nonneg q p.2 p.1 h.1)
      ⟨p, Finset.mem_univ p, hterm_pos⟩
  have hgap_zero_of_not_strict (p : N.R × N.R)
      (horder : N.sourceLogProjection w p.1 ≤ N.sourceLogProjection w p.2)
      (h : ¬ strict p) : gap z p = 0 := by
    rw [hgap_sum]
    apply Finset.sum_eq_zero
    intro q _
    have hnonneg := hterm_nonneg q p.2 p.1 horder
    have hnotpos : ¬ 0 < gap (witness q) p := by
      intro hpos
      exact h ⟨horder, witness q, hwitness_mem q, hpos⟩
    linarith
  refine ⟨z, hzD, ?_⟩
  intro r q horder
  constructor
  · intro hpos
    by_contra hnot
    have hnotStrict : ¬ strict (r, q) := fun h => hnot h.2
    have hz0 := hgap_zero_of_not_strict (r, q) horder hnotStrict
    linarith
  · rintro ⟨y, hyD, hpos⟩
    exact hgap_pos_of_strict (r, q) ⟨horder, y, hyD, hpos⟩

/-- A face of a stoichiometrically restricted source-order cone is the intersection
with the source-order cone selected by a point in that face. The face point is strict exactly on
the comparisons that are not forced to equality; a small perturbation then shows that these
        comparisons cut out precisely the face. -/
theorem relativeSourceOrderStoichProperCone_face_eq_inter
    (N : Network S) (w : S → ℝ) {D : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hD : PointedCone.IsFaceOf (D : PointedCone ℝ (EuclideanSpace ℝ S))
      (N.relativeSourceOrderStoichProperCone w : PointedCone ℝ (EuclideanSpace ℝ S))) :
    ∃ v : S → ℝ,
      D = N.relativeSourceOrderStoichProperCone w ⊓
        N.relativeSourceOrderStoichProperCone v := by
  classical
  obtain ⟨z, hzD, hzorder⟩ := N.exists_relativeSourceOrderFace_orderPoint w hD
  let v : S → ℝ := CRNT.toEuclid.symm z
  let gap (x : EuclideanSpace ℝ S) (r q : N.R) : ℝ :=
    N.sourceLogProjection (CRNT.toEuclid.symm x) q -
      N.sourceLogProjection (CRNT.toEuclid.symm x) r
  have hDsubset : ∀ x, x ∈ D → x ∈ N.relativeSourceOrderStoichProperCone w := by
    intro x hx
    exact hD.le hx
  have hzC : z ∈ N.relativeSourceOrderStoichProperCone w := hDsubset z hzD
  have hzStoich : CRNT.toEuclid.symm z ∈ N.stoichSubspace := by
    change z ∈ N.relativeSourceOrderStoichCone w at hzC
    exact (N.mem_relativeSourceOrderStoichCone w).mp hzC |>.2
  have hD_subset_v : ∀ x, x ∈ D →
      x ∈ N.relativeSourceOrderStoichProperCone v := by
    intro x hx
    have hxC := hDsubset x hx
    change x ∈ N.relativeSourceOrderStoichCone v
    apply (N.mem_relativeSourceOrderStoichCone v).2
    constructor
    · intro r q horderV
      by_cases horderW : N.sourceLogProjection w r ≤ N.sourceLogProjection w q
      · have hxorder := (N.mem_relativeSourceOrderStoichCone w).mp hxC |>.1
        exact hxorder r q horderW
      · have horderW' : N.sourceLogProjection w q ≤ N.sourceLogProjection w r :=
          le_of_not_ge horderW
        have hzrev : N.sourceLogProjection v q ≤ N.sourceLogProjection v r := by
          have hzorderC := (N.mem_relativeSourceOrderStoichCone w).mp hzC |>.1
          exact hzorderC q r horderW'
        have hvEq : N.sourceLogProjection v r = N.sourceLogProjection v q :=
          le_antisymm horderV hzrev
        have hgapzZero : gap z q r = 0 := by
          dsimp [gap, v] at hvEq ⊢
          linarith
        have hnoWitness : ¬ ∃ y ∈ D, 0 < gap y q r := by
          intro he
          have hgapzPos := (hzorder q r horderW').2 he
          change 0 < gap z q r at hgapzPos
          rw [hgapzZero] at hgapzPos
          linarith
        have hxorderW := (N.mem_relativeSourceOrderStoichCone w).mp hxC |>.1
        have hxgapNonneg : 0 ≤ gap x q r := by
          dsimp [gap]
          linarith [hxorderW q r horderW']
        have hxgapNonpos : gap x q r ≤ 0 := by
          by_contra hpos
          exact hnoWitness ⟨x, hx, lt_of_not_ge hpos⟩
        have hxgapZero : gap x q r = 0 := le_antisymm hxgapNonpos hxgapNonneg
        change N.sourceLogProjection (CRNT.toEuclid.symm x) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm x) q
        change N.sourceLogProjection (CRNT.toEuclid.symm x) r -
          N.sourceLogProjection (CRNT.toEuclid.symm x) q = 0 at hxgapZero
        linarith
    · have hxStoich : CRNT.toEuclid.symm x ∈ N.stoichSubspace := by
        change x ∈ N.relativeSourceOrderStoichCone w at hxC
        exact (N.mem_relativeSourceOrderStoichCone w).mp hxC |>.2
      exact hxStoich
  have hgap_sub_smul (ε : ℝ) (x : EuclideanSpace ℝ S) (r q : N.R) :
      gap (z - ε • x) r q = gap z r q - ε * gap x r q := by
    have hproj (t : EuclideanSpace ℝ S) (j : N.R) :
        N.sourceLogProjection (CRNT.toEuclid.symm (z - ε • x)) j =
          N.sourceLogProjection (CRNT.toEuclid.symm z) j -
            ε * N.sourceLogProjection (CRNT.toEuclid.symm x) j := by
      rw [N.sourceLogProjection_eq_inner_toEuclid, N.sourceLogProjection_eq_inner_toEuclid,
        N.sourceLogProjection_eq_inner_toEuclid]
      simp only [CRNT.toEuclid.apply_symm_apply, map_sub, map_smul]
      rw [inner_sub_right, real_inner_smul_right]
    dsimp [gap]
    rw [hproj x q, hproj x r]
    ring
  refine ⟨v, ?_⟩
  apply ProperCone.ext
  intro x
  constructor
  · intro hx
    have hxC := hDsubset x hx
    have hxV := hD_subset_v x hx
    exact ⟨hxC, hxV⟩
  · rintro ⟨hxC, hxV⟩
    have hxStoich : CRNT.toEuclid.symm x ∈ N.stoichSubspace := by
      change x ∈ N.relativeSourceOrderStoichCone w at hxC
      exact (N.mem_relativeSourceOrderStoichCone w).mp hxC |>.2
    have hxorderW : ∀ r q : N.R,
        N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
          N.sourceLogProjection (CRNT.toEuclid.symm x) r ≤
            N.sourceLogProjection (CRNT.toEuclid.symm x) q := by
      change x ∈ N.relativeSourceOrderStoichCone w at hxC
      exact (N.mem_relativeSourceOrderStoichCone w).mp hxC |>.1
    have hxorderV : ∀ r q : N.R,
        N.sourceLogProjection v r ≤ N.sourceLogProjection v q →
          N.sourceLogProjection (CRNT.toEuclid.symm x) r ≤
            N.sourceLogProjection (CRNT.toEuclid.symm x) q := by
      change x ∈ N.relativeSourceOrderStoichCone v at hxV
      exact (N.mem_relativeSourceOrderStoichCone v).mp hxV |>.1
    let active : Finset (N.R × N.R) :=
      Finset.univ.filter (fun p => 0 < gap z p.1 p.2)
    let ratio : N.R × N.R → ℝ := fun p =>
      gap z p.1 p.2 / (1 + |gap x p.1 p.2|)
    have heps : ∃ ε : ℝ, 0 < ε ∧ ∀ p : N.R × N.R,
        0 < gap z p.1 p.2 → ε * |gap x p.1 p.2| < gap z p.1 p.2 := by
      by_cases hactive : active.Nonempty
      · let ε := (active.image ratio).min' (Finset.image_nonempty.mpr hactive)
        have hminpos : 0 < ε := by
          dsimp [ε]
          obtain ⟨p, hp, hEq⟩ := Finset.mem_image.mp
            (Finset.min'_mem (active.image ratio) (Finset.image_nonempty.mpr hactive))
          have hp' := (Finset.mem_filter.mp hp).2
          rw [← hEq]
          dsimp [ratio]
          positivity
        refine ⟨ε, hminpos, ?_⟩
        intro p hp
        have hpActive : p ∈ active := by
          simp [active, hp]
        have hpRatio : ratio p ∈ active.image ratio :=
          Finset.mem_image.mpr ⟨p, hpActive, rfl⟩
        have hminle : ε ≤ ratio p :=
          Finset.min'_le (active.image ratio) _ hpRatio
        calc
          ε * |gap x p.1 p.2| ≤ ratio p * |gap x p.1 p.2| :=
            mul_le_mul_of_nonneg_right hminle (abs_nonneg _)
          _ < gap z p.1 p.2 := by
            have hratio : ratio p * |gap x p.1 p.2| =
                gap z p.1 p.2 * |gap x p.1 p.2| /
                  (1 + |gap x p.1 p.2|) := by
              dsimp [ratio]
              ring
            have hden : 0 < 1 + |gap x p.1 p.2| := by positivity
            have habs : |gap x p.1 p.2| < 1 + |gap x p.1 p.2| := by
              have := abs_nonneg (gap x p.1 p.2)
              linarith
            rw [hratio]
            exact (div_lt_iff₀ hden).2
              (mul_lt_mul_of_pos_left habs hp)
      · refine ⟨1, by norm_num, ?_⟩
        intro p hp
        exact (hactive ⟨p, by simp [active, hp]⟩).elim
    obtain ⟨ε, hε, hepsbound⟩ := heps
    have hxgapVzero (r q : N.R)
        (horder : N.sourceLogProjection w r ≤ N.sourceLogProjection w q)
        (hzero : gap z r q = 0) : gap x r q = 0 := by
      have hzv : N.sourceLogProjection v r = N.sourceLogProjection v q := by
        dsimp [gap, v] at hzero ⊢
        linarith
      have hxrv := hxorderV r q (by rw [hzv])
      have hxqr := hxorderV q r (by rw [hzv])
      dsimp [gap]
      linarith
    have hperturbOrder : ∀ r q : N.R,
        N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
          N.sourceLogProjection (CRNT.toEuclid.symm (z - ε • x)) r ≤
            N.sourceLogProjection (CRNT.toEuclid.symm (z - ε • x)) q := by
      intro r q horder
      have hzGap : 0 ≤ gap z r q := by
        have hzorderW := (N.mem_relativeSourceOrderStoichCone w).mp hzC |>.1
        dsimp [gap]
        linarith [hzorderW r q horder]
      by_cases hpos : 0 < gap z r q
      · have hxGap : 0 ≤ gap x r q := by
          dsimp [gap]
          linarith [hxorderW r q horder]
        have hbound := hepsbound (r, q) hpos
        rw [abs_of_nonneg hxGap] at hbound
        have hgap := hgap_sub_smul ε x r q
        have hperturbGap : 0 ≤ gap (z - ε • x) r q := by
          rw [hgap]
          linarith
        dsimp [gap] at hperturbGap ⊢
        linarith
      · have hzero : gap z r q = 0 := le_antisymm (le_of_not_gt hpos) hzGap
        have hxzero := hxgapVzero r q horder hzero
        have hperturbGap : 0 ≤ gap (z - ε • x) r q := by
          rw [hgap_sub_smul, hzero, hxzero]
          simp
        dsimp [gap] at hperturbGap ⊢
        linarith
    have hperturbStoich : CRNT.toEuclid.symm (z - ε • x) ∈ N.stoichSubspace := by
      have hlin := N.stoichSubspace.smul_mem ε hxStoich
      have hdiff := N.stoichSubspace.sub_mem hzStoich hlin
      simpa only [map_sub, map_smul] using hdiff
    have hperturbC : z - ε • x ∈ N.relativeSourceOrderStoichProperCone w := by
      change z - ε • x ∈ N.relativeSourceOrderStoichCone w
      exact (N.mem_relativeSourceOrderStoichCone w).2 ⟨hperturbOrder, hperturbStoich⟩
    have hdecomp : ε • x + (z - ε • x) = z := by module
    have hsumD : ε • x + (z - ε • x) ∈ D := by
      rw [hdecomp]
      exact hzD
    exact hD.mem_of_smul_add_mem hxC hperturbC hε hsumD

/-- Exposed-face intersection representation follows from the general face theorem. -/
theorem relativeSourceOrderStoichProperCone_exposedFace_eq_inter
    (N : Network S) (w : S → ℝ) {D : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hD : CRNT.IsExposedFaceOf D (N.relativeSourceOrderStoichProperCone w)) :
    ∃ v : S → ℝ,
      D = N.relativeSourceOrderStoichProperCone w ⊓
        N.relativeSourceOrderStoichProperCone v :=
  N.relativeSourceOrderStoichProperCone_face_eq_inter w
    (CRNT.isExposedFaceOf_isFaceOf hD)

/-- The finite stoichiometric source-order family is closed under faces. The face theorem
represents any face as an intersection with another chamber, and pairwise intersection
closure keeps that face in the family. -/
theorem relativeSourceOrderStoichConeFamily_face_mem
    (N : Network S) {C D : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hC : C ∈ N.relativeSourceOrderStoichConeFamily)
    (hface : PointedCone.IsFaceOf (D : PointedCone ℝ (EuclideanSpace ℝ S))
      (C : PointedCone ℝ (EuclideanSpace ℝ S))) :
    D ∈ N.relativeSourceOrderStoichConeFamily := by
  rw [N.mem_relativeSourceOrderStoichConeFamily] at hC
  rcases hC with ⟨w, rfl⟩
  obtain ⟨v, hEq⟩ := N.relativeSourceOrderStoichProperCone_face_eq_inter w hface
  have hleft : N.relativeSourceOrderStoichProperCone w ∈
      N.relativeSourceOrderStoichConeFamily :=
    (N.mem_relativeSourceOrderStoichConeFamily).2 ⟨w, rfl⟩
  have hright : N.relativeSourceOrderStoichProperCone v ∈
      N.relativeSourceOrderStoichConeFamily :=
    (N.mem_relativeSourceOrderStoichConeFamily).2 ⟨v, rfl⟩
  have hinter := N.relativeSourceOrderStoichConeFamily_inter_mem hleft hright
  rw [← hEq] at hinter
  exact hinter

/-- Exposed-face closure follows from the general face-closure theorem. -/
theorem relativeSourceOrderStoichConeFamily_exposedFace_mem
    (N : Network S) {C D : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hC : C ∈ N.relativeSourceOrderStoichConeFamily)
    (hface : CRNT.IsExposedFaceOf D C) :
    D ∈ N.relativeSourceOrderStoichConeFamily :=
  N.relativeSourceOrderStoichConeFamily_face_mem hC
    (CRNT.isExposedFaceOf_isFaceOf hface)

/-- A direction belongs to the source-order chamber it itself selects. -/
theorem toEuclid_mem_relativeSourceOrderCone (N : Network S) (w : S → ℝ) :
    CRNT.toEuclid w ∈ N.relativeSourceOrderCone w := by
  change (∀ r q,
    N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
      N.sourceLogProjection
        (CRNT.toEuclid.symm (CRNT.toEuclid w)) r ≤
        N.sourceLogProjection
          (CRNT.toEuclid.symm (CRNT.toEuclid w)) q)
  intro r q h
  simpa using h

/-- The finite family of relative source-order chambers covers the stoichiometric subspace:
each stoichiometric vector is contained in the chamber indexed by its own projection order.
Combined with `finite_relativeSourceOrderCone_range` and the lineality lemma, this gives the
cover and salience components of the candidate fan inside stoichiometric space. -/
theorem relativeSourceOrderCone_covers_stoichSubspace (N : Network S)
    {z : EuclideanSpace ℝ S}
    (hz : CRNT.toEuclid.symm z ∈ N.stoichSubspace) :
    ∃ w : S → ℝ, w ∈ N.stoichSubspace ∧
      z = CRNT.toEuclid w ∧ z ∈ N.relativeSourceOrderCone w := by
  refine ⟨CRNT.toEuclid.symm z, hz,
    (CRNT.toEuclid.apply_symm_apply z).symm, ?_⟩
  simpa using N.toEuclid_mem_relativeSourceOrderCone (CRNT.toEuclid.symm z)

/-- The finite family of closed stoichiometric source-order cones covers exactly the
stoichiometric subspace: every vector in that subspace belongs to one of the cones, and every
cone member remains stoichiometric. -/
theorem exists_relativeSourceOrderStoichProperCone_mem
    (N : Network S) {z : EuclideanSpace ℝ S}
    (hz : CRNT.toEuclid.symm z ∈ N.stoichSubspace) :
    ∃ C ∈ Set.range (N.relativeSourceOrderStoichProperCone), z ∈ C := by
  obtain ⟨w, hw, rfl, hcone⟩ := N.relativeSourceOrderCone_covers_stoichSubspace hz
  refine ⟨N.relativeSourceOrderStoichProperCone w, ⟨w, rfl⟩, ?_⟩
  change CRNT.toEuclid w ∈ N.relativeSourceOrderStoichCone w
  exact (N.mem_relativeSourceOrderStoichCone w).2 ⟨hcone, hw⟩

/-- Membership in any cone of the candidate finite family implies stoichiometric membership. -/
theorem stoich_of_mem_relativeSourceOrderStoichProperCone
    (N : Network S) {C : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hC : C ∈ Set.range (N.relativeSourceOrderStoichProperCone))
    {z : EuclideanSpace ℝ S} (hz : z ∈ C) :
    CRNT.toEuclid.symm z ∈ N.stoichSubspace := by
  rcases hC with ⟨w, rfl⟩
  exact (N.mem_relativeSourceOrderStoichCone w).mp hz |>.2

/-- The exact finite family covers every stoichiometric direction. -/
theorem exists_relativeSourceOrderStoichConeFamily_mem
    (N : Network S) {z : EuclideanSpace ℝ S}
    (hz : CRNT.toEuclid.symm z ∈ N.stoichSubspace) :
    ∃ C ∈ N.relativeSourceOrderStoichConeFamily, z ∈ C := by
  obtain ⟨C, hC, hzC⟩ := N.exists_relativeSourceOrderStoichProperCone_mem hz
  exact ⟨C, (N.mem_relativeSourceOrderStoichConeFamily).2 hC, hzC⟩

/-- Every cone in the finite family remains inside the stoichiometric subspace. -/
theorem stoich_of_mem_relativeSourceOrderStoichConeFamily
    (N : Network S) {C : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hC : C ∈ N.relativeSourceOrderStoichConeFamily)
    {z : EuclideanSpace ℝ S} (hz : z ∈ C) :
    CRNT.toEuclid.symm z ∈ N.stoichSubspace :=
  N.stoich_of_mem_relativeSourceOrderStoichProperCone
    ((N.mem_relativeSourceOrderStoichConeFamily).1 hC) hz

/-- **Pointwise toric inclusion for a complex-balanced field.** At every positive state `x`, the
mass-action vector field lies in the polar cone of the source-order cone determined by
`log(x/xstar)`. This is the exact finite-dimensional toric differential-inclusion statement: the
full field, not just one reaction or one cycle, has nonpositive pairing with every direction in the
closed source-order chamber. -/
theorem massActionVectorField_mem_polar_relativeSourceOrderCone
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    CRNT.toEuclid (N.massActionVectorField κ x) ∈
      polarCone (N.relativeSourceOrderCone
        (fun s => Real.log (x s) - Real.log (xstar s))) := by
  rw [mem_polarCone]
  intro z hz
  change (∀ r q,
    N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r ≤
      N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) q →
    N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
      N.sourceLogProjection (CRNT.toEuclid.symm z) q) at hz
  have horder : ∀ r q, N.Linked (N.sourceIdx r).val (N.sourceIdx q).val →
      N.sourceLogProjection (CRNT.toEuclid.symm z) r <
        N.sourceLogProjection (CRNT.toEuclid.symm z) q →
      N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r <
        N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) q := by
    intro r q _ htest
    by_contra hnot
    have hreverse :
        N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) q ≤
          N.sourceLogProjection (fun s => Real.log (x s) - Real.log (xstar s)) r :=
      le_of_not_gt hnot
    have hcompat := hz q r hreverse
    exact (not_lt_of_ge hcompat) htest
  have hproj := N.massActionVectorField_projected_nonpos_of_relativeSourceOrder
    κ hx hxs hcb (CRNT.toEuclid.symm z) horder
  have hinner :
      ⟪z, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ =
        ∑ s, (CRNT.toEuclid.symm z) s * N.massActionVectorField κ x s := by
    calc
      ⟪z, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ =
          ⟪CRNT.toEuclid (CRNT.toEuclid.symm z),
            CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ := by
              rw [LinearEquiv.apply_symm_apply]
      _ = ∑ s, (CRNT.toEuclid.symm z) s * N.massActionVectorField κ x s :=
            CRNT.inner_toEuclid _ _
  rw [hinner]
  exact hproj

/-- Restricting the source-order chamber to stoichiometric directions preserves the pointwise
toric inclusion for the mass-action field. This is the form consumed by the finite cone family. -/
theorem massActionVectorField_mem_polar_relativeSourceOrderStoichCone
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    CRNT.toEuclid (N.massActionVectorField κ x) ∈
      polarCone (N.relativeSourceOrderStoichCone
        (fun s => Real.log (x s) - Real.log (xstar s))) := by
  have hfield := N.massActionVectorField_mem_polar_relativeSourceOrderCone κ hx hxs hcb
  rw [mem_polarCone] at hfield ⊢
  intro z hz
  exact hfield ((N.mem_relativeSourceOrderStoichCone _).mp hz).1

/-- At every positive state, the mass-action field lies in the polar of the finite chamber
selected by the projection of its relative logarithm onto stoichiometric space. The projection
preserves every source comparison within a linkage class, which is exactly what the closed-cycle
entropy estimate needs. -/
theorem massActionVectorField_mem_polar_relativeSourceOrderStoichProjection
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    CRNT.toEuclid (N.massActionVectorField κ x) ∈
      polarCone (N.relativeSourceOrderStoichCone
        (N.relativeLogStoichProjection
          (fun s => Real.log (x s) - Real.log (xstar s)))) := by
  let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let w : S → ℝ := N.relativeLogStoichProjection u
  have horth : CRNT.toEuclid (u - w) ∈ N.euclideanStoichSubspaceᗮ := by
    change CRNT.toEuclid u -
        N.euclideanStoichSubspace.starProjection (CRNT.toEuclid u) ∈
      N.euclideanStoichSubspaceᗮ
    exact N.euclideanStoichSubspace.sub_starProjection_mem_orthogonal _
  rw [mem_polarCone]
  intro z hz
  have hzorder := (N.mem_relativeSourceOrderStoichCone w).mp hz |>.1
  change (∀ r q,
      N.sourceLogProjection w r ≤ N.sourceLogProjection w q →
        N.sourceLogProjection (CRNT.toEuclid.symm z) r ≤
          N.sourceLogProjection (CRNT.toEuclid.symm z) q) at hzorder
  have horder : ∀ r q, N.Linked (N.sourceIdx r).val (N.sourceIdx q).val →
      N.sourceLogProjection (CRNT.toEuclid.symm z) r <
        N.sourceLogProjection (CRNT.toEuclid.symm z) q →
      N.sourceLogProjection u r < N.sourceLogProjection u q := by
    intro r q hlinked htest
    have hnot : ¬ N.sourceLogProjection w q ≤ N.sourceLogProjection w r := by
      intro hreverse
      exact (not_lt_of_ge (hzorder q r hreverse)) htest
    have hw : N.sourceLogProjection w r < N.sourceLogProjection w q :=
      lt_of_not_ge hnot
    have hsame := N.sourceLogProjection_sub_eq_of_linked_orthogonal
      horth r q hlinked
    have hdiff : N.sourceLogProjection u r - N.sourceLogProjection u q < 0 := by
      rw [hsame]
      exact sub_neg.mpr hw
    exact sub_neg.mp hdiff
  have hproj := N.massActionVectorField_projected_nonpos_of_relativeSourceOrder
    κ hx hxs hcb (CRNT.toEuclid.symm z) horder
  have hinner :
      ⟪z, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ =
        ∑ s, (CRNT.toEuclid.symm z) s * N.massActionVectorField κ x s := by
    calc
      ⟪z, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ =
          ⟪CRNT.toEuclid (CRNT.toEuclid.symm z),
            CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ := by
              rw [LinearEquiv.apply_symm_apply]
      _ = ∑ s, (CRNT.toEuclid.symm z) s * N.massActionVectorField κ x s :=
            CRNT.inner_toEuclid _ _
  rw [hinner]
  exact hproj

/-- Reorient a stoichiometrically restricted source-order cone so its nonnegative dual is the
nonpositive polar used by the cycle-dissipation argument. -/
noncomputable def relativeSourceOrderNegativeCone (N : Network S) (w : S → ℝ) :
    ProperCone ℝ (EuclideanSpace ℝ S) :=
  (N.relativeSourceOrderStoichProperCone w).comap
    (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S)))

@[simp] theorem mem_relativeSourceOrderNegativeCone (N : Network S) (w : S → ℝ)
    (z : EuclideanSpace ℝ S) :
    z ∈ N.relativeSourceOrderNegativeCone w ↔
      -z ∈ N.relativeSourceOrderStoichProperCone w := by
  simp [relativeSourceOrderNegativeCone, ProperCone.mem_comap]

/-- The exact finite family of sign-reversed chambers for the nonnegative-dual toric field. -/
noncomputable def relativeSourceOrderNegativeConeFamily (N : Network S) :
    CRNT.Fan (EuclideanSpace ℝ S) := by
  classical
  exact N.relativeSourceOrderStoichConeFamily.image fun C =>
    C.comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S)))

/-- Every sign-reversed chamber is a member of the finite toric generator family. -/
theorem relativeSourceOrderNegativeCone_mem_family (N : Network S) (w : S → ℝ) :
    N.relativeSourceOrderNegativeCone w ∈ N.relativeSourceOrderNegativeConeFamily := by
  classical
  rw [relativeSourceOrderNegativeConeFamily]
  apply Finset.mem_image.mpr
  refine ⟨N.relativeSourceOrderStoichProperCone w, ?_, rfl⟩
  exact (N.mem_relativeSourceOrderStoichConeFamily).2 ⟨w, rfl⟩

/-- The sign-reversed finite chamber family covers the stoichiometric subspace as well. A vector
`z` is in the sign-reversed cone generated from `C` precisely when `-z ∈ C`; since the
stoichiometric subspace is closed under negation, applying the existing source-order cover to
`-z` gives the corresponding cover for `z`. This is the covering property in the orientation used
by the complex-balanced toric field. -/
theorem exists_relativeSourceOrderNegativeConeFamily_mem
    (N : Network S) {z : EuclideanSpace ℝ S}
    (hz : CRNT.toEuclid.symm z ∈ N.stoichSubspace) :
    ∃ C ∈ N.relativeSourceOrderNegativeConeFamily, z ∈ C := by
  classical
  have hneg : CRNT.toEuclid.symm (-z) ∈ N.stoichSubspace := by
    simpa using N.stoichSubspace.neg_mem hz
  obtain ⟨D, hD, hDz⟩ := N.exists_relativeSourceOrderStoichConeFamily_mem hneg
  refine ⟨D.comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))), ?_, ?_⟩
  · rw [relativeSourceOrderNegativeConeFamily]
    exact Finset.mem_image.mpr ⟨D, hD, rfl⟩
  · simpa [ProperCone.mem_comap] using hDz

/-- Every cone of the sign-reversed family remains inside the stoichiometric subspace. Together
with `exists_relativeSourceOrderNegativeConeFamily_mem`, this identifies its union exactly with
the subspace whose directions govern a compatibility class. -/
theorem stoich_of_mem_relativeSourceOrderNegativeConeFamily
    (N : Network S) {C : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hC : C ∈ N.relativeSourceOrderNegativeConeFamily)
    {z : EuclideanSpace ℝ S} (hz : z ∈ C) :
    CRNT.toEuclid.symm z ∈ N.stoichSubspace := by
  classical
  rw [relativeSourceOrderNegativeConeFamily] at hC
  rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
  have hnegz : -z ∈ D := by
    simpa [ProperCone.mem_comap] using hz
  have hnegStoich := N.stoich_of_mem_relativeSourceOrderStoichConeFamily hD hnegz
  simpa using N.stoichSubspace.neg_mem hnegStoich

/-- The union of the sign-reversed source-order cones is exactly the stoichiometric subspace.
This packages the two directions of the relative cover: every stoichiometric vector belongs to
some cone, and no cone contains a direction outside the stoichiometric subspace. -/
theorem iUnion_relativeSourceOrderNegativeConeFamily (N : Network S) :
    (⋃ C ∈ N.relativeSourceOrderNegativeConeFamily,
        (C : Set (EuclideanSpace ℝ S))) =
      {z | CRNT.toEuclid.symm z ∈ N.stoichSubspace} := by
  ext z
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · rintro ⟨C, hC, hz⟩
    exact N.stoich_of_mem_relativeSourceOrderNegativeConeFamily hC hz
  · intro hz
    rcases N.exists_relativeSourceOrderNegativeConeFamily_mem hz with ⟨C, hC, hzC⟩
    exact ⟨C, ⟨hC, hzC⟩⟩

/-- The sign-reversed finite family is closed under pairwise intersections. Preimage under
negation commutes with intersection, so this is inherited directly from the source-order chamber
family. -/
theorem relativeSourceOrderNegativeConeFamily_inter_mem
    (N : Network S) {C₁ C₂ : ProperCone ℝ (EuclideanSpace ℝ S)}
    (h₁ : C₁ ∈ N.relativeSourceOrderNegativeConeFamily)
    (h₂ : C₂ ∈ N.relativeSourceOrderNegativeConeFamily) :
    C₁ ⊓ C₂ ∈ N.relativeSourceOrderNegativeConeFamily := by
  classical
  rw [relativeSourceOrderNegativeConeFamily] at h₁ h₂ ⊢
  rcases Finset.mem_image.mp h₁ with ⟨D₁, hD₁, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨D₂, hD₂, rfl⟩
  have hD := N.relativeSourceOrderStoichConeFamily_inter_mem hD₁ hD₂
  have hpreimage :
      D₁.comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))) ⊓
          D₂.comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))) =
        (D₁ ⊓ D₂).comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))) := by
    apply ProperCone.ext
    intro z
    simp
  rw [hpreimage]
  exact Finset.mem_image.mpr ⟨D₁ ⊓ D₂, hD, rfl⟩

/-- Negation transports an exposed-face certificate to the corresponding sign-reversed cones.
The supporting functional changes from `a` to `-a`, since both the cone and every point in it are
reoriented. -/
private theorem isExposedFaceOf_comap_neg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {D C : ProperCone ℝ E} (h : CRNT.IsExposedFaceOf D C) :
    CRNT.IsExposedFaceOf
      (D.comap (-(ContinuousLinearMap.id ℝ E)))
      (C.comap (-(ContinuousLinearMap.id ℝ E))) := by
  obtain ⟨a, ha, hface⟩ := h
  refine ⟨-a, ?_, ?_⟩
  · rw [CRNT.mem_coneDual]
    intro x hx
    have hxC : -x ∈ C := by simpa using hx
    have hnonneg : 0 ≤ ⟪-x, a⟫_ℝ := CRNT.mem_coneDual.mp ha hxC
    simpa [inner_neg_left, inner_neg_right] using hnonneg
  ·
    apply Set.ext
    intro x
    change x ∈ D.comap (-(ContinuousLinearMap.id ℝ E)) ↔
      x ∈ CRNT.exposedFace
        (C.comap (-(ContinuousLinearMap.id ℝ E) : E →L[ℝ] E) : PointedCone ℝ E) (-a)
    rw [CRNT.mem_exposedFace]
    constructor
    · intro hx
      have hxD : -x ∈ D := by simpa using hx
      have hxDset : (-x : E) ∈ ((D : PointedCone ℝ E) : Set E) := by simpa using hxD
      have hface_mem := congrArg (fun A : Set E => (-x : E) ∈ A) hface
      have hxface : -x ∈ CRNT.exposedFace (C : PointedCone ℝ E) a :=
        hface_mem.mp hxDset
      rcases CRNT.mem_exposedFace.mp hxface with ⟨hxC, hzero⟩
      exact ⟨by simpa using hxC,
        by simpa [inner_neg_left, inner_neg_right] using hzero⟩
    · rintro ⟨hxC, hzero⟩
      have hxnegC : -x ∈ C := by simpa using hxC
      have hzero' : ⟪a, -x⟫_ℝ = 0 := by
        simpa [inner_neg_left, inner_neg_right] using hzero
      have hxface : -x ∈ CRNT.exposedFace (C : PointedCone ℝ E) a :=
        CRNT.mem_exposedFace.mpr ⟨hxnegC, hzero'⟩
      have hxface_set : (-x : E) ∈
          (CRNT.exposedFace (C : PointedCone ℝ E) a : Set E) := by simpa using hxface
      have hface_mem := congrArg (fun A : Set E => (-x : E) ∈ A) hface
      have hxDset : (-x : E) ∈ ((D : PointedCone ℝ E) : Set E) :=
        hface_mem.mpr hxface_set
      have hxD : -x ∈ D := by simpa using hxDset
      simpa using hxD

/-- Negation transports arbitrary faces between the sign-reversed cone and its source cone. -/
private theorem isFaceOf_uncomap_neg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {D C : ProperCone ℝ E}
    (h : PointedCone.IsFaceOf (D : PointedCone ℝ E)
      (C.comap (-(ContinuousLinearMap.id ℝ E)) : PointedCone ℝ E)) :
    PointedCone.IsFaceOf (D.comap (-(ContinuousLinearMap.id ℝ E)) : PointedCone ℝ E)
      (C : PointedCone ℝ E) := by
  have h' := PointedCone.IsFaceOf.comap
    ((-(ContinuousLinearMap.id ℝ E)).toLinearMap) h
  have hright :
      ((C.comap (-(ContinuousLinearMap.id ℝ E)) : ProperCone ℝ E) :
        PointedCone ℝ E).comap ((-(ContinuousLinearMap.id ℝ E)).toLinearMap) =
        (C : PointedCone ℝ E) := by
    apply PointedCone.ext
    intro x
    simp
  have hleft :
      (D : PointedCone ℝ E).comap ((-(ContinuousLinearMap.id ℝ E)).toLinearMap) =
        ((D.comap (-(ContinuousLinearMap.id ℝ E)) : ProperCone ℝ E) :
          PointedCone ℝ E) := by
    apply PointedCone.ext
    intro x
    simp
  rw [hright] at h'
  exact hleft ▸ h'

/-- Pairwise intersections in the sign-reversed family are common exposed faces of both cones.
The positive source-order family already has supporting normals for both sides; the preceding
transport lemma reverses each normal and carries the face equations across negation. -/
theorem relativeSourceOrderNegativeConeFamily_inter_commonExposedFace
    (N : Network S) {C₁ C₂ : ProperCone ℝ (EuclideanSpace ℝ S)}
    (h₁ : C₁ ∈ N.relativeSourceOrderNegativeConeFamily)
    (h₂ : C₂ ∈ N.relativeSourceOrderNegativeConeFamily) :
    CRNT.IsExposedFaceOf (C₁ ⊓ C₂) C₁ ∧
      CRNT.IsExposedFaceOf (C₁ ⊓ C₂) C₂ := by
  classical
  rw [relativeSourceOrderNegativeConeFamily] at h₁ h₂
  rcases Finset.mem_image.mp h₁ with ⟨D₁, hD₁, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨D₂, hD₂, rfl⟩
  have hfaces := N.relativeSourceOrderStoichConeFamily_inter_commonExposedFace hD₁ hD₂
  have hpreimage :
      D₁.comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))) ⊓
          D₂.comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))) =
        (D₁ ⊓ D₂).comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))) := by
    apply ProperCone.ext
    intro z
    simp
  constructor
  · simpa only [hpreimage] using isExposedFaceOf_comap_neg hfaces.1
  · simpa only [hpreimage] using isExposedFaceOf_comap_neg hfaces.2

/-- The sign-reversed family is closed under faces. Negation carries an arbitrary face back to
the positive source-order family, whose face closure is already proved, then the involutive
preimage returns the resulting cone to this family. -/
theorem relativeSourceOrderNegativeConeFamily_face_mem
    (N : Network S) {C D : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hC : C ∈ N.relativeSourceOrderNegativeConeFamily)
    (hface : PointedCone.IsFaceOf (D : PointedCone ℝ (EuclideanSpace ℝ S))
      (C : PointedCone ℝ (EuclideanSpace ℝ S))) :
    D ∈ N.relativeSourceOrderNegativeConeFamily := by
  classical
  rw [relativeSourceOrderNegativeConeFamily] at hC ⊢
  obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
  have hface₀ : PointedCone.IsFaceOf
      (D.comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))) :
        PointedCone ℝ (EuclideanSpace ℝ S))
      (C₀ : PointedCone ℝ (EuclideanSpace ℝ S)) :=
    isFaceOf_uncomap_neg hface
  have hD₀ := N.relativeSourceOrderStoichConeFamily_face_mem hC₀ hface₀
  apply Finset.mem_image.mpr
  refine ⟨D.comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))), hD₀, ?_⟩
  have hdouble (K : ProperCone ℝ (EuclideanSpace ℝ S)) :
      (K.comap (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S)))).comap
        (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ S))) = K := by
    apply ProperCone.ext
    intro x
    simp
  exact hdouble D

/-- Exposed-face closure follows from the general face-closure theorem. -/
theorem relativeSourceOrderNegativeConeFamily_exposedFace_mem
    (N : Network S) {C D : ProperCone ℝ (EuclideanSpace ℝ S)}
    (hC : C ∈ N.relativeSourceOrderNegativeConeFamily)
    (hface : CRNT.IsExposedFaceOf D C) :
    D ∈ N.relativeSourceOrderNegativeConeFamily :=
  N.relativeSourceOrderNegativeConeFamily_face_mem hC
    (CRNT.isExposedFaceOf_isFaceOf hface)

/-- The projected relative log state lies in the negative of its selected source-order cone. -/
theorem negativeRelativeLogStoichProjection_mem_relativeSourceOrderNegativeCone
    (N : Network S) (u : S → ℝ) :
    -CRNT.toEuclid (N.relativeLogStoichProjection u) ∈
      N.relativeSourceOrderNegativeCone (N.relativeLogStoichProjection u) := by
  rw [N.mem_relativeSourceOrderNegativeCone, neg_neg]
  change CRNT.toEuclid (N.relativeLogStoichProjection u) ∈
    N.relativeSourceOrderStoichCone (N.relativeLogStoichProjection u)
  exact (N.mem_relativeSourceOrderStoichCone _).2
    ⟨N.toEuclid_mem_relativeSourceOrderCone _, N.relativeLogStoichProjection_mem u⟩

/-- A positive non-equilibrium of a complex-balanced system cannot have zero velocity: zero
velocity makes the relative-entropy dissipation vanish, which forces complex balance. -/
theorem massActionVectorField_ne_zero_of_not_complexBalanced
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnotcb : ¬ N.IsComplexBalanced κ x) :
    N.massActionVectorField κ x ≠ 0 := by
  intro hzero
  have hdiss : (∑ s, (Real.log (x s) - Real.log (xstar s)) *
      N.massActionVectorField κ x s) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [congrFun hzero s]
    simp
  exact hnotcb (complexBalanced_of_dissipation_eq_zero N κ hx hxs hcb hdiss)

/-- **Strict source-order support away from complex balance.** The field belongs to the polar of
the source-order cone selected by the projected relative logarithm. If a point in that cone can be
perturbed a positive distance along the field while remaining in the cone, the pairing is strict:
the field is nonzero away from complex balance, so polar membership rules out equality. -/
theorem massActionVectorField_inner_lt_zero_of_positiveConePerturbation
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnotcb : ¬ N.IsComplexBalanced κ x)
    {z : EuclideanSpace ℝ S}
    (hperturb : ∃ ε : ℝ, 0 < ε ∧ z + ε • CRNT.toEuclid
      (N.massActionVectorField κ x) ∈ N.relativeSourceOrderStoichCone
        (N.relativeLogStoichProjection
          (fun s => Real.log (x s) - Real.log (xstar s)))) :
    ⟪z, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ < 0 := by
  have hpolar := N.massActionVectorField_mem_polar_relativeSourceOrderStoichProjection
    κ hx hxs hcb
  have hfieldne := N.massActionVectorField_ne_zero_of_not_complexBalanced
    κ hx hxs hcb hnotcb
  have hne : CRNT.toEuclid (N.massActionVectorField κ x) ≠ 0 := by
    intro h
    apply hfieldne
    exact CRNT.toEuclid.injective h
  exact CRNT.polarCone_inner_lt_zero_of_positivePerturbation hpolar hne hperturb

/-- **Complex-balanced vector field in the finite toric field.** At every positive concentration,
the projected relative logarithmic state is in one sign-reversed source-order chamber, and the
full mass-action vector field is in that chamber's nonnegative dual. Hence the vector field is a
member of the toric field generated by the exact finite family of source-order chambers. -/
theorem massActionVectorField_mem_relativeSourceOrderToricField
    (N : Network S) (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {δ : ℝ} (hδ : 0 < δ) :
    CRNT.toEuclid (N.massActionVectorField κ x) ∈
      CRNT.toricField N.relativeSourceOrderNegativeConeFamily δ
        (-CRNT.toEuclid (N.relativeLogStoichProjection
          (fun s => Real.log (x s) - Real.log (xstar s)))) := by
  let u : S → ℝ := fun s => Real.log (x s) - Real.log (xstar s)
  let w : S → ℝ := N.relativeLogStoichProjection u
  let C : ProperCone ℝ (EuclideanSpace ℝ S) :=
    N.relativeSourceOrderNegativeCone w
  have hstate : -CRNT.toEuclid w ∈ C := by
    change -CRNT.toEuclid w ∈ N.relativeSourceOrderNegativeCone w
    exact N.negativeRelativeLogStoichProjection_mem_relativeSourceOrderNegativeCone u
  have hdist : Metric.infDist (-CRNT.toEuclid w) (C : Set (EuclideanSpace ℝ S)) = 0 :=
    Metric.infDist_zero_of_mem hstate
  have hnear : Metric.infDist (-CRNT.toEuclid w) (C : Set (EuclideanSpace ℝ S)) < δ := by
    rw [hdist]
    exact hδ
  have hCmem : C ∈ N.relativeSourceOrderNegativeConeFamily := by
    change N.relativeSourceOrderNegativeCone w ∈
      N.relativeSourceOrderNegativeConeFamily
    exact N.relativeSourceOrderNegativeCone_mem_family w
  have hpolar := N.massActionVectorField_mem_polar_relativeSourceOrderStoichProjection
    κ hx hxs hcb
  have hdual : CRNT.toEuclid (N.massActionVectorField κ x) ∈
      CRNT.coneDual (C : Set (EuclideanSpace ℝ S)) := by
    rw [CRNT.mem_coneDual]
    intro z hz
    have hneg : -z ∈ N.relativeSourceOrderStoichProperCone w := by
      change z ∈ N.relativeSourceOrderNegativeCone w at hz
      exact (N.mem_relativeSourceOrderNegativeCone w z).mp hz
    have hpolar' :
        CRNT.toEuclid (N.massActionVectorField κ x) ∈
          CRNT.polarCone (N.relativeSourceOrderStoichCone w) := by
      simpa [u, w] using hpolar
    have hle : ⟪-z, CRNT.toEuclid (N.massActionVectorField κ x)⟫_ℝ ≤ 0 :=
      (CRNT.mem_polarCone.mp hpolar') hneg
    rw [inner_neg_left] at hle
    linarith
  exact CRNT.coneDual_le_toricField hCmem hnear hdual

/-- **Eventual order-cone dissipation on every logarithmic ray.** Fix a positive complex-balanced
equilibrium and any direction `w` in log-concentration space. Along `xₜ = exp(t w)`, the field
has nonpositive projection against every test direction `z` whose strict source-complex order is
preserved by `w`.

This follows from the chamberwise estimate above because every strictly ordered pair of source
levels has a positive minimum gap in this finite network, while the equilibrium source factors
have a fixed finite range. If there are no strict source-level gaps, both ordering hypotheses are
vacuous and the same estimate applies immediately. This gives the field's polar-cone sign on the
closed source-order chamber at infinity; it does not provide the global glued separating surface
needed for permanence. -/
theorem eventually_orderCompatible_projected_nonpos_on_exp_ray
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) [Nonempty N.R]
    (w : S → ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ z : S → ℝ,
      (∀ r q, N.sourceLogProjection z r < N.sourceLogProjection z q →
        N.sourceLogProjection w r < N.sourceLogProjection w q) →
      (∑ s, z s * N.massActionVectorField κ (fun s => Real.exp (t * w s)) s) ≤ 0 := by
  obtain ⟨kmin, kmax, δ, hkmin, hk, hscale⟩ :=
    N.exists_uniform_equilibriumSourceFactor_bounds xstar
  obtain ⟨r₀⟩ := ‹Nonempty N.R›
  have hminlemax : kmin ≤ kmax := (hk r₀).1.trans (hk r₀).2
  have hratio : 1 ≤ kmax / kmin := (one_le_div hkmin).2 hminlemax
  have hratioExp : 1 ≤ Real.exp δ :=
    hratio.trans ((div_le_iff₀ hkmin).2 (by simpa [mul_comm] using hscale))
  have hδnonneg : 0 ≤ δ := by
    rw [← Real.exp_zero, Real.exp_le_exp] at hratioExp
    exact hratioExp
  let p : N.R → ℝ := fun r => N.sourceLogProjection w r
  let xt (t : ℝ) : Concentration S := fun s => Real.exp (t * w s)
  have hlogproj (t : ℝ) (r : N.R) :
      N.sourceLogProjection (fun s => Real.log (xt t s)) r = t * p r := by
    have hlog : (fun s => Real.log (xt t s)) = fun s => t * w s := by
      funext s
      simp [xt, Real.log_exp]
    rw [hlog]
    unfold sourceLogProjection p
    calc
      (∑ s, ((N.sourceIdx r).val s : ℝ) * (t * w s)) =
          ∑ s, t * (((N.sourceIdx r).val s : ℝ) * w s) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ = t * ∑ s, ((N.sourceIdx r).val s : ℝ) * w s := by
            rw [Finset.mul_sum]
  by_cases hstrict : ∃ r q : N.R, p r < p q
  · obtain ⟨ε, hεpos, hεgap⟩ := exists_positive_uniform_strict_gap hstrict
    let T : ℝ := δ / ε + 1
    refine ⟨T, ?_, ?_⟩
    · dsimp [T]
      positivity
    · intro t ht
      have hdivnonneg : 0 ≤ δ / ε := div_nonneg hδnonneg (le_of_lt hεpos)
      have htpos : 0 < t := by dsimp [T] at ht; linarith
      have hδt : δ ≤ t * ε := by
        apply (div_le_iff₀ hεpos).mp
        dsimp [T] at ht
        linarith
      have hgap : ∀ r q : N.R,
          N.sourceLogProjection (fun s => Real.log (xt t s)) r <
            N.sourceLogProjection (fun s => Real.log (xt t s)) q →
          N.sourceLogProjection (fun s => Real.log (xt t s)) r + δ ≤
            N.sourceLogProjection (fun s => Real.log (xt t s)) q := by
        intro r q hrq
        have hpq : p r < p q := by
          rw [hlogproj t r, hlogproj t q] at hrq
          exact (mul_lt_mul_iff_of_pos_left htpos).mp hrq
        have hscaled : δ ≤ t * (p q - p r) := by
          calc
            δ ≤ t * ε := hδt
            _ ≤ t * (p q - p r) :=
              mul_le_mul_of_nonneg_left (hεgap r q hpq) (le_of_lt htpos)
        rw [hlogproj t r, hlogproj t q]
        nlinarith [hscaled]
      intro z hzorder
      have horder : ∀ r q : N.R,
          N.sourceLogProjection z r < N.sourceLogProjection z q →
          N.sourceLogProjection (fun s => Real.log (xt t s)) r <
            N.sourceLogProjection (fun s => Real.log (xt t s)) q := by
        intro r q hrq
        have hworder := hzorder r q hrq
        rw [hlogproj t r, hlogproj t q]
        exact mul_lt_mul_of_pos_left (by simpa [p] using hworder) htpos
      have hxt : (xt t).Positive := fun s => Real.exp_pos _
      exact N.massActionVectorField_projected_nonpos_of_rateSeparatedSourceOrder
        κ hxt hxs hcb z hkmin.le hscale (fun r => hk r) hgap horder
  · let T : ℝ := 1
    refine ⟨T, by norm_num [T], ?_⟩
    intro t ht
    have htpos : 0 < t := by dsimp [T] at ht; linarith
    have hno : ∀ r q : N.R, ¬ p r < p q := by
      intro r q hpq
      exact hstrict ⟨r, q, hpq⟩
    have hgap : ∀ r q : N.R,
        N.sourceLogProjection (fun s => Real.log (xt t s)) r <
          N.sourceLogProjection (fun s => Real.log (xt t s)) q →
        N.sourceLogProjection (fun s => Real.log (xt t s)) r + δ ≤
          N.sourceLogProjection (fun s => Real.log (xt t s)) q := by
      intro r q hrq
      rw [hlogproj t r, hlogproj t q] at hrq
      exact (hno r q ((mul_lt_mul_iff_of_pos_left htpos).mp hrq)).elim
    intro z hzorder
    have horder : ∀ r q : N.R,
        N.sourceLogProjection z r < N.sourceLogProjection z q →
        N.sourceLogProjection (fun s => Real.log (xt t s)) r <
          N.sourceLogProjection (fun s => Real.log (xt t s)) q := by
      intro r q hrq
      have hpq := hzorder r q hrq
      exact (hno r q (by simpa [p] using hpq)).elim
    have hxt : (xt t).Positive := fun s => Real.exp_pos _
    exact N.massActionVectorField_projected_nonpos_of_rateSeparatedSourceOrder
      κ hxt hxs hcb z hkmin.le hscale (fun r => hk r) hgap horder

/-- The radial specialization of `eventually_orderCompatible_projected_nonpos_on_exp_ray`.
The ray direction itself always preserves its own source order. -/
theorem eventually_radially_nonpos_on_exp_ray
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) [Nonempty N.R]
    (w : S → ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      (∑ s, w s * N.massActionVectorField κ (fun s => Real.exp (t * w s)) s) ≤ 0 := by
  obtain ⟨T, hT, hprojected⟩ :=
    N.eventually_orderCompatible_projected_nonpos_on_exp_ray κ hxs hcb w
  refine ⟨T, hT, ?_⟩
  intro t ht
  apply hprojected t ht w
  intro r q hrq
  exact hrq

end CRNT.Network
