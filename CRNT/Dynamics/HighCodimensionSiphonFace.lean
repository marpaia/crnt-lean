import CRNT.Dynamics.FaceCodimension
import CRNT.Dynamics.SiphonDimensionDescent
import CRNT.Dynamics.ToricBarrierTrapping
import CRNT.Dynamics.SingleLinkageGAC
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Equilibria.ComplexBalanced
import CRNT.Dynamics.VertexOmegaExclusion
import CRNT.Persistence.ComplexBalancedFloor

/-!
# The codimension ≥ 2 case of the Global Attractor Theorem (closed)

`CRNT.Dynamics.GlobalAttractorTheorem` reduces `Network.complexBalanced_genuinePermanent` to the
case treated here: the ω-limit set of a bounded genuine positive mass-action trajectory of a
complex-balanced system contains a point `wmax` whose zero set `Pmax` is a maximal critical
siphon whose face has codimension at least two in the compatibility class.

This case is **closed**, with no axioms beyond `propext`, `Classical.choice`, `Quot.sound`:

* the vertex sub-case by `Network.false_of_vertex_omegaPoint`
  (`CRNT.Dynamics.VertexOmegaExclusion`; Craciun–Dickenstein–Shiu–Sturmfels 2009, Prop. 20);
* the non-vertex sub-case `exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex`
  by `Network.complexBalanced_forward_floor` (`CRNT.Persistence.ComplexBalancedFloor`): every
  bounded forward solution of a complex-balanced system starting at a positive state has a
  positive lower bound on all coordinates for all `t ≥ 0`, so no ω-point can vanish on `Pmax`.

The floor theorem follows Craciun's toric-differential-inclusion strategy (v3, Theorem B) with
the following explicit constructions in place of v3 §7–§8.

* **Field decomposition** (`dot_massActionField_nonneg`): along any inward normal `a` with
  `⟨a, c − c'⟩ < 0 → δ ≤ ⟨c − c', log x⟩` for all complex pairs, `⟨a, f(x)⟩ ≥ 0`.  The
  complex-balanced fluxes form a circulation; `circulation_pairing_nonneg` eliminates the
  complex of largest height.
* **Region** (`exists_zsh`): an intersection of half-spaces with nonnegative normals, organized
  by level `m` (acting on the `m + 1` smallest coordinates at scale `ε ^ e_m`) and closed under
  permutations.  Each level's facets come from a blueprint tree (`build_spec`) whose offsets
  realize a nested lower envelope; `realized_of_isMin` localizes the active facet, `walk` and
  `level_validity` turn that into the sign condition, and `sort_reduce` reduces arbitrary
  points to sorted ones.
* **Invariance**: `PolyhedralBarrier.barrier_le_of_local_descent_in_band`.

Depends on: `CRNT.Dynamics.FaceCodimension`, `CRNT.Dynamics.SiphonDimensionDescent`,
`CRNT.Dynamics.ToricBarrierTrapping`, `CRNT.Persistence.ComplexBalancedFloor`.
-/

open scoped NNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A face whose projection keeps the full stoichiometric rank is a vertex. -/
theorem isVertexZeroSet_of_finrank_map_eq (N : Network S) {P : Finset S}
    (h : Module.finrank ℝ (N.stoichSubspace.map (projOn P)) = N.stoichRank) :
    N.IsVertexZeroSet P := by
  intro u hu hzero
  set f := (projOn P).domRestrict N.stoichSubspace with hf
  have hrange : LinearMap.range f = N.stoichSubspace.map (projOn P) := LinearMap.range_domRestrict _ _
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, h] at hrn
  have hker : Module.finrank ℝ (LinearMap.ker f) = 0 := by
    unfold stoichRank at hrn; omega
  have hbot : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp hker
  have hmem : (⟨u, hu⟩ : N.stoichSubspace) ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, hf, LinearMap.domRestrict_apply]
    funext s
    by_cases hs : s ∈ P <;> simp [projOn_apply, hs, hzero]
  rw [hbot, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem

/-- **The non-vertex residual needs stoichiometric rank at least three.** -/
theorem three_le_stoichRank_of_nonVertex (N : Network S) {P : Finset S}
    (hcodim : 2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn P)))
    (hnv : ¬ N.IsVertexZeroSet P) : 3 ≤ N.stoichRank := by
  have hle : Module.finrank ℝ (N.stoichSubspace.map (projOn P)) ≤ N.stoichRank :=
    Submodule.finrank_map_le _ _
  have hne : Module.finrank ℝ (N.stoichSubspace.map (projOn P)) ≠ N.stoichRank :=
    fun h => hnv (N.isVertexZeroSet_of_finrank_map_eq h)
  omega

/-- **Residual obligation, non-vertex case.**  Exactly the hypotheses of
`exists_positive_omegaPoint_of_highCodimension_siphonFace`, plus `hnv`: the `Pmax`-face of the
compatibility class is not a single point, i.e. some nonzero stoichiometric vector vanishes on
`Pmax`.  The vertex case is closed by `Network.false_of_vertex_omegaPoint`
(Craciun–Dickenstein–Shiu–Sturmfels 2009, Proposition 20).  Together with `hcodim` this forces
`3 ≤ N.stoichRank`.  Proved by `Network.complexBalanced_forward_floor`: the orbit has a positive
coordinate floor, so `wmax`, which vanishes on the nonempty `Pmax`, cannot be an ω-point. -/
theorem exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hzcard : ∀ z ∈ omegaLimit atTop ϕ {x₀},
      (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card)
    (hcodim : 2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax)))
    (hcard : 2 ≤ Pmax.card)
    (hrank : N.stoichRank ≠ 1)
    (hnv : ¬ N.IsVertexZeroSet Pmax) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  exfalso
  -- the orbit is bounded above
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hbdd : ∀ t : ℝ, 0 ≤ t → ∀ s, γ x₀ t s ≤ C := by
    intro t ht s
    have hmem : γ x₀ t ∈ K := by
      have h1 := hmaps ⟨t, ht⟩
      rw [hϕγ x₀ ⟨t, ht⟩] at h1
      exact h1
    have h1 : ‖γ x₀ t s‖ ≤ ‖γ x₀ t‖ := norm_le_pi_norm (γ x₀ t) s
    rw [Real.norm_eq_abs] at h1
    exact le_trans (le_abs_self _) (le_trans h1 (hC _ hmem))
  have hγ0 : (γ x₀ 0).Positive := by
    have h0 := hϕγ x₀ 0
    simp only [Flow.map_zero_apply, NNReal.coe_zero] at h0
    rw [← h0]; exact hx₀
  -- a positive floor along the whole forward orbit (Persistence route)
  obtain ⟨η, hη, hfl⟩ := N.complexBalanced_forward_floor κ hxs hcb hγ0 hsol hbdd
  -- hence every ω-point is above the floor, contradicting `wmax s0 = 0`
  obtain ⟨s0, hs0⟩ := hPmaxne
  have hw0 : wmax s0 = 0 := (hzeroMax s0).mp hs0
  have hclosed : IsClosed {y : Concentration S | η ≤ y s0} :=
    isClosed_Ici.preimage (continuous_apply s0)
  have horbit : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ {y : Concentration S | η ≤ y s0} := by
    rintro y ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [hϕγ]
    exact hfl t t.coe_nonneg s0
  have hω : omegaLimit atTop ϕ {x₀} ⊆ {y : Concentration S | η ≤ y s0} :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem).trans ((IsClosed.closure_subset_iff hclosed).mpr horbit)
  have := hω hwmax
  simp only [Set.mem_setOf_eq, hw0] at this
  linarith

/-- **Residual obligation: the ω-limit set cannot sit on a critical-siphon face of codimension
at least two.**

All hypotheses are exactly the data available at the corresponding point of
`Network.complexBalanced_genuinePermanent`:

* `hxs`, `hcb`: a positive complex-balanced equilibrium for the rates `κ`;
* `hϕγ`, `hsol`, `hK`, `hmaps`: a bounded genuine forward trajectory through the positive
  point `x₀`, presented as a cutoff semiflow;
* `hωnn`, `hgenω`, `hωaff`: the ω-limit set is nonnegative, consists of genuine orbits, and
  lies in the compatibility class of `x₀`;
* `hPmaxne`, `hwmax`, `hzeroMax`, `hmaxExact`, `hzcard`: `wmax` is an ω-point whose zero set is
  exactly the nonempty species set `Pmax`, and `Pmax` is maximal among zero sets of ω-points —
  no ω-point has a zero set of larger cardinality (`hzcard`), and every ω-point vanishing on
  `Pmax` vanishes exactly on `Pmax` (`hmaxExact`);
* `hcodim`, `hcard`: the `Pmax`-face has codimension at least two in the compatibility class
  and `Pmax` has at least two species — both supplied by
  `Network.highCodimension_of_not_facet`;
* `hrank`: the stoichiometric rank is not one.

The conclusion is the interior certificate `PositiveOmegaPointForRates` consumes. -/
theorem exists_positive_omegaPoint_of_highCodimension_siphonFace
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hzcard : ∀ z ∈ omegaLimit atTop ϕ {x₀},
      (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card)
    (hcodim : 2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax)))
    (hcard : 2 ≤ Pmax.card)
    (hrank : N.stoichRank ≠ 1) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  by_cases hvert : N.IsVertexZeroSet Pmax
  · exact (N.false_of_vertex_omegaPoint κ hxs hcb hϕγ hsol hx₀ hwmax (hωnn wmax hwmax)
      (hωaff wmax hwmax) hzeroMax hPmaxne hvert).elim
  · exact N.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex κ hxs hcb hϕγ
      hsol hK hmaps hωnn hgenω hωaff hx₀ hPmaxne hwmax hzeroMax hmaxExact hzcard hcodim hcard
      hrank hvert

/-! ## Why the packaged barrier criteria cannot be instantiated inside this theorem

`docs/gac-bridge-gap-analysis.lean` derives the conclusion of the theorem above from the blueprint
data consumed by `Network.exists_positive_omegaPoint_of_blueprintData`, so the residue there is
purely geometric: the tiles, their normals and their levels.  The two lemmas below record the
obstruction found while trying to close that instantiation from this theorem's hypotheses: the
blueprint data *cannot* exist under them.

Every packaged criterion — `exists_positive_omegaPoint_of_convex_tiles`,
`exists_positive_omegaPoint_of_selfConsistent_normals`,
`exists_positive_omegaPoint_of_blueprintData` — demands a separation clause `hsep` bounding each
coordinate below by some `ε > 0` on **every** positive compatible point of the closed sublevel
`{barrier ≤ R}`.  Two facts collide there:

* `hstart` puts the start point `x₀` into the sublevel, and the trapping theorem
  `Network.barrier_le_of_toric_descent_in_band` (fed by the `hnear` clause assembled from `hm`,
  `hassign` and `hregime`) bounds the barrier by `R` along the whole orbit, so
  `barrier_le_of_mem_omegaLimit` puts the boundary ω-point `wmax` into the sublevel as well;
* every piece `innerSL ℝ (-m i)` of the barrier is affine, hence the sublevel is convex, so the
  segment from `x₀` to `wmax` stays inside it — and `hsep_fails_of_boundaryPoint_mem_sublevel`
  refutes `hsep` on that segment: its points are positive and compatible, but at any `s ∈ Pmax`
  the segment takes the value `(x₀ s) / n`, which tends to zero.

So instantiating any of these criteria from this theorem's hypotheses would derive `False` — it
would prove that `omegaLimit` meets **no** boundary face at all (full permanence), a strictly
stronger statement than the conclusion demanded here, which only asks for a positive ω-point *in
addition to* the boundary ones.  (`hMclass`, which
`exists_positive_omegaPoint_of_blueprintData` needs separately, is itself unavailable for
non-conservative networks, whose positive compatibility classes are unbounded.)

What is still missing is a criterion that exhibits an interior ω-point without uniform coordinate
floors: an Anderson-style comparable-growth descent (`Network.ComparableGrowthDescent`, whose
finite induction `omegaLimit_positive_of_descend` is already proved) or a direct
polyhedral-surface argument.  The two lemmas below are the machine-checked core of this analysis;
the wiring to each criterion's hypotheses is the paragraph above.

Depends additionally on: `CRNT.Dynamics.ToricBarrierTrapping`.
-/

/-- **The separation clause `hsep` of the packaged barrier criteria is refutable as soon as a
boundary point of the ω-limit set sits in the closed sublevel together with the start point.**

Each piece of `PolyhedralBarrier.barrier` is affine, so the sublevel `{barrier ≤ R}` is convex;
the segment from `x₀` to `wmax` therefore stays inside it.  Its points
`z = x₀ / n + (1 - 1/n) · wmax` are positive (`x₀` positive, `wmax` nonnegative) and compatible
with `x₀` (the displacement is a scalar multiple of `wmax - x₀`), but at a zero coordinate
`wmax s = 0` of `wmax` the segment value is `x₀ s / n → 0`, which no `ε > 0` can bound below. -/
theorem hsep_fails_of_boundaryPoint_mem_sublevel {ι' : Type*} [Fintype ι'] [Nonempty ι']
    (N : Network S) (m : ι' → N.euclideanStoichSubspace) (b : ι' → ℝ) (R : ℝ)
    {x₀ wmax : Concentration S} {s : S}
    (hx₀ : x₀.Positive) (hwnn : Concentration.Nonnegative wmax)
    (hcompat : N.StoichCompatible x₀ wmax) (hsw : wmax s = 0)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x₀) ≤ R)
    (hwmax : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState wmax) ≤ R) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive → N.StoichCompatible x₀ x →
        PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
          (N.euclideanStoichState x) ≤ R → ε ≤ x s := by
  rintro ⟨ε, hε, hsep⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (x₀ s / ε)
  have hnpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (0 : ℕ) < n + 2)
  have hnle : x₀ s / ε < ((n + 2 : ℕ) : ℝ) :=
    lt_of_lt_of_le hn (by exact_mod_cast Nat.le_add_right n 2)
  have hxE : x₀ s < ε * ((n + 2 : ℕ) : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hnle
    rwa [mul_comm] at h
  have hqpos : (0 : ℝ) < 1 / ((n + 2 : ℕ) : ℝ) := one_div_pos.mpr hnpos
  have hq1 : 1 / ((n + 2 : ℕ) : ℝ) < 1 :=
    (div_lt_one hnpos).mpr (by exact_mod_cast (by omega : (1 : ℕ) < n + 2))
  -- the segment from `x₀` to `wmax` at parameter `1 - 1/(n+2)`
  set z : Concentration S :=
    fun u => 1 / ((n + 2 : ℕ) : ℝ) * x₀ u + (1 - 1 / ((n + 2 : ℕ) : ℝ)) * wmax u with hz
  have hzdef : z =
      (1 / ((n + 2 : ℕ) : ℝ)) • x₀ + (1 - 1 / ((n + 2 : ℕ) : ℝ)) • wmax := by
    funext u
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hzpos : z.Positive := fun u =>
    add_pos_of_pos_of_nonneg (mul_pos hqpos (hx₀ u))
      (mul_nonneg (sub_nonneg.mpr hq1.le) (hwnn u))
  have hzcompat : N.StoichCompatible x₀ z := by
    have h2 : z - x₀ = (1 - 1 / ((n + 2 : ℕ) : ℝ)) • (wmax - x₀) := by
      rw [hzdef]
      funext u
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [StoichCompatible, h2]
    exact N.stoichSubspace.smul_mem _ hcompat
  have hstate : N.euclideanStoichState z =
      (1 / ((n + 2 : ℕ) : ℝ)) • N.euclideanStoichState x₀
        + (1 - 1 / ((n + 2 : ℕ) : ℝ)) • N.euclideanStoichState wmax := by
    rw [hzdef]
    simp only [← euclideanStoichStateL_apply, map_add, map_smul]
  have hzbar : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState z) ≤ R := by
    rw [hstate, PolyhedralBarrier.barrier_le_iff]
    intro i
    have hA : innerSL ℝ (-m i) (N.euclideanStoichState x₀) - b i ≤ R :=
      le_trans (PolyhedralBarrier.le_barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x₀) i) hstart
    have hB : innerSL ℝ (-m i) (N.euclideanStoichState wmax) - b i ≤ R :=
      le_trans (PolyhedralBarrier.le_barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState wmax) i) hwmax
    have hkey : innerSL ℝ (-m i)
        ((1 / ((n + 2 : ℕ) : ℝ)) • N.euclideanStoichState x₀
          + (1 - 1 / ((n + 2 : ℕ) : ℝ)) • N.euclideanStoichState wmax) - b i
        = (1 / ((n + 2 : ℕ) : ℝ)) *
            (innerSL ℝ (-m i) (N.euclideanStoichState x₀) - b i)
          + (1 - 1 / ((n + 2 : ℕ) : ℝ)) *
            (innerSL ℝ (-m i) (N.euclideanStoichState wmax) - b i) := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
    rw [hkey]
    have hc1 : (0 : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) := le_of_lt hqpos
    have hc2 : (0 : ℝ) ≤ 1 - 1 / ((n + 2 : ℕ) : ℝ) := sub_nonneg.mpr hq1.le
    have hsum : (1 / ((n + 2 : ℕ) : ℝ)) * R
        + (1 - 1 / ((n + 2 : ℕ) : ℝ)) * R = R := by ring
    exact le_trans
      (add_le_add (mul_le_mul_of_nonneg_left hA hc1) (mul_le_mul_of_nonneg_left hB hc2))
      (le_of_eq hsum)
  have hsepz : ε ≤ z s := hsep z hzpos hzcompat hzbar
  have hzval : z s = 1 / ((n + 2 : ℕ) : ℝ) * x₀ s
      + (1 - 1 / ((n + 2 : ℕ) : ℝ)) * wmax s := by rw [hz]
  rw [hzval, hsw, mul_zero, add_zero] at hsepz
  have hle : ε * ((n + 2 : ℕ) : ℝ) ≤ x₀ s := by
    have h1 : ε ≤ x₀ s / ((n + 2 : ℕ) : ℝ) := by
      rwa [div_eq_mul_inv, mul_comm, ← one_div]
    exact (le_div_iff₀ hnpos).mp h1
  exact (not_lt.mpr hle) hxE

/-- **Trapping along the orbit puts every ω-limit point into the closed sublevel.**  If the
barrier is at most `R` along the whole forward orbit, the sublevel `{barrier ≤ R}` is closed,
contains the forward orbit, and every ω-limit point lies in the closure of the forward orbit — so
`wmax ∈ omegaLimit` inherits `barrier … ≤ R`.  This is the step that makes the separation clause
`hsep` untenable whenever the ω-limit set meets the boundary (see
`hsep_fails_of_boundaryPoint_mem_sublevel`). -/
theorem barrier_le_of_mem_omegaLimit {ι' : Type*} [Fintype ι'] [Nonempty ι']
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ wmax : Concentration S} (N : Network S) (m : ι' → N.euclideanStoichSubspace)
    (b : ι' → ℝ) (R : ℝ)
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (htrap : ∀ t : ℝ, 0 ≤ t →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R)
    (hw : wmax ∈ omegaLimit atTop ϕ {x₀}) :
    PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState wmax) ≤ R := by
  have hc : Continuous fun x : Concentration S =>
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b (N.euclideanStoichState x) :=
    (PolyhedralBarrier.continuous_barrier _ _).comp N.euclideanStoichStateL.continuous
  have hclosed : IsClosed {x : Concentration S |
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R} :=
    isClosed_le hc continuous_const
  have hsub : Set.image2 ϕ Set.univ {x₀} ⊆ {x : Concentration S |
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R} := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    rw [hϕγ x t]
    rw [hx]
    exact htrap t t.coe_nonneg
  have hω : omegaLimit atTop ϕ {x₀} ⊆ {x : Concentration S |
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R} :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem).trans ((IsClosed.closure_subset_iff hclosed).mpr hsub)
  exact hω hw

/-! ## The packaging audit against Craciun v3 (arXiv:1501.02860v3)

The question raised while reading the paper — do Theorem B / Lemma 9.5 / Lemma 9.7 *assume*
uniform coordinate floors, or *prove* them? — has a definite answer, and it fixes two places where
the repo's packaging is stronger than the paper's text, plus one place where it is exactly right.

**1. `hsep` is a conclusion of the paper, never a hypothesis.**  Definition 4.6 defines a ZSH by
(i) `𝒵 ⊂ ℝⁿ₊ \ (η + ℝⁿ₊)` — the *surface* stays out of the deep interior box, i.e. it hugs the
boundary, the opposite direction from a floor — (ii) `𝒵` meets every toric ray exactly once, and
(iii) `𝒵` cannot be crossed inside some cube `(0,M)ⁿ`.  Lemma 9.5 assumes only "`𝒵` is a ZSH" and
concludes that the outer normal at `x` lies in every cone `𝒞` with `log x ∈ 𝒞`.  Lemma 9.7 assumes
only (i) for the unit cube (`𝒵 ⊂ (0,1)³ \ (ε̂ + [0,1]³)`) together with the normal-in-`K_𝒞`
condition, and concludes non-crossing inside the unit cube.  No coordinate floor appears in either
statement.  The floor on the *region* — "the upper region of `ℋ` is at positive distance from
`∂ℝⁿ`", part of the statement of Theorem B — is produced by the construction: §8 Step 2 chooses
`ε₀ < x₀ⁱ`, so `(ε₀,…,ε₀) + ℝⁿ₊` lies above `𝒵_{ε₀}`, and the compact invariant set is
`K_{x₀} = (above 𝒵_{ε₀}) ∩ [0,M]ⁿ ∩ {V ≤ L}` with `V` the Horn–Jackson Lyapunov function (§6.1 and
Fig. 3(e); Lemma 9.11 puts `{V ≤ L}` between two simplices, which is where the outer bound comes
from).

**2. The two lemmas above therefore say something stronger than "the criteria are mis-packaged":
every uniform-floor statement is refutable under this theorem's hypotheses, because `wmax` sits in
`ω`.**  For the repo's *convex* barrier sublevels this is
`hsep_fails_of_boundaryPoint_mem_sublevel` — the segment `x₀ / n + (1 - 1/n) · wmax` stays inside
and takes the value `x₀ s / n → 0` — together with `barrier_le_of_mem_omegaLimit`, which puts
`wmax` into any sublevel that traps the orbit.  For the paper's own region no convexity is needed
and none should be assumed (the paper never claims `K_{x₀}` is convex; see 4): compactness plus
`K_{x₀} ⊂ ℝⁿ_{>0}` already forces `wmax ∈ K_{x₀}` to be positive, contradicting
`hPmaxne`/`hzeroMax`.  So no weaker geometric statement and no repackaging of a *uniform-floor*
criterion can be instantiated here — each of them proves full permanence, which `wmax` refutes —
and once the §4 existence claim (item 5) is available this theorem closes by `False`.

**3. `hMclass` is the repo's hypothesis, not the paper's.**  Craciun never assumes bounded
compatibility classes.  His standing hypotheses are weak reversibility (Theorem 4.3 embeds a
variable-`k` weakly reversible system into a toric differential inclusion), and the boundedness he
uses is that of the *trajectory*: §8's remark proves that "any bounded trajectory of a variable-`k`
weakly reversible system is persistent", and the outer bound `M` comes from the cube `[0,M]ⁿ`
containing the chosen level surface `ℒ` (§6.1) together with `V ≤ L` — it bounds the invariant
region, not the class.  The class-wide bound fails in the paper's own setting:
`CRNT.Examples.OpenSystem.exists_complexBalanced_unbounded_class` constructs a weakly reversible
network of deficiency zero — hence complex balanced for *every* rate vector, so it carries exactly
this theorem's `hxs`/`hcb` — whose stoichiometric subspace is everything, so no `M` bounds its
positive compatibility classes.  `hMclass` is therefore not derivable here; it is available only on
conservative networks (the all-ones law bounds the class), which is what the `ToricBarrierExplicit`
docstrings scope it to.

**4. The convex obstruction checks out.**  `ConvexBarrierObstruction.not_exists_weights_vector`
proves that no globally homogeneous max-of-affine barrier can carry a normal lying inside every
cone of a generic three-dimensional arrangement fan.  The paper never asks for one: its
non-crossing requirement is confined to a bounded window — the unit cube of Lemma 9.7, the blue box
`[0,M_{n+1}]×…×[0,M₂]` of §8 Step 1 in compactified log coordinates — and inside a bounded window
the constant offsets `b_i` *can* repair the violations, which is precisely the step ("the deficit
scales linearly in `X` along `𝒞`") that fails on an unbounded cone.  The §7.4.3 `ε(α)` scale
hierarchy then handles the remaining self-consistency fixed point.  The repo's reading of the
obstruction, recorded in that module's header, matches the paper.

**5. The missing object already has a name in this tree.**  v3 §4 states the whole content in one
sentence: "for any positive initial condition `x₀ ∈ ℝⁿ_{>0}` of a toric dynamical system there
exists a compact forward invariant region `K_{x₀} ⊂ ℝⁿ_{>0}` such that `x₀ ∈ K_{x₀}`.  Of course,
this implies that toric dynamical systems are persistent."  Up to the packaging of forward
invariance, that is `N.PersistentFrom κ x₀` (`SingleLinkageGAC.lean:46`: a compact `K₀`, every
point of `K₀` strictly positive, every genuine solution through `x₀` staying in `K₀`), whose
orbit-level shadow is `Permanent ϕ x₀` (`EndotacticPermanence.lean:58`).  Both already yield this
theorem's conclusion: `omegaLimit_meets_positive_of_permanent` *is* the conclusion above, and
`persistentOrbit_of_persistentFrom` plus `PersistentOrbit.omegaLimit_positive` gives it for
`PersistentFrom`.  Two remarks, both checked against the text: (a) `K_{x₀}` compact and inside the
*open* orthant already forces `dist(K_{x₀}, ∂) > 0`, so no separate separation statement is
needed — in particular the segment argument of `hsep_fails_of_boundaryPoint_mem_sublevel` plays no
role here (it belongs to the repo's convex max-of-affine packaging, which the paper's tile-by-tile
surface is not — see 4); (b) feeding `PersistentFrom` to the chain above under this theorem's
hypotheses produces a *positive* `wmax` (`wmax ∈ ω ⊆ K₀`, `K₀` closed), contradicting
`hPmaxne`/`hzeroMax` — i.e. the residual is inconsistent with `PersistentFrom`, which is the
machine-checkable form of "closing this residual = supplying that compact positive absorbing set
for the bounded orbit at hand".  *Correction, verified against the v3 source by `GacLit` (shared
log, `[GacLit] 19:47`): the paper does **not** prove that such a `K_{x₀}` exists.*  The claim
appears only as statements — §4 (plan lines 598/637, whose "Step 4" is the assembly), 2D figure
captions, §5 LaSalle prose — while §8 carries out Steps 1–2 and then stops; there is no
"§8 Step 4".  Lemmas 9.5/9.7 are stated only for `ℝ³`/`(0,1)³` although §8 Step 2 invokes Lemma 9.7
in `n` dimensions, and Lemma 9.11's proof is a one-paragraph sketch.  The honest accounting of the
gap is therefore: **Theorem B (§§5–8) + the Step-4 assembly the paper asserts but does not write
down + LaSalle/persistence.**  v3 is a preprint (v1 2015, v2 2016, v3 2026-09-23, no journal-ref)
treated as open in current literature — Wiuf, arXiv:2609.24553v1, lists the GAC as proved only in
special cases and does not cite 1501.02860; no erratum or refutation was found — so speak of the
*claimed* proof.

-/

/-- **The paper's §4 region cannot exist under this theorem's hypotheses.**
`N.PersistentFrom κ x₀` (`SingleLinkageGAC.lean:46`) is verbatim Craciun v3 §4 — "a compact
forward invariant region `K_{x₀} ⊂ ℝⁿ_{>0}` such that `x₀ ∈ K_{x₀}`" — and it already implies
this file's conclusion (`omegaLimit_meets_positive_of_permanent`, or
`persistentOrbit_of_persistentFrom` together with `PersistentOrbit.omegaLimit_positive`).  The
lemma below records the other side of the collision: if the ω-limit set contains a point that is
not strictly positive — this theorem has `wmax`, with `wmax s = 0` for the nonempty set `Pmax` —
then `PersistentFrom κ x₀` is refutable, because the certificate's compact set would have to
contain that point while being entirely inside the open orthant.

Consequently the residual above is discharged by *any* construction of `PersistentFrom κ x₀` for
this orbit — which is what v3 *claims* to obtain from boundedness alone (the residual has
boundedness: `hK`/`hmaps`; the claim is the "Step 4" of §4's plan, asserted but not carried out —
see the audit above) — and, read the other way, the residual hypotheses are inconsistent with that
claim, i.e. with the *claimed* Theorem B/C. -/
theorem not_persistentFrom_of_mem_omegaLimit_notPositive (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S} (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀}) (hwn : ¬ w.Positive) :
    ¬ N.PersistentFrom κ x₀ := by
  rintro ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  -- the genuine curve `γ x₀` starts at `x₀` and stays in the certificate's set
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ 0
    simpa using h.symm
  have hsub : ∀ t : ℝ, 0 ≤ t → γ x₀ t ∈ K₀ := fun t ht => hgen (γ x₀) hγ0 hsol t ht
  -- hence the whole forward orbit does, and so does its ω-limit set
  have himg : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K₀ := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    rw [hϕγ x t]
    rw [hx]
    exact hsub t t.coe_nonneg
  have hω : omegaLimit atTop ϕ {x₀} ⊆ K₀ :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem).trans ((IsClosed.closure_subset_iff hK₀cpt.isClosed).mpr himg)
  exact hwn (hK₀pos w (hω hw))

/-! ## The static slice of Anderson's descent that IS available here

Route (A)/(B) of the residual: apply `omegaLimit_positive_of_descend` from
`CRNT.Dynamics.SiphonDimensionDescent`, whose strong induction on the siphon cardinality is already
proved.  Its sole input is `N.ComparableGrowthDescent ϕ x₀`, and all the structural data it needs
*along the way* is derivable from this theorem's own hypotheses — no call-site fields are missing:
`criticalBoundaryOmegaFace_lowerRank` (from `weaklyReversible_of_positive_complexBalanced` and
`exists_relEntropy_const_on_omegaLimit`) supplies `IsCriticalSiphon Pmax`, the complex-balance of
the avoiding-face restriction at `fillSiphonFace Pmax xstar wmax`, the strict stoichiometric rank
drop, and `massActionVectorField κ wmax = 0`, and `⟨wmax, hwmax, hzeroMax⟩` is the carriedness
witness.

Two facts then resist, and the lemma below discharges the part of them that is static:

* `hmaxExact` can only ever *exclude* candidates for the descent's right disjunct, never produce
  one: a carried `Q` with `Q.card < Pmax.card` cannot contain `Pmax`, so its witness `z` does not
  satisfy the premise `∀ s ∈ Pmax, z s = 0` that `hmaxExact z` needs.  Eliminating all candidates
  would make `descend Pmax` equivalent to the very goal of this theorem — circular.
* what the right disjunct needs is a carried critical siphon of **strictly smaller** cardinality.
  `exists_smaller_carried_siphon_of_zeroSet_inside` constructs one whenever some ω-point is
  positive on `Pmaxᶜ`, vanishes at some species of `Pmax`, and is positive at some species of
  `Pmax` — in the absence of a positive ω-point.  The uncovered branch — every ω-point that is
  positive on `Pmax` also vanishes *outside* `Pmax`, where no static cardinality bound is
  available — is exactly
  Anderson's comparable-growth estimate: comparing relative-entropy growth across an escape from
  the face, which is the analytic content `ComparableGrowthDescent` isolates and the tree does not
  formalise.  (The degenerate ω-limit set `ω = {wmax}` shows why no purely static argument can
  finish: there the right disjunct at `Pmax` is false outright, so any static proof of
  `descend Pmax` would prove this theorem's goal — i.e. would already be the missing result.) -/

/-- **A strictly smaller carried critical siphon, from an ω-point whose zero set sits strictly
inside `Pmax`.**

Under this theorem's orbit hypotheses, if the ω-limit set contains no positive point, and some
`z ∈ ω` is positive on every species outside `Pmax`, vanishes at some species of `Pmax`, and is
positive at some species of `Pmax`, then the zero set `Q` of `z` is nonempty (positivity fails
somewhere, and off `Pmax` nothing vanishes, so the failure is on `Pmax`), strictly smaller than
`Pmax` (it omits the species where `z` is positive), carried by `z`, and critical — so it is
exactly a right-disjunct witness for `descend Pmax` of `Network.ComparableGrowthDescent`. -/
theorem exists_smaller_carried_siphon_of_zeroSet_inside
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S}
    (hnoG : ¬ ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive)
    {z : Concentration S} (hz : z ∈ omegaLimit atTop ϕ {x₀})
    (hzoff : ∀ s, s ∉ Pmax → 0 < z s)
    (hzon : ∃ s₀ ∈ Pmax, 0 < z s₀) :
    ∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < Pmax.card ∧
      N.SiphonCarried ϕ x₀ Q := by
  classical
  set Q : Finset S := Finset.univ.filter (fun s => z s = 0) with hQ
  have hQz : ∀ s, s ∈ Q ↔ z s = 0 := fun s => by simp [hQ]
  -- `z` is not positive: the ω-limit set has no positive point
  have hznpos : ¬ z.Positive := fun h => hnoG ⟨z, hz, h⟩
  obtain ⟨s, hs⟩ : ∃ s, ¬ 0 < z s := not_forall.mp hznpos
  have hz0 : z s = 0 := le_antisymm (not_lt.mp hs) (hωnn z hz s)
  have hQne : Q.Nonempty := ⟨s, (hQz s).mpr hz0⟩
  have hsub : Q ⊆ Pmax := by
    intro t ht
    by_contra htn
    have h1 : z t = 0 := (hQz t).mp ht
    have h2 : 0 < z t := hzoff t htn
    linarith
  have hne : Q ≠ Pmax := by
    intro hQeq
    obtain ⟨s₀, hs₀P, hs₀z⟩ := hzon
    rw [← hQeq] at hs₀P
    have h1 : z s₀ = 0 := (hQz s₀).mp hs₀P
    linarith
  have hcard : Q.card < Pmax.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hcarr : N.SiphonCarried ϕ x₀ Q := ⟨z, hz, hQz⟩
  have hcrit : N.IsCriticalSiphon Q :=
    N.isCriticalSiphon_of_siphonCarried κ hϕγ hK hmaps hωnn hgenω hωaff hx₀ hQne hcarr
  exact ⟨Q, hQne, hcrit, hcard, hcarr⟩

/-! ## The exact residue: the vanishing-off-`Pmax` pin, the conservation mechanism, and the
exhaustive trichotomy

`hzcard` (newly exported from `exists_maximal_zeroSet_omegaPoint` and threaded through the call
site) bounds every ω-point's zero set by `Pmax.card`.  With it, four lemmas pin down *exactly*
what remains of Anderson's descent at `Pmax`:

* `exists_positive_on_pmax_of_zero_outside`: an ω-point that vanishes **outside** `Pmax` must be
  positive somewhere **on** `Pmax` — otherwise `hmaxExact` would force its zero set to equal
  `Pmax`, contradicting the outside zero.  So the “vanishes off `Pmax`” configuration cannot hide
  from `hmaxExact`; it simply cannot be *killed* by it.
* `eq_zero_on_pmax_of_conservation_eq`: the compatibility-class mechanism.  If the invariant `c`
  does not see the off-`Pmax` part of `z - wmax` (`hout`), then a `P`-invariant that is
  nonnegative and strictly positive on `Pmax` forces `z = 0` on `Pmax`, and `hmaxExact` then
  collapses `z` to `Pmax` exactly — contradicting any outside zero.  What resists: `hout` is
  *agreement off `Pmax`* (or `c` supported inside `Pmax`), and neither is available for an
  arbitrary ω-point — ω-points of one class vary freely off the face — while an invariant that
  is nonnegative everywhere and positive on **all** of `Pmax` would be a witness to
  `¬ N.IsCriticalSiphon Pmax`, which the derived `IsCriticalSiphon Pmax` forbids.  The mechanism
  is exact but not instantiable here.
* `smaller_carried_siphon_iff_zeroSet_card_lt`: absent a positive ω-point, the descent's right
  disjunct is *equivalent* to “some ω-point has a strictly smaller zero set”.
* `omegaPoint_zeroSet_trichotomy`: every ω-point either is strictly positive (the goal of this
  theorem), or its zero set is exactly `Pmax`, or it witnesses a strictly smaller carried siphon
  (the right disjunct), or it is an exact tie — positive somewhere on `Pmax`, vanishing
  somewhere off it, with `card = Pmax.card`.  Exhaustive.  **Two** disjuncts stay open, not one:
  “every ω-point has zero set exactly `Pmax`” (the degenerate model `ω = {wmax}` lives there) and
  the exact ties (where the conservation mechanism above is blocked as recorded).  Both are
  dynamical: no static lemma can close either, since the model satisfies every static hypothesis
  and every derived fact. -/

/-- **An ω-point vanishing outside `Pmax` is positive somewhere on `Pmax`.**  Feeding `hmaxExact`
its premise would force the zero set to equal `Pmax` exactly, which the outside zero contradicts;
so the premise must fail. -/
theorem exists_positive_on_pmax_of_zero_outside
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {Pmax : Finset S}
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    {z : Concentration S} (hz : z ∈ omegaLimit atTop ϕ {x₀})
    (ht : ∃ t, t ∉ Pmax ∧ z t = 0) :
    ∃ s ∈ Pmax, 0 < z s := by
  by_contra h
  push Not at h
  have hzeroP : ∀ u ∈ Pmax, z u = 0 :=
    fun u hu => le_antisymm (h u hu) (hωnn z hz u)
  obtain ⟨t, htn, ht0⟩ := ht
  exact htn ((hmaxExact z hz hzeroP t).1 ht0)

/-- **The compatibility-class pin (Lead 1).**  Stoichiometric compatibility gives
`weightedTotal c z = weightedTotal c wmax` for every `P`-invariant `c`; if `c` sees no off-`Pmax`
part of the difference (`hout` — subsuming both “`z` and `wmax` agree off `Pmax`” and “`c` is
supported inside `Pmax`”), the whole invariant total sits on `Pmax`, and a nonnegative `c`
positive there forces `z = 0` on `Pmax`.  Then `hmaxExact` collapses `z` to `Pmax` exactly. -/
theorem eq_zero_on_pmax_of_conservation_eq
    (N : Network S) {z wmax : Concentration S} {Pmax : Finset S}
    (hznn : Concentration.Nonnegative z) (hcompat : N.StoichCompatible wmax z)
    (hzero : ∀ s ∈ Pmax, wmax s = 0)
    (c : S → ℝ) (hc : N.IsPInvariant c)
    (hout : ∀ t, t ∉ Pmax → c t * (z t - wmax t) = 0)
    (hcnn : ∀ s ∈ Pmax, 0 ≤ c s) (hcpos : ∀ s ∈ Pmax, 0 < c s) :
    ∀ s ∈ Pmax, z s = 0 := by
  intro s hsp
  have hwt : weightedTotal c z = weightedTotal c wmax :=
    (N.weightedTotal_eq_of_stoichCompatible hc hcompat).symm
  have hsum : ∑ u : S, c u * (z u - wmax u) = 0 := by
    have hz : ∑ u : S, c u * z u - ∑ u : S, c u * wmax u = 0 := by
      simpa [weightedTotal] using sub_eq_zero.mpr hwt
    rwa [show ∑ u : S, c u * (z u - wmax u) =
        ∑ u : S, c u * z u - ∑ u : S, c u * wmax u
      by simp [mul_sub, Finset.sum_sub_distrib]]
  have hsplit : (∑ u ∈ Pmax, c u * (z u - wmax u))
      + (∑ u ∈ Pmaxᶜ, c u * (z u - wmax u)) = 0 :=
    (Finset.sum_add_sum_compl Pmax _).trans hsum
  have houts : ∑ u ∈ Pmaxᶜ, c u * (z u - wmax u) = 0 :=
    Finset.sum_eq_zero (fun u hu => hout u (Finset.mem_compl.mp hu))
  have hp : ∑ u ∈ Pmax, c u * (z u - wmax u) = 0 := by linarith [hsplit, houts]
  have hpz : ∑ u ∈ Pmax, c u * z u = 0 := by
    rw [← hp]
    exact Finset.sum_congr rfl (fun u hu => by rw [hzero u hu, sub_zero])
  have hnn : ∀ u ∈ Pmax, 0 ≤ c u * z u := fun u hu => mul_nonneg (hcnn u hu) (hznn u)
  by_contra hzn
  have hpos : 0 < z s := lt_of_le_of_ne (hznn s) (Ne.symm hzn)
  have hterm : 0 < c s * z s := mul_pos (hcpos s hsp) hpos
  have hrest : 0 ≤ ∑ u ∈ Pmax.erase s, c u * z u :=
    Finset.sum_nonneg (fun u hu => hnn u (Finset.mem_of_mem_erase hu))
  have hadd := Finset.sum_erase_add Pmax (fun u => c u * z u) hsp
  linarith

/-- **Exact reduction of the descent's right disjunct (absent a positive ω-point).**  The
right-disjunct witness of `ComparableGrowthDescent.descend` at `Pmax` exists if and only if some
ω-point has a strictly smaller zero set than `Pmax`; criticality and carriedness are then
manufactured by `isCriticalSiphon_of_siphonCarried` and the carrier is the point itself. -/
theorem smaller_carried_siphon_iff_zeroSet_card_lt
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S}
    (hnoG : ¬ ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) :
    ((∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < Pmax.card ∧
        N.SiphonCarried ϕ x₀ Q) ↔
      ∃ z ∈ omegaLimit atTop ϕ {x₀},
        (Finset.univ.filter (fun s => z s = 0)).card < Pmax.card) := by
  constructor
  · rintro ⟨Q, _, _, hlt, z, hz, hzQ⟩
    refine ⟨z, hz, ?_⟩
    have hQeq : Finset.univ.filter (fun s => z s = 0) = Q := by
      apply Finset.ext
      intro u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hzQ u).symm
    rw [hQeq]
    exact hlt
  · rintro ⟨z, hz, hlt⟩
    have hznpos : ¬ z.Positive := fun h => hnoG ⟨z, hz, h⟩
    obtain ⟨s, hs⟩ : ∃ s, ¬ 0 < z s := not_forall.mp hznpos
    have hz0 : z s = 0 := le_antisymm (not_lt.mp hs) (hωnn z hz s)
    have hQne : (Finset.univ.filter (fun s => z s = 0)).Nonempty :=
      ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, hz0⟩⟩
    have hcarr : N.SiphonCarried ϕ x₀ (Finset.univ.filter (fun s => z s = 0)) :=
      ⟨z, hz, fun u => by simp⟩
    refine ⟨Finset.univ.filter (fun s => z s = 0), hQne, ?_, hlt, hcarr⟩
    exact N.isCriticalSiphon_of_siphonCarried κ hϕγ hK hmaps hωnn hgenω hωaff hx₀ hQne hcarr

/-- **The exhaustive trichotomy for the residue of the descent.**  Under this theorem's orbit
hypotheses, `hmaxExact` and `hzcard` split *every* ω-point into exactly one of four shapes:

1. strictly positive — the goal of this theorem;
2. zero set exactly `Pmax`;
3. witness of a strictly smaller carried critical siphon (the right disjunct of `descend Pmax`);
4. an exact tie: positive somewhere on `Pmax`, vanishing somewhere off `Pmax`, with
   `(Finset.univ.filter (· = 0)).card = Pmax.card`.

Disjuncts 2 and 4 are the open residue (assuming 1 and 3 fail globally): 2 contains the
degenerate model `ω = {wmax}`, and 4 is where the conservation pin of
`eq_zero_on_pmax_of_conservation_eq` is blocked.  Both are dynamical, not static. -/
theorem omegaPoint_zeroSet_trichotomy
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S}
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hzcard : ∀ z ∈ omegaLimit atTop ϕ {x₀},
      (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card) :
    (∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive) ∨
    (∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < Pmax.card ∧
      N.SiphonCarried ϕ x₀ Q) ∨
    (∀ z ∈ omegaLimit atTop ϕ {x₀},
      (Finset.univ.filter (fun s => z s = 0)) = Pmax ∨
        ((∃ s ∈ Pmax, 0 < z s) ∧ (∃ t, t ∉ Pmax ∧ z t = 0) ∧
          (Finset.univ.filter (fun s => z s = 0)).card = Pmax.card)) := by
  classical
  by_cases hG : ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive
  · exact Or.inl hG
  by_cases hm : ∃ Q : Finset S, Q.Nonempty ∧ N.IsCriticalSiphon Q ∧ Q.card < Pmax.card ∧
      N.SiphonCarried ϕ x₀ Q
  · exact Or.inr (Or.inl hm)
  refine Or.inr (Or.inr ?_)
  intro z hz
  have hnoG : ¬ ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := hG
  have hznpos : ¬ z.Positive := fun h => hG ⟨z, hz, h⟩
  obtain ⟨s, hs⟩ : ∃ s, ¬ 0 < z s := not_forall.mp hznpos
  have hz0 : z s = 0 := le_antisymm (not_lt.mp hs) (hωnn z hz s)
  by_cases hsub : ∀ u ∈ Pmax, z u = 0
  · -- zero set contains `Pmax`: `hmaxExact` pins it to `Pmax` exactly
    left
    apply Finset.ext
    intro u
    constructor
    · intro hu
      exact (hmaxExact z hz hsub u).1 ((Finset.mem_filter.mp hu).2)
    · intro hu
      exact Finset.mem_filter.2 ⟨Finset.mem_univ u, (hmaxExact z hz hsub u).2 hu⟩
  · right
    push Not at hsub
    obtain ⟨s₀, hs₀P, hs₀pos⟩ := hsub
    have hs₀z : 0 < z s₀ := lt_of_le_of_ne (hωnn z hz s₀) (Ne.symm hs₀pos)
    by_cases hoff : ∀ t, t ∉ Pmax → 0 < z t
    · -- positive off `Pmax`, zero and positive on `Pmax`: the smaller siphon exists
      exact absurd
        (N.exists_smaller_carried_siphon_of_zeroSet_inside κ hϕγ hK hmaps hωnn hgenω hωaff
          hx₀ hnoG hz hoff ⟨s₀, hs₀P, hs₀z⟩) hm
    · push Not at hoff
      obtain ⟨t₀, ht₀n, ht₀z⟩ := hoff
      have ht₀0 : z t₀ = 0 := le_antisymm ht₀z (hωnn z hz t₀)
      rcases lt_or_ge (Finset.univ.filter (fun s => z s = 0)).card Pmax.card with hlt | hge
      · -- strictly smaller zero set: the right-disjunct witness exists
        exact absurd
          ((smaller_carried_siphon_iff_zeroSet_card_lt N κ hϕγ hK hmaps hωnn hgenω hωaff hx₀
            hnoG).mpr ⟨z, hz, hlt⟩) hm
      · -- exact tie
        exact ⟨⟨s₀, hs₀P, hs₀z⟩, ⟨t₀, ht₀n, ht₀0⟩,
          le_antisymm (hzcard z hz) hge⟩

/-! ## One consequence of the standing hypotheses that the trichotomy alone does not record

`massActionVectorField_eq_zero_on_omegaLimit_of_hypotheses`: **every ω-point is an equilibrium**
of the mass-action field.  LaSalle for the relative entropy (available from
`hxs`/`hcb`/`hϕγ`/`hsol`/`hK`/`hmaps`) feeds
`GACOmegaPositive.massActionVectorField_eq_zero_on_omegaLimit`, which covers boundary ω-points as
well (their zero sets are siphons, so the face argument applies).

Note that the *third* disjunct of `omegaPoint_zeroSet_trichotomy` (a strictly smaller carried
critical siphon) is **not** refutable from `hzcard`: `hzcard` only says no ω-point's zero set is
*larger* than `Pmax.card`, which is perfectly consistent with one being strictly smaller. -/

/-- **Every ω-point is a stationary point of the mass-action vector field.**  Under exactly the
orbit hypotheses of this module, together with a positive complex-balanced reference and the
genuine solution property of the start orbit, relative entropy is constant on the ω-limit set and
the boundary-face analysis of `CRNT.Dynamics.GACOmegaPositive` turns that constancy into
`N.massActionVectorField κ z = 0` for *every* `z ∈ omegaLimit atTop ϕ {x₀}` — boundary points
included. -/
theorem massActionVectorField_eq_zero_on_omegaLimit_of_hypotheses
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hx₀ : x₀.Positive) :
    ∀ z ∈ omegaLimit atTop ϕ {x₀}, N.massActionVectorField κ z = 0 := by
  have hwr : N.WeaklyReversible := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  have hγ0 : ∀ x, γ x 0 = x := fun x => by simpa using (hϕγ x 0).symm
  -- LaSalle for the relative entropy, re-derived here: the packaged
  -- `GlobalAttractorTheorem.exists_relEntropy_const_on_omegaLimit` lives in a module that
  -- imports this one, so it cannot be used below its own call site.
  have hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos κ (by rw [hγ0]; exact hx₀) hsol
  have hd := fun (t : ℝ) (ht : 0 ≤ t) =>
    relEntropy_hasDerivAt hxs (hpos t ht) (fun s => (hasDerivAt_pi.mp (hsol t ht)) s)
  have hAnti : AntitoneOn (fun t => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt) ?_ ?_
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      exact (hd t ht.le).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(hd t ht.le).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxs hcb
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hK.isClosed).mpr hsubK⟩
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xstar (ϕ b x₀) ≤ relEntropy xstar (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg)
      (by exact_mod_cast hab)
  obtain ⟨c, -, -, hωc⟩ := Flow.laSalle ϕ (relEntropy_continuous hxs) x₀ hK habs hmono
  exact N.massActionVectorField_eq_zero_on_omegaLimit hwr κ hxs hcb hγ0 hϕγ hK hmaps hgenω
    hωnn hωc

/-! ## The open residue is pinned: off-`Pmax` coordinates never approach zero

Both disjuncts left open by `omegaPoint_zeroSet_trichotomy` share one feature — some ω-point
vanishes on all of `Pmax` (`hface` below), which every tie witness also satisfies after
specialising `hmaxExact`.  The lemma then says that the failure of positivity is *confined* to
`Pmax`: every coordinate outside `Pmax` keeps a uniform positive floor for all forward time, so
the trajectory converges to the **relative interior** of the `Pmax` face and all of its limit
points are positive exactly on `Pmaxᶜ`.

This does not close the theorem — it sharpens what has to be closed.  Excluding this
configuration is the dynamical content of Craciun's Theorem B (v3 §7–§8): the degenerate model
`ω = {wmax}` satisfies every static hypothesis of this module and satisfies the conclusion of the
lemma below, so no static refinement can finish. -/

omit [DecidableEq S] [Fintype S] in
/-- **Off-`Pmax` coordinates are uniformly bounded below along the entire orbit.**  If every
ω-point vanishes on `Pmax`, `hmaxExact` holds, and `t₀ ∉ Pmax`, then there is `ε > 0` with
`ε ≤ γ x₀ t t₀` for every `t ≥ 0`.

Minimize the continuous coordinate `t₀` over the compact ω-limit set; the minimum `m` is strictly
positive, since `m = 0` would put a ω-point with `z t₀ = 0` in front of `hmaxExact`, contradicting
`t₀ ∉ Pmax`.  The open half-space `{y | m/2 < y t₀}` therefore contains ω, so
`eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset` pushes the whole
forward orbit into it after some time `T`; on the compact initial segment `[0,T]` continuity and
orbit positivity supply a second floor, and the minimum of the two floors is the witness. -/
theorem uniformLowerBound_offFace_of_zeroSet_eq
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hΓcont : ContinuousOn (γ x₀) (Set.Ici 0))
    (hΓpos : ∀ t : ℝ, 0 ≤ t → (γ x₀ t).Positive)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    {Pmax : Finset S}
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hface : ∀ z ∈ omegaLimit atTop ϕ {x₀}, ∀ s ∈ Pmax, z s = 0)
    {t₀ : S} (ht₀ : t₀ ∉ Pmax) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → ε ≤ γ x₀ t t₀ := by
  classical
  -- the orbit is absorbed by the compact `K`, so the ω-limit set is compact and nonempty
  have hKcl : IsClosed K := hK.isClosed
  have himg : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, hKcl.closure_subset_iff.mpr himg⟩
  have hωcpt : IsCompact (omegaLimit atTop ϕ {x₀}) :=
    isCompact_omegaLimit_of_absorbing ϕ x₀ hK habs
  have hωne : (omegaLimit atTop ϕ {x₀}).Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs
      (Set.singleton_nonempty x₀)
  -- the minimum of the coordinate `t₀` over ω
  obtain ⟨zstar, hzstar, hzmin⟩ :=
    hωcpt.exists_isMinOn hωne (continuous_apply t₀).continuousOn
  have hm0 : 0 < zstar t₀ := by
    by_contra h
    push Not at h
    have hz0 : zstar t₀ = 0 := le_antisymm h (hωnn zstar hzstar t₀)
    exact ht₀ ((hmaxExact zstar hzstar (fun s hs => hface zstar hzstar s hs) t₀).mp hz0)
  -- the open half-space strictly above the minimum contains the whole ω-limit set
  have hn1 : IsOpen {y : Concentration S | zstar t₀ / 2 < y t₀} :=
    isOpen_lt continuous_const (continuous_apply t₀)
  have hn2 : omegaLimit atTop ϕ {x₀} ⊆ {y : Concentration S | zstar t₀ / 2 < y t₀} := by
    intro z hz
    have hle : zstar t₀ ≤ z t₀ := isMinOn_iff.mp hzmin z hz
    exact lt_of_lt_of_le (half_lt_self hm0) hle
  -- hence the orbit eventually lies in that half-space
  obtain ⟨u, hu, hun⟩ :=
    eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset'
      atTop ϕ {x₀} hK habs hn1 hn2
  obtain ⟨T, hT⟩ := Filter.mem_atTop_sets.mp hu
  -- a second positive floor on the compact initial segment `[0, T]`
  have hIne : (Set.Icc (0 : ℝ) (T : ℝ)).Nonempty := ⟨0, le_rfl, T.coe_nonneg⟩
  have hγI : ContinuousOn (γ x₀) (Set.Icc (0 : ℝ) (T : ℝ)) :=
    hΓcont.mono Set.Icc_subset_Ici_self
  have hscont : ContinuousOn (fun u : ℝ => γ x₀ u t₀) (Set.Icc (0 : ℝ) (T : ℝ)) :=
    (continuous_apply t₀).comp_continuousOn hγI
  obtain ⟨pI, hpII, hpImin⟩ := isCompact_Icc.exists_isMinOn hIne hscont
  have hpIpos : 0 < γ x₀ pI t₀ := hΓpos pI hpII.1 t₀
  refine ⟨min (γ x₀ pI t₀) (zstar t₀ / 2), lt_min hpIpos (half_pos hm0), ?_⟩
  intro t ht
  by_cases hTt : t ≤ T
  · -- inside the initial segment: the continuity floor
    have htI : t ∈ Set.Icc (0 : ℝ) (T : ℝ) := ⟨ht, hTt⟩
    exact (min_le_left _ _).trans (isMinOn_iff.mp hpImin _ htI)
  · -- beyond `T`: the ω-half-space floor
    have hTle : (T : ℝ) ≤ t := le_of_lt (lt_of_not_ge hTt)
    have htu : (⟨t, ht⟩ : ℝ≥0) ∈ u := hT ⟨t, ht⟩ (by exact_mod_cast hTle)
    have hineq : zstar t₀ / 2 < ϕ (⟨t, ht⟩ : ℝ≥0) x₀ t₀ := by
      have h1 := hun (subset_closure (Set.mem_image2_of_mem htu (Set.mem_singleton x₀)))
      simpa using h1
    have heq : ϕ (⟨t, ht⟩ : ℝ≥0) x₀ = γ x₀ t := hϕγ x₀ ⟨t, ht⟩
    exact (min_le_right _ _).trans (le_of_lt (heq ▸ hineq))

/-! ## The chemical reading: what the relative entropy does at the boundary

The Horn–Jackson Lyapunov function in this repository is the finite sum
`relEntropy xstar x = ∑ i, (x i * log (x i / xstar i) - x i + xstar i)`
(`CRNT/Theorems/DeficiencyZero/Lyapunov.lean:58`), evaluated with Mathlib's convention
`Real.log 0 = 0`.  At a coordinate whose species has gone extinct the summand is
`0 * log 0 - 0 + xstar i = xstar i`: the entropy is **finite on the whole closed orthant** and
continuous there (`relEntropy_continuous`).  So the heuristic "relative entropy blows up at zero
concentration, contradicting its constancy on the ω-limit set" is unavailable here — it dies
precisely at the definition, where the boundary value is defined to be the finite number
`xstar s` per extinct coordinate rather than `+∞`.

What survives the failed blow-up is exact bookkeeping, and it is what the two lemmas below
record.  Every extinct species *raises* the entropy by exactly its reference value (the
`- x i + xstar i` part contributes `xstar s` at `x i = 0`), every surviving coordinate
contributes a nonnegative amount (Gibbs' inequality, `relEntropyTerm_nonneg`), hence:

* `relEntropy_ge_sum_zeroSet` — the total reference weight of any extinct set is capped by the
  entropy value at the point;
* `relEntropy_le_of_mem_omegaLimit` — Lyapunov descent plus continuity put the entire ω-limit
  set inside the sublevel `{relEntropy xstar · ≤ relEntropy xstar x₀}`;
* `sum_xstar_le_relEntropy_x₀_of_zero_omegaPoint` — transporting the cap through the ω-limit
  set: for the residual's `wmax` with zero set `Pmax`, the extinct set's reference weight is
  bounded by the *initial* entropy,

      ∑ s ∈ Pmax, xstar s ≤ relEntropy xstar x₀.

Combined with `exists_relEntropy_const_on_omegaLimit` (the LaSalle constant `c` is the value of
the entropy on every ω-point) this pins `c ≥ ∑ s ∈ Pmax, xstar s > 0`: a strictly positive floor
on the LaSalle constant of any trajectory whose ω-limit meets the boundary.  It is a genuine
constraint — but not a contradiction: `relEntropy xstar x₀` is an arbitrary nonnegative number
and can exceed any finite reference weight, so the cap alone cannot exclude `Pmax` and cannot
deliver the positive ω-point.  The missing dynamical content remains Craciun v3 Theorem B, as
documented at the head of this file.
-/

/-- **The reference weight of an extinct set is capped by the relative entropy.** For a
nonnegative concentration `x` and any set `Z` of coordinates vanishing at `x`, the sum of the
reference values `xstar s` over `s ∈ Z` is at most `relEntropy xstar x`.  Each summand of the
entropy over `Z` equals `xstar s` (by `Real.log 0 = 0`) and each summand outside `Z` is
nonnegative by `relEntropyTerm_nonneg`.  This is the finite substitute for entropy blow-up at
the boundary: the entropy does not diverge as a species goes extinct, it rises by exactly the
extinct species' reference value. -/
theorem relEntropy_ge_sum_zeroSet {xstar x : Concentration S} (hxs : xstar.Positive)
    (hx : x.Nonnegative) {Z : Finset S} (hZ : ∀ s ∈ Z, x s = 0) :
    ∑ s ∈ Z, xstar s ≤ relEntropy xstar x := by
  unfold relEntropy
  have hnn : ∀ i : S, 0 ≤ x i * Real.log (x i / xstar i) - x i + xstar i :=
    fun i => relEntropyTerm_nonneg (hx i) (hxs i)
  have hterm : ∀ i ∈ Z, x i * Real.log (x i / xstar i) - x i + xstar i = xstar i := by
    intro i hi
    rw [hZ i hi]
    simp
  have hzsum : (∑ i ∈ Z, (x i * Real.log (x i / xstar i) - x i + xstar i)) = ∑ i ∈ Z, xstar i :=
    Finset.sum_congr rfl hterm
  have hsplit :
      (∑ i ∈ Z, (x i * Real.log (x i / xstar i) - x i + xstar i))
          + (∑ i ∈ Zᶜ, (x i * Real.log (x i / xstar i) - x i + xstar i))
        = ∑ i : S, (x i * Real.log (x i / xstar i) - x i + xstar i) :=
    Finset.sum_add_sum_compl Z _
  have hcompl : 0 ≤ ∑ i ∈ Zᶜ, (x i * Real.log (x i / xstar i) - x i + xstar i) :=
    Finset.sum_nonneg fun i _ => hnn i
  linarith

/-- **Lyapunov descent puts the whole ω-limit set in the initial sublevel.** Every ω-point of
the bounded genuine orbit through the positive `x₀` satisfies
`relEntropy xstar z ≤ relEntropy xstar x₀`: the forward orbit lies in the closed sublevel by
`genuineOrbit_relEntropy_le` (Lyapunov descent along the positive genuine orbit), the sublevel
is closed by `relEntropy_continuous`, and ω-points are limits of forward-orbit points. -/
theorem relEntropy_le_of_mem_omegaLimit
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {z : Concentration S} (hz : z ∈ omegaLimit atTop ϕ {x₀}) :
    relEntropy xstar z ≤ relEntropy xstar x₀ := by
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ (0 : ℝ≥0)
    rw [NNReal.coe_zero] at h
    exact h.symm.trans (ϕ.map_zero_apply x₀)
  have hpos : ∀ t : ℝ, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos κ (by rw [hγ0]; exact hx₀) hsol
  have himg : Set.image2 ϕ Set.univ {x₀} ⊆
      {y : Concentration S | relEntropy xstar y ≤ relEntropy xstar x₀} := by
    rintro y ⟨t, _, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hϕγ]
    have hle := N.genuineOrbit_relEntropy_le κ hxs hcb hpos hsol t t.coe_nonneg
    rwa [hγ0] at hle
  have hclosed : IsClosed {y : Concentration S | relEntropy xstar y ≤ relEntropy xstar x₀} :=
    isClosed_le (relEntropy_continuous hxs) continuous_const
  exact ((omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem).trans ((IsClosed.closure_subset_iff hclosed).mpr himg)) hz

/-- **The extinct set's reference weight is bounded by the initial relative entropy.** If an
ω-point `wmax` of the bounded genuine orbit through `x₀` vanishes exactly on `Pmax`, then

    ∑ s ∈ Pmax, xstar s ≤ relEntropy xstar x₀.

This is the quantitative residue of the entropy-blow-up heuristic: since the entropy is finite
at the boundary and equals `xstar s` per extinct coordinate, extinction of `Pmax` costs at
least `∑ s ∈ Pmax, xstar s` of relative entropy, which the Lyapunov descent caps by the initial
value.  Instantiated together with `exists_relEntropy_const_on_omegaLimit` it gives the strict
floor `∑ s ∈ Pmax, xstar s ≤ c` on the LaSalle constant `c` of the residual's hypotheses. -/
theorem sum_xstar_le_relEntropy_x₀_of_zero_omegaPoint
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} {wmax : Concentration S}
    (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hwnn : Concentration.Nonnegative wmax)
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0) :
    ∑ s ∈ Pmax, xstar s ≤ relEntropy xstar x₀ := by
  have hzero : ∀ s ∈ Pmax, wmax s = 0 := fun s hs => (hzeroMax s).1 hs
  exact (relEntropy_ge_sum_zeroSet hxs hwnn hzero).trans
    (relEntropy_le_of_mem_omegaLimit N κ hxs hcb hϕγ hsol hx₀ hwmax)
/-! ## Three hypotheses of the residual are redundant

`CRNT.Examples.CodimTwoFaceModel` shows by an explicit model that every hypothesis of
`exists_positive_omegaPoint_of_highCodimension_siphonFace` except the orbit-ODE premise `hsol`
is satisfiable simultaneously with the conclusion false, so `hsol` is the only load-bearing
premise no static argument can avoid.  Within the remaining hypotheses, three are derivable
from the others and carry no independent content; they are recorded here so that no future
argument spends effort on them:

* `hmaxExact_of_zeroSet_card_le`: `hmaxExact` follows from `hzcard` alone (the maximality
  argument of `exists_maximal_zeroSet_omegaPoint` needs no more than the cardinality bound);
* `two_le_card_of_two_le_finrank_map_projOn`: `hcard` follows from `hcodim`, since the
  `Pmax`-projection lives in the space of functions supported on `Pmax`, of dimension
  `Pmax.card` (so `hPmaxne` follows from `hcard` in turn);
* `stoichRank_ne_one_of_two_le_finrank_map_projOn`: `hrank` follows from `hcodim`, since the
  rank of a projected subspace never exceeds the rank of `stoichSubspace` itself
  (`stoichRank = finrank stoichSubspace ≥ 2`). -/

omit [DecidableEq S] in
/-- **`hmaxExact` is derivable from `hzcard`.** If no ω-point has a zero set of larger
cardinality than `Pmax`, then any ω-point vanishing on all of `Pmax` has zero set exactly
`Pmax`: its zero set contains `Pmax` and is no larger, so the two finite sets coincide. -/
theorem hmaxExact_of_zeroSet_card_le {Ω : Set (Concentration S)} {Pmax : Finset S}
    (hzcard : ∀ z ∈ Ω, (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card)
    {z : Concentration S} (hz : z ∈ Ω) (hzero : ∀ s ∈ Pmax, z s = 0) :
    ∀ s, z s = 0 ↔ s ∈ Pmax := by
  have hmem : ∀ u : S, u ∈ (Finset.univ.filter (fun s => z s = 0)) ↔ z u = 0 := by
    intro u
    simp
  have hsub : Pmax ⊆ Finset.univ.filter (fun s => z s = 0) :=
    fun u hu => (hmem u).2 (hzero u hu)
  have hEq : Pmax = Finset.univ.filter (fun s => z s = 0) :=
    Finset.eq_of_subset_of_card_le hsub (hzcard z hz)
  intro s
  rw [hEq]
  exact (hmem s).symm

/-- **`hcard` is derivable from `hcodim`.** Every element of the projected subspace
`stoichSubspace.map (projOn W)` vanishes outside `W` (by definition of `projOn`), and a
nonempty projected subspace then forces `W` to carry that many species: dimension two needs
at least two species. -/
theorem two_le_card_of_two_le_finrank_map_projOn {W : Finset S} (U : Submodule ℝ (S → ℝ))
    (h : 2 ≤ Module.finrank ℝ (U.map (projOn W))) : 2 ≤ W.card := by
  by_contra hcard
  have hle : W.card ≤ 1 := by omega
  rcases Finset.eq_empty_or_nonempty W with hW | hne
  · -- the empty face projects everything to zero
    subst hW
    have hz : projOn (∅ : Finset S) = 0 := by
      apply LinearMap.ext
      intro p
      funext s
      simp [projOn_apply]
    have himg : U.map (projOn (∅ : Finset S)) = ⊥ := by
      apply le_antisymm
      · intro q hq
        obtain ⟨p, -, hp⟩ := Submodule.mem_map.mp hq
        rw [hz] at hp
        subst hp
        exact Submodule.zero_mem _
      · exact bot_le
    have h0 : Module.finrank ℝ (U.map (projOn (∅ : Finset S))) = 0 := by
      rw [himg]
      exact finrank_bot ℝ (S → ℝ)
    omega
  · -- a one-species face projects to dimension at most one
    obtain ⟨s, hs⟩ := hne
    have hsingle : W = {s} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hs, ?_⟩
      intro t ht
      exact Finset.card_le_one.mp hle t ht s hs
    rw [hsingle] at h
    have h1 := finrank_map_projOn_singleton_le_one U s
    omega

/-- **`hrank` is derivable from `hcodim`.** Rank--nullity for the `W`-projection restricted to
`stoichSubspace` gives `finrank (map …) + finrank (ker …) = finrank stoichSubspace
= stoichRank`, so a projected rank of at least two forces `stoichRank ≥ 2 ≠ 1`. -/
theorem stoichRank_ne_one_of_two_le_finrank_map_projOn (N : Network S) {W : Finset S}
    (h : 2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn W))) :
    N.stoichRank ≠ 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((projOn W).domRestrict N.stoichSubspace)
  rw [LinearMap.range_domRestrict] at hrn
  show Module.finrank ℝ N.stoichSubspace ≠ 1
  omega

/-! ## The exact applicability boundary of `uniformLowerBound_offFace_of_zeroSet_eq`

Its hypothesis `hface : ∀ z ∈ omegaLimit …, ∀ s ∈ Pmax, z s = 0` is *universal*: every
ω-point must vanish on the whole face.  The trichotomy
`omegaPoint_zeroSet_trichotomy` only yields, in its third disjunct, a **per-point** split
`∀ z, Z(z) = Pmax ∨ tie(z)`, where a tie witness is positive somewhere on `Pmax` and therefore
violates `hface`.  The lemma below pins the boundary exactly: given `hmaxExact`, `hface` is
equivalent to "every ω-point has zero set exactly `Pmax`" — so it is obtainable when the
branch-(2) shape holds for *all* ω-points (in particular in the degenerate model
`ω = {wmax}`), and it *fails* whenever a tie witness (or any mixed ω-set) exists.  The module
docstring above `uniformLowerBound_offFace_of_zeroSet_eq` says both open disjuncts "share" `hface`;
that is correct only for the existential reading ("some ω-point vanishes on `Pmax`", namely
`wmax` itself) — for the universal `hface` of the lemma the tie branch is not covered. -/

omit [DecidableEq S] in
/-- **`hface` holds exactly when every ω-point's zero set is `Pmax`.** The forward direction
feeds each ω-point's vanishing to `hmaxExact`; the backward direction is the definition of the
zero-set filter. -/
theorem hface_iff_zeroSet_eq {Ω : Set (Concentration S)} {Pmax : Finset S}
    (hmaxExact : ∀ z ∈ Ω, (∀ s ∈ Pmax, z s = 0) → ∀ s, z s = 0 ↔ s ∈ Pmax) :
    (∀ z ∈ Ω, ∀ s ∈ Pmax, z s = 0) ↔
      ∀ z ∈ Ω, (Finset.univ.filter (fun s => z s = 0)) = Pmax := by
  constructor
  · intro hface z hz
    apply Finset.ext
    intro s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmaxExact z hz (fun t ht => hface z hz t ht) s
  · intro h z hz s hs
    rw [← h z hz] at hs
    exact (Finset.mem_filter.mp hs).2
/-! ## The ω-limit set cannot be split by two closed sets: ties do not mix with face points

`omegaPoint_zeroSet_trichotomy`'s third disjunct is a *per-point* disjunction, so it permits a
mixed ω-limit set — some points exactly on the `Pmax`-face, some exact ties.  The two lemmas
below rule the mixture out.  `omegaLimit_eq_iInter_closure_tail` writes ω as the intersection of
the closures of the forward tails of the orbit; each such tail closure is compact (the orbit
lives in `K`) and contains ω.  `not_disjoint_closed_cover_omegaLimit` is then Cantor's
intersection theorem in disguise: two disjoint nonempty closed subsets of ω would give disjoint
open neighborhoods `U`, `V`, some tail closure would fall inside `U ∪ V`, and a continuous
segment of the orbit meeting both `U` and `V` would have to cross `U ∩ V = ∅`. -/

/-- The `atTop` ω-limit set of a single point is the intersection of the closures of the forward
tails of its orbit. -/
theorem omegaLimit_eq_iInter_closure_tail {α : Type*} [TopologicalSpace α]
    (ϕ : ℝ≥0 → α → α) (x₀ : α) :
    omegaLimit atTop ϕ {x₀} =
      ⋂ T : ℝ≥0, closure (Set.image2 ϕ {t | T ≤ t} {x₀}) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    rw [Set.mem_iInter]
    intro T
    exact omegaLimit_subset_closure_image2 atTop ϕ {x₀} (Ici_mem_atTop T) hy
  · intro y hy
    rw [omegaLimit_eq_iInter]
    refine Set.mem_iInter.mpr ?_
    intro u
    obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.mp u.2
    have hsub : {t | a ≤ t} ⊆ (u : Set ℝ≥0) := fun t ht => ha t ht
    have hmono : Set.image2 ϕ {t | a ≤ t} {x₀} ⊆ Set.image2 ϕ u {x₀} :=
      Set.image2_subset hsub (fun _ h => h)
    exact closure_mono hmono (Set.mem_iInter.mp hy a)

/-- **The ω-limit set of a precompact orbit with continuous time dependence cannot be covered by
two disjoint nonempty closed sets.**  Hypotheses: the orbit through `x₀` is a continuous map
`ℝ≥0 → α` whose range lies in the compact `K`, and `A`, `T` are closed subsets of ω, disjoint and
nonempty. -/
theorem not_disjoint_closed_cover_omegaLimit
    {α : Type*} [MetricSpace α]
    {ϕ : ℝ≥0 → α → α} {x₀ : α}
    (hcont : Continuous fun t : ℝ≥0 => ϕ t x₀)
    {K : Set α} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    {A T : Set α} (hA : IsClosed A) (hT : IsClosed T)
    (hsubA : A ⊆ omegaLimit atTop ϕ {x₀}) (hsubT : T ⊆ omegaLimit atTop ϕ {x₀})
    (hdisj : A ∩ T = ∅) (hcov : omegaLimit atTop ϕ {x₀} ⊆ A ∪ T)
    (hAne : A.Nonempty) (hTne : T.Nonempty) : False := by
  classical
  have hKcl : IsClosed K := hK.isClosed
  have habs : ∀ v : Set ℝ≥0, v ∈ (atTop : Filter ℝ≥0) →
      closure (Set.image2 ϕ v {x₀}) ⊆ K := by
    intro v hv
    refine hKcl.closure_subset_iff.mpr ?_
    rintro y ⟨t, ht, x, hx, hyy⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    subst y
    exact hmaps t
  -- the ω-limit set is compact (absorbed by `K`)
  have hωcpt : IsCompact (omegaLimit atTop ϕ {x₀}) :=
    hK.of_isClosed_subset (isClosed_omegaLimit atTop ϕ {x₀})
      ((omegaLimit_subset_closure_image2 atTop ϕ {x₀} (univ_mem :
          (Set.univ : Set ℝ≥0) ∈ (atTop : Filter ℝ≥0))).trans (habs Set.univ univ_mem))
  -- every forward-tail closure is compact, contains ω, and is characterized by ω
  have htailsub : ∀ T₀ : ℝ≥0, closure (Set.image2 ϕ {t | T₀ ≤ t} {x₀}) ⊆ K :=
    fun T₀ => habs {t | T₀ ≤ t} (Ici_mem_atTop T₀)
  have htail : ∀ T₀ : ℝ≥0, IsCompact (closure (Set.image2 ϕ {t | T₀ ≤ t} {x₀})) :=
    fun T₀ => (hK.of_isClosed_subset isClosed_closure (htailsub T₀))
  have hωsub : ∀ T₀ : ℝ≥0, omegaLimit atTop ϕ {x₀} ⊆
      closure (Set.image2 ϕ {t | T₀ ≤ t} {x₀}) :=
    fun T₀ => omegaLimit_subset_closure_image2 atTop ϕ {x₀} (Ici_mem_atTop T₀)
  have hEq : omegaLimit atTop ϕ {x₀} =
      ⋂ T₀ : ℝ≥0, closure (Set.image2 ϕ {t | T₀ ≤ t} {x₀}) :=
    omegaLimit_eq_iInter_closure_tail ϕ x₀
  -- `A` and `T` are compact: closed subsets of the compact ω
  have hAcmp : IsCompact A := hωcpt.of_isClosed_subset hA hsubA
  have hTcmp : IsCompact T := hωcpt.of_isClosed_subset hT hsubT
  -- a uniform positive gap between the two disjoint compacts
  obtain ⟨p, hpA, hpT, hmin⟩ :
      ∃ p : α × α, p.1 ∈ A ∧ p.2 ∈ T ∧
        IsMinOn (fun q : α × α => dist q.1 q.2) (A ×ˢ T) p := by
    obtain ⟨q, hq, hqmin⟩ := (IsCompact.prod hAcmp hTcmp).exists_isMinOn
      (Set.Nonempty.prod hAne hTne)
      continuous_dist.continuousOn
    exact ⟨q, hq.1, hq.2, hqmin⟩
  have hne : p.1 ≠ p.2 := fun he =>
    (Set.mem_empty_iff_false p.1).mp
      (hdisj ▸ (⟨hpA, by rw [he]; exact hpT⟩ : p.1 ∈ A ∩ T))
  set m : ℝ := dist p.1 p.2 with hmdef
  have hm0 : 0 < m := dist_pos.mpr hne
  have hmdist : ∀ a ∈ A, ∀ t ∈ T, m ≤ dist a t := by
    intro a ha t ht
    exact isMinOn_iff.mp hmin (a, t) ⟨ha, ht⟩
  have hthird : 0 < m / 3 := div_pos hm0 (by norm_num)
  -- disjoint open neighborhoods of `A` and `T`
  set U : Set α := ⋃ a ∈ A, Metric.ball a (m / 3) with hUdef
  set V : Set α := ⋃ t ∈ T, Metric.ball t (m / 3) with hVdef
  have hUopen : IsOpen U := isOpen_iUnion fun a => isOpen_iUnion fun _ => Metric.isOpen_ball
  have hVopen : IsOpen V := isOpen_iUnion fun t => isOpen_iUnion fun _ => Metric.isOpen_ball
  have hUV : U ∩ V = ∅ := by
    by_contra h
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
    have hxA : x ∈ U := hx.1
    have hxV : x ∈ V := hx.2
    obtain ⟨a, ha, hax⟩ : ∃ a ∈ A, dist x a < m / 3 := by
      simpa [hUdef, Metric.mem_ball] using hxA
    obtain ⟨t, ht, htx⟩ : ∃ t ∈ T, dist x t < m / 3 := by
      simpa [hVdef, Metric.mem_ball] using hxV
    have hlt : dist a t < m / 3 + m / 3 :=
      lt_of_le_of_lt (dist_triangle a x t) (by
        rw [dist_comm a x]
        exact add_lt_add hax htx)
    have hle : m ≤ dist a t := hmdist a ha t ht
    linarith
  -- ω is inside `U ∪ V`
  have hcovUV : omegaLimit atTop ϕ {x₀} ⊆ U ∪ V := by
    intro x hx
    rcases hcov hx with hxA | hxT
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨x, hxA, Metric.mem_ball_self hthird⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨x, hxT, Metric.mem_ball_self hthird⟩)
  -- hence some forward-tail closure is inside `U ∪ V`
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ≥0, closure (Set.image2 ϕ {t | T₀ ≤ t} {x₀}) ⊆ U ∪ V := by
    by_contra h
    rw [not_exists] at h
    set G : ℝ≥0 → Set α := (fun T₀ =>
      Set.diff (closure (Set.image2 ϕ {t | T₀ ≤ t} {x₀})) (U ∪ V)) with hGdef
    have hF : ∀ T₀ : ℝ≥0, (G T₀).Nonempty := by
      intro T₀
      obtain ⟨z, hz₁, hz₂⟩ := Set.not_subset.mp (h T₀)
      exact ⟨z, hz₁, hz₂⟩
    have hFin : ∀ u : Finset ℝ≥0,
        (K ∩ ⋂ T ∈ u, G T).Nonempty := by
      intro u
      set T₀ : ℝ≥0 := u.sup id with hT₀def
      have hT₀le : ∀ i ∈ u, i ≤ T₀ := fun i hi => Finset.le_sup (f := id) hi
      obtain ⟨z, hzC, hzUV⟩ := hF T₀
      refine ⟨z, htailsub T₀ hzC, ?_⟩
      simp only [Set.mem_iInter]
      intro i hi
      exact ⟨closure_mono (Set.image2_subset
        (fun t ht => le_trans (hT₀le i hi) ht) (fun _ h => h)) hzC, hzUV⟩
    have hbig : (K ∩ ⋂ T : ℝ≥0, G T).Nonempty :=
      hK.inter_iInter_nonempty G
        (fun T₀ => IsClosed.sdiff isClosed_closure (hUopen.union hVopen)) hFin
    obtain ⟨y, hyK, hy⟩ := hbig
    have hyall : ∀ T₀ : ℝ≥0, y ∈ G T₀ := Set.mem_iInter.mp hy
    have hyω : y ∈ omegaLimit atTop ϕ {x₀} := by
      rw [hEq, Set.mem_iInter]
      intro T₁
      exact (hyall T₁).1
    have hyUV : y ∈ U ∪ V := hcovUV hyω
    exact (hyall 0).2 hyUV
  -- the orbit visits `U` and then `V` at arbitrarily late times
  obtain ⟨a₀, ha₀⟩ := hAne
  obtain ⟨t₀, ht₀⟩ := hTne
  obtain ⟨t₁, hge₁, ht₁U⟩ : ∃ t₁ : ℝ≥0, T₀ ≤ t₁ ∧ ϕ t₁ x₀ ∈ U := by
    obtain ⟨y, hy, hdist⟩ :=
      Metric.mem_closure_iff.mp (hωsub T₀ (hsubA ha₀)) (m / 3) hthird
    obtain ⟨t₁, htail₁, x, hx, hyy⟩ := hy
    rw [Set.mem_singleton_iff] at hx
    subst x
    subst y
    rw [dist_comm] at hdist
    exact ⟨t₁, htail₁, Set.mem_iUnion₂.mpr ⟨a₀, ha₀, hdist⟩⟩
  obtain ⟨t₂, hge₂, ht₂V⟩ : ∃ t₂ : ℝ≥0, t₁ ≤ t₂ ∧ ϕ t₂ x₀ ∈ V := by
    obtain ⟨y, hy, hdist⟩ :=
      Metric.mem_closure_iff.mp (hωsub t₁ (hsubT ht₀)) (m / 3) hthird
    obtain ⟨t₂, htail₂, x, hx, hyy⟩ := hy
    rw [Set.mem_singleton_iff] at hx
    subst x
    subst y
    rw [dist_comm] at hdist
    exact ⟨t₂, htail₂, Set.mem_iUnion₂.mpr ⟨t₀, ht₀, hdist⟩⟩
  -- a continuous segment of the orbit crosses from `U` into `V`
  have hsub' : Set.Icc t₁ t₂ ⊆
      (fun t : ℝ≥0 => ϕ t x₀) ⁻¹' U ∪ (fun t : ℝ≥0 => ϕ t x₀) ⁻¹' V := by
    intro t ht
    have hgeT : (T₀ : ℝ≥0) ≤ t := le_trans hge₁ ht.1
    have hmem : ϕ t x₀ ∈ closure (Set.image2 ϕ {s | T₀ ≤ s} {x₀}) :=
      subset_closure (Set.mem_image2_of_mem hgeT (Set.mem_singleton x₀))
    rcases hT₀ hmem with hU | hV
    · exact Or.inl (Set.mem_preimage.mpr hU)
    · exact Or.inr (Set.mem_preimage.mpr hV)
  have hn1 : (Set.Icc t₁ t₂ ∩ (fun t : ℝ≥0 => ϕ t x₀) ⁻¹' U).Nonempty := by
    refine ⟨t₁, ?_⟩
    exact ⟨⟨le_rfl, hge₂⟩, Set.mem_preimage.mpr ht₁U⟩
  have hn2 : (Set.Icc t₁ t₂ ∩ (fun t : ℝ≥0 => ϕ t x₀) ⁻¹' V).Nonempty := by
    refine ⟨t₂, ?_⟩
    exact ⟨⟨hge₂, le_rfl⟩, Set.mem_preimage.mpr ht₂V⟩
  have hconn : IsConnected (Set.Icc t₁ t₂) := isConnected_Icc hge₂
  obtain ⟨t, -, htuv⟩ := hconn.isPreconnected _ _
    (hcont.isOpen_preimage _ hUopen) (hcont.isOpen_preimage _ hVopen) hsub' hn1 hn2
  have hUv : ϕ t x₀ ∈ U ∩ V :=
    ⟨Set.mem_preimage.mp htuv.1, Set.mem_preimage.mp htuv.2⟩
  rw [hUV] at hUv
  exact hUv

/-! ## Branch (4) of the residue is dead: ties cannot coexist with face points

`omegaPoint_zeroSet_trichotomy`'s third disjunct is a *per-point* disjunction, so it permits a
mixed ω-limit set — some points exactly on the `Pmax`-face, some exact ties.  The lemma below
rules the mixture out and therefore pins the residue: whenever the third disjunct holds, **every**
ω-point vanishes on `Pmax`, i.e. the `hface` hypothesis of
`uniformLowerBound_offFace_of_zeroSet_eq` is available. -/

/-- **Ties cannot mix with face points: the trichotomy's third disjunct forces `hface`.**

Under the standing orbit hypotheses, if every ω-point either vanishes on all of `Pmax` or
vanishes somewhere outside `Pmax` (the shape of the trichotomy's third disjunct), then in fact
*every* ω-point vanishes on `Pmax`.

Proof: the face points `A` and the tie witnesses `T` are closed subsets of ω (ω itself is closed),
disjoint by `hmaxExact`, cover ω by the hypothesis, and `A` is nonempty because `wmax` lies in it.
`not_disjoint_closed_cover_omegaLimit` (Cantor's intersection theorem applied to the closures of
the forward tails of the orbit) says such a partition cannot exist unless `T` is empty. -/
theorem hface_of_trichotomyThird
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    {Pmax : Finset S} {wmax : Concentration S}
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    (hthird : ∀ z ∈ omegaLimit atTop ϕ {x₀},
      (∀ s ∈ Pmax, z s = 0) ∨ (∃ t, t ∉ Pmax ∧ z t = 0)) :
    ∀ z ∈ omegaLimit atTop ϕ {x₀}, ∀ s ∈ Pmax, z s = 0 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨z, hz, s, hsp, hzs⟩ := h
  -- the tie witnesses form a nonempty set
  have hTne : ∃ w, w ∈ omegaLimit atTop ϕ {x₀} ∧ ∃ t ∈ (Pmaxᶜ : Finset S), w t = 0 := by
    rcases hthird z hz with hall | htie
    · exact absurd (hall s hsp) hzs
    · obtain ⟨t, htn, hz0⟩ := htie
      exact ⟨z, hz, t, Finset.mem_compl.mpr htn, hz0⟩
  -- closedness of the two defining sets, by induction on the relevant Finset
  have hAfC : IsClosed {q : Concentration S | ∀ s ∈ Pmax, q s = 0} := by
    refine Pmax.induction_on ?_ ?_
    · have h0 : {q : Concentration S | ∀ s ∈ (∅ : Finset S), q s = 0} = Set.univ := by
        ext q; simp
      rw [h0]; exact isClosed_univ
    · intro a F ha ih
      have h1 : {q : Concentration S | ∀ s ∈ insert a F, q s = 0} =
          {q | q a = 0} ∩ {q | ∀ s ∈ F, q s = 0} := by
        ext q; simp [Finset.mem_insert]
      rw [h1]
      exact IsClosed.inter (isClosed_eq (continuous_apply a) continuous_const) ih
  have hTfC : IsClosed {q : Concentration S | ∃ t ∈ (Pmaxᶜ : Finset S), q t = 0} := by
    refine (Pmaxᶜ).induction_on ?_ ?_
    · have h0 : {q : Concentration S | ∃ t ∈ (∅ : Finset S), q t = 0} = ∅ := by
        ext q; simp
      rw [h0]; exact isClosed_empty
    · intro a F ha ih
      have h1 : {q : Concentration S | ∃ t ∈ insert a F, q t = 0} =
          {q | q a = 0} ∪ {q | ∃ t ∈ F, q t = 0} := by
        ext q; simp [Finset.mem_insert]
      rw [h1]
      exact IsClosed.union (isClosed_eq (continuous_apply a) continuous_const) ih
  -- the face points and the tie witnesses
  set A : Set (Concentration S) :=
    omegaLimit atTop ϕ {x₀} ∩ {q | ∀ s ∈ Pmax, q s = 0} with hAdef
  set T : Set (Concentration S) :=
    omegaLimit atTop ϕ {x₀} ∩ {q | ∃ t ∈ (Pmaxᶜ : Finset S), q t = 0} with hTdef
  have hAc : IsClosed A := by
    rw [hAdef]; exact IsClosed.inter (isClosed_omegaLimit atTop ϕ {x₀}) hAfC
  have hTc : IsClosed T := by
    rw [hTdef]; exact IsClosed.inter (isClosed_omegaLimit atTop ϕ {x₀}) hTfC
  have hAs : A ⊆ omegaLimit atTop ϕ {x₀} := by
    rw [hAdef]; exact Set.inter_subset_left
  have hTs : T ⊆ omegaLimit atTop ϕ {x₀} := by
    rw [hTdef]; exact Set.inter_subset_left
  have hdisj : A ∩ T = ∅ := by
    by_contra hne
    obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hne
    rw [hAdef] at hq
    rw [hTdef] at hq
    obtain ⟨hqω, hall⟩ := hq.1
    obtain ⟨_, ⟨t, htn, hq0⟩⟩ := hq.2
    exact (Finset.mem_compl.mp htn) ((hmaxExact q hqω hall t).1 hq0)
  have hcov : omegaLimit atTop ϕ {x₀} ⊆ A ∪ T := by
    intro q hq
    rcases hthird q hq with hall | htie
    · refine Or.inl ?_
      rw [hAdef]; exact ⟨hq, hall⟩
    · obtain ⟨t, htn, hq0⟩ := htie
      refine Or.inr ?_
      rw [hTdef]; exact ⟨hq, t, Finset.mem_compl.mpr htn, hq0⟩
  have hAne : A.Nonempty := by
    refine ⟨wmax, ?_⟩
    rw [hAdef]
    exact ⟨hwmax, fun u hu => (hzeroMax u).1 hu⟩
  have hTne' : T.Nonempty := by
    obtain ⟨w, hw, t, htm, hw0⟩ := hTne
    refine ⟨w, ?_⟩
    rw [hTdef]
    exact ⟨hw, t, htm, hw0⟩
  -- the orbit is a continuous map on time
  have hcont : Continuous fun t : ℝ≥0 => ϕ t x₀ := by
    have heq : (fun t : ℝ≥0 => ϕ t x₀) = fun t : ℝ≥0 => γ x₀ t := by
      funext t; exact hϕγ x₀ t
    rw [heq]
    exact continuous_iff_continuousAt.mpr fun t =>
      (hsol t t.coe_nonneg).continuousAt.comp NNReal.continuous_coe.continuousAt
  exact not_disjoint_closed_cover_omegaLimit hcont hK hmaps hAc hTc hAs hTs hdisj hcov
    hAne hTne'

/-! ## Branch (2): the Step-4 `K_{x₀}` assembly — exact statement, provenance, and the bridge v3
never writes

This is the compact forward-invariant `K_{x₀} ⊂ ℝⁿ_{>0}` route (v3 §4 line 598, the claim the
paper asserts but never proves).  The transcription below was checked against both arXiv sources
by `GacLit` (verbatim quotes recorded in the collaboration log, 2026-09-28).  Three layers:

**Layer A — what this file's proof actually consumes** (pure repo, no paper):

```
∃ K : Set (Concentration S), IsCompact K ∧ (∀ y ∈ K, Concentration.Positive y) ∧
  x₀ ∈ K ∧ ∀ t : ℝ≥0, ϕ t x₀ ∈ K
```

Its orbit-level form is `Permanent ϕ x₀`; both certificate forms are already in-tree —
`PersistentFrom κ x₀` (`SingleLinkageGAC.lean`, *verbatim* line 598: "compact forward invariant
region `K_{x₀} ⊂ ℝⁿ_{>0}` such that `x₀ ∈ K_{x₀}`") and `SeparatingConfinement κ x₀`
(`GACSeparatingCapstone.lean`, the floor form) — and both directions are pinned: the certificate
implies this theorem's conclusion (`omegaLimit_meets_positive_of_permanent`), and a non-positive
ω-point refutes it (`not_persistentFrom_of_mem_omegaLimit_notPositive` above).

**Layer B — the paper-asserted claim.**  v3 §4 line 598, verbatim: "for any positive initial
condition `x₀ ∈ ℝⁿ_{>0}` of a toric dynamical system there exists a compact forward invariant
region `K_{x₀} ⊂ ℝⁿ_{>0}` such that `x₀ ∈ K_{x₀}`".  Asserted outright; region-level invariance
(all solutions starting in `K`) at lines 598/637, cube-conditional only at intro line 309; no
proof anywhere in v3 — §8 stops after Steps 1–2 and there is no "§8 Step 4".

**Layer C — the construction shape.**  v3 tex line 586 (commented-out draft, verbatim):
`ℝⁿ₊ⁿ \ 𝒵` is the union of two disjoint connected open sets `Zlow`, `Zupper` with `Zlow ⊂ V₀` (`V₀` a
neighborhood of the origin, defined inline in the same sentence and nowhere else), `Zupper` invariant,
and the closure of `Zupper` does not contain the origin — the *origin-avoidance* era: it does **not**
give `K ⊂ ℝⁿ₊ⁿ` (a point like `(1,0)` misses the origin yet has a zero coordinate).  The full
boundary floor exists only (i) in v2 §6 verbatim — the final region "does not contain any points
at distance less than `ε_{n-1} > 0` from the boundary of `ℝ₊ⁿ`" — and (ii) as bare assertions in
v3: line 598 (`K ⊂ ℝⁿ₊ⁿ`) and intro line 309 ("at positive distance from `∂ℝⁿ₊ⁿ`").  The familiar
formula `K = (upper region) ∩ [0,M]ⁿ ∩ {V ≤ L}` is an **[INFERENCE]-reconstruction**: lines
600/637/946 (Horn–Jackson level sets determine `K`) + 309 (the cube) assert its factors
separately; no source writes the formula.  The published three-species `K` of CNP §7 is an
analogous but different box-and-cuts shape.

**The remaining burden** is therefore exactly one interface, which the three lemmas below consume
and assemble (and the C ⟹ B ⟹ A chain they form is machine-checked: `persistentFrom_of_upperRegion`,
`orbit_stays_in_upperRegion`, `exists_positive_omegaPoint_of_upperRegion`): a surface split of the open orthant whose upper side `Zupper` (i) contains `x₀`,
(ii) has a uniform coordinate floor `ε`, and (iii) is never left by the orbit (the orbit never
meets `𝒵 = {x | x.Positive} \ (Zlow ∪ Zupper)` — non-crossing of Def. 4.6(iii)).  Note what is *not*
consumed: the connectedness of `Zlow`/`Zupper` from line 586, and `V₀` — the connectivity that the
assembly needs is that of the orbit's time-image, supplied by `orbit_stays_in_upperRegion`.
That lemma is v3 §9.1's announced-but-never-stated "non-crossing ⟹ forward invariance" bridge in
the two-region form; the repo already holds the barrier form of the same bridge
(`forwardInvariant_barrier_toricInclusion`, `barrier_le_of_toric_descent_in_band`).  The second
lemma assembles Layer A with
`K := closure Zupper ∩ {y | y.Nonnegative ∧ relEntropy xstar y ≤ relEntropy xstar x₀}`: closed floors
survive into `closure Zupper`, boundedness and closedness come from `isCompact_relEntropy_sublevel`
(the Horn–Jackson level through `x₀`, the [INFERENCE] Layer-C factor), invariance from the bridge
plus Lyapunov descent, and positivity from the floor.  No `hMclass`, no convex barrier, no `hsep`,
so the packaged criteria's refutable clauses (`hsep_fails_of_boundaryPoint_mem_sublevel`) do not
touch this shape.

**But the floor clause `hfloor` is refutable here anyway, and non-convexity does not save it.**  An
earlier version of this paragraph claimed that "a non-convex upper region is exactly what escapes the
segment argument".  That is **false**, and
`CRNT.UpperRegionAdjudication.upperRegion_criterion_inconsistent_with_boundaryOmegaPoint` proves it:
take these lemmas' hypotheses together with `hwmax : wmax ∈ omegaLimit`, `hPmaxne`, and
`hzeroMax`, and you get `False`.  The floor is consumed at `hfloorC` by `closure_minimal`, i.e. as a
fact about `closure Zupper`, and ω-limit points lie in `closure (image2 ϕ v {x₀})` — which `hstay`
puts inside `Zupper`.  So the floor reaches the ω-set through the closure whether or not `Zupper` is
convex.  The mechanism is the same as `Permanent`: `K` is universally positive and `ω ⊆ K`.

Consequence: **this pair of lemmas is not a route to hole A.**  The criterion is a correct conditional
— a genuine trajectory whose ω-limit set never meets the boundary does satisfy it — but its surface
data cannot be built *in the case hole A is about*, because a boundary ω-point is in the region.
For the same reason `CRNT.Network.ComparableGrowthDescent`, named below as the live alternative, is
equivalent to the goal rather than weaker than it
(`CRNT.UpperRegionAdjudication.comparableGrowthDescent_is_not_a_weaker_route`).
-/

/-- **The missing §9.1 bridge: non-crossing ⟹ the orbit stays in the upper region.**

A continuous orbit defined on the nonnegative times whose values always lie in the union of two
disjoint open sets, and which starts in `Zupper`, stays in `Zupper` for all forward time.  The orbit's
time-image is connected (`IsConnected.image` of `Ici 0`), a connected subset of a disjoint open
cover lies entirely in one side (`IsPreconnected.subset_or_subset`), and the start point picks
the side.  In the paper's language: a solution that never meets the zero-separating surface `𝒵`
cannot pass from the upper region `Zupper` to `Zlow` — v3 §9.1 announces this transfer for forward
invariant regions and never states it; v3 tex line 586's `Zupper`-invariance is the same claim as
commented-out text. -/
theorem orbit_stays_in_upperRegion {γ : ℝ → Concentration S}
    (hcont : ContinuousOn γ (Set.Ici 0))
    {Zlow Zupper : Set (Concentration S)}
    (hopenLow : IsOpen Zlow) (hopenUp : IsOpen Zupper)
    (hdisj : Disjoint Zlow Zupper)
    (hmem : ∀ t, 0 ≤ t → γ t ∈ Zlow ∪ Zupper)
    (hx₀ : γ 0 ∈ Zupper) :
    ∀ t, 0 ≤ t → γ t ∈ Zupper := by
  intro t ht
  have hconn : IsConnected (γ '' Set.Ici 0) :=
    isConnected_Ici.image γ hcont
  have hsub : γ '' Set.Ici 0 ⊆ Zlow ∪ Zupper := by
    rintro y ⟨u, hu, rfl⟩
    exact hmem u (Set.mem_Ici.mp hu)
  rcases hconn.isPreconnected.subset_or_subset hopenLow hopenUp hdisj hsub with hz0 | hz1
  · exfalso
    exact Set.disjoint_left.mp hdisj (hz0 ⟨0, Set.mem_Ici.mpr (le_refl 0), rfl⟩) hx₀
  · exact hz1 ⟨t, ht, rfl⟩

/-- **Layer C ⟹ Layer B: the surface interface yields the paper's §4 certificate.**

Under the same surface hypotheses as the criterion below, but with non-crossing required of
*every* genuine curve through `x₀` (region-level, the strength v3 line 598 claims), the paper's
own object — `N.PersistentFrom κ x₀`, *verbatim* "compact forward invariant region
`K_{x₀} ⊂ ℝⁿ_{>0}` such that `x₀ ∈ K_{x₀}`" — is constructed outright, with
`K = closure Zupper ∩ {y | y.Nonnegative ∧ relEntropy xstar y ≤ relEntropy xstar x₀}`.  This
machine-checks the C ⟹ B link of the three-layer transcription; the B ⟹ A direction is
`persistentOrbit_of_persistentFrom` + `PersistentOrbit.omegaLimit_positive` (in-tree), and
`persistentFrom_of_upperRegion` composed with them is `exists_positive_omegaPoint_of_upperRegion`
specialised to region-level non-crossing. -/
theorem persistentFrom_of_upperRegion (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {Zlow Zupper : Set (Concentration S)} {ε : ℝ} (hε : 0 < ε)
    (hopenLow : IsOpen Zlow) (hopenUp : IsOpen Zupper) (hdisj : Disjoint Zlow Zupper)
    (hsplit : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) →
      ∀ t, 0 ≤ t → Γ t ∈ Zlow ∪ Zupper)
    (hx₀Z : x₀ ∈ Zupper)
    (hfloor : ∀ y ∈ Zupper, ∀ s, ε ≤ y s) :
    N.PersistentFrom κ x₀ := by
  have hFloorClosed : IsClosed {y : Concentration S | ∀ s, ε ≤ y s} := by
    have hrw : {y : Concentration S | ∀ s, ε ≤ y s} = ⋂ s, {y | ε ≤ y s} := by
      ext y; simp [Set.mem_iInter]
    rw [hrw]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have hfloorC : closure Zupper ⊆ {y | ∀ s, ε ≤ y s} :=
    closure_minimal (fun y hy s => hfloor y hy s) hFloorClosed
  set K : Set (Concentration S) :=
    closure Zupper ∩ {y | y.Nonnegative ∧ relEntropy xstar y ≤ relEntropy xstar x₀} with hKdef
  have hKcpt : IsCompact K := by
    rw [hKdef]
    exact (isCompact_relEntropy_sublevel hxs (relEntropy xstar x₀)).inter_left isClosed_closure
  have hKpos : ∀ y ∈ K, Concentration.Positive y := by
    intro y hy s
    exact lt_of_lt_of_le hε (hfloorC hy.1 s)
  refine ⟨K, hKcpt, hKpos, ?_⟩
  intro Γ hΓ0 hΓd t ht
  -- the genuine curve is positive and its relative entropy never rises
  have hΓpos : ∀ u, 0 ≤ u → (Γ u).Positive :=
    N.genuineOrbit_pos (Γ := Γ) κ (by rw [hΓ0]; exact hx₀) hΓd
  have hle : ∀ u, 0 ≤ u → relEntropy xstar (Γ u) ≤ relEntropy xstar x₀ :=
    fun u hu =>
      (N.genuineOrbit_relEntropy_le (Γ := Γ) κ hxs hcb hΓpos hΓd u hu).trans_eq
        (congrArg (relEntropy xstar) hΓ0)
  -- non-crossing ⟹ the curve stays on the upper side (the §9.1 bridge)
  have hstay : ∀ u, 0 ≤ u → Γ u ∈ Zupper :=
    orbit_stays_in_upperRegion
      (fun u hu => ((hΓd u hu).continuousAt).continuousWithinAt)
      hopenLow hopenUp hdisj (hsplit Γ hΓ0 hΓd) (by rw [hΓ0]; exact hx₀Z)
  exact ⟨subset_closure (hstay t ht), (hΓpos t ht).nonnegative, hle t ht⟩

/-- **The Step-4 assembly, as a criterion: a floored, never-crossed upper region closes the goal.**

This is the Lean statement of what `K_{x₀}` must satisfy, with the surface burden isolated in the
hypotheses (the three-layer transcription and its provenance are in the module doc above):

* `hopenLow hopenUp hdisj hsplit` — the two-region split: `Zlow ∪ Zupper` is the complement of the
  surface `𝒵` inside the open orthant (tex 586), and the orbit never meets `𝒵`;
* `hx₀Z` — `x₀` sits on the upper side (Thm B footnote: "`x₀` is in the upper region");
* `hfloor` — the upper region is at distance `ε > 0` from `∂ℝⁿ₊ⁿ` (line 309; v2 §6's final floor);
* `hε hxs hcb hx₀ hϕγ hsol` — the complex-balanced genuine orbit.

The assembled `K` is `closure Zupper ∩ {y | y.Nonnegative ∧ relEntropy xstar y ≤ relEntropy xstar x₀}`:
compact (Horn–Jackson level through `x₀`), inside the open orthant (floor survives closure),
containing `x₀`, and absorbing the orbit (bridge + Lyapunov descent) — Layer A above, hence the
conclusion.  What remains unconstructed in the tree is exactly the surface data: the blueprint of
v3 §§5–8 whose non-crossing and floor properties the hypotheses record. -/
theorem exists_positive_omegaPoint_of_upperRegion (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {Zlow Zupper : Set (Concentration S)} {ε : ℝ} (hε : 0 < ε)
    (hopenLow : IsOpen Zlow) (hopenUp : IsOpen Zupper) (hdisj : Disjoint Zlow Zupper)
    (hsplit : ∀ t : ℝ, 0 ≤ t → γ x₀ t ∈ Zlow ∪ Zupper)
    (hx₀Z : x₀ ∈ Zupper)
    (hfloor : ∀ y ∈ Zupper, ∀ s, ε ≤ y s) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  -- the orbit starts at `x₀`
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ 0
    simpa using h.symm
  -- continuity of the orbit on the nonnegative times
  have hcont : ContinuousOn (γ x₀) (Set.Ici 0) :=
    fun t ht => ((hsol t ht).continuousAt).continuousWithinAt
  -- the orbit is positive (no boundary contact at any forward time)
  have hpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos (Γ := γ x₀) κ (by rw [hγ0]; exact hx₀) hsol
  -- Lyapunov descent: the relative entropy never rises above its value at the start
  have hle : ∀ t, 0 ≤ t → relEntropy xstar (γ x₀ t) ≤ relEntropy xstar x₀ :=
    fun t ht =>
      (N.genuineOrbit_relEntropy_le (Γ := γ x₀) κ hxs hcb hpos hsol t ht).trans_eq
        (congrArg (relEntropy xstar) hγ0)
  -- non-crossing ⟹ the orbit stays on the upper side (the §9.1 bridge)
  have hstay : ∀ t, 0 ≤ t → γ x₀ t ∈ Zupper :=
    orbit_stays_in_upperRegion hcont hopenLow hopenUp hdisj hsplit (by rw [hγ0]; exact hx₀Z)
  -- the floor survives passage to the closure of the upper region
  have hFloorClosed : IsClosed {y : Concentration S | ∀ s, ε ≤ y s} := by
    have hrw : {y : Concentration S | ∀ s, ε ≤ y s} = ⋂ s, {y | ε ≤ y s} := by
      ext y; simp [Set.mem_iInter]
    rw [hrw]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have hfloorC : closure Zupper ⊆ {y | ∀ s, ε ≤ y s} :=
    closure_minimal (fun y hy s => hfloor y hy s) hFloorClosed
  -- the assembled K: closed floors ∧ the Horn–Jackson level through x₀
  set K : Set (Concentration S) :=
    closure Zupper ∩ {y | y.Nonnegative ∧ relEntropy xstar y ≤ relEntropy xstar x₀} with hKdef
  have hKcpt : IsCompact K := by
    rw [hKdef]
    exact (isCompact_relEntropy_sublevel hxs (relEntropy xstar x₀)).inter_left isClosed_closure
  have hKpos : ∀ y ∈ K, Concentration.Positive y := by
    intro y hy s
    exact lt_of_lt_of_le hε (hfloorC hy.1 s)
  have hx₀K : x₀ ∈ K :=
    ⟨subset_closure hx₀Z, hx₀.nonnegative, le_refl _⟩
  have horbit : ∀ t : ℝ≥0, ϕ t x₀ ∈ K := by
    intro t
    rw [hϕγ x₀ t]
    have ht : 0 ≤ (t : ℝ) := t.coe_nonneg
    exact ⟨subset_closure (hstay (t : ℝ) ht), (hpos (t : ℝ) ht).nonnegative, hle (t : ℝ) ht⟩
  -- Layer A: the whole forward orbit lies in the compact positive set
  have himgs : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact horbit t
  have hperm : Permanent ϕ x₀ :=
    permanent_of_eventually_in_compact_interior ϕ x₀ hKcpt hKpos univ_mem
      ((IsClosed.closure_subset_iff hKcpt.isClosed).mpr himgs)
  exact omegaLimit_meets_positive_of_permanent ϕ x₀ hperm

/-! ## The topological route stops here: a species split always has a bridging ω-point

Branch (I) of the residue — some ω-point carries a strictly smaller critical siphon — was the
next candidate for the two-closed-sets technology that eliminated branch (4)
(`hface_of_trichotomyThird`): split the species set into two parts, partition ω by *which side
its points' zeros live on*, and contradict connectedness.  The two lemmas below record the exact
boundary of that attack: **it cannot fire.**  Whenever both sides of a species partition
`I ∪ J = univ` are visited by zeros of ω-points (and no positive ω-point exists, so every
ω-point has a zero), some ω-point vanishes on *both* sides at once — the candidate sets
`{q | ∃ s ∈ I, q s = 0}` and `{q | ∃ t ∈ J, q t = 0}` are then nonempty, closed, and *not*
disjoint, so `not_disjoint_closed_cover_omegaLimit` returns no contradiction.  The mixed
zero-set configuration of branch (I) is connected through a straddling point, not separable.

`exists_omegaPoint_vanishing_across_siphon` is the face-shaped specialization: a carried siphon
`P` whose complement still holds an ω-point zero is straddled by an ω-point vanishing both inside
`P` and outside it.  Under branch (I) with `P` the cardinality-minimal carried critical siphon
(`exists_cardMinimal_carried_siphon_lt` in `CRNT.Dynamics.SiphonDimensionDescent`), the complement
condition is met by `wmax` itself, since `P.card < Pmax.card` forces `Pmax ⊄ P`
[INFERENCE: the one-line Finset argument, not machine-checked here].

So the connectedness method that killed branch (4) does not extend to branch (I); excluding (I)
needs genuinely dynamical input — and the descent-iteration route has its own machine-checked
wall in `CRNT.Dynamics.SiphonDimensionDescent`
(`descendStep_iff_omegaPointPositive_of_cardMinimal`: at the bottom of the iteration the descent
step *is* this theorem's conclusion). -/

/-- **A species partition that is used on both sides is straddled by an ω-point.**  Under the
orbit hypotheses of `hface_of_trichotomyThird` and the absence of a positive ω-point, for any
`I ∪ J = univ` whose two sides are both hit by zeros of ω-points, some single ω-point vanishes
at a member of `I` *and* at a member of `J`. -/
theorem exists_omegaPoint_vanishing_on_both_sides
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hnoG : ¬ ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive)
    {I J : Finset S} (hIJ : I ∪ J = Finset.univ)
    (hI : ∃ z ∈ omegaLimit atTop ϕ {x₀}, ∃ s ∈ I, z s = 0)
    (hJ : ∃ z ∈ omegaLimit atTop ϕ {x₀}, ∃ t ∈ J, z t = 0) :
    ∃ z ∈ omegaLimit atTop ϕ {x₀}, ∃ s ∈ I, ∃ t ∈ J, z s = 0 ∧ z t = 0 := by
  classical
  by_contra hc
  -- no ω-point straddles the two sides
  have hnoCross : ∀ z ∈ omegaLimit atTop ϕ {x₀}, ∀ s ∈ I, ∀ t ∈ J,
      ¬ (z s = 0 ∧ z t = 0) := by
    intro z hz s hsI t htJ hzst
    exact hc ⟨z, hz, s, hsI, t, htJ, hzst⟩
  -- closedness of the two candidate sets, by induction on the relevant Finset
  have hIfC : IsClosed {q : Concentration S | ∃ s ∈ I, q s = 0} := by
    refine I.induction_on ?_ ?_
    · have h0 : {q : Concentration S | ∃ s ∈ (∅ : Finset S), q s = 0} = ∅ := by
        ext q; simp
      rw [h0]; exact isClosed_empty
    · intro a F ha ih
      have h1 : {q : Concentration S | ∃ s ∈ insert a F, q s = 0} =
          {q | q a = 0} ∪ {q | ∃ s ∈ F, q s = 0} := by
        ext q; simp [Finset.mem_insert]
      rw [h1]
      exact IsClosed.union (isClosed_eq (continuous_apply a) continuous_const) ih
  have hJfC : IsClosed {q : Concentration S | ∃ t ∈ J, q t = 0} := by
    refine J.induction_on ?_ ?_
    · have h0 : {q : Concentration S | ∃ t ∈ (∅ : Finset S), q t = 0} = ∅ := by
        ext q; simp
      rw [h0]; exact isClosed_empty
    · intro a F ha ih
      have h1 : {q : Concentration S | ∃ t ∈ insert a F, q t = 0} =
          {q | q a = 0} ∪ {q | ∃ t ∈ F, q t = 0} := by
        ext q; simp [Finset.mem_insert]
      rw [h1]
      exact IsClosed.union (isClosed_eq (continuous_apply a) continuous_const) ih
  -- the two candidate subsets of ω
  set A : Set (Concentration S) :=
    omegaLimit atTop ϕ {x₀} ∩ {q | ∃ s ∈ I, q s = 0} with hAdef
  set T : Set (Concentration S) :=
    omegaLimit atTop ϕ {x₀} ∩ {q | ∃ t ∈ J, q t = 0} with hTdef
  have hAc : IsClosed A := by
    rw [hAdef]; exact IsClosed.inter (isClosed_omegaLimit atTop ϕ {x₀}) hIfC
  have hTc : IsClosed T := by
    rw [hTdef]; exact IsClosed.inter (isClosed_omegaLimit atTop ϕ {x₀}) hJfC
  have hAs : A ⊆ omegaLimit atTop ϕ {x₀} := by
    rw [hAdef]; exact Set.inter_subset_left
  have hTs : T ⊆ omegaLimit atTop ϕ {x₀} := by
    rw [hTdef]; exact Set.inter_subset_left
  have hdisj : A ∩ T = ∅ := by
    by_contra hne
    obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hne
    rw [hAdef] at hq
    rw [hTdef] at hq
    obtain ⟨hqω, ⟨s, hsI, hqs⟩⟩ := hq.1
    obtain ⟨_, ⟨t, htJ, hqt⟩⟩ := hq.2
    exact hnoCross q hqω s hsI t htJ ⟨hqs, hqt⟩
  have hcov : omegaLimit atTop ϕ {x₀} ⊆ A ∪ T := by
    intro z hz
    have hznpos : ¬ z.Positive := fun h => hnoG ⟨z, hz, h⟩
    obtain ⟨s, hs⟩ : ∃ s, ¬ 0 < z s := not_forall.mp hznpos
    have hz0 : z s = 0 := le_antisymm (not_lt.mp hs) (hωnn z hz s)
    have hsu : s ∈ I ∪ J := by rw [hIJ]; exact Finset.mem_univ s
    rcases Finset.mem_union.mp hsu with hI' | hJ'
    · refine Or.inl ?_
      rw [hAdef]; exact ⟨hz, s, hI', hz0⟩
    · refine Or.inr ?_
      rw [hTdef]; exact ⟨hz, s, hJ', hz0⟩
  have hAne : A.Nonempty := by
    obtain ⟨z, hz, s, hsI, hz0⟩ := hI
    refine ⟨z, ?_⟩
    rw [hAdef]; exact ⟨hz, s, hsI, hz0⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz, t, htJ, hz0⟩ := hJ
    refine ⟨z, ?_⟩
    rw [hTdef]; exact ⟨hz, t, htJ, hz0⟩
  -- the orbit is a continuous map on time
  have hcont : Continuous fun t : ℝ≥0 => ϕ t x₀ := by
    have heq : (fun t : ℝ≥0 => ϕ t x₀) = fun t : ℝ≥0 => γ x₀ t := by
      funext t; exact hϕγ x₀ t
    rw [heq]
    exact continuous_iff_continuousAt.mpr fun t =>
      (hsol t t.coe_nonneg).continuousAt.comp NNReal.continuous_coe.continuousAt
  exact not_disjoint_closed_cover_omegaLimit hcont hK hmaps hAc hTc hAs hTs hdisj hcov
    hAne hTne

/-- **A carried siphon whose complement still holds an ω-point zero is straddled by an
ω-point.**  Specialization of `exists_omegaPoint_vanishing_on_both_sides` to the face split
`I = P`, `J = Pᶜ`: some ω-point vanishes at a species of the carried siphon `P` and at a species
outside it. -/
theorem exists_omegaPoint_vanishing_across_siphon
    (N : Network S) (κ : N.RateConstants)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hnoG : ¬ ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive)
    {P : Finset S} (hPne : P.Nonempty)
    (hcarr : N.SiphonCarried ϕ x₀ P)
    (hout : ∃ w ∈ omegaLimit atTop ϕ {x₀}, ∃ t ∉ P, w t = 0) :
    ∃ z ∈ omegaLimit atTop ϕ {x₀}, ∃ s ∈ P, ∃ t ∉ P, z s = 0 ∧ z t = 0 := by
  obtain ⟨w, hw, hPw⟩ := hcarr
  obtain ⟨s, hsP⟩ := hPne
  have hI : ∃ z ∈ omegaLimit atTop ϕ {x₀}, ∃ s ∈ P, z s = 0 :=
    ⟨w, hw, s, hsP, (hPw s).mp hsP⟩
  obtain ⟨u, hu, t, htn, hu0⟩ := hout
  have hJ : ∃ z ∈ omegaLimit atTop ϕ {x₀}, ∃ t ∈ (Pᶜ : Finset S), z t = 0 :=
    ⟨u, hu, t, Finset.mem_compl.mpr htn, hu0⟩
  have hIJ : P ∪ (Pᶜ : Finset S) = Finset.univ := by
    ext x
    simp
  obtain ⟨z, hz, s', hs', t', ht', hz0s, hz0t⟩ :=
    N.exists_omegaPoint_vanishing_on_both_sides κ hϕγ hsol hK hmaps hωnn hnoG hIJ hI hJ
  exact ⟨z, hz, s', hs', t', Finset.mem_compl.mp ht', hz0s, hz0t⟩

end Network
end CRNT
