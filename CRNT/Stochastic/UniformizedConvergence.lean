import CRNT.Stochastic.RegionPrimitive
import CRNT.Stochastic.Semigroup

/-!
# Non-vacuous geometric convergence via the uniformized kernel

The embedded jump chain of a mass-action network carries no holding self-loop at any enabled count:
a positive-probability reaction is the untruncated count shift `n − source + target`, which equals
`n` only when source and target coincide, impossible between distinct complexes. So the finite-state
aperiodicity hypothesis driving the Perron–Frobenius convergence theorems of
`CRNT.Stochastic.RegionPrimitive` is unsatisfiable on the embedded chain of any genuine network — the
obstruction recorded as `no_aperiodic_self_loop`.

Uniformization supplies the missing self-loop. The bounded uniformized kernel
`U = (1 − w)·δ + w·jumpKernel` of `CRNT.Stochastic.Semigroup`, with holding weight
`1 − w = 1 − exitRate/Λ`, carries a genuine holding term at every region state once the
uniformization rate `Λ` strictly dominates the region exit rates. The dominating bound
`uniformizationRate κ = 1 + ∑ exitRate` over a finite region already exceeds every single member's
exit rate, so the holding weight is strictly positive on the region: `U` has a positive diagonal
where the embedded chain has none. With strong connectivity inherited from the embedded chain — the
jump term `w·jumpKernel` keeps every embedded support edge, since `w > 0` on the region — the
uniformized region matrix is *primitive* by the finite-state Perron–Frobenius criterion
(irreducibility plus an aperiodicity self-loop, Meyn & Tweedie, "Markov Chains and Stochastic
Stability"). The self-loop is supplied by `U`'s holding term, not by a network reaction.

Primitivity then drives geometric convergence through
`colStochastic_primitive_pow_mulVec_tendsto`: the powers `U^{∘n}` carry every region-supported
initial law to the unique stationary law, `ℓ¹` and entrywise. Because the continuous-time semigroup
`P_t = exp(tQ)` is the Poisson mixture `∑_k e^{−Λt}(Λt)^k/k!·U^{∘k}` of these powers (Jensen,
"Markoff chains as an aid in the study of Markoff processes"; Norris, "Markov Chains"), the
convergence of `U^{∘n}` is the discrete engine of the continuous-time relaxation. This convergence is
*non-vacuous* on the uniformized kernel exactly where the embedded-chain version failed: the
self-loop obstruction `no_aperiodic_self_loop` concerns `jumpKernel`, while the diagonal of the
uniformized region matrix is the holding mass `1 − w > 0`, untouched by that obstruction.

## Main results

* `uRegionMatrix` — the restricted transition matrix of the uniformized kernel `U` on a finite
  region, the analogue of `regionMatrix` for `U`.
* `uRegionMatrix_nonneg`, `uRegionMatrix_colStochastic` — `U`'s region matrix is entrywise
  nonnegative and column-stochastic.
* `uRegionMatrix_diag_pos` — the diagonal entry at a region state is strictly positive, at least the
  holding weight `1 − w = 1 − exitRate/Λ`: `U` has a self-loop at every region state.
* `uRegionMatrix_stronglyConnected_of_regionStronglyConnected` — `U`'s region matrix inherits the
  strong connectivity of the embedded jump chain, since the jump term keeps every embedded edge.
* `uRegionMatrix_primitive` — `U`'s region matrix is primitive: positive diagonal plus strong
  connectivity gives a strictly positive fixed power. The self-loop comes from `U`'s holding term,
  not a network reaction, so the embedded-chain obstruction does not apply.
* `uRegionMatrix_pow_mulVec_tendsto` — geometric convergence of the powers `U^{∘n}` to the unique
  stationary probability vector, the non-vacuous deliverable.

The finite-region existence — exhibiting a finite strongly connected region of the genuine count
lattice carrying `U` — is parameterized here as the hypotheses `Fintype ↥T`,
`ClosedEnabledRegion`, `Nonempty`, and `regionStronglyConnected`; the convergence chain is proved
under them.

Depends on:
`CRNT.Stochastic.RegionPrimitive`, `CRNT.Stochastic.Semigroup`.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal NNReal BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- The restricted transition matrix of the uniformized kernel `U` on a finite region `T`, the
analogue of `regionMatrix` for `U = (1 − w)·δ + w·jumpKernel`. Following the column-stochastic
Perron–Frobenius convention, the entry at row `i` (target), column `j` (source) is the kernel mass
`U(j, {i})` cast to a real. -/
noncomputable def uRegionMatrix (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) [Fintype ↥T] : Matrix ↥T ↥T ℝ :=
  fun i j => (N.uniformizedKernel κ hTfin (j : S → ℕ) {(i : S → ℕ)}).toReal

/-- Each entry of the uniformized region matrix is nonnegative: it is the real cast of an
extended-nonnegative kernel mass. -/
theorem uRegionMatrix_nonneg (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) [Fintype ↥T] : ∀ i j, 0 ≤ N.uRegionMatrix κ hTfin i j :=
  fun _ _ => ENNReal.toReal_nonneg

/-- **Column-stochasticity of the uniformized region matrix.** Each column sums to one: the column
`j` totals `∑_{i ∈ T} U(j, {i})`, and the holding Dirac stays at `j ∈ T` while the jump term keeps
all of `j`'s outgoing mass inside `T` by forward closure, so this equals the full unit row mass
`U(j, Set.univ) = 1` of the Markov kernel. -/
theorem uRegionMatrix_colStochastic (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) :
    ∀ j, ∑ i, N.uRegionMatrix κ hTfin i j = 1 := by
  intro j
  -- the column sum is the toReal of the kernel mass of `T`, the full unit row mass.
  have hsum : (∑ i : ↥T, N.uniformizedKernel κ hTfin (j : S → ℕ) {(i : S → ℕ)})
      = N.uniformizedKernel κ hTfin (j : S → ℕ) T := by
    rw [← measure_biUnion_finset]
    · congr 1
      ext x
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, Finset.mem_univ,
        true_and, Subtype.exists, exists_prop]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hx; exact ⟨x, hx, rfl⟩
    · intro a _ b _ hab
      simp only [Function.onFun, Set.disjoint_singleton]
      exact fun h => hab (Subtype.ext h)
    · exact fun _ _ => MeasurableSpace.measurableSet_top
  have hjT : (j : S → ℕ) ∈ T := j.2
  haveI : IsProbabilityMeasure (N.uniformizedKernel κ hTfin (j : S → ℕ)) :=
    (N.instIsMarkovKernel_uniformizedKernel κ hTfin).isProbabilityMeasure (j : S → ℕ)
  have hcover : N.uniformizedKernel κ hTfin (j : S → ℕ) T = 1 := by
    -- the row mass leaving `T` vanishes: the holding Dirac sits at `j ∈ T`, and the jump term lands
    -- in `T` by forward closure, so the complement carries zero mass.
    have hcompl : N.uniformizedKernel κ hTfin (j : S → ℕ) Tᶜ = 0 := by
      rw [uniformizedKernel_apply, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
        Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      have hdir : Measure.dirac (j : S → ℕ) (Tᶜ : Set (S → ℕ)) = 0 := by
        rw [Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := (Tᶜ : Set (S → ℕ)))),
          Set.indicator_of_notMem (by simp [hjT])]
      have hjmp : N.jumpKernel κ (j : S → ℕ) (Tᶜ : Set (S → ℕ)) = 0 := by
        rw [N.jumpKernel_apply_of_exitRate_pos κ (j : S → ℕ) (hT.exit_ne _ hjT)]
        refine Finset.sum_eq_zero (fun r _ => ?_)
        have hfwd : N.jumpNextCount (j : S → ℕ) r ∈ T := hT.forward _ hjT r
        rw [Set.indicator_of_notMem
          (show N.jumpNextCount (j : S → ℕ) r ∉ (Tᶜ : Set (S → ℕ)) from fun h => h hfwd), mul_zero]
      rw [hdir, hjmp, mul_zero, mul_zero, add_zero]
    exact (prob_compl_eq_zero_iff (MeasurableSpace.measurableSet_top (s := T))).mp hcompl
  -- assemble
  have heq : (∑ i : ↥T, N.uRegionMatrix κ hTfin i j)
      = (∑ i : ↥T, N.uniformizedKernel κ hTfin (j : S → ℕ) {(i : S → ℕ)}).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
    rfl
  rw [heq, hsum, hcover]; rfl

/-- **A positive diagonal: `U` has a self-loop at every region state.** At a region state `j ∈ T`
the uniformization rate strictly dominates the exit rate, so the holding weight `1 − w` with
`w = exitRate κ j / Λ < 1` is strictly positive, and the diagonal entry of the uniformized region
matrix is at least this holding weight:
`0 < 1 − w ≤ uRegionMatrix κ hTfin j j`. The embedded jump chain has no such diagonal entry — this
is the self-loop supplied by uniformization, breaking the period the embedded chain cannot. -/
theorem uRegionMatrix_diag_pos (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) [Fintype ↥T] (j : ↥T) :
    0 < N.uRegionMatrix κ hTfin j j := by
  -- the holding weight is strictly positive: `Λ = 1 + ∑ exitRate` strictly exceeds `exitRate j`.
  have hjT : (j : S → ℕ) ∈ T := j.2
  have hΛ : 0 < N.uniformizationRate κ hTfin := N.uniformizationRate_pos κ hTfin
  have hwlt : N.uniformWeight κ hTfin (j : S → ℕ) < 1 := by
    rw [N.uniformWeight_eq_of_mem κ hTfin hjT, div_lt_one hΛ, uniformizationRate]
    have hsingle : N.exitRate κ (j : S → ℕ) ≤ ∑ m ∈ hTfin.toFinset, N.exitRate κ m :=
      Finset.single_le_sum (fun m _ => N.exitRate_nonneg κ m) (hTfin.mem_toFinset.mpr hjT)
    linarith
  have hhold : 0 < 1 - N.uniformWeight κ hTfin (j : S → ℕ) := by linarith
  -- the diagonal kernel mass dominates its holding-Dirac term `ofReal (1 − w)`.
  have hmass : N.uniformizedKernel κ hTfin (j : S → ℕ) {(j : S → ℕ)} =
      ENNReal.ofReal (1 - N.uniformWeight κ hTfin (j : S → ℕ)) +
        ENNReal.ofReal (N.uniformWeight κ hTfin (j : S → ℕ)) *
          N.jumpKernel κ (j : S → ℕ) {(j : S → ℕ)} := by
    rw [uniformizedKernel_apply, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
      Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := ({(j : S → ℕ)} : Set (S → ℕ)))),
      Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, mul_one]
  have hposE : 0 < N.uniformizedKernel κ hTfin (j : S → ℕ) {(j : S → ℕ)} := by
    rw [hmass]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hhold) le_self_add
  have hne : N.uniformizedKernel κ hTfin (j : S → ℕ) {(j : S → ℕ)} ≠ ∞ := measure_ne_top _ _
  show 0 < (N.uniformizedKernel κ hTfin (j : S → ℕ) {((j : ↥T) : S → ℕ)}).toReal
  exact ENNReal.toReal_pos hposE.ne' hne

/-- **The uniformized region matrix dominates the embedded one on the jump term.** Off the diagonal
the uniformized region matrix carries at least the jump weight `w` times the embedded matrix entry:
the uniformized mass is `U(j, {i}) = ofReal (1 − w)·δ + ofReal w · jumpKernel(j, {i})`, so a positive
embedded entry forces a positive uniformized entry. With `w > 0` on the region this transfers the
embedded jump chain's support edges to `U`. -/
theorem regionMatrix_pos_imp_uRegionMatrix_pos (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T] (hT : N.ClosedEnabledRegion κ T) {i j : ↥T}
    (hij : 0 < N.regionMatrix κ T i j) : 0 < N.uRegionMatrix κ hTfin i j := by
  -- the embedded entry being positive means the jump-kernel singleton mass is positive.
  have hjmp : 0 < N.jumpKernel κ (j : S → ℕ) {(i : S → ℕ)} := by
    have hne : N.jumpKernel κ (j : S → ℕ) {(i : S → ℕ)} ≠ ∞ := measure_ne_top _ _
    rw [regionMatrix] at hij
    by_contra hle
    rw [not_lt, nonpos_iff_eq_zero] at hle
    rw [hle, ENNReal.toReal_zero] at hij
    exact lt_irrefl _ hij
  -- the jump weight is strictly positive at `j ∈ T`: `w = exitRate j / Λ` with `exitRate j ≠ 0`.
  have hjT : (j : S → ℕ) ∈ T := j.2
  have hΛ : 0 < N.uniformizationRate κ hTfin := N.uniformizationRate_pos κ hTfin
  have hwpos : 0 < N.uniformWeight κ hTfin (j : S → ℕ) := by
    rw [N.uniformWeight_eq_of_mem κ hTfin hjT]
    exact div_pos (lt_of_le_of_ne (N.exitRate_nonneg κ _) (Ne.symm (hT.exit_ne _ hjT))) hΛ
  -- the uniformized mass dominates its jump term `ofReal w · jumpKernel(j, {i})`.
  have hmass : N.uniformizedKernel κ hTfin (j : S → ℕ) {(i : S → ℕ)} =
      ENNReal.ofReal (1 - N.uniformWeight κ hTfin (j : S → ℕ)) *
          Measure.dirac (j : S → ℕ) {(i : S → ℕ)} +
        ENNReal.ofReal (N.uniformWeight κ hTfin (j : S → ℕ)) *
          N.jumpKernel κ (j : S → ℕ) {(i : S → ℕ)} := by
    rw [uniformizedKernel_apply, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
      Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  have hposE : 0 < N.uniformizedKernel κ hTfin (j : S → ℕ) {(i : S → ℕ)} := by
    rw [hmass]
    have hterm : 0 < ENNReal.ofReal (N.uniformWeight κ hTfin (j : S → ℕ)) *
        N.jumpKernel κ (j : S → ℕ) {(i : S → ℕ)} :=
      pos_of_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr hwpos).ne' hjmp.ne')
    exact lt_of_lt_of_le hterm le_add_self
  have hne : N.uniformizedKernel κ hTfin (j : S → ℕ) {(i : S → ℕ)} ≠ ∞ := measure_ne_top _ _
  show 0 < (N.uniformizedKernel κ hTfin (j : S → ℕ) {((i : ↥T) : S → ℕ)}).toReal
  exact ENNReal.toReal_pos hposE.ne' hne

/-- **The uniformized region matrix inherits strong connectivity.** If the embedded jump chain's
restricted transition matrix is strongly connected (`regionStronglyConnected`), then so is `U`'s
region matrix: every embedded support edge is a uniformized support edge
(`regionMatrix_pos_imp_uRegionMatrix_pos`, using `w > 0` on the region), so each walk along the
embedded support digraph is a walk along the uniformized one. -/
theorem uRegionMatrix_stronglyConnected_of_regionStronglyConnected (N : Network S)
    (κ : RateConstants N) {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T]
    (hT : N.ClosedEnabledRegion κ T) (hsc : N.regionStronglyConnected κ T) :
    ∀ i j : ↥T, supportReaches (N.uRegionMatrix κ hTfin) i j := by
  intro i j
  -- lift the embedded support walk edge by edge to the uniformized support digraph.
  have hsc' := hsc i j
  unfold supportReaches at hsc' ⊢
  refine (Relation.ReflTransGen.mono
    (r := fun a c => N.regionMatrix κ T a c ≠ 0)
    (p := fun a c => N.uRegionMatrix κ hTfin a c ≠ 0) ?_) i j hsc'
  intro a c hac
  -- a nonzero embedded entry is a positive entry, which forces a positive uniformized entry.
  have hpos : 0 < N.regionMatrix κ T a c :=
    lt_of_le_of_ne (N.regionMatrix_nonneg κ T a c) (Ne.symm hac)
  exact (N.regionMatrix_pos_imp_uRegionMatrix_pos κ hTfin hT hpos).ne'

/-- **Primitivity of the uniformized region matrix.** On a finite strongly connected closed enabled
region, `U`'s region matrix is primitive: some fixed power is entrywise strictly positive. The
positive diagonal `uRegionMatrix_diag_pos` supplies the aperiodicity self-loop — from `U`'s holding
term, *not* a network reaction — and the inherited strong connectivity supplies irreducibility, so
the finite-state Perron–Frobenius criterion `regionPrimitive_of_stronglyConnected_self_loop` (Meyn &
Tweedie, "Markov Chains and Stochastic Stability") applies. This is exactly the conclusion the
embedded jump chain cannot reach, whose diagonal `regionMatrix κ T j j` vanishes for a network of
genuine reactions (`no_aperiodic_self_loop`). -/
theorem uRegionMatrix_primitive (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) [Fintype ↥T] [Nonempty ↥T] (hT : N.ClosedEnabledRegion κ T)
    (hsc : N.regionStronglyConnected κ T) :
    ∃ k : ℕ, 0 < k ∧ ∀ i j : ↥T, 0 < (N.uRegionMatrix κ hTfin ^ k) i j := by
  obtain ⟨s⟩ := (inferInstance : Nonempty ↥T)
  exact primitive_of_stronglyConnected_self_loop (N.uRegionMatrix κ hTfin)
    (N.uRegionMatrix_nonneg κ hTfin)
    (N.uRegionMatrix_stronglyConnected_of_regionStronglyConnected κ hTfin hT hsc)
    (N.uRegionMatrix_diag_pos κ hTfin s)

/-- **Non-vacuous geometric convergence of the uniformized chain.** On a finite strongly connected
closed enabled region, the powers `U^{∘n}` of the uniformized region matrix carry every region
probability vector `x` to the unique stationary probability vector `b`: as `n → ∞`,
`(uRegionMatrix)^n x → b`, both in the `ℓ¹` distance and entrywise. The uniformized region matrix is
column-stochastic (`uRegionMatrix_colStochastic`), nonnegative (`uRegionMatrix_nonneg`), and
primitive (`uRegionMatrix_primitive`, the self-loop coming from `U`'s holding term), so
`colStochastic_primitive_pow_mulVec_tendsto` gives geometric mixing. This convergence is
non-vacuous precisely where the embedded-chain version of
`CRNT.Stochastic.RegionPrimitive` failed: the aperiodicity self-loop here is the strictly positive
holding mass `1 − w > 0`, untouched by the embedded-chain obstruction `no_aperiodic_self_loop`.

Since the continuous-time semigroup `P_t = cmeSemigroup κ hTfin t` is the Poisson mixture
`∑_k e^{−Λt}(Λt)^k/k! · U^{∘k}` of these powers (`cmeSemigroup`), this is the discrete engine of the
continuous-time relaxation to the Anderson–Craciun–Kurtz product-Poisson stationary law (Jensen,
"Markoff chains as an aid in the study of Markoff processes"; Norris, "Markov Chains"). -/
theorem uRegionMatrix_pow_mulVec_tendsto (N : Network S) (κ : RateConstants N) {T : Set (S → ℕ)}
    (hTfin : T.Finite) [Fintype ↥T] [Nonempty ↥T] (hT : N.ClosedEnabledRegion κ T)
    (hsc : N.regionStronglyConnected κ T) (x : ↥T → ℝ) (hx : ∑ i, x i = 1) :
    ∃ b : ↥T → ℝ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧
      (N.uRegionMatrix κ hTfin).mulVec b = b ∧
      Tendsto (fun n => l1Dist ((N.uRegionMatrix κ hTfin ^ n).mulVec x) b) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => (N.uRegionMatrix κ hTfin ^ n).mulVec x i) atTop (𝓝 (b i)) := by
  obtain ⟨k, hk, hkpos⟩ := N.uRegionMatrix_primitive κ hTfin hT hsc
  exact colStochastic_primitive_pow_mulVec_tendsto (N.uRegionMatrix κ hTfin)
    (N.uRegionMatrix_nonneg κ hTfin) (N.uRegionMatrix_colStochastic κ hTfin hT) hk hkpos x hx

end Network

end CRNT
