import CRNT.Stochastic.UniformizedConvergence
import CRNT.Stochastic.RegionStronglyConnected
import CRNT.Examples.StochasticConvergenceExample

/-!
# A relaxed finite region carrying unconditional uniformized convergence

The geometric-convergence chain of `CRNT.Stochastic.UniformizedConvergence` runs on a
`ClosedEnabledRegion`: a finite set whose every member dominates and is enabled for *every*
reaction. That hypothesis is jointly unsatisfiable on the genuine count lattice of a mass-action
network (`CRNT.Examples.StochasticConvergenceExample.pair_not_closed_of_mem`): enabled-everywhere
forces members away from the propensity-vanishing boundary of the conservation simplex, while
forward-closure drags firings of boundary-adjacent members back onto that boundary. No nonempty
conservation window of a real network is a closed enabled region.

This module replaces enabled-everywhere by exactly what column-stochasticity of the uniformized
kernel `U = (1 − w)·δ + w·jumpKernel` actually needs: that *positive-probability* jumps stay inside
the region. A `ConservationClassRegion` is a finite set `T` of counts on which

* no member is absorbing (`exit_ne` — the exit rate is positive, so the uniformization weight is a
  genuine mixing coefficient and the embedded jump rows are stochastic), and
* every positive-probability reaction firing from a member lands inside `T` (`forward` — disabled
  reactions contribute zero to `jumpKernel`, so closure is about actual positive-probability jumps,
  not enabled-everywhere).

Boundary members keep their disabled reactions; those reactions carry zero jump probability and so
zero kernel mass, untouched by closure. The holding term `1 − w` and the surviving in-region jumps
together carry the full unit row mass, so `U`'s region matrix is column-stochastic
(`uRegionMatrix_colStochastic_of_conservationClass`). The strictly positive holding diagonal
(`uRegionMatrix_diag_pos`, independent of the region notion) supplies aperiodicity, and count-level
jump-strong-connectivity (`RegionJumpStronglyConnected`) supplies irreducibility, so `U`'s region
matrix is primitive (`uRegionMatrix_primitive_of_conservationClass`) and its powers converge
geometrically to the unique stationary law (`uRegionMatrix_pow_mulVec_tendsto_of_conservationClass`).

## A concrete non-vacuous instance: `A ⇌ B` on a conservation class

The reversible pair `A ⇌ B` on a fixed conservation class `{n : n_A + n_B = K}` is exhibited as a
`ConservationClassRegion`. Firing either reaction preserves the sum `n_A + n_B`, and a
positive-probability firing is an enabled untruncated shift that stays in the simplex, so the class
is jump-forward-closed even at its boundary points `(K, 0)` and `(0, K)` — where one reaction is
disabled and simply contributes nothing. The class is a birth–death chain on `{0, …, K}`, strongly
connected by single forward/backward jumps, and the uniformized self-loop supplies aperiodicity. The
convergence theorem then fires *unconditionally* on this region: a genuinely non-vacuous geometric
convergence instance on a real weakly reversible network, with no unsatisfiable hypothesis remaining.

## Main results

* `ConservationClassRegion` — the relaxed region notion: non-absorbing members, jump-forward-closed.
* `uRegionMatrix_colStochastic_of_conservationClass` — `U`'s region matrix is column-stochastic on
  a `ConservationClassRegion`, needing only positive-probability closure.
* `uRegionMatrix_primitive_of_conservationClass` — `U`'s region matrix is primitive on a
  jump-strongly-connected `ConservationClassRegion`.
* `uRegionMatrix_pow_mulVec_tendsto_of_conservationClass` — geometric convergence of `U^{∘n}` on
  such a region.
* `conservationClass`, `conservationClass_finite`, `conservationClassRegion`,
  `conservationClass_jumpStronglyConnected` — the `A ⇌ B` conservation class `{n_A + n_B = K}` as a
  finite, jump-forward-closed, jump-strongly-connected `ConservationClassRegion`.
* `conservationClass_pow_mulVec_tendsto` — unconditional geometric convergence of `U^{∘n}` on the
  `A ⇌ B` conservation class, the non-vacuous deliverable.

This is the Anderson–Craciun–Kurtz recurrence picture (Anderson, Craciun & Kurtz, "Product-form
stationary distributions for deficiency zero chemical reaction networks") realized on a finite
conservation class, with the finite-state holding-self-loop aperiodicity of Norris, "Markov Chains",
§1.8 supplied by uniformization rather than a network reaction.

Depends on:
`CRNT.Stochastic.UniformizedConvergence`, `CRNT.Stochastic.RegionStronglyConnected`,
`CRNT.Examples.StochasticConvergenceExample`.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal NNReal BigOperators

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- **A relaxed finite region: a conservation class.** A set of counts is a *conservation-class
region* when no member is absorbing (`exit_ne` — the exit rate is positive) and every
positive-probability reaction firing from a member lands inside the region (`forward`). Unlike
`ClosedEnabledRegion` this imposes no enabled-everywhere or target-domination demand: a boundary
member may have some reactions disabled, and those carry zero jump probability, so closure is about
actual positive-probability jumps. This is the exact hypothesis under which the uniformized kernel
`U` restricted to the region is column-stochastic. -/
structure ConservationClassRegion (N : Network S) (κ : RateConstants N) (T : Set (S → ℕ)) :
    Prop where
  /-- No member of the region is absorbing. -/
  exit_ne : ∀ n ∈ T, N.exitRate κ n ≠ 0
  /-- Every positive-probability reaction firing from a member lands inside the region. -/
  forward : ∀ n ∈ T, ∀ r, 0 < N.jumpProb κ n r → N.jumpNextCount n r ∈ T

/-- Every `ClosedEnabledRegion` is a `ConservationClassRegion`: enabled-everywhere is stronger than
needed. The non-absorbing condition is shared, and unconditional forward-closure
(`ClosedEnabledRegion.forward`) implies positive-probability forward-closure. -/
theorem ClosedEnabledRegion.toConservationClassRegion (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hT : N.ClosedEnabledRegion κ T) : N.ConservationClassRegion κ T where
  exit_ne := hT.exit_ne
  forward n hn r _ := hT.forward n hn r

/-- **Column-stochasticity of the uniformized region matrix on a conservation class.** Each column
sums to one, exactly as for a closed enabled region but under the weaker
`ConservationClassRegion` hypothesis: the holding Dirac stays at `j ∈ T`, and the jump term keeps
all of `j`'s *positive-probability* outgoing mass inside `T` — disabled reactions contribute zero —
so the row mass leaving `T` vanishes and the column totals the full unit mass
`U(j, Set.univ) = 1`. -/
theorem uRegionMatrix_colStochastic_of_conservationClass (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T] (hT : N.ConservationClassRegion κ T) :
    ∀ j, ∑ i, N.uRegionMatrix κ hTfin i j = 1 := by
  intro j
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
    have hcompl : N.uniformizedKernel κ hTfin (j : S → ℕ) Tᶜ = 0 := by
      rw [uniformizedKernel_apply, Measure.coe_add, Pi.add_apply, Measure.smul_apply,
        Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      have hdir : Measure.dirac (j : S → ℕ) (Tᶜ : Set (S → ℕ)) = 0 := by
        rw [Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top (s := (Tᶜ : Set (S → ℕ)))),
          Set.indicator_of_notMem (by simp [hjT])]
      have hjmp : N.jumpKernel κ (j : S → ℕ) (Tᶜ : Set (S → ℕ)) = 0 := by
        rw [N.jumpKernel_apply_of_exitRate_pos κ (j : S → ℕ) (hT.exit_ne _ hjT)]
        refine Finset.sum_eq_zero (fun r _ => ?_)
        -- a disabled reaction has zero jump probability, so its `ofReal` factor vanishes; an enabled
        -- one lands in `T` by `forward`, so the `Tᶜ`-indicator vanishes.
        rcases eq_or_lt_of_le (N.jumpProb_nonneg κ (j : S → ℕ) r) with hz | hpos
        · rw [← hz, ENNReal.ofReal_zero, zero_mul]
        · have hfwd : N.jumpNextCount (j : S → ℕ) r ∈ T := hT.forward _ hjT r hpos
          rw [Set.indicator_of_notMem
            (show N.jumpNextCount (j : S → ℕ) r ∉ (Tᶜ : Set (S → ℕ)) from fun h => h hfwd), mul_zero]
      rw [hdir, hjmp, mul_zero, mul_zero, add_zero]
    exact (prob_compl_eq_zero_iff (MeasurableSpace.measurableSet_top (s := T))).mp hcompl
  have heq : (∑ i : ↥T, N.uRegionMatrix κ hTfin i j)
      = (∑ i : ↥T, N.uniformizedKernel κ hTfin (j : S → ℕ) {(i : S → ℕ)}).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
    rfl
  rw [heq, hsum, hcover]; rfl

/-- **The uniformized region matrix dominates the embedded one on a conservation class.** Off the
diagonal a positive embedded entry forces a positive uniformized entry, exactly as for a closed
enabled region but under the relaxed hypothesis: a positive embedded entry means the
positive-probability jump term `ofReal w · jumpKernel(j, {i})` is positive, and the jump weight `w`
is positive at `j ∈ T` since `j` is non-absorbing (`exit_ne`). -/
theorem regionMatrix_pos_imp_uRegionMatrix_pos_of_conservationClass (N : Network S)
    (κ : RateConstants N) {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T]
    (hT : N.ConservationClassRegion κ T) {i j : ↥T} (hij : 0 < N.regionMatrix κ T i j) :
    0 < N.uRegionMatrix κ hTfin i j := by
  have hjmp : 0 < N.jumpKernel κ (j : S → ℕ) {(i : S → ℕ)} := by
    have hne : N.jumpKernel κ (j : S → ℕ) {(i : S → ℕ)} ≠ ∞ := measure_ne_top _ _
    rw [regionMatrix] at hij
    by_contra hle
    rw [not_lt, nonpos_iff_eq_zero] at hle
    rw [hle, ENNReal.toReal_zero] at hij
    exact lt_irrefl _ hij
  have hjT : (j : S → ℕ) ∈ T := j.2
  have hΛ : 0 < N.uniformizationRate κ hTfin := N.uniformizationRate_pos κ hTfin
  have hwpos : 0 < N.uniformWeight κ hTfin (j : S → ℕ) := by
    rw [N.uniformWeight_eq_of_mem κ hTfin hjT]
    exact div_pos (lt_of_le_of_ne (N.exitRate_nonneg κ _) (Ne.symm (hT.exit_ne _ hjT))) hΛ
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

/-- **The uniformized region matrix inherits strong connectivity on a conservation class.** From
count-level jump-strong-connectivity (`RegionJumpStronglyConnected`) the embedded restricted matrix
is strongly connected (`regionStronglyConnected_of_jumpReaches`), and every embedded support edge is
a uniformized support edge (`regionMatrix_pos_imp_uRegionMatrix_pos_of_conservationClass`), so `U`'s
region matrix is strongly connected. -/
theorem uRegionMatrix_stronglyConnected_of_conservationClass (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T] (hT : N.ConservationClassRegion κ T)
    (hjsc : N.RegionJumpStronglyConnected κ T) :
    ∀ i j : ↥T, supportReaches (N.uRegionMatrix κ hTfin) i j := by
  intro i j
  have hsc : N.regionStronglyConnected κ T := N.regionStronglyConnected_of_jumpReaches κ hjsc
  have hsc' := hsc i j
  unfold supportReaches at hsc' ⊢
  refine (Relation.ReflTransGen.mono
    (r := fun a c => N.regionMatrix κ T a c ≠ 0)
    (p := fun a c => N.uRegionMatrix κ hTfin a c ≠ 0) ?_) i j hsc'
  intro a c hac
  have hpos : 0 < N.regionMatrix κ T a c :=
    lt_of_le_of_ne (N.regionMatrix_nonneg κ T a c) (Ne.symm hac)
  exact (N.regionMatrix_pos_imp_uRegionMatrix_pos_of_conservationClass κ hTfin hT hpos).ne'

/-- **Primitivity of the uniformized region matrix on a conservation class.** On a finite
jump-strongly-connected conservation-class region, `U`'s region matrix is primitive: the positive
holding diagonal `uRegionMatrix_diag_pos` supplies the aperiodicity self-loop — from `U`'s holding
term, not a network reaction — and the inherited strong connectivity supplies irreducibility, so the
finite-state Perron–Frobenius criterion `primitive_of_stronglyConnected_self_loop` (Meyn & Tweedie,
"Markov Chains and Stochastic Stability") applies. -/
theorem uRegionMatrix_primitive_of_conservationClass (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T] [Nonempty ↥T]
    (hT : N.ConservationClassRegion κ T) (hjsc : N.RegionJumpStronglyConnected κ T) :
    ∃ k : ℕ, 0 < k ∧ ∀ i j : ↥T, 0 < (N.uRegionMatrix κ hTfin ^ k) i j := by
  obtain ⟨s⟩ := (inferInstance : Nonempty ↥T)
  exact primitive_of_stronglyConnected_self_loop (N.uRegionMatrix κ hTfin)
    (N.uRegionMatrix_nonneg κ hTfin)
    (N.uRegionMatrix_stronglyConnected_of_conservationClass κ hTfin hT hjsc)
    (N.uRegionMatrix_diag_pos κ hTfin s)

/-- **Non-vacuous geometric convergence of the uniformized chain on a conservation class.** On a
finite jump-strongly-connected conservation-class region, the powers `U^{∘n}` carry every region
probability vector `x` to the unique stationary probability vector `b`, in the `ℓ¹` distance and
entrywise. The uniformized region matrix is column-stochastic
(`uRegionMatrix_colStochastic_of_conservationClass`), nonnegative (`uRegionMatrix_nonneg`), and
primitive (`uRegionMatrix_primitive_of_conservationClass`), so
`colStochastic_primitive_pow_mulVec_tendsto` gives geometric mixing. The aperiodicity self-loop is
the strictly positive holding mass `1 − w > 0`, available even at the propensity-vanishing boundary
where a closed enabled region cannot exist. -/
theorem uRegionMatrix_pow_mulVec_tendsto_of_conservationClass (N : Network S) (κ : RateConstants N)
    {T : Set (S → ℕ)} (hTfin : T.Finite) [Fintype ↥T] [Nonempty ↥T]
    (hT : N.ConservationClassRegion κ T) (hjsc : N.RegionJumpStronglyConnected κ T)
    (x : ↥T → ℝ) (hx : ∑ i, x i = 1) :
    ∃ b : ↥T → ℝ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧
      (N.uRegionMatrix κ hTfin).mulVec b = b ∧
      Tendsto (fun n => l1Dist ((N.uRegionMatrix κ hTfin ^ n).mulVec x) b) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => (N.uRegionMatrix κ hTfin ^ n).mulVec x i) atTop (𝓝 (b i)) := by
  obtain ⟨k, hk, hkpos⟩ := N.uRegionMatrix_primitive_of_conservationClass κ hTfin hT hjsc
  exact colStochastic_primitive_pow_mulVec_tendsto (N.uRegionMatrix κ hTfin)
    (N.uRegionMatrix_nonneg κ hTfin)
    (N.uRegionMatrix_colStochastic_of_conservationClass κ hTfin hT) hk hkpos x hx

end Network

end CRNT

namespace CRNT.Examples.ConservationClassRegion

open CRNT CRNT.Network
open CRNT.Examples.StochasticConvergenceExample
open Filter Topology
open scoped BigOperators

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- The stochastic mass-action propensity of `fwd : A → B` at a count `n` is `κ.k fwd · n_A`: the
source complex `A = (1, 0)` contributes the falling factorial `(n_A)^{(1)} = n_A` at species `A`
and the unit falling factorial `(n_B)^{(0)} = 1` at species `B`. -/
theorem smar_fwd (κ : RateConstants N) (n : Species → ℕ) :
    N.stochasticMassActionRate κ n Rxn.fwd = κ.k Rxn.fwd * (n Species.A : ℝ) := by
  simp only [stochasticMassActionRate]
  rw [Fintype.prod_eq_mul Species.A Species.B (by decide)
    (fun x hx => by rcases x with _ | _ <;> simp_all)]
  simp [N, rxn, cA, Nat.descFactorial]

/-- The stochastic mass-action propensity of `bwd : B → A` at a count `n` is `κ.k bwd · n_B`. -/
theorem smar_bwd (κ : RateConstants N) (n : Species → ℕ) :
    N.stochasticMassActionRate κ n Rxn.bwd = κ.k Rxn.bwd * (n Species.B : ℝ) := by
  simp only [stochasticMassActionRate]
  rw [Fintype.prod_eq_mul Species.A Species.B (by decide)
    (fun x hx => by rcases x with _ | _ <;> simp_all)]
  simp [N, rxn, cB, Nat.descFactorial]

/-- The exit rate of the pair at a count `n` is `κ.k fwd · n_A + κ.k bwd · n_B`: the two-reaction sum
of the mass-action propensities. -/
theorem exitRate_eq (κ : RateConstants N) (n : Species → ℕ) :
    N.exitRate κ n = κ.k Rxn.fwd * (n Species.A : ℝ) + κ.k Rxn.bwd * (n Species.B : ℝ) := by
  rw [exitRate, show (∑ r, N.stochasticMassActionRate κ n r)
      = N.stochasticMassActionRate κ n Rxn.fwd + N.stochasticMassActionRate κ n Rxn.bwd from
    Fintype.sum_eq_add Rxn.fwd Rxn.bwd (by decide)
      (fun x hx => by rcases x with _ | _ <;> simp_all), smar_fwd, smar_bwd]

/-- **The `A ⇌ B` conservation class `{n : n_A + n_B = K}`.** The fixed-total-count slice of the
count lattice; firing either reaction preserves `n_A + n_B`, so this is a single conservation class
of the reversible pair. -/
def conservationClass (K : ℕ) : Set (Species → ℕ) := {n | n Species.A + n Species.B = K}

/-- The canonical class member with `n_A = j` and `n_B = K − j`. -/
def ccPoint (K j : ℕ) : Species → ℕ := fun s => if s = Species.A then j else K - j

/-- **Jump-forward-closure of the conservation class.** A positive-probability reaction is enabled
(`enabled_of_jumpProb_pos`), so its firing is the exact untruncated shift that moves one unit between
`A` and `B`; the total `n_A + n_B` is preserved, so the post-firing count stays in the class — even
at the boundary points, where the disabled reaction simply carries zero probability and is never the
firing reaction. -/
theorem conservationClass_forward (κ : RateConstants N) (K : ℕ) :
    ∀ n ∈ conservationClass K, ∀ r, 0 < N.jumpProb κ n r →
      N.jumpNextCount n r ∈ conservationClass K := by
  intro n hn r hprob
  simp only [conservationClass, Set.mem_setOf_eq] at hn ⊢
  have henabled : N.Enabled n r := N.enabled_of_jumpProb_pos κ hprob
  cases r
  · have hA : 1 ≤ n Species.A := by simpa [N, rxn, cA] using henabled Species.A
    have e1 : N.jumpNextCount n Rxn.fwd Species.A = n Species.A - 1 := by
      simp [jumpNextCount, N, rxn, cA, cB]
    have e2 : N.jumpNextCount n Rxn.fwd Species.B = n Species.B + 1 := by
      simp [jumpNextCount, N, rxn, cA, cB]
    rw [e1, e2]; omega
  · have hB : 1 ≤ n Species.B := by simpa [N, rxn, cB] using henabled Species.B
    have e1 : N.jumpNextCount n Rxn.bwd Species.A = n Species.A + 1 := by
      simp [jumpNextCount, N, rxn, cA, cB]
    have e2 : N.jumpNextCount n Rxn.bwd Species.B = n Species.B - 1 := by
      simp [jumpNextCount, N, rxn, cA, cB]
    rw [e1, e2]; omega

/-- **No member of a nonempty conservation class is absorbing.** With `1 ≤ K` and `n_A + n_B = K`, at
least one coordinate is positive, so the exit rate `κ.k fwd · n_A + κ.k bwd · n_B` has a strictly
positive term (the rate constants are positive), hence is nonzero. The boundary points `(K, 0)` and
`(0, K)` are non-absorbing because the single enabled reaction there still carries positive
propensity. -/
theorem conservationClass_exit_ne (κ : RateConstants N) (K : ℕ) (hK : 1 ≤ K) :
    ∀ n ∈ conservationClass K, N.exitRate κ n ≠ 0 := by
  intro n hn
  simp only [conservationClass, Set.mem_setOf_eq] at hn
  rw [exitRate_eq]
  have hkf : 0 < κ.k Rxn.fwd := κ.positive Rxn.fwd
  have hkb : 0 < κ.k Rxn.bwd := κ.positive Rxn.bwd
  rcases Nat.eq_zero_or_pos (n Species.A) with hA | hA
  · have hB : 0 < n Species.B := by omega
    have h1 : 0 < κ.k Rxn.bwd * (n Species.B : ℝ) := mul_pos hkb (by exact_mod_cast hB)
    have h2 : 0 ≤ κ.k Rxn.fwd * (n Species.A : ℝ) := mul_nonneg hkf.le (by positivity)
    positivity
  · have h1 : 0 < κ.k Rxn.fwd * (n Species.A : ℝ) := mul_pos hkf (by exact_mod_cast hA)
    have h2 : 0 ≤ κ.k Rxn.bwd * (n Species.B : ℝ) := mul_nonneg hkb.le (by positivity)
    positivity

/-- The conservation class is finite: every member is `ccPoint K (n_A)` for some `n_A ≤ K`, so the
class sits inside the finite range of `ccPoint K` over `Fin (K + 1)`. -/
theorem conservationClass_finite (K : ℕ) : (conservationClass K).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun j : Fin (K + 1) => ccPoint K j))
  intro n hn
  simp only [conservationClass, Set.mem_setOf_eq] at hn
  refine ⟨⟨n Species.A, by omega⟩, ?_⟩
  funext s
  cases s
  · simp [ccPoint]
  · simp only [ccPoint, if_neg (by decide : Species.B ≠ Species.A)]
    omega

noncomputable instance fintypeConservationClass (K : ℕ) : Fintype ↥(conservationClass K) :=
  (conservationClass_finite K).fintype

/-- **A single forward jump inside the class.** At a class member with `1 ≤ n_A`, reaction `fwd` is
enabled and carries positive probability (`jumpProb_pos_of_enabled`), and its image stays in the
class (`conservationClass_forward`); this is a `JumpStep`. -/
theorem step_fwd (κ : RateConstants N) (K : ℕ) (hK : 1 ≤ K)
    {n : Species → ℕ} (hn : n ∈ conservationClass K) (hA : 1 ≤ n Species.A) :
    N.JumpStep κ (conservationClass K) n (N.jumpNextCount n Rxn.fwd) := by
  have henabled : N.Enabled n Rxn.fwd := by
    intro s; cases s
    · simpa [N, rxn, cA] using hA
    · simp [N, rxn, cA]
  have hexit : N.exitRate κ n ≠ 0 := conservationClass_exit_ne κ K hK n hn
  have hprob : 0 < N.jumpProb κ n Rxn.fwd := N.jumpProb_pos_of_enabled κ henabled hexit
  have hmem : N.jumpNextCount n Rxn.fwd ∈ conservationClass K :=
    conservationClass_forward κ K n hn Rxn.fwd hprob
  exact ⟨hn, hmem, hexit, Rxn.fwd, rfl, hprob⟩

/-- **A single backward jump inside the class.** At a class member with `1 ≤ n_B`, reaction `bwd` is
enabled and carries positive probability, and its image stays in the class; this is a `JumpStep`. -/
theorem step_bwd (κ : RateConstants N) (K : ℕ) (hK : 1 ≤ K)
    {n : Species → ℕ} (hn : n ∈ conservationClass K) (hB : 1 ≤ n Species.B) :
    N.JumpStep κ (conservationClass K) n (N.jumpNextCount n Rxn.bwd) := by
  have henabled : N.Enabled n Rxn.bwd := by
    intro s; cases s
    · simp [N, rxn, cB]
    · simpa [N, rxn, cB] using hB
  have hexit : N.exitRate κ n ≠ 0 := conservationClass_exit_ne κ K hK n hn
  have hprob : 0 < N.jumpProb κ n Rxn.bwd := N.jumpProb_pos_of_enabled κ henabled hexit
  have hmem : N.jumpNextCount n Rxn.bwd ∈ conservationClass K :=
    conservationClass_forward κ K n hn Rxn.bwd hprob
  exact ⟨hn, hmem, hexit, Rxn.bwd, rfl, hprob⟩

/-- The all-`A` boundary count `(K, 0)`, a member of the conservation class. -/
def allA (K : ℕ) : Species → ℕ := fun s => if s = Species.A then K else 0

theorem allA_mem (K : ℕ) : allA K ∈ conservationClass K := by
  simp [conservationClass, allA]

/-- **Every class member jump-reaches the all-`A` boundary `(K, 0)`.** Repeatedly firing `bwd`
decreases `n_B` by one each step while staying in the class, terminating at `n_B = 0`, i.e. `(K, 0)`;
the walk is built by strong induction on `n_B`. -/
theorem reaches_allA (κ : RateConstants N) (K : ℕ) (hK : 1 ≤ K) :
    ∀ n ∈ conservationClass K, N.JumpReaches κ (conservationClass K) n (allA K) := by
  intro n hn
  generalize hb : n Species.B = b
  induction b using Nat.strong_induction_on generalizing n with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · have hnA : n Species.A = K := by
        simp only [conservationClass, Set.mem_setOf_eq] at hn; omega
      have hne : n = allA K := by funext s; cases s <;> simp [allA] <;> omega
      rw [hne]; exact Relation.ReflTransGen.refl
    · have hB : 1 ≤ n Species.B := by omega
      have hstep := step_bwd κ K hK hn hB
      set m := N.jumpNextCount n Rxn.bwd with hm
      have hmmem : m ∈ conservationClass K := hstep.2.1
      have hmB : m Species.B = b - 1 := by
        rw [hm]; simp [jumpNextCount, N, rxn, cA, cB]; omega
      have hrec : N.JumpReaches κ (conservationClass K) m (allA K) :=
        ih (b - 1) (by omega) m hmmem hmB
      exact Relation.ReflTransGen.head hstep hrec

/-- **The all-`A` boundary `(K, 0)` jump-reaches every class member.** From `(K, 0)`, firing `fwd`
toward the target decreases `n_A`; the walk to a member with `n_B = b` is built by strong induction
on `b`, prepending the predecessor `(n_A + 1, n_B − 1)` and one `fwd` step. -/
theorem allA_reaches (κ : RateConstants N) (K : ℕ) (hK : 1 ≤ K) :
    ∀ n ∈ conservationClass K, N.JumpReaches κ (conservationClass K) (allA K) n := by
  intro n hn
  generalize hb : n Species.B = b
  induction b using Nat.strong_induction_on generalizing n with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · have hnA : n Species.A = K := by
        simp only [conservationClass, Set.mem_setOf_eq] at hn; omega
      have hne : n = allA K := by funext s; cases s <;> simp [allA] <;> omega
      rw [hne]; exact Relation.ReflTransGen.refl
    · set p : Species → ℕ := fun s => if s = Species.A then n Species.A + 1 else n Species.B - 1
        with hp
      have hnsum : n Species.A + n Species.B = K := by simpa [conservationClass] using hn
      have hpmem : p ∈ conservationClass K := by
        show p Species.A + p Species.B = K
        show (if Species.A = Species.A then n Species.A + 1 else n Species.B - 1)
          + (if Species.B = Species.A then n Species.A + 1 else n Species.B - 1) = K
        rw [if_pos rfl, if_neg (by decide)]; omega
      have hpB : p Species.B = b - 1 := by
        show (if Species.B = Species.A then n Species.A + 1 else n Species.B - 1) = b - 1
        rw [if_neg (by decide)]; omega
      have hpA : 1 ≤ p Species.A := by
        show 1 ≤ (if Species.A = Species.A then n Species.A + 1 else n Species.B - 1)
        rw [if_pos rfl]; omega
      have hrec : N.JumpReaches κ (conservationClass K) (allA K) p :=
        ih (b - 1) (by omega) p hpmem hpB
      have hstep := step_fwd κ K hK hpmem hpA
      have hjn : N.jumpNextCount p Rxn.fwd = n := by
        funext s; simp only [jumpNextCount]
        cases s
        · show n Species.A + 1 - (N.reaction Rxn.fwd).source Species.A
            + (N.reaction Rxn.fwd).target Species.A = n Species.A
          simp [N, rxn, cA, cB]
        · show n Species.B - 1 - (N.reaction Rxn.fwd).source Species.B
            + (N.reaction Rxn.fwd).target Species.B = n Species.B
          simp only [N, rxn, cA, cB]; omega
      rw [hjn] at hstep
      exact Relation.ReflTransGen.tail hrec hstep

/-- **The conservation class is jump-strongly-connected.** Every ordered pair of members is connected
by routing through the all-`A` boundary `(K, 0)`: the source reaches `(K, 0)` (`reaches_allA`) and
`(K, 0)` reaches the target (`allA_reaches`). The class is a birth–death chain on `{0, …, K}`. -/
theorem conservationClass_jumpStronglyConnected (κ : RateConstants N) (K : ℕ) (hK : 1 ≤ K) :
    N.RegionJumpStronglyConnected κ (conservationClass K) := by
  intro n hn m hm
  exact Relation.ReflTransGen.trans (reaches_allA κ K hK n hn) (allA_reaches κ K hK m hm)

/-- **The `A ⇌ B` conservation class is a `ConservationClassRegion`.** It is non-absorbing on every
member (`conservationClass_exit_ne`) and jump-forward-closed (`conservationClass_forward`), with no
enabled-everywhere demand — the boundary points belong, satisfying the relaxed region notion exactly
where a closed enabled region cannot exist. -/
theorem conservationClassRegion (κ : RateConstants N) (K : ℕ) (hK : 1 ≤ K) :
    N.ConservationClassRegion κ (conservationClass K) where
  exit_ne := conservationClass_exit_ne κ K hK
  forward := conservationClass_forward κ K

/-- **Unconditional geometric convergence of the uniformized chain on the `A ⇌ B` conservation
class.** For `1 ≤ K`, the powers `U^{∘n}` of the uniformized region matrix on the conservation class
`{n : n_A + n_B = K}` carry every region probability vector `x` to the unique stationary probability
vector `b`, in the `ℓ¹` distance and entrywise. Every hypothesis is discharged: finiteness
(`conservationClass_finite`), the relaxed region structure (`conservationClassRegion`), and count-level
strong connectivity (`conservationClass_jumpStronglyConnected`); the aperiodicity self-loop is the
uniformized holding mass, available even at the simplex boundary. This is a genuinely non-vacuous
convergence instance on a real weakly reversible network, with no unsatisfiable hypothesis remaining —
the conservation-class realization of the Anderson–Craciun–Kurtz recurrence picture (Anderson, Craciun
& Kurtz, "Product-form stationary distributions for deficiency zero chemical reaction networks") with
the finite-state holding-self-loop aperiodicity of Norris, "Markov Chains", §1.8. -/
theorem conservationClass_pow_mulVec_tendsto (κ : RateConstants N) (K : ℕ) (hK : 1 ≤ K)
    (x : ↥(conservationClass K) → ℝ) (hx : ∑ i, x i = 1) :
    ∃ b : ↥(conservationClass K) → ℝ, (∀ i, 0 < b i) ∧ (∑ i, b i = 1) ∧
      (N.uRegionMatrix κ (conservationClass_finite K)).mulVec b = b ∧
      Tendsto (fun n => l1Dist
        ((N.uRegionMatrix κ (conservationClass_finite K) ^ n).mulVec x) b) atTop (𝓝 0) ∧
      ∀ i, Tendsto
        (fun n => (N.uRegionMatrix κ (conservationClass_finite K) ^ n).mulVec x i) atTop
        (𝓝 (b i)) := by
  haveI : Nonempty ↥(conservationClass K) := ⟨⟨allA K, allA_mem K⟩⟩
  exact N.uRegionMatrix_pow_mulVec_tendsto_of_conservationClass κ (conservationClass_finite K)
    (conservationClassRegion κ K hK) (conservationClass_jumpStronglyConnected κ K hK) x hx

end CRNT.Examples.ConservationClassRegion
