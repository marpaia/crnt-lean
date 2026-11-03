import CRNT.Stochastic.HarrisTheorem
import CRNT.Stochastic.MinimalSemigroupNonExplosion
import CRNT.Stochastic.MinimalSemigroupFoster
import CRNT.Stochastic.MinimalSemigroupErgodicInfinite
import CRNT.Stochastic.RecurrenceDichotomy
import CRNT.Dynamics.StrongEndotacticTier

/-!
# Recurrence from an additional count-tier structure

The explicit `CountTier` structure provides separation and inward-consumption
hypotheses from which a multiplicative count-generator drift is derived. Foster
and Harris results give the stated non-explosion and recurrence consequences,
with the displayed irreducibility hypotheses. These count-tier data are
additional restrictions, not consequences of arbitrary strong endotacticity.
The unrestricted several-species stochastic assertion is false; see
arXiv:1808.05328, Examples 3.1–3.2.
-/

open Filter Topology
open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 1. The count-lattice tier object -/

/-- The **tier potential** of a complex `y` in the direction `w : S → ℝ`: the linear functional
`∑_s w_s y_s`.  Two complexes lie in the same tier iff their tier potentials coincide; `y'` lies
strictly below `y` iff its tier potential is smaller. -/
def countTierPotential (w : S → ℝ) (y : Complex S) : ℝ := complexWValue w y

/-- Two complexes lie in the **same count-lattice tier** for the direction `w`. -/
def IsSameCountTier (w : S → ℝ) (y y' : Complex S) : Prop :=
  countTierPotential w y = countTierPotential w y'

/-- `y'` lies in a **strictly lower count-lattice tier** than `y`. -/
def IsCountTierBelow (w : S → ℝ) (y y' : Complex S) : Prop :=
  countTierPotential w y' < countTierPotential w y

/-- **Count-lattice tier chain.**  The occurring complexes of `N` are linearly ordered by the tier
potential of the direction `w`: the tiers are the level sets of `countTierPotential w`, and they
are totally ordered by it.  This is the count-lattice reading of the deterministic tier structure
of `CRNT.Dynamics.TierPersistence`. -/
def CountTierChain (N : Network S) (w : S → ℝ) : Prop :=
  ∀ y ∈ N.complexes, ∀ y' ∈ N.complexes,
    IsSameCountTier w y y' ∨ IsCountTierBelow w y y' ∨ IsCountTierBelow w y' y

/-- The tier chain of a network exists for every direction: the tier potential is a real number,
so the tier potentials of two complexes are always comparable. -/
theorem countTierChain_of_linear (N : Network S) (w : S → ℝ) : CountTierChain N w := by
  intro y _ y' _
  rcases lt_trichotomy (countTierPotential w y) (countTierPotential w y') with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- The **top tier** of `N` for the direction `w`: the source complexes whose tier potential is
maximal among the reaction sources, i.e. the `w`-maximal face of the Newton polytope. -/
noncomputable def countTierTop (N : Network S) (w : S → ℝ) : Finset (Complex S) :=
  (Finset.univ.image fun r : N.R => (N.reaction r).source).filter
    fun y => ∀ r' : N.R,
      countTierPotential w ((N.reaction r').source) ≤ countTierPotential w y

/-- The source complex of a maximal reaction lies in the top tier. -/
theorem mem_countTierTop_of_isMaxSource {N : Network S} {w : S → ℝ} {r : N.R}
    (hmax : N.IsMaxSource w r) : (N.reaction r).source ∈ N.countTierTop w := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩, ?_⟩
  intro r'
  show countTierPotential w ((N.reaction r').source) ≤
      countTierPotential w ((N.reaction r).source)
  rw [countTierPotential, countTierPotential, ← N.wValue_eq_complexWValue_source,
    ← N.wValue_eq_complexWValue_source]
  exact hmax r'

/-- **Top-tier descent.**  The reactions whose source complex lies in the top tier — the
`w`-maximal face — do not ascend the tier potential, and at least one of them descends strictly.
This is the count-lattice analogue of the deterministic tier descent. -/
def CountTierDescent (N : Network S) (w : S → ℝ) : Prop :=
  (∀ r : N.R, N.IsMaxSource w r → N.wRate w r ≤ 0) ∧
    (∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0)

/-- **Bridge to the repository's strong endotacticity.**  If `N` is strongly endotactic in the
standard sense, then in every stoichiometrically active direction the count-lattice tier descent
holds: the `w`-maximal sources are exactly the top tier of `w`, strong endotacticity says that no
reaction out of that face ascends the tier potential, and that some reaction of that face
descends it strictly. -/
theorem countTierDescent_of_stronglyEndotacticStd {N : Network S}
    (h : N.StronglyEndotacticStd) {w : S → ℝ} (hw : N.StoichActiveDirection w) :
    N.CountTierDescent w :=
  ⟨fun r hmax => h.1 w r hmax, h.2 w hw⟩

/-- The count-lattice tier structure of a network `N`.

* `w` is the **tier weight**: a strictly positive direction whose level sets on the complexes are
  the tiers of the network;
* `chain` is the tier chain of the occurring complexes;
* `descent` is the top-tier descent;
* `inflow` is the **tier separation of the ascending reactions**: a reaction that ascends the
  tier potential has the zero source complex, so its propensity is the constant `κ_r`, independent
  of the count;
* `coverage` says that every species is consumed by a strictly descending top-tier reaction
  supported on that species alone: the inward drift is then felt in every coordinate of the count
  lattice. -/
structure CountTier (N : Network S) where
  /-- The tier weight. -/
  w : S → ℝ
  /-- The tier weight is strictly positive. -/
  hw : ∀ s, 0 < w s
  /-- The tier chain of the occurring complexes. -/
  chain : CountTierChain N w
  /-- The top tier does not ascend, and descends strictly in at least one reaction. -/
  descent : CountTierDescent N w
  /-- Every ascending reaction has the zero source complex. -/
  inflow : ∀ r : N.R, N.wRate w r > 0 → ∀ s, (N.reaction r).source s = 0
  /-- Every species is consumed by a strictly descending top-tier reaction supported on it. -/
  coverage : ∀ s, ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0 ∧
    (N.reaction r).source s ≠ 0 ∧ ∀ t, t ≠ s → (N.reaction r).source t = 0

/-- The tier structure of a network forces the species type to be inhabited: with no species the
tier potential of every complex vanishes and the top tier cannot descend strictly. -/
theorem CountTier.nonempty_species {N : Network S} (T : CountTier N) : Nonempty S := by
  by_contra h
  have hnot : ¬ (Finset.univ : Finset S).Nonempty := by
    rintro ⟨a, ha⟩
    exact h ⟨a⟩
  have hU : (Finset.univ : Finset S) = ∅ :=
    (Finset.not_nonempty_iff_eq_empty (s := (Finset.univ : Finset S))).mp hnot
  obtain ⟨r, _, hneg⟩ := T.descent.2
  have hzero : N.wRate T.w r = 0 := by
    unfold Network.wRate Network.dotProduct
    rw [hU, Finset.sum_empty]
  linarith

/-- The strictly descending top-tier reaction that consumes the species `s`. -/
noncomputable def CountTier.inwardReaction {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (T : CountTier N) (s : S) : N.R :=
  Classical.choose (T.coverage s)

/-- The specification of the inward reaction of a species. -/
theorem CountTier.inwardReaction_spec {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (T : CountTier N) (s : S) :
    N.IsMaxSource T.w (T.inwardReaction s) ∧ N.wRate T.w (T.inwardReaction s) < 0 ∧
      (N.reaction (T.inwardReaction s)).source s ≠ 0 ∧
      ∀ t, t ≠ s → (N.reaction (T.inwardReaction s)).source t = 0 :=
  Classical.choose_spec (T.coverage s)

/-- The number of molecules of `s` consumed by the inward reaction of `s`. -/
noncomputable def CountTier.inwardMol {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (T : CountTier N) (s : S) : ℕ :=
  (N.reaction (T.inwardReaction s)).source s

/-- The inward reaction of `s` consumes at least one molecule of `s`. -/
theorem CountTier.inwardMol_pos {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (T : CountTier N) (s : S) : 0 < T.inwardMol s :=
  Nat.pos_of_ne_zero (T.inwardReaction_spec s).2.2.1

/-- The **inward drift weight** of the species `s`: the rate constant of the inward reaction
times the size of its tier drop. -/
noncomputable def CountTier.inwardWeight {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (T : CountTier N) (κ : N.RateConstants) (s : S) : ℝ :=
  κ.k (T.inwardReaction s) * |N.wRate T.w (T.inwardReaction s)|

/-- The inward drift weight of a species is strictly positive. -/
theorem CountTier.inwardWeight_pos {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (T : CountTier N) (κ : N.RateConstants) (s : S) :
    0 < T.inwardWeight κ s := by
  unfold CountTier.inwardWeight
  exact mul_pos (κ.positive (T.inwardReaction s))
    (abs_pos.mpr (ne_of_lt (T.inwardReaction_spec s).2.1))

/-- The inward reactions of two distinct species are distinct: they have different source
complexes. -/
theorem CountTier.inwardReaction_ne {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (T : CountTier N) {s t : S} (hst : s ≠ t) :
    T.inwardReaction s ≠ T.inwardReaction t := by
  intro h
  have hsrc : (N.reaction (T.inwardReaction s)).source =
      (N.reaction (T.inwardReaction t)).source := by rw [h]
  have hzero : (N.reaction (T.inwardReaction t)).source s = 0 :=
    (T.inwardReaction_spec t).2.2.2 s hst
  have hne : (N.reaction (T.inwardReaction s)).source s ≠ 0 :=
    (T.inwardReaction_spec s).2.2.1
  rw [hsrc, hzero] at hne
  exact absurd hne (by simp)

/-- The inward reaction of `s` is a strictly descending reaction. -/
theorem CountTier.inwardReaction_descending {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (T : CountTier N) (s : S) :
    N.wRate T.w (T.inwardReaction s) < 0 :=
  (T.inwardReaction_spec s).2.1

/-! ## 2. Falling-factorial estimates -/

/-- The falling factorial `n.descFactorial k` dominates `n` as soon as `1 ≤ k ≤ n`. -/
theorem nat_descFactorial_ge_self : ∀ {n k : ℕ}, 1 ≤ k → k ≤ n → n ≤ n.descFactorial k := by
  intro n k
  induction k with
  | zero => omega
  | succ k ih =>
      intro hk hkn
      rw [Nat.descFactorial_succ]
      by_cases hk0 : k = 0
      · subst hk0
        simp
      · have hk1 : 1 ≤ k := by omega
        have hkn' : k ≤ n := by omega
        have h1 := ih hk1 hkn'
        have h2 : 1 ≤ n - k := by omega
        calc n = 1 * n := by ring
          _ ≤ (n - k) * n := by exact mul_le_mul_of_nonneg_right h2 (by positivity)
          _ ≤ (n - k) * n.descFactorial k := by
                exact mul_le_mul_of_nonneg_left h1 (by omega)
          _ = n.descFactorial (k + 1) := by rw [Nat.descFactorial_succ]

/-- The propensity of a reaction whose source complex is supported on the single species `s` is
the rate constant times the falling factorial of the count of `s`.  This is the exact
count-lattice counterpart of the mass-action monomial `x^{source}` of a complex supported on
`s`. -/
theorem stochasticMassActionRate_eq_descFactorial (N : Network S) (κ : RateConstants N)
    (n : S → ℕ) (r : N.R) (s : S) (hs : ∀ t, t ≠ s → (N.reaction r).source t = 0) :
    N.stochasticMassActionRate κ n r =
      κ.k r * ((n s).descFactorial ((N.reaction r).source s) : ℝ) := by
  have hprod : (∏ t : S, ((n t).descFactorial ((N.reaction r).source t) : ℝ)) =
      ((n s).descFactorial ((N.reaction r).source s) : ℝ) := by
    refine Finset.prod_eq_single s ?_ ?_
    · intro b _ hbs
      rw [hs b hbs, Nat.descFactorial_zero]
      norm_num
    · intro h
      exact (h (Finset.mem_univ s)).elim
  unfold stochasticMassActionRate
  rw [hprod]

/-- If all the terms of a sum are nonpositive, the sum over a superset is at most the sum over a
subset: the omitted terms are nonpositive. -/
private theorem sum_le_sum_of_subset_of_nonpos {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (A B : Finset ι) (hBA : B ⊆ A) (hf : ∀ i ∈ A, f i ≤ 0) :
    ∑ i ∈ A, f i ≤ ∑ i ∈ B, f i := by
  classical
  have hfilter : A.filter (fun i => i ∈ B) = B := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hBA h, h⟩
  have hsplit : (∑ i ∈ A, f i) = (∑ i ∈ A.filter (fun i => i ∈ B), f i) +
      (∑ i ∈ A.filter (fun i => i ∉ B), f i) :=
    (Finset.sum_filter_add_sum_filter_not A (fun i => i ∈ B) f).symm
  rw [hsplit, hfilter]
  have hrest : (∑ i ∈ A.filter (fun i => i ∉ B), f i) ≤ 0 :=
    Finset.sum_nonpos fun i hi => hf i (Finset.mem_filter.mp hi).1
  linarith

/-! ## 3. The count-lattice tier drift -/

set_option linter.unusedVariables false in
/-- The count-lattice tier Lyapunov function: the tier weight of the count vector.  It is the
extension of the deterministic tier function to the count lattice. -/
noncomputable def CountLyapunov {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (T : CountTier N) : ((S → ℕ) → ℝ) :=
  linearObservable T.w

/-- The count-lattice tier Lyapunov function is nonnegative. -/
theorem countLyapunov_nonneg {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (κ : N.RateConstants) (T : CountTier N) (n : S → ℕ) :
    0 ≤ CountLyapunov N κ T n :=
  linearObservable_nonneg_of_positive T.hw n

/-- The sublevel sets of the count-lattice tier Lyapunov function are finite. -/
theorem countLyapunov_finiteSublevel {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (κ : N.RateConstants) (T : CountTier N) (R : ℝ) :
    {n | CountLyapunov N κ T n ≤ R}.Finite :=
  finite_linearObservable_le T.w T.hw R

/-- **The multiplicative Foster--Lyapunov drift of the count-lattice tier Lyapunov function.**

The drift of the tier Lyapunov function along the stochastic mass-action chain satisfies

`Q V (n) ≤ -ε · V (n) + K`   with `ε > 0` and `K ≥ 0`.

This is the heart of the deterministic-to-stochastic transfer: the ascending reactions of the tier
structure contribute the constant `K₀` (their propensity does not depend on the count), while the
strictly descending reaction of the top tier that consumes the species `s` contributes at most
`-β_s · (n s)` with `β_s > 0`, so the drift decreases along every coordinate of the count
lattice. -/
theorem tierDrift_multiplicative {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (T : CountTier N) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ n : S → ℕ, N.observableGenerator κ (CountLyapunov N κ T) n ≤
        -ε * CountLyapunov N κ T n + K := by
  classical
  set w : S → ℝ := T.w with hwdef
  -- the generator of the tier Lyapunov function
  have hgen : ∀ n : S → ℕ,
      N.observableGenerator κ (linearObservable w) n =
        ∑ r : N.R, N.stochasticMassActionRate κ n r * N.wRate w r := by
    intro n
    rw [N.observableGenerator_linear]
    apply Finset.sum_congr rfl
    intro r _
    rw [N.wRate_eq]
    have h : (∑ s : S, w s * N.reactionVector r s) =
        ∑ s : S, w s * (((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Network.reactionVector_apply]
    rw [h]
  -- the termwise bound: an ascending reaction has a count-independent propensity, a descending
  -- one contributes a nonpositive amount
  have hterm : ∀ (n : S → ℕ) (r : N.R),
      N.stochasticMassActionRate κ n r * N.wRate w r =
        (if 0 < N.wRate w r then κ.k r * N.wRate w r else 0) +
          (if N.wRate w r < 0 then N.stochasticMassActionRate κ n r * N.wRate w r else 0) := by
    intro n r
    by_cases h1 : 0 < N.wRate w r
    · have h2 : ¬ (N.wRate w r < 0) := by linarith
      rw [ite_eq_left h1, ite_eq_right h2]
      have hsrc : ∀ s, (N.reaction r).source s = 0 := T.inflow r h1
      have hrate : N.stochasticMassActionRate κ n r = κ.k r := by
        unfold stochasticMassActionRate
        have hprod : (∏ s : S, ((n s).descFactorial ((N.reaction r).source s) : ℝ)) = 1 := by
          apply Finset.prod_eq_one
          intro s _
          rw [hsrc s, Nat.descFactorial_zero]
          norm_num
        rw [hprod]
        simp
      rw [hrate]
      linarith
    · by_cases h2 : N.wRate w r < 0
      · rw [ite_eq_right h1, ite_eq_left h2]
        ring
      · rw [ite_eq_right h1, ite_eq_right h2]
        have hc0 : N.wRate w r = 0 := by linarith
        rw [hc0, mul_zero]
        ring
  -- splitting the drift sum into the ascending, zero and descending reactions
  have hsplit : ∀ (n : S → ℕ),
      (∑ r : N.R, N.stochasticMassActionRate κ n r * N.wRate w r) =
        (∑ r : N.R, (if 0 < N.wRate w r then κ.k r * N.wRate w r else 0)) +
          (∑ r : N.R, (if N.wRate w r < 0 then
              N.stochasticMassActionRate κ n r * N.wRate w r else 0)) := by
    intro n
    calc (∑ r : N.R, N.stochasticMassActionRate κ n r * N.wRate w r)
        = ∑ r : N.R, (N.stochasticMassActionRate κ n r * N.wRate w r) := rfl
      _ = ∑ r : N.R, ((if 0 < N.wRate w r then κ.k r * N.wRate w r else 0) +
            (if N.wRate w r < 0 then
              N.stochasticMassActionRate κ n r * N.wRate w r else 0)) := by
            apply Finset.sum_congr rfl
            intro r _
            exact hterm n r
      _ = (∑ r : N.R, (if 0 < N.wRate w r then κ.k r * N.wRate w r else 0)) +
            (∑ r : N.R, (if N.wRate w r < 0 then
              N.stochasticMassActionRate κ n r * N.wRate w r else 0)) := by
            rw [Finset.sum_add_distrib]
  -- the ascending reactions contribute the constant `K₀`
  have hasc : ∀ (n : S → ℕ),
      (∑ r : N.R, (if 0 < N.wRate w r then κ.k r * N.wRate w r else 0)) =
        ∑ r ∈ (Finset.univ.filter fun r : N.R => 0 < N.wRate w r), κ.k r * N.wRate w r := by
    intro n
    rw [(Finset.sum_filter (fun r : N.R => 0 < N.wRate w r)
      (fun r : N.R => κ.k r * N.wRate w r)).symm]
  have hK0 : 0 ≤ ∑ r ∈ (Finset.univ.filter fun r : N.R => 0 < N.wRate w r),
      κ.k r * N.wRate w r :=
    Finset.sum_nonneg fun r hr => by
      have h1 := (Finset.mem_filter.mp hr).2
      exact mul_nonneg (κ.positive r).le h1.le
  -- the descending reactions are dominated by the inward reactions
  have himg : (Finset.univ.image fun s : S => T.inwardReaction s : Finset N.R) ⊆
      Finset.univ.filter fun r : N.R => N.wRate w r < 0 := by
    intro r hr
    have hmem : r ∈ Finset.univ.image (fun s : S => T.inwardReaction s) := hr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hmem
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ (T.inwardReaction s), T.inwardReaction_descending s⟩
  have hinj : Set.InjOn (fun s : S => T.inwardReaction s) ((Finset.univ : Finset S) : Set S) := by
    intro a b _ _ hab
    by_contra h
    exact (T.inwardReaction_ne h) hab
  -- the per-species contribution of the inward reaction
  have hspec : ∀ (n : S → ℕ) (s : S),
      N.stochasticMassActionRate κ n (T.inwardReaction s) * N.wRate w (T.inwardReaction s) ≤
        -T.inwardWeight κ s * (n s : ℝ) +
          T.inwardWeight κ s * ((T.inwardMol s : ℝ) - 1) := by
    intro n s
    have hdesc : N.wRate w (T.inwardReaction s) < 0 := T.inwardReaction_descending s
    have hsrc' : ∀ t, t ≠ s → (N.reaction (T.inwardReaction s)).source t = 0 :=
      (T.inwardReaction_spec s).2.2.2
    have hrate : N.stochasticMassActionRate κ n (T.inwardReaction s) =
        κ.k (T.inwardReaction s) *
          ((n s).descFactorial (T.inwardMol s) : ℝ) :=
      stochasticMassActionRate_eq_descFactorial N κ n (T.inwardReaction s) s hsrc'
    have habs : |N.wRate w (T.inwardReaction s)| = -N.wRate w (T.inwardReaction s) :=
      abs_of_nonpos hdesc.le
    have hβ : T.inwardWeight κ s =
        κ.k (T.inwardReaction s) * (-N.wRate w (T.inwardReaction s)) := by
      unfold CountTier.inwardWeight
      rw [habs]
    rw [hrate]
    by_cases hkn : T.inwardMol s ≤ n s
    · have hd : (n s : ℝ) ≤ ((n s).descFactorial (T.inwardMol s) : ℝ) := by
        have h1 : 1 ≤ T.inwardMol s := T.inwardMol_pos s
        exact_mod_cast nat_descFactorial_ge_self h1 hkn
      have h1 : ((n s).descFactorial (T.inwardMol s) : ℝ) * N.wRate w (T.inwardReaction s) ≤
          (n s : ℝ) * N.wRate w (T.inwardReaction s) :=
        mul_le_mul_of_nonpos_right hd hdesc.le
      have h2 : κ.k (T.inwardReaction s) *
            ((n s).descFactorial (T.inwardMol s) : ℝ) * N.wRate w (T.inwardReaction s) ≤
          κ.k (T.inwardReaction s) * (n s : ℝ) * N.wRate w (T.inwardReaction s) := by
        have hz := mul_le_mul_of_nonneg_left h1 (κ.positive (T.inwardReaction s)).le
        have hz' : κ.k (T.inwardReaction s) *
              (((n s).descFactorial (T.inwardMol s) : ℝ) * N.wRate w (T.inwardReaction s)) ≤
            κ.k (T.inwardReaction s) * ((n s : ℝ) * N.wRate w (T.inwardReaction s)) := hz
        simpa [mul_assoc] using hz'
      have h3 : κ.k (T.inwardReaction s) * (n s : ℝ) * N.wRate w (T.inwardReaction s) =
          -T.inwardWeight κ s * (n s : ℝ) := by
        rw [hβ]
        ring
      have h4 : 0 ≤ T.inwardWeight κ s * ((T.inwardMol s : ℝ) - 1) := by
        have hp := T.inwardWeight_pos κ s
        have hk : (1 : ℝ) ≤ (T.inwardMol s : ℝ) := by
          exact_mod_cast T.inwardMol_pos s
        exact mul_nonneg hp.le (by linarith)
      linarith
    · have hz : ((n s).descFactorial (T.inwardMol s) : ℝ) = 0 := by
        have h1 : (n s).descFactorial (T.inwardMol s) = 0 :=
          (Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)
        exact_mod_cast h1
      have hp : 0 < T.inwardWeight κ s := T.inwardWeight_pos κ s
      have hk : (n s : ℝ) ≤ (T.inwardMol s : ℝ) - 1 := by
        have h1 : n s + 1 ≤ T.inwardMol s := by omega
        have h2 : ((n s + 1 : ℕ) : ℝ) ≤ (T.inwardMol s : ℝ) := by exact_mod_cast h1
        rw [Nat.cast_add, Nat.cast_one] at h2
        linarith
      rw [hz, mul_zero]
      have : 0 ≤ T.inwardWeight κ s * ((T.inwardMol s : ℝ) - 1 - (n s : ℝ)) := by
        exact mul_nonneg hp.le (by linarith)
      linarith
  -- the descending sum is bounded by the sum of the inward contributions
  have hdesc (n : S → ℕ) :
      (∑ r : N.R, (if N.wRate w r < 0 then
          N.stochasticMassActionRate κ n r * N.wRate w r else 0)) ≤
        ∑ s : S, (N.stochasticMassActionRate κ n (T.inwardReaction s) *
          N.wRate w (T.inwardReaction s)) := by
    rw [(Finset.sum_filter (fun r : N.R => N.wRate w r < 0)
      (fun r : N.R => N.stochasticMassActionRate κ n r * N.wRate w r)).symm]
    have h1 : (∑ r ∈ (Finset.univ.filter fun r : N.R => N.wRate w r < 0),
          N.stochasticMassActionRate κ n r * N.wRate w r) ≤
        ∑ r ∈ (Finset.univ.image fun s : S => T.inwardReaction s),
          N.stochasticMassActionRate κ n r * N.wRate w r := by
      refine sum_le_sum_of_subset_of_nonpos
        (fun r : N.R => N.stochasticMassActionRate κ n r * N.wRate w r)
        (Finset.univ.filter fun r : N.R => N.wRate w r < 0)
        (Finset.univ.image fun s : S => T.inwardReaction s) himg ?_
      intro r hr
      have hc : N.wRate w r < 0 := (Finset.mem_filter.mp hr).2
      exact mul_nonpos_of_nonneg_of_nonpos (N.stochasticMassActionRate_nonneg κ n r) hc.le
    have h2 : (∑ r ∈ (Finset.univ.image fun s : S => T.inwardReaction s),
          N.stochasticMassActionRate κ n r * N.wRate w r) =
        ∑ s : S, (N.stochasticMassActionRate κ n (T.inwardReaction s) *
          N.wRate w (T.inwardReaction s)) := by
      exact Finset.sum_image hinj
    linarith
  -- the multiplicative coefficient
  obtain ⟨s0⟩ := T.nonempty_species
  have hvalsne :
      ((Finset.univ : Finset S).image (fun s : S => T.inwardWeight κ s / w s)).Nonempty := by
    refine ⟨T.inwardWeight κ s0 / w s0, ?_⟩
    exact Finset.mem_image.mpr ⟨s0, Finset.mem_univ s0, rfl⟩
  set ε : ℝ :=
    ((Finset.univ : Finset S).image (fun s : S => T.inwardWeight κ s / w s)).min' hvalsne
    with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    have hmem := Finset.min'_mem _ hvalsne
    obtain ⟨b, hb, hfb⟩ := Finset.mem_image.mp hmem
    have heq : ((Finset.univ : Finset S).image (fun t : S => T.inwardWeight κ t / w t)).min' hvalsne
        = T.inwardWeight κ b / w b := hfb.symm
    rw [heq]
    exact div_pos (T.inwardWeight_pos κ b) (T.hw b)
  have hεle : ∀ s : S, ε ≤ T.inwardWeight κ s / w s := by
    intro s
    rw [hεdef]
    exact Finset.min'_le _ (T.inwardWeight κ s / w s)
      (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩)
  have hεw : ∀ s : S, ε * w s ≤ T.inwardWeight κ s := by
    intro s
    have h1 : ε * w s ≤ (T.inwardWeight κ s / w s) * w s :=
      mul_le_mul_of_nonneg_right (hεle s) (T.hw s).le
    have h2 : (T.inwardWeight κ s / w s) * w s = T.inwardWeight κ s :=
      div_mul_cancel₀ _ (ne_of_gt (T.hw s))
    linarith
  -- the constant
  set K1 : ℝ := ∑ s : S, T.inwardWeight κ s * ((T.inwardMol s : ℝ) - 1) with hK1def
  have hK1 : 0 ≤ K1 := by
    rw [hK1def]
    exact Finset.sum_nonneg fun s _ => by
      have hp := T.inwardWeight_pos κ s
      have hk : (1 : ℝ) ≤ (T.inwardMol s : ℝ) := by exact_mod_cast T.inwardMol_pos s
      exact mul_nonneg hp.le (by linarith)
  refine ⟨ε, hεpos, ∑ r ∈ (Finset.univ.filter fun r : N.R => 0 < N.wRate w r),
      κ.k r * N.wRate w r + K1, ?_, ?_⟩
  · exact add_nonneg hK0 hK1
  · intro n
    have hV : CountLyapunov N κ T = linearObservable w := by
      simp [CountLyapunov, hwdef]
    rw [hV, hgen]
    have h1 : (∑ r : N.R, N.stochasticMassActionRate κ n r * N.wRate w r) ≤
        (∑ r ∈ (Finset.univ.filter fun r : N.R => 0 < N.wRate w r), κ.k r * N.wRate w r) +
          (∑ s : S, (N.stochasticMassActionRate κ n (T.inwardReaction s) *
            N.wRate w (T.inwardReaction s))) := by
      calc (∑ r : N.R, N.stochasticMassActionRate κ n r * N.wRate w r)
          = (∑ r : N.R, (if 0 < N.wRate w r then κ.k r * N.wRate w r else 0)) +
              (∑ r : N.R, (if N.wRate w r < 0 then
                N.stochasticMassActionRate κ n r * N.wRate w r else 0)) := hsplit n
        _ ≤ (∑ r : N.R, (if 0 < N.wRate w r then κ.k r * N.wRate w r else 0)) +
              (∑ s : S, (N.stochasticMassActionRate κ n (T.inwardReaction s) *
                N.wRate w (T.inwardReaction s))) :=
          add_le_add_right (hdesc n)
            (∑ r : N.R, (if 0 < N.wRate w r then κ.k r * N.wRate w r else 0))
        _ = (∑ r ∈ (Finset.univ.filter fun r : N.R => 0 < N.wRate w r), κ.k r * N.wRate w r) +
              (∑ s : S, (N.stochasticMassActionRate κ n (T.inwardReaction s) *
                N.wRate w (T.inwardReaction s))) := by rw [hasc n]
    have h2 : (∑ s : S, (N.stochasticMassActionRate κ n (T.inwardReaction s) *
          N.wRate w (T.inwardReaction s))) ≤
        ∑ s : S, (-T.inwardWeight κ s * (n s : ℝ) +
          T.inwardWeight κ s * ((T.inwardMol s : ℝ) - 1)) :=
      Finset.sum_le_sum fun s _ => hspec n s
    have h3 : (∑ s : S, (-T.inwardWeight κ s * (n s : ℝ) +
          T.inwardWeight κ s * ((T.inwardMol s : ℝ) - 1))) =
        -∑ s : S, T.inwardWeight κ s * (n s : ℝ) + K1 := by
      rw [Finset.sum_add_distrib, hK1def]
      have hneg : (∑ s : S, -T.inwardWeight κ s * (n s : ℝ)) =
          -∑ s : S, T.inwardWeight κ s * (n s : ℝ) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro s _
        ring
      rw [hneg]
    have h4 : ε * (∑ s : S, w s * (n s : ℝ)) ≤ ∑ s : S, T.inwardWeight κ s * (n s : ℝ) := by
      have hnonneg : ∀ s : S, 0 ≤ (n s : ℝ) := fun s => Nat.cast_nonneg _
      calc ε * (∑ s : S, w s * (n s : ℝ)) = ∑ s : S, ε * (w s * (n s : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ s : S, (ε * (w s * (n s : ℝ)) +
              (T.inwardWeight κ s - ε * w s) * (n s : ℝ)) := by
            apply Finset.sum_le_sum
            intro s _
            exact le_add_of_nonneg_right (mul_nonneg (by linarith [hεw s]) (hnonneg s))
        _ = ∑ s : S, T.inwardWeight κ s * (n s : ℝ) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
    have hVsum : linearObservable w n = ∑ s : S, w s * (n s : ℝ) := by
      simp [linearObservable]
    rw [hVsum]
    linarith


/-! ## 4. The Anderson--Cappelletti--Kim--Nguyen drift condition -/

/-- A **count-lattice tier drift certificate**: a count-lattice Lyapunov function `V` with
nonnegative values, finite sublevel sets, and a *constant* negative drift outside a finite set of
counts.  This is the drift condition of the Anderson--Cappelletti--Kim--Nguyen theorem. -/
structure CountTierDrift {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (κ : N.RateConstants) where
  /-- The count-lattice Lyapunov function. -/
  V : (S → ℕ) → ℝ
  /-- Nonnegativity. -/
  hV : ∀ n, 0 ≤ V n
  /-- Finite sublevel sets. -/
  hfinV : ∀ R : ℝ, {n | V n ≤ R}.Finite
  /-- The drift constant. -/
  c : ℝ
  /-- The drift constant is positive. -/
  hc : 0 < c
  /-- The exceptional set of counts. -/
  C : Set (S → ℕ)
  /-- The exceptional set is finite. -/
  hC : C.Finite
  /-- Outside the exceptional set the drift is at most `-c`. -/
  hdrift : ∀ n, n ∉ C → N.observableGenerator κ V n ≤ -c

/-- **The count-lattice tier drift.**  The tier Lyapunov function of a network carrying a
count-lattice tier structure satisfies the Anderson--Cappelletti--Kim--Nguyen drift condition:
a constant negative drift outside a finite set of counts. -/
theorem tierDrift_le {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (T : CountTier N) :
    ∃ D : CountTierDrift N κ, D.V = CountLyapunov N κ T := by
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierDrift_multiplicative N κ T
  refine ⟨{ V := CountLyapunov N κ T
            hV := countLyapunov_nonneg κ T
            hfinV := countLyapunov_finiteSublevel κ T
            c := 1
            hc := one_pos
            C := {n | CountLyapunov N κ T n ≤ (K + 1) / ε}
            hC := countLyapunov_finiteSublevel κ T _
            hdrift := ?_ }, rfl⟩
  intro n hn
  have hV : (K + 1) / ε < CountLyapunov N κ T n := by
    simpa [Set.mem_ofPred_eq] using hn
  have hεV : K + 1 < ε * CountLyapunov N κ T n := by
    have h := (div_lt_iff₀ hε).mp hV
    linarith
  have h := hdrift n
  linarith

/-- **The count-lattice tier drift, in set form.**  The tier Lyapunov function is nonnegative, has
finite sublevel sets, and its drift is bounded above by `-c` outside a finite set of counts. -/
theorem tierDrift_le_of {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (T : CountTier N) :
    ∃ V : (S → ℕ) → ℝ, (∀ n, 0 ≤ V n) ∧ (∀ R : ℝ, {n | V n ≤ R}.Finite) ∧
      ∃ C : Set (S → ℕ), C.Finite ∧ ∃ c : ℝ, 0 < c ∧
        ∀ n ∉ C, N.observableGenerator κ V n ≤ -c := by
  obtain ⟨D, hD⟩ := tierDrift_le N κ T
  refine ⟨D.V, D.hV, D.hfinV, D.C, D.hC, D.c, D.hc, ?_⟩
  intro n hn
  have hmem' : n ∉ D.C := fun h => hn h
  have h1 := D.hdrift n hmem'
  exact hD ▸ h1

/-! ## 5. The generator is the drift of the jump system, and non-explosion -/

/-- **The observable generator is the drift of the jump system.**  The backward generator of the
stochastic mass-action chain coincides with the drift of the embedded jump system. -/
theorem observableGenerator_eq_jumpSystem_drift {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (V : (S → ℕ) → ℝ) (n : S → ℕ) :
    N.observableGenerator κ V n = (N.jumpSystem κ).drift V n := by
  have h1 : (N.jumpSystem κ).drift V n =
      ∑ r : N.R, N.stochasticMassActionRate κ n r * (V (N.jumpNextCount n r) - V n) := by
    show ∑ r : N.R, N.stochasticMassActionRate κ n r * (V (N.jumpNextCount n r) - V n) = _
    rfl
  rw [h1]
  unfold observableGenerator
  apply Finset.sum_congr rfl
  intro r _
  by_cases hen : N.Enabled n r
  · have hfire : N.fireCount n r = N.jumpNextCount n r := by
      unfold fireCount jumpNextCount
      rw [dite_eq_left hen]
    rw [hfire]
  · rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen]
    simp

/-- **Non-explosion of a tier-structured network.**  The minimal transition function of the
stochastic mass-action chain is stochastic: the chain makes only finitely many jumps in a finite
time interval. -/
theorem tier_nonExplosion {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (T : CountTier N)
    {t : ℝ} (ht : 0 ≤ t) (n : S → ℕ) :
    HasSum (fun m => N.transition κ t n m) 1 := by
  classical
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierDrift_multiplicative N κ T
  have hV : ∀ m : S → ℕ, 0 ≤ CountLyapunov N κ T m := countLyapunov_nonneg κ T
  refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (CountLyapunov N κ T) hV
    (countLyapunov_finiteSublevel κ T) (le_refl 0) hK (fun m => ?_) ht n
  rw [← N.observableGenerator_eq_jumpSystem_drift κ (CountLyapunov N κ T) m]
  have h := hdrift m
  have := mul_nonneg hε.le (hV m)
  linarith

/-! ## 6. Foster's criterion: hitting times and absorption -/

/-- **Foster's criterion for the tier-structured chain.**  Under the count-lattice tier drift
condition, the chain enters the finite set of exceptional counts with probability one, and the
expected time of entry is bounded by `V (a) / (c t)` after time `t`.

This is the *continuous-time* Foster criterion of `CRNT.Stochastic.MinimalSemigroupFoster`
(`JumpSystem.notAbsorbed_le`, `JumpSystem.tendsto_absorbed_one`); the embedded-jump-chain
version (`CRNT.Network.jumpChain_foster_hitting_time`) would need a bounded exit rate, which an
unbounded count lattice does not provide. -/
theorem tierFoster_hitting_time {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (T : CountTier N)
    {c : ℝ} (hc : 0 < c) {C : Set (S → ℕ)} (hC : C.Finite)
    (hdrift : ∀ n, n ∉ C → N.observableGenerator κ (CountLyapunov N κ T) n ≤ -c)
    (a : S → ℕ) :
    (∀ t, 0 < t →
        1 - ∑ b ∈ hC.toFinset, ((N.jumpSystem κ).stopOn hC.toFinset).Pmin t a b ≤
          CountLyapunov N κ T a / (c * t)) ∧
      Tendsto (fun t => ∑ b ∈ hC.toFinset, ((N.jumpSystem κ).stopOn hC.toFinset).Pmin t a b)
        atTop (𝓝 1) := by
  classical
  set CF : Finset (S → ℕ) := hC.toFinset with hCFdef
  have hgen : ∀ n, n ∉ CF → (N.jumpSystem κ).drift (CountLyapunov N κ T) n ≤ -c := by
    intro n hn
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (CountLyapunov N κ T) n]
    apply hdrift n
    intro hmem
    exact hn ((Set.Finite.mem_toFinset hC).mpr hmem)
  refine ⟨fun t ht => ?_, ?_⟩
  · exact (N.jumpSystem κ).notAbsorbed_le CF (CountLyapunov N κ T)
      (countLyapunov_nonneg κ T) (countLyapunov_finiteSublevel κ T) hc hgen ht a
  · exact (N.jumpSystem κ).tendsto_absorbed_one CF (CountLyapunov N κ T)
      (countLyapunov_nonneg κ T) (countLyapunov_finiteSublevel κ T) hc hgen a

/-! ## 7. Positive recurrence -/

/-- **Positive recurrence of a tier-structured network.**  The stochastic mass-action chain of a
network carrying a count-lattice tier structure is *geometrically ergodic*: it has a unique
stationary probability `π` which charges every count, and the chain converges to `π`.  In
particular the probability of being at the starting count converges to the strictly positive
number `π a`. -/
theorem tier_positiveRecurrence {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (T : CountTier N)
    (hirr : ∀ a b : S → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      (∀ b, 0 < π b) ∧
      (∀ a : S → ℕ, Tendsto (fun t => N.transition κ t a a) atTop (𝓝 (π a))) := by
  classical
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierDrift_multiplicative N κ T
  have hV : ∀ n : S → ℕ, 0 ≤ CountLyapunov N κ T n := countLyapunov_nonneg κ T
  have hstoch : ∀ t, 0 ≤ t → ∀ c : S → ℕ, HasSum (fun b => (N.jumpSystem κ).Pmin t c b) 1 := by
    intro t ht c
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (CountLyapunov N κ T) hV
      (countLyapunov_finiteSublevel κ T) (le_refl 0) hK (fun m => ?_) ht c
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (CountLyapunov N κ T) m]
    have h := hdrift m
    have := mul_nonneg hε.le (hV m)
    linarith
  have hfinf : ∀ R : ℝ, {x | ε * CountLyapunov N κ T x ≤ R}.Finite := by
    intro R
    refine (countLyapunov_finiteSublevel κ T (R / ε)).subset fun x hx => ?_
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [le_div_iff₀ hε]
    linarith
  have hdrift' : ∀ x : S → ℕ,
      (N.jumpSystem κ).drift (CountLyapunov N κ T) x ≤
        -(ε * CountLyapunov N κ T x) + K := by
    intro x
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (CountLyapunov N κ T) x]
    have h := hdrift x
    linarith
  obtain ⟨π, hπ0, hπ1, hπinv, hπE, hπpos, hconv, -⟩ :=
    (N.jumpSystem κ).foster_lyapunov_ergodic (CountLyapunov N κ T)
      (fun x => ε * CountLyapunov N κ T x) hV (fun x => mul_nonneg hε.le (hV x)) hfinf hK
      hdrift' hstoch (E := Set.univ) (fun _ _ _ _ => Set.mem_univ _)
      (fun _ _ _ _ => hirr _ _) (Set.mem_univ (fun _ => 0))
  refine ⟨π, hπ0, hπ1, hπinv, fun b => hπpos b (Set.mem_univ b), ?_⟩
  intro a
  have hlim : Tendsto (fun t => (N.jumpSystem κ).Pmin t a a) atTop (𝓝 (π a)) :=
    (N.jumpSystem κ).tendsto_Pmin_of_invariant
      (fun _ _ _ _ => Set.mem_univ _) (fun _ _ _ _ => hirr _ _)
      (fun t ht c _ => hstoch t ht c) hπ0 (fun b h => (h (Set.mem_univ b)).elim) hπ1 hπinv
      (Set.mem_univ a) a
  simpa only [Network.transition] using hlim

/-- **Geometric ergodicity of a tier-structured network.**  The tier-structured chain satisfies the
Meyn--Tweedie `V`-uniform ergodicity estimate with the count-lattice tier Lyapunov function. -/
theorem tier_geometricErgodic {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (T : CountTier N)
    (hirr : ∀ a b : S → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(N.jumpSystem κ).Pmin t a b - π b| * (1 + β * CountLyapunov N κ T b) ≤
          C₀ * (1 + CountLyapunov N κ T a) * ρ ^ ⌊t⌋₊ := by
  classical
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierDrift_multiplicative N κ T
  have hV : ∀ n : S → ℕ, 0 ≤ CountLyapunov N κ T n := countLyapunov_nonneg κ T
  have hstoch : ∀ t, 0 ≤ t → ∀ c : S → ℕ, HasSum (fun b => (N.jumpSystem κ).Pmin t c b) 1 := by
    intro t ht c
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (CountLyapunov N κ T) hV
      (countLyapunov_finiteSublevel κ T) (le_refl 0) hK (fun m => ?_) ht c
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (CountLyapunov N κ T) m]
    have h := hdrift m
    have := mul_nonneg hε.le (hV m)
    linarith
  have hdrift' : ∀ x : S → ℕ,
      (N.jumpSystem κ).drift (CountLyapunov N κ T) x ≤
        -ε * CountLyapunov N κ T x + K := by
    intro x
    rw [← N.observableGenerator_eq_jumpSystem_drift κ (CountLyapunov N κ T) x]
    exact hdrift x
  exact (N.jumpSystem κ).geometric_ergodic (CountLyapunov N κ T) hV
    (countLyapunov_finiteSublevel κ T) hε hK hdrift' hstoch hirr


/-! ## 8. A concrete strongly endotactic instance -/

end Network

namespace Examples
namespace EndotacticTrimerDecay

open Network

/-- The one-species network `0 → X`, `X → 0`, `2X → 0`: a birth channel, a death channel and a
dimer-decay channel.  Its tier structure (for the total-count direction `w = 1`) is genuine: the
top tier is the complex `2X`, of molecularity two, and the reaction `2X → 0` leaves it strictly
downwards; the lower tiers are `X` and `0`. -/
abbrev net : Network (Fin 1) :=
  ⟨Fin 3, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![0], ![1]⟩ else if r = 1 then ⟨![1], ![0]⟩ else ⟨![2], ![0]⟩⟩

/-- The tier potential of the source of the birth channel `0 → X`. -/
theorem wValue_zero (w : Fin 1 → ℝ) : net.wValue w 0 = 0 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]

/-- The tier potential of the source `X` of the death channel. -/
theorem wValue_one (w : Fin 1 → ℝ) : net.wValue w 1 = w 0 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]

/-- The tier potential of the source `2X` of the dimer-decay channel: the top tier. -/
theorem wValue_two (w : Fin 1 → ℝ) : net.wValue w 2 = 2 * w 0 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]; ring

/-- The tier rate of the birth channel `0 → X`: it ascends the tier potential. -/
theorem wRate_zero (w : Fin 1 → ℝ) : net.wRate w 0 = w 0 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]

/-- The tier rate of the death channel `X → 0`: it descends the tier potential. -/
theorem wRate_one (w : Fin 1 → ℝ) : net.wRate w 1 = -w 0 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]

/-- The tier rate of the dimer-decay channel `2X → 0`: it descends the tier potential strictly. -/
theorem wRate_two (w : Fin 1 → ℝ) : net.wRate w 2 = -2 * w 0 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]; ring

/-- **The instance is strongly endotactic.**  For every direction `w` with `w 0 > 0` the top
source is the dimer `2X` and the reaction `2X → 0` descends strictly; for `w 0 < 0` the top
source is the empty complex `0` and the reaction `0 → X` descends strictly; for `w 0 = 0` the
direction is not stoichiometrically active. -/
theorem stronglyEndotacticStd : net.StronglyEndotacticStd := by
  refine ⟨?_, ?_⟩
  · intro w r hmax
    fin_cases r
    · have hA := hmax 1
      simp [Network.wRate, Network.wValue, Network.dotProduct, Network.reactionVector_apply,
        exponentVector] at hA ⊢
      linarith
    · have hA := hmax 0
      simp [Network.wRate, Network.wValue, Network.dotProduct, Network.reactionVector_apply,
        exponentVector] at hA ⊢
      linarith
    · have hA := hmax 1
      simp [Network.wRate, Network.wValue, Network.dotProduct, Network.reactionVector_apply,
        exponentVector] at hA ⊢
      linarith
  · intro w hactive
    by_cases hA : 0 < w 0
    · refine ⟨2, ?_, ?_⟩
      · intro r'
        fin_cases r'
        · simp [Network.wValue, Network.dotProduct, exponentVector]; linarith
        · simp [Network.wValue, Network.dotProduct, exponentVector]; linarith
        · simp [Network.wValue, Network.dotProduct, exponentVector]
      · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]; linarith
    · by_cases hB : w 0 < 0
      · refine ⟨0, ?_, ?_⟩
        · intro r'
          fin_cases r'
          · simp [Network.wValue, Network.dotProduct, exponentVector]
          · simp [Network.wValue, Network.dotProduct, exponentVector]; linarith
          · simp [Network.wValue, Network.dotProduct, exponentVector]; linarith
        · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]; linarith
      · exfalso
        have hw0 : w 0 = 0 := le_antisymm (le_of_not_gt hA) (not_lt.mp hB)
        obtain ⟨r, hr⟩ := hactive
        fin_cases r
        · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, hw0] at hr
        · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, hw0] at hr
        · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, hw0] at hr

/-- **The count-lattice tier structure of the instance.**  The tier weight is the total-count
direction; the top tier is the dimer `2X`, whose reaction `2X → 0` descends strictly; the only
ascending reaction, `0 → X`, has the empty source complex, so its propensity is the constant
`κ₀`; and the species `X` is consumed by the strictly descending top-tier reaction `2X → 0`. -/
noncomputable def countTier : CountTier net where
  w := fun _ => 1
  hw := by intro s; fin_cases s; norm_num
  chain := countTierChain_of_linear net (fun _ => 1)
  descent := countTierDescent_of_stronglyEndotacticStd stronglyEndotacticStd (by
    refine ⟨0, ?_⟩
    simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply])
  inflow := by
    intro r hr s
    fin_cases r
    · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply] at hr
      fin_cases s
      simp
    · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply] at hr
      linarith
    · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply] at hr
      linarith
  coverage := by
    intro s
    fin_cases s
    refine ⟨2, ?_, ?_, ?_, ?_⟩
    · intro r'
      fin_cases r'
      · simp [Network.wValue, Network.dotProduct, exponentVector]
      · simp [Network.wValue, Network.dotProduct, exponentVector]
      · simp [Network.wValue, Network.dotProduct, exponentVector]
    · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
    · simp
    · intro t ht
      fin_cases t
      simp at ht

/-- **Reachability of the instance.**  The embedded jump chain of the instance is irreducible:
from any count one may reach any other count by firing the birth channel and the death channel. -/
theorem reachPos (κ : net.RateConstants) (a b : Fin 1 → ℕ) :
    (net.jumpSystem κ).ReachPos a b := by
  have ha : a = fun _ => a 0 := by funext s; fin_cases s; rfl
  have hb : b = fun _ => b 0 := by funext s; fin_cases s; rfl
  rw [ha, hb]
  have toZero : ∀ m : ℕ, (net.jumpSystem κ).ReachPos (fun _ => m) (fun _ => 0) := by
    intro m
    induction m with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
        have hen : net.Enabled (fun _ => m + 1) (1 : Fin 3) := by
          intro s; fin_cases s; simp
        have hrate : 0 < (net.jumpSystem κ).rate (1 : Fin 3) (fun _ => m + 1) :=
          CRNT.Network.stochasticMassActionRate_pos_of_enabled net κ hen
        have hnext : (net.jumpSystem κ).next (1 : Fin 3) (fun _ => m + 1) = (fun _ => m) := by
          funext s
          fin_cases s
          simp [Network.jumpSystem, Network.jumpNextCount, net]
        exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single ⟨(1 : Fin 3), hrate, hnext.symm⟩) ih
  have fromZero : ∀ n : ℕ, (net.jumpSystem κ).ReachPos (fun _ => 0) (fun _ => n) := by
    intro n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
        have hen : net.Enabled (fun _ => n) (0 : Fin 3) := by
          intro s; fin_cases s; simp
        have hrate : 0 < (net.jumpSystem κ).rate (0 : Fin 3) (fun _ => n) :=
          CRNT.Network.stochasticMassActionRate_pos_of_enabled net κ hen
        have hnext : (net.jumpSystem κ).next (0 : Fin 3) (fun _ => n) = (fun _ => n + 1) := by
          funext s
          fin_cases s
          simp [Network.jumpSystem, Network.jumpNextCount, net]
        exact Relation.ReflTransGen.trans ih
          (Relation.ReflTransGen.single ⟨(0 : Fin 3), hrate, hnext.symm⟩)
  exact Relation.ReflTransGen.trans (toZero (a 0)) (fromZero (b 0))

/-- **Positive recurrence of the instance.**  The stochastic mass-action chain of
`0 → X`, `X → 0`, `2X → 0` is non-explosive and positively recurrent: it has a stationary
probability which charges every count, and the probability of being at the starting count
converges to a strictly positive limit. -/
theorem positiveRecurrence (κ : net.RateConstants) :
    ∃ π : (Fin 1 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (net.jumpSystem κ).Pmin s x b = π b) ∧
      (∀ b, 0 < π b) ∧
      (∀ a : Fin 1 → ℕ, Tendsto (fun t => net.transition κ t a a) atTop (𝓝 (π a))) :=
  tier_positiveRecurrence net κ countTier (fun a b => reachPos κ a b)

/-- **Non-explosion of the instance.** -/
theorem nonExplosion (κ : net.RateConstants) {t : ℝ} (ht : 0 ≤ t) (n : Fin 1 → ℕ) :
    HasSum (fun m => net.transition κ t n m) 1 :=
  tier_nonExplosion net κ countTier ht n

/-- **Geometric ergodicity of the instance.** -/
theorem geometricErgodic (κ : net.RateConstants) :
    ∃ π : (Fin 1 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (net.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(net.jumpSystem κ).Pmin t a b - π b| *
            (1 + β * CountLyapunov net κ countTier b) ≤
          C₀ * (1 + CountLyapunov net κ countTier a) * ρ ^ ⌊t⌋₊ :=
  tier_geometricErgodic net κ countTier (fun a b => reachPos κ a b)

end EndotacticTrimerDecay
end Examples

end CRNT
