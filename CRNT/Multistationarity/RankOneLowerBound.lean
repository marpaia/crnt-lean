import CRNT.Multistationarity.RevRevReaction

/-!
# Lower bounds on the number of steady states of rank-one networks

Let `N` have all reaction vectors multiples of `v` (`reactionVector r = c_r v`) and let `i` be a
species with `v_i ≠ 0`.

* `rankOne_steadyStates_of_signChanges`: if the embedded one-species steady-state polynomial
  `p(u) = ∑_r k_r c_r u^{y_{r,i}}` alternates in sign at `m + 1` increasing positive points, then
  for some rate constants `N` has `m` distinct positive steady states in one compatibility class
  (frozen-species limit, as in `RankOneLifting`).
* `exists_alternating_signs`: for strictly increasing exponents `e₀ < ⋯ < e_m` and alternating
  signs `σ_j`, positive coefficients `a_j` exist such that `∑_j σ_j a_j u^{e_j}` has sign `σ_j` at
  increasing points `u_j` (each new term, with a tiny coefficient, adds one sign change far out).
* `rankOne_steadyStates_of_alternating`: if `m + 1` reactions have strictly increasing source
  coefficients at `i` and alternating multipliers, then `N` has `m` distinct positive steady states
  in one class for some rate constants (a lower bound in the spirit of Descartes' rule; with the
  rule of signs this is sharp for one-species networks).
-/

namespace CRNT

namespace Network

open Filter Topology

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **`m` sign changes lift to `m` steady states.** -/
theorem rankOne_steadyStates_of_signChanges (N : Network S) {v : S → ℝ}
    (c : N.R → ℝ) (hc : ∀ r s, N.reactionVector r s = c r * v s) (i : S) (hvi : v i ≠ 0)
    (k : N.R → ℝ) (hk : ∀ r, 0 < k r) (m : ℕ) {u : ℕ → ℝ} (hu : StrictMono u) (hu0 : 0 < u 0)
    (hsign : ∀ j < m, (∑ r, k r * c r * u j ^ (N.reaction r).source i) *
        (∑ r, k r * c r * u (j + 1) ^ (N.reaction r).source i) < 0) :
    ∃ (κ : RateConstants N) (x₀ : Concentration S) (X : ℕ → Concentration S),
      (∀ j < m, X j ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ (X j)) ∧
        ∀ j < m, ∀ j' < m, X j = X j' → j = j' := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · refine ⟨⟨fun _ => 1, fun _ => one_pos⟩, 0, fun _ => 0, fun j hj => ?_, fun j hj => ?_⟩
    · omega
    · omega
  set p : ℝ → ℝ := fun w => ∑ r, k r * c r * w ^ (N.reaction r).source i with hp
  set t : ℕ → ℝ := fun j => (u j - 1) / v i with ht
  have hut : ∀ j, 1 + t j * v i = u j := fun j => by simp only [ht]; field_simp; ring
  let κM : ℝ → N.R → ℝ := fun M r => k r / ∏ s ∈ Finset.univ.erase i, M ^ (N.reaction r).source s
  let Φ : ℝ → ℝ → ℝ := fun M τ =>
    ∑ r, κM M r * (N.reaction r).source.massActionMonomial (frozenPoint i v M τ) * c r
  -- the frozen limit
  have hlim : ∀ τ, Tendsto (fun M => Φ M τ) atTop (𝓝 (p (1 + τ * v i))) := by
    intro τ
    have hterm : ∀ r, Tendsto (fun M => κM M r *
        (N.reaction r).source.massActionMonomial (frozenPoint i v M τ) * c r) atTop
        (𝓝 (k r * c r * (1 + τ * v i) ^ (N.reaction r).source i)) := by
      intro r
      have hprod : Tendsto (fun M : ℝ => ∏ s ∈ Finset.univ.erase i,
          ((M + τ * v s) / M) ^ (N.reaction r).source s) atTop (𝓝 1) := by
        have := tendsto_finsetProd (Finset.univ.erase i) fun s _ =>
          tendsto_frozen_ratio_pow (τ * v s) ((N.reaction r).source s)
        simpa using this
      have key : ∀ M : ℝ, 0 < M → κM M r *
          (N.reaction r).source.massActionMonomial (frozenPoint i v M τ) * c r =
          k r * (1 + τ * v i) ^ (N.reaction r).source i *
            (∏ s ∈ Finset.univ.erase i, ((M + τ * v s) / M) ^ (N.reaction r).source s) * c r := by
        intro M hM
        have hprodfp : (N.reaction r).source.massActionMonomial (frozenPoint i v M τ) =
            (1 + τ * v i) ^ (N.reaction r).source i *
              ∏ s ∈ Finset.univ.erase i, (M + τ * v s) ^ (N.reaction r).source s := by
          rw [Complex.massActionMonomial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
          congr 1
          · simp [frozenPoint]
          · exact Finset.prod_congr rfl fun s hs => by
              simp [frozenPoint, Finset.ne_of_mem_erase hs]
        have hdiv : ∏ s ∈ Finset.univ.erase i, ((M + τ * v s) / M) ^ (N.reaction r).source s =
            (∏ s ∈ Finset.univ.erase i, (M + τ * v s) ^ (N.reaction r).source s) /
              ∏ s ∈ Finset.univ.erase i, M ^ (N.reaction r).source s := by
          rw [← Finset.prod_div_distrib]
          exact Finset.prod_congr rfl fun s _ => div_pow _ _ _
        have hP : ∏ s ∈ Finset.univ.erase i, M ^ (N.reaction r).source s ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun s _ => pow_ne_zero _ hM.ne'
        simp only [κM]
        rw [hprodfp, hdiv]
        field_simp
      have h := (hprod.const_mul (k r * (1 + τ * v i) ^ (N.reaction r).source i)).mul_const (c r)
      have hval : k r * (1 + τ * v i) ^ (N.reaction r).source i * 1 * c r =
          k r * c r * (1 + τ * v i) ^ (N.reaction r).source i := by ring
      rw [hval] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
      rw [key M hM]
    have := tendsto_finsetSum (Finset.univ : Finset N.R) fun r _ => hterm r
    simpa [hp] using this
  -- choose `M` large
  set T : ℝ := ∑ j ∈ Finset.range (m + 1), |t j| with hT
  set V : ℝ := ∑ s, |v s| + 1 with hV
  have hV0 : 0 < V := by positivity
  obtain ⟨M, hMsign, hMb⟩ : ∃ M : ℝ, (∀ j ∈ Finset.range m, Φ M (t j) * Φ M (t (j + 1)) < 0) ∧
      T * V + 1 < M := by
    have hev : ∀ j ∈ Finset.range m, ∀ᶠ M in atTop, Φ M (t j) * Φ M (t (j + 1)) < 0 := by
      intro j hj
      have e1 := hlim (t j)
      have e2 := hlim (t (j + 1))
      rw [hut] at e1 e2
      exact (e1.mul e2).eventually (gt_mem_nhds (hsign j (Finset.mem_range.mp hj)))
    exact (((eventually_all_finset _).mpr hev).and (eventually_gt_atTop (T * V + 1))).exists
  have hMpos : 0 < M := by
    have : 0 ≤ T * V := mul_nonneg (by positivity) hV0.le
    linarith
  have hcont : Continuous (Φ M) := by
    simp only [Φ, Complex.massActionMonomial, frozenPoint]
    fun_prop
  -- zeros between consecutive sample points, strictly inside
  have hzero : ∀ j < m, ∃ τ, Φ M τ = 0 ∧ τ ∈ Set.uIcc (t j) (t (j + 1)) ∧ τ ≠ t j ∧
      τ ≠ t (j + 1) := by
    intro j hj
    have hab := hMsign j (Finset.mem_range.mpr hj)
    have hmem : (0 : ℝ) ∈ Set.uIcc (Φ M (t j)) (Φ M (t (j + 1))) := by
      rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Set.mem_uIcc.mpr (Or.inr ⟨hb.le, ha.le⟩)
      · exact Set.mem_uIcc.mpr (Or.inl ⟨ha.le, hb.le⟩)
    obtain ⟨τ, hτ, hΦτ⟩ := intermediate_value_uIcc hcont.continuousOn hmem
    refine ⟨τ, hΦτ, hτ, ?_, ?_⟩
    · rintro rfl; rw [hΦτ, zero_mul] at hab; exact lt_irrefl 0 hab
    · rintro rfl; rw [hΦτ, mul_zero] at hab; exact lt_irrefl 0 hab
  choose! τ hτΦ hτmem hτne1 hτne2 using hzero
  -- `t` is strictly monotone (direction given by the sign of `v_i`)
  have htmono : (0 < v i → StrictMono t) ∧ (v i < 0 → StrictAnti t) := by
    constructor
    · intro hv a b hab; simp only [ht]; exact div_lt_div_of_pos_right (by linarith [hu hab]) hv
    · intro hv a b hab; simp only [ht]; exact (div_lt_div_right_of_neg hv).mpr (by linarith [hu hab])
  -- the zeros lie strictly between consecutive sample points
  have hopen : ∀ j < m, (0 < v i → t j < τ j ∧ τ j < t (j + 1)) ∧
      (v i < 0 → t (j + 1) < τ j ∧ τ j < t j) := by
    intro j hj
    have h := Set.mem_uIcc.mp (hτmem j hj)
    have n1 := hτne1 j hj
    have n2 := hτne2 j hj
    constructor
    · intro hv
      have e := htmono.1 hv (show j < j + 1 by omega)
      rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact ⟨lt_of_le_of_ne a1 (Ne.symm n1), lt_of_le_of_ne a2 n2⟩
      · exact absurd e (not_lt.mpr (a1.trans a2))
    · intro hv
      have e := htmono.2 hv (show j < j + 1 by omega)
      rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact absurd e (not_lt.mpr (a1.trans a2))
      · exact ⟨lt_of_le_of_ne a1 (Ne.symm n2), lt_of_le_of_ne a2 n1⟩
  have hτlt : ∀ j < m, ∀ j' < m, j < j' → τ j ≠ τ j' := by
    intro j hj j' hj' hlt heq
    rcases lt_or_gt_of_ne hvi with hv | hv
    · have h1 := ((hopen j hj).2 hv).1
      have h2 := ((hopen j' hj').2 hv).2
      have hle : t j' ≤ t (j + 1) := (htmono.2 hv).antitone (by omega)
      linarith
    · have h1 := ((hopen j hj).1 hv).2
      have h2 := ((hopen j' hj').1 hv).1
      have hle : t (j + 1) ≤ t j' := (htmono.1 hv).monotone (by omega)
      linarith
  have hτinj : ∀ j < m, ∀ j' < m, τ j = τ j' → j = j' := by
    intro j hj j' hj' heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hτlt j hj j' hj' hlt heq
    · exact hτlt j' hj' j hj hlt heq.symm
  -- positivity of the points
  have hpos : ∀ j < m, (frozenPoint i v M (τ j)).Positive := by
    intro j hj s
    have hmem := Set.mem_uIcc.mp (hτmem j hj)
    by_cases hs : s = i
    · subst hs
      simp only [frozenPoint, ↓reduceIte]
      -- `1 + τ v_i` lies between `u j` and `u (j+1)`
      have e1 := hut j
      have e2 := hut (j + 1)
      have hu1 := hu (show j < j + 1 by omega)
      have hu0' : 0 < u j := lt_of_lt_of_le hu0 (hu.monotone (Nat.zero_le j))
      rcases lt_or_gt_of_ne hvi with hv | hv
      · rcases hmem with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          nlinarith [mul_le_mul_of_nonpos_right a1 hv.le, mul_le_mul_of_nonpos_right a2 hv.le]
      · rcases hmem with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          nlinarith [mul_le_mul_of_nonneg_right a1 hv.le, mul_le_mul_of_nonneg_right a2 hv.le]
    · simp only [frozenPoint, hs, ↓reduceIte]
      have hTj : |τ j| ≤ T := by
        have h1 : |t j| ≤ T := Finset.single_le_sum (f := fun j => |t j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
        have h2 : |t (j + 1)| ≤ T := Finset.single_le_sum (f := fun j => |t j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
        rw [abs_le] at h1 h2 ⊢
        rcases hmem with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> constructor <;> linarith
      have hvs : |v s| ≤ V := by
        have := Finset.single_le_sum (f := fun s => |v s|) (fun s _ => abs_nonneg _)
          (Finset.mem_univ s)
        simp only [hV]; linarith
      have : |τ j * v s| ≤ T * V := by
        rw [abs_mul]; exact mul_le_mul hTj hvs (abs_nonneg _) (by positivity)
      have := neg_abs_le (τ j * v s)
      linarith
  -- rate constants and steady states
  have hκpos : ∀ r, 0 < κM M r := fun r =>
    div_pos (hk r) (Finset.prod_pos fun s _ => pow_pos hMpos _)
  let κ : RateConstants N := ⟨κM M, hκpos⟩
  have hsteady : ∀ τ', Φ M τ' = 0 → N.IsMassActionSteadyState κ (frozenPoint i v M τ') := by
    intro τ' hτ' s
    show N.massActionVectorField κ (frozenPoint i v M τ') s = 0
    rw [massActionVectorField_apply]
    have : ∑ r, N.massActionRate κ r (frozenPoint i v M τ') * N.reactionVector r s =
        Φ M τ' * v s := by
      simp only [Φ, Finset.sum_mul, hc, massActionRate]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [this, hτ', zero_mul]
  -- `v` is in the stoichiometric subspace
  obtain ⟨r₀, hr₀⟩ : ∃ r, c r ≠ 0 := by
    by_contra hall
    push Not at hall
    have h := hsign 0 hmpos
    have : ∀ w : ℝ, (∑ r, k r * c r * w ^ (N.reaction r).source i) = 0 := fun w => by
      simp [hall]
    rw [this, zero_mul] at h
    exact lt_irrefl 0 h
  have hvS : v ∈ N.stoichSubspace := by
    have : v = (c r₀)⁻¹ • N.reactionVector r₀ := by
      funext s; rw [Pi.smul_apply, smul_eq_mul, hc]; field_simp
    rw [this]; exact Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r₀)
  refine ⟨κ, frozenPoint i v M (τ 0), fun j => frozenPoint i v M (τ j), fun j hj =>
    ⟨⟨?_, hpos j hj⟩, hsteady _ (hτΦ j hj)⟩, fun j hj j' hj' heq => hτinj j hj j' hj' ?_⟩
  · show frozenPoint i v M (τ j) - frozenPoint i v M (τ 0) ∈ N.stoichSubspace
    have : frozenPoint i v M (τ j) - frozenPoint i v M (τ 0) = (τ j - τ 0) • v := by
      funext s; simp only [frozenPoint, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]; exact Submodule.smul_mem _ _ hvS
  · have := congrFun heq i
    simp only [frozenPoint, ↓reduceIte, add_right_inj] at this
    exact mul_right_cancel₀ hvi this

theorem le_of_chain (e : ℕ → ℕ) : ∀ m : ℕ, (∀ j < m, e j < e (j + 1)) → ∀ l ≤ m, e l ≤ e m := by
  intro m
  induction m with
  | zero => intro _ l hl; rw [show l = 0 by omega]
  | succ n ih =>
    intro he l hl
    rcases Nat.lt_or_ge l (n + 1) with h | h
    · exact (ih (fun j hj => he j (by omega)) l (by omega)).trans (he n (by omega)).le
    · rw [show l = n + 1 by omega]

/-- **Prescribed signs at increasing points.** For exponents increasing on `[0, m]` and any signs
`σ_j ∈ {±1}`, there are positive coefficients `a_j` and increasing positive points `u_j` such that
`q(u) = ∑_{l ≤ m} σ_l a_l u^{e_l}` has sign `σ_j` at `u_j` for every `j ≤ m`. Each new term gets a
coefficient so small that the old signs survive, and dominates far out. -/
theorem exists_prescribed_signs (e : ℕ → ℕ) (σ : ℕ → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) :
    ∀ m : ℕ, (∀ j < m, e j < e (j + 1)) →
      ∃ a : ℕ → ℝ, (∀ j, 0 < a j) ∧ ∃ u : ℕ → ℝ, StrictMono u ∧ 0 < u 0 ∧
        ∀ j ≤ m, 0 < σ j * ∑ l ∈ Finset.range (m + 1), σ l * a l * u j ^ e l := by
  have hσsq : ∀ j, σ j * σ j = 1 := fun j => by rcases hσ j with h | h <;> rw [h] <;> norm_num
  have hσabs : ∀ j, |σ j| = 1 := fun j => by rcases hσ j with h | h <;> rw [h] <;> norm_num
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun _ => 1, fun _ => one_pos, fun j => (j : ℝ) + 1, ?_, by norm_num, fun j hj => ?_⟩
    · intro a b hab; simp only; exact_mod_cast Nat.add_lt_add_right hab 1
    · have : j = 0 := by omega
      subst this
      simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, one_pow,
        mul_one]
      rw [hσsq]; exact one_pos
  | succ m ih =>
    intro he
    obtain ⟨a, ha, u, hu, hu0, hsign⟩ := ih fun j hj => he j (by omega)
    set q : ℝ → ℝ := fun x => ∑ l ∈ Finset.range (m + 1), σ l * a l * x ^ e l with hq
    -- the margin at the old points
    obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ j ≤ m, δ ≤ σ j * q (u j) := by
      obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image (Finset.range (m + 1))
        (fun j => σ j * q (u j)) ⟨0, by simp⟩
      exact ⟨_, hsign j₀ (by simpa [Nat.lt_succ_iff] using hj₀),
        fun j hj => hmin j (by simp; omega)⟩
    set X : ℝ := max 1 (u m) with hX
    have hX1 : 1 ≤ X := le_max_left _ _
    set B : ℝ := X ^ e (m + 1) with hB
    have hB0 : 0 < B := by positivity
    set ε : ℝ := δ / (2 * B) with hε
    have hε0 : 0 < ε := by positivity
    set A : ℝ := ∑ l ∈ Finset.range (m + 1), a l with hA
    have hA0 : 0 < A := Finset.sum_pos (fun l _ => ha l) ⟨0, by simp⟩
    set W : ℝ := A / ε + X + 1 with hW
    -- new data
    refine ⟨fun l => if l = m + 1 then ε else a l, fun l => by
        dsimp only; split_ifs; exacts [hε0, ha l],
      fun j => if j ≤ m then u j else W + j, ?_, ?_, fun j hj => ?_⟩
    · apply strictMono_nat_of_lt_succ
      intro n
      by_cases h1 : n + 1 ≤ m
      · simp only [show n ≤ m by omega, h1, ↓reduceIte]; exact hu (by omega)
      · by_cases h2 : n ≤ m
        · simp only [h2, h1, ↓reduceIte]
          have : n = m := by omega
          subst this
          have : u n ≤ X := le_max_right _ _
          have : 0 ≤ A / ε := by positivity
          have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
          push_cast; linarith
        · simp only [h2, h1, ↓reduceIte]; push_cast; linarith
    · simp only [Nat.zero_le, ↓reduceIte]; exact hu0
    · -- split off the new term
      have hsplit : ∀ x : ℝ, ∑ l ∈ Finset.range (m + 1 + 1),
          σ l * (if l = m + 1 then ε else a l) * x ^ e l =
          q x + σ (m + 1) * ε * x ^ e (m + 1) := by
        intro x
        rw [Finset.sum_range_succ]
        simp only [↓reduceIte, hq]
        congr 1
        exact Finset.sum_congr rfl fun l hl => by
          simp only [show l ≠ m + 1 by simp at hl; omega, ↓reduceIte]
      rw [hsplit]
      by_cases hjm : j ≤ m
      · simp only [hjm, ↓reduceIte]
        have hpos : 0 < u j := lt_of_lt_of_le hu0 (hu.monotone (Nat.zero_le j))
        have hle : u j ^ e (m + 1) ≤ B := by
          apply pow_le_pow_left₀ hpos.le
          exact (hu.monotone hjm).trans (le_max_right _ _)
        have hsm : |σ j * (σ (m + 1) * ε * u j ^ e (m + 1))| ≤ ε * B := by
          rw [abs_mul, abs_mul, abs_mul, hσabs, hσabs, abs_of_pos hε0,
            abs_of_pos (pow_pos hpos _)]
          nlinarith
        have hεB : ε * B = δ / 2 := by rw [hε]; field_simp
        have := neg_abs_le (σ j * (σ (m + 1) * ε * u j ^ e (m + 1)))
        have := hδle j hjm
        nlinarith
      · have hj : j = m + 1 := by omega
        subst hj
        simp only [show ¬ (m + 1 ≤ m) by omega, ↓reduceIte]
        set x : ℝ := W + ((m + 1 : ℕ) : ℝ) with hx
        have hx1 : 1 ≤ x := by
          have : 0 ≤ A / ε := by positivity
          have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
          rw [hx, hW]; linarith
        have hxA : A / ε < x := by
          have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
          rw [hx, hW]; linarith
        -- the old part is at most `A x^{e m}`
        have hold : |q x| ≤ A * x ^ e m := by
          rw [hq, hA, Finset.sum_mul]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
          rw [abs_mul, abs_mul, hσabs, one_mul, abs_of_pos (ha l),
            abs_of_pos (pow_pos (by linarith) _)]
          refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 ?_) (ha l).le
          -- `e l ≤ e m` on `[0, m]`
          have hl' : l ≤ m := by simp at hl; omega
          exact le_of_chain e m (fun j hj => he j (by omega)) l hl'
        have hdom : A * x ^ e m < ε * x ^ e (m + 1) := by
          have hgap : x * x ^ e m ≤ x ^ e (m + 1) := by
            rw [← pow_succ']
            exact pow_le_pow_right₀ hx1 (he m (by omega))
          have hxe : 0 < x ^ e m := pow_pos (by linarith) _
          have : A < ε * x := by rw [div_lt_iff₀ hε0] at hxA; linarith
          calc A * x ^ e m < ε * x * x ^ e m := mul_lt_mul_of_pos_right this hxe
            _ = ε * (x * x ^ e m) := by ring
            _ ≤ ε * x ^ e (m + 1) := mul_le_mul_of_nonneg_left hgap hε0.le
        have hexp : σ (m + 1) * (q x + σ (m + 1) * ε * x ^ e (m + 1)) =
            σ (m + 1) * q x + ε * x ^ e (m + 1) := by
          have := hσsq (m + 1)
          linear_combination ε * x ^ e (m + 1) * this
        rw [hexp]
        have h1 : -(|q x|) ≤ σ (m + 1) * q x := by
          have := neg_abs_le (σ (m + 1) * q x)
          rw [abs_mul, hσabs, one_mul] at this
          exact this
        linarith

/-- **Lower bound for rank-one networks.** If `m + 1` reactions `r₀, …, r_m` have strictly
increasing source coefficients at a species `i` with `v_i ≠ 0` and alternating multipliers
(`c_{r_j} c_{r_{j+1}} < 0`), then for some rate constants the network has `m` distinct positive
steady states in one compatibility class. -/
theorem rankOne_steadyStates_of_alternating (N : Network S) {v : S → ℝ}
    (c : N.R → ℝ) (hc : ∀ r s, N.reactionVector r s = c r * v s) (i : S) (hvi : v i ≠ 0)
    (m : ℕ) (r : ℕ → N.R)
    (hsrc : ∀ j < m, (N.reaction (r j)).source i < (N.reaction (r (j + 1))).source i)
    (halt : ∀ j < m, c (r j) * c (r (j + 1)) < 0) :
    ∃ (κ : RateConstants N) (x₀ : Concentration S) (X : ℕ → Concentration S),
      (∀ j < m, X j ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ (X j)) ∧
        ∀ j < m, ∀ j' < m, X j = X j' → j = j' := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact rankOne_steadyStates_of_signChanges N c hc i hvi (fun _ => 1) (fun _ => one_pos) 0
      (u := fun j => (j : ℝ) + 1) (fun a b hab => by simp only; exact_mod_cast Nat.add_lt_add_right hab 1)
      (by norm_num) (fun j hj => absurd hj (Nat.not_lt_zero _))
  have hcne : ∀ j ≤ m, c (r j) ≠ 0 := by
    intro j hj h0
    rcases Nat.lt_or_ge j m with h | h
    · have := halt j h; rw [h0, zero_mul] at this; exact lt_irrefl 0 this
    · have := halt (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega, h0, mul_zero] at this; exact lt_irrefl 0 this
  set e : ℕ → ℕ := fun j => (N.reaction (r j)).source i with hedef
  set σ : ℕ → ℝ := fun j => if 0 < c (r j) then 1 else -1 with hσdef
  have hσ : ∀ j, σ j = 1 ∨ σ j = -1 := fun j => by simp only [hσdef]; split_ifs <;> simp
  have hσc : ∀ j ≤ m, σ j * c (r j) = |c (r j)| := by
    intro j hj
    simp only [hσdef]
    split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) (hcne j hj))]; ring
  have hσsq : ∀ j, σ j * σ j = 1 := fun j => by rcases hσ j with h | h <;> rw [h] <;> norm_num
  have hσalt : ∀ j < m, σ j * σ (j + 1) = -1 := by
    intro j hj
    have hp := halt j hj
    simp only [hσdef]
    split_ifs with h1 h2 h2
    · nlinarith [mul_pos h1 h2]
    · norm_num
    · norm_num
    · have a1 := lt_of_le_of_ne (not_lt.mp h1) (hcne j (by omega))
      have a2 := lt_of_le_of_ne (not_lt.mp h2) (hcne (j + 1) (by omega))
      nlinarith [mul_pos_of_neg_of_neg a1 a2]
  obtain ⟨a, ha, u, hu, hu0, hsignq⟩ := exists_prescribed_signs e σ hσ m (fun j hj => hsrc j hj)
  set q : ℝ → ℝ := fun x => ∑ l ∈ Finset.range (m + 1), σ l * a l * x ^ e l with hq
  -- `r` is injective on `[0, m]`
  have hemono : ∀ j j', j < j' → j' ≤ m → e j < e j' := by
    intro j j' hjj' hj'
    induction j' with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_or_ge j n with h | h
      · exact (ih h (by omega)).trans (hsrc n (by omega))
      · rw [show j = n by omega]; exact hsrc n (by omega)
  have hrinj : Set.InjOn r (Finset.range (m + 1) : Set ℕ) := by
    intro j hj j' hj' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hemono j j' hlt (by omega); simp only [hedef, heq] at this; exact lt_irrefl _ this
    · have := hemono j' j hlt (by omega); simp only [hedef, heq] at this; exact lt_irrefl _ this
  set Tset := (Finset.range (m + 1)).image r with hTset
  -- the remaining reactions
  set R : ℝ → ℝ := fun x => ∑ r' ∈ Finset.univ.filter (· ∉ Tset),
    c r' * x ^ (N.reaction r').source i with hR
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ j ≤ m, δ ≤ |q (u j)| := by
    obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image (Finset.range (m + 1))
      (fun j => |q (u j)|) ⟨0, by simp⟩
    have hj₀' : j₀ ≤ m := by simp at hj₀; omega
    refine ⟨_, ?_, fun j hj => hmin j (by simp; omega)⟩
    have := hsignq j₀ hj₀'
    exact abs_pos.mpr fun h0 => by
      simp only [hq] at h0; rw [h0, mul_zero] at this; exact lt_irrefl 0 this
  set Bd : ℝ := ∑ j ∈ Finset.range (m + 1), |R (u j)| + 1 with hBd
  have hBd0 : 0 < Bd := by positivity
  set ε : ℝ := δ / (2 * Bd) with hε
  have hε0 : 0 < ε := by positivity
  have hsmall : ∀ j ≤ m, |ε * R (u j)| < δ := by
    intro j hj
    have hRj : |R (u j)| < Bd := by
      have := Finset.single_le_sum (f := fun j => |R (u j)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (show j < m + 1 by omega))
      simp only [hBd]; linarith
    rw [abs_mul, abs_of_pos hε0, hε]
    calc δ / (2 * Bd) * |R (u j)| ≤ δ / (2 * Bd) * Bd :=
          mul_le_mul_of_nonneg_left hRj.le (by positivity)
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  -- the rates
  let jOf : N.R → ℕ := fun r' =>
    if h : ∃ j ∈ Finset.range (m + 1), r j = r' then Classical.choose h else 0
  have hjOf : ∀ j ≤ m, jOf (r j) = j := by
    intro j hj
    have hex : ∃ j' ∈ Finset.range (m + 1), r j' = r j :=
      ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
    simp only [jOf, hex, ↓reduceDIte]
    obtain ⟨hmem, heq⟩ := Classical.choose_spec hex
    exact hrinj (Finset.mem_coe.mpr hmem) (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)))
      heq
  set k : N.R → ℝ := fun r' => if r' ∈ Tset then a (jOf r') / |c r'| else ε with hk
  have hkpos : ∀ r', 0 < k r' := by
    intro r'
    simp only [hk]
    split_ifs with h
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      have hj' : j ≤ m := by simp at hj; omega
      exact div_pos (ha _) (abs_pos.mpr (hcne j hj'))
    · exact hε0
  have hdecomp : ∀ x, ∑ r', k r' * c r' * x ^ (N.reaction r').source i = q x + ε * R x := by
    intro x
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Tset)]
    have hT' : Finset.univ.filter (· ∈ Tset) = Tset := by ext r'; simp
    rw [hT']
    have hrest : ∑ r' ∈ Finset.univ.filter (· ∉ Tset), k r' * c r' * x ^ (N.reaction r').source i
        = ε * R x := by
      rw [hR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r' hr' => ?_
      have : r' ∉ Tset := (Finset.mem_filter.mp hr').2
      simp only [hk, this, ↓reduceIte]; ring
    rw [hrest, hTset, Finset.sum_image hrinj]
    congr 1
    simp only [hq]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ m := by simp at hj; omega
    have hmem : r j ∈ Tset := Finset.mem_image.mpr ⟨j, hj, rfl⟩
    simp only [hk, hmem, ↓reduceIte, hjOf j hj']
    have hc0 := hcne j hj'
    have habs : |c (r j)| ≠ 0 := abs_ne_zero.mpr hc0
    have hσ' : c (r j) / |c (r j)| = σ j := by
      rw [div_eq_iff habs, ← hσc j hj', ← mul_assoc, hσsq, one_mul]
    calc a j / |c (r j)| * c (r j) * x ^ (N.reaction (r j)).source i
        = (c (r j) / |c (r j)|) * a j * x ^ e j := by simp only [hedef]; ring
      _ = σ j * a j * x ^ e j := by rw [hσ']
  -- the signs at the sample points
  have hsigned : ∀ j ≤ m, 0 < σ j * (q (u j) + ε * R (u j)) := by
    intro j hj
    have h1 := hsignq j hj
    have h2 : |q (u j)| = σ j * q (u j) := by
      rw [← abs_of_pos h1, abs_mul]
      rcases hσ j with h | h <;> rw [h] <;> simp [hq]
    have h3 : |σ j * (ε * R (u j))| = |ε * R (u j)| := by
      rw [abs_mul]; rcases hσ j with h | h <;> rw [h] <;> simp
    have h4 := neg_abs_le (σ j * (ε * R (u j)))
    have h5 := hsmall j hj
    have h6 := hδle j hj
    rw [mul_add]
    linarith
  refine rankOne_steadyStates_of_signChanges N c hc i hvi k hkpos m hu hu0 fun j hj => ?_
  rw [hdecomp, hdecomp]
  have p1 := hsigned j (by omega)
  have p2 := hsigned (j + 1) (by omega)
  have hal := hσalt j hj
  set P₁ := q (u j) + ε * R (u j)
  set P₂ := q (u (j + 1)) + ε * R (u (j + 1))
  have e1 : P₁ = σ j * (σ j * P₁) := by rw [← mul_assoc, hσsq, one_mul]
  have e2 : P₂ = σ (j + 1) * (σ (j + 1) * P₂) := by rw [← mul_assoc, hσsq, one_mul]
  have : P₁ * P₂ = (σ j * σ (j + 1)) * ((σ j * P₁) * (σ (j + 1) * P₂)) := by
    conv_lhs => rw [e1, e2]
    ring
  rw [this, hal]
  nlinarith [mul_pos p1 p2]

end Network

end CRNT
