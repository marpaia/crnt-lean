import CRNT.Stochastic.ACRExtinction
import CRNT.Stochastic.ClosedSetAbsorption
import CRNT.Stochastic.JumpAbsorption

/-!
# Extinction with probability one (Anderson–Enciso–Johnston)

The probabilistic conclusion of Anderson–Enciso–Johnston (2014): "a trajectory of the stochastically
modeled system will, with a probability of one, be absorbed by a set of states for which all of the
non-terminal complexes are turned off".

On a conservative network the counts reachable from `n₀` form a finite set `T`, closed under the
jumps of positive propensity. Its recurrent counts (`IsRecurrentVia`, the closed communicating
classes) form a closed set for the embedded jump chain, reachable from every count. Hence the
probability that the jump chain is at a recurrent count after `n` steps tends to one
(`FiniteAbsorption.tendsto_closedMass_one`), for every choice of positive stochastic rate
constants, and by `acrExtinction` all non-terminal complexes are off there.

* `IsRecurrentVia.of_reachVia`: recurrence propagates along jumps.
* `jumpClosed_reachFin`, `recurrentCounts`, `jumpMatrix_closedChain`.
* `acrExtinction_absorption`: absorption with probability one into the recurrent counts, at which
  all non-terminal complexes are off.
* `acrExtinction_offMass_tendsto_one`: the probability that all non-terminal complexes are off at
  step `n` tends to one.
-/

namespace CRNT

namespace Network

open Filter Topology FiniteAbsorption

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Recurrence propagates along reachability. -/
theorem IsRecurrentVia.of_reachVia {N : Network S} {P : N.R → Prop} {m m' : S → ℕ}
    (hm : N.IsRecurrentVia P m) (h : N.ReachVia P m m') : N.IsRecurrentVia P m' :=
  fun m'' h'' => (hm m'' (h.trans h'')).trans h

section

variable (N : Network S) (κ : RateConstants N) (w : S → ℝ) (hw : ∀ s, 0 < w s)
  (hcons : ∀ r, ∑ s, w s * N.reactionVector r s = 0)

include hw hcons in
/-- The counts reachable from `n₀` are closed under jumps of positive propensity. -/
theorem jumpClosed_reachFin (n₀ : S → ℕ) : N.JumpClosed κ (reachFin N w (fun _ => True) n₀) := by
  intro n hn r hr
  have hf : N.CanFire n r := (canFire_iff_stochasticMassActionRate_pos N κ n r).mpr hr
  exact (mem_reachFin N w hw hcons).mpr
    (((mem_reachFin N w hw hcons).mp hn).tail ⟨r, trivial, hf, rfl⟩)

end

/-- The recurrent counts of `T`. -/
noncomputable def recurrentCounts (N : Network S) (T : Finset (S → ℕ)) : Finset T := by
  classical
  exact Finset.univ.filter fun j => N.IsRecurrentVia (fun _ => True) j.val

theorem mem_recurrentCounts {N : Network S} {T : Finset (S → ℕ)} {j : T} :
    j ∈ N.recurrentCounts T ↔ N.IsRecurrentVia (fun _ => True) j.val := by
  classical
  unfold recurrentCounts
  simp

/-- **The recurrent counts form a closed set for the jump chain.** -/
theorem jumpMatrix_closedChain (N : Network S) (κ : RateConstants N) {T : Finset (S → ℕ)}
    (hT : N.JumpClosed κ T) : ClosedChain (N.jumpMatrix κ T) (N.recurrentCounts T) where
  nonneg := (N.jumpMatrix_absorbingChain κ hT).nonneg
  colSum := (N.jumpMatrix_absorbingChain κ hT).colSum
  closed := by
    intro a ha i hi
    have harec := mem_recurrentCounts.mp ha
    by_cases h0 : N.exitRate κ a = 0
    · have hia : i ≠ a := fun e => hi (e ▸ ha)
      simp [jumpMatrix, h0, hia]
    · simp only [jumpMatrix, h0, ↓reduceIte]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hn : N.jumpNextCount a r = (i : S → ℕ)
      · rcases (N.stochasticMassActionRate_nonneg κ a r).lt_or_eq with hr | hr
        · exfalso
          apply hi
          apply mem_recurrentCounts.mpr
          have hf := (canFire_iff_stochasticMassActionRate_pos N κ a r).mpr hr
          have := harec.of_reachVia (Relation.ReflTransGen.single ⟨r, trivial, hf, rfl⟩)
          rwa [hn] at this
        · rw [stochasticMassActionRate_eq_zero_of_jumpProb N κ hr.symm, zero_mul]
      · simp [hn]

/-- Reachability inside a jump-closed set gives a path of positive-propensity jumps. -/
theorem jumpAbsStep_of_reachVia (N : Network S) (κ : RateConstants N) {T : Finset (S → ℕ)}
    (hT : N.JumpClosed κ T) {j : T} {m : S → ℕ} (h : N.ReachVia (fun _ => True) j.val m) :
    ∃ hm : m ∈ T, Relation.ReflTransGen (N.JumpAbsStep κ T) j ⟨m, hm⟩ := by
  induction h with
  | refl => exact ⟨j.2, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
    obtain ⟨hm, hpath⟩ := ih
    obtain ⟨r, -, hf, rfl⟩ := hstep
    have hr := (canFire_iff_stochasticMassActionRate_pos N κ _ r).mp hf
    exact ⟨hT _ hm r hr, hpath.tail ⟨r, hr, rfl⟩⟩

/-- **Anderson–Enciso–Johnston: absorption with probability one.** Under the hypotheses of
`acrExtinction`, for every choice of positive stochastic rate constants `κ'` and every initial
count `n₀`, the embedded jump chain on the counts reachable from `n₀` is at a recurrent count after
`n` steps with probability tending to one, and every non-terminal complex is off at every
recurrent count. -/
theorem acrExtinction_absorption (N : Network S) (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (hcons : ∀ r, ∑ s, w s * N.reactionVector r s = 0) (hδ : N.DeficiencyOne)
    (κ : RateConstants N) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hss : N.IsMassActionSteadyState κ x₀) (y₁ y₂ : N.ComplexIdx)
    (hy₁ : ¬ N.IsTerminalSLC y₁.val) (hy₂ : ¬ N.IsTerminalSLC y₂.val) (hne : y₁ ≠ y₂)
    (hdom : ∀ s, y₂.val s ≤ y₁.val s) (κ' : RateConstants N) (n₀ : S → ℕ) :
    (∀ j : reachFin N w (fun _ => True) n₀,
      Tendsto (fun n => absorbedMass (N.jumpMatrix κ' (reachFin N w (fun _ => True) n₀))
        (N.recurrentCounts (reachFin N w (fun _ => True) n₀)) n j) atTop (𝓝 1)) ∧
    ∀ a ∈ N.recurrentCounts (reachFin N w (fun _ => True) n₀),
      ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → ¬ IsOn c.val a.val := by
  set T := reachFin N w (fun _ => True) n₀
  have hT : N.JumpClosed κ' T := N.jumpClosed_reachFin κ' w hw hcons n₀
  have hc := N.jumpMatrix_closedChain κ' hT
  refine ⟨fun j => tendsto_closedMass_one hc (fun j => ?_) j, fun a ha c hc =>
    acrExtinction N w hw hcons hδ κ hx₀ hss y₁ y₂ hy₁ hy₂ hne hdom
      (mem_recurrentCounts.mp ha) c hc⟩
  obtain ⟨m, hjm, hrec⟩ := exists_recurrent_reachable N w hw hcons (fun _ => True) j.val
  obtain ⟨hm, hpath⟩ := N.jumpAbsStep_of_reachVia κ' hT hjm
  obtain ⟨n, hn⟩ := N.exists_pow_pos_of_jumpReach κ' hT hpath
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  exact Finset.single_le_sum (f := fun b => (N.jumpMatrix κ' T ^ n) b j)
    (fun b _ => hc.pow_nonneg n b j) (mem_recurrentCounts.mpr hrec)

open scoped Classical in
/-- **The probability that all non-terminal complexes are off tends to one.** -/
theorem acrExtinction_offMass_tendsto_one (N : Network S) (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (hcons : ∀ r, ∑ s, w s * N.reactionVector r s = 0) (hδ : N.DeficiencyOne)
    (κ : RateConstants N) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hss : N.IsMassActionSteadyState κ x₀) (y₁ y₂ : N.ComplexIdx)
    (hy₁ : ¬ N.IsTerminalSLC y₁.val) (hy₂ : ¬ N.IsTerminalSLC y₂.val) (hne : y₁ ≠ y₂)
    (hdom : ∀ s, y₂.val s ≤ y₁.val s) (κ' : RateConstants N) (n₀ : S → ℕ)
    (j : reachFin N w (fun _ => True) n₀) :
    Tendsto (fun n => ∑ a ∈ (Finset.univ : Finset (reachFin N w (fun _ => True) n₀)).filter
        (fun a => ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → ¬ IsOn c.val a.val),
        (N.jumpMatrix κ' (reachFin N w (fun _ => True) n₀) ^ n) a j) atTop (𝓝 1) := by
  classical
  have hT : N.JumpClosed κ' (reachFin N w (fun _ => True) n₀) := N.jumpClosed_reachFin κ' w hw hcons n₀
  have hc := N.jumpMatrix_closedChain κ' hT
  obtain ⟨hlim, hoff⟩ := acrExtinction_absorption N w hw hcons hδ κ hx₀ hss y₁ y₂ hy₁ hy₂ hne hdom
    κ' n₀
  have hsub : N.recurrentCounts (reachFin N w (fun _ => True) n₀) ⊆
      (Finset.univ : Finset (reachFin N w (fun _ => True) n₀)).filter
      (fun a => ∀ c : N.ComplexIdx, ¬ N.IsTerminalSLC c.val → ¬ IsOn c.val a.val) :=
    fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoff a ha⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim j) tendsto_const_nhds (fun n => ?_)
    (fun n => ?_)
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hc.pow_nonneg n b j
  · rw [← hc.pow_colSum n j]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun b _ _ => hc.pow_nonneg n b j

end Network

end CRNT
