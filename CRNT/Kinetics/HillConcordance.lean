import CRNT.Kinetics.Hill
import CRNT.Multistationarity.Concordance

/-!
# Hill kinetics is weakly monotonic; concordance consequences

Hill (and Michaelis–Menten) kinetics is weakly monotonic in the sense of Shinar–Feinberg
(`CRNT.Network.Kinetics.WeaklyMonotonic`): on the source support, a strict rate increase forces a
strict increase of some source concentration, and equal rates force either equal source
concentrations or a mixed change. Consequently every concordant network with Hill kinetics has at
most one positive steady state in each stoichiometric compatibility class (Shinar–Feinberg 2012,
Theorem 4.11, here for a non-mass-action kinetics).

Main results:
* `CRNT.hillFactor_strictMonoOn`.
* `CRNT.Network.hillKinetics_weaklyMonotonic`.
* `CRNT.Network.Concordant.hill_subsingleton_steadyState`,
  `CRNT.Network.Concordant.michaelisMenten_subsingleton_steadyState`.
-/

namespace CRNT

open scoped BigOperators

/-- The Hill function with positive Hill coefficient is strictly increasing on `[0, ∞)`. -/
theorem hillFactor_strictMonoOn {K : ℝ} (hK : 0 < K) {n : ℕ} (hn : n ≠ 0) :
    StrictMonoOn (hillFactor K n) (Set.Ici 0) := by
  intro x hx y _ hxy
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := le_trans hx0 hxy.le
  rw [hillFactor, hillFactor, div_lt_div_iff₀ (hillFactor_denom_pos hK n hx0)
    (hillFactor_denom_pos hK n hy0)]
  have hp : x ^ n < y ^ n := pow_lt_pow_left₀ hxy hx0 hn
  nlinarith [pow_pos hK n]

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Rates are monotone in the source-support concentrations. -/
theorem hillRate_le_of_source_le (N : Network S) (P : HillParameters N) (r : N.R)
    {a b : Concentration S} (ha : a.Nonnegative) (hb : b.Nonnegative)
    (hab : ∀ s, (N.reaction r).source s ≠ 0 → a s ≤ b s) :
    N.hillRate P r a ≤ N.hillRate P r b := by
  unfold hillRate
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
    (fun s _ => N.hillSpeciesFactor_nonneg P r s ha) (fun s _ => ?_)) (P.V_pos r).le
  unfold hillSpeciesFactor
  split_ifs with h
  · exact le_rfl
  · exact hillFactor_monotoneOn (P.K_pos r s) _ (Set.mem_Ici.mpr (ha s))
      (Set.mem_Ici.mpr (hb s)) (hab s h)

/-- Strict increase on the source support with positive source concentrations gives a strict
rate increase. -/
theorem hillRate_lt_of_source_lt (N : Network S) (P : HillParameters N) (r : N.R)
    {a b : Concentration S} (ha : a.Nonnegative) (hb : b.Nonnegative)
    (hapos : ∀ s, (N.reaction r).source s ≠ 0 → 0 < a s)
    (hab : ∀ s, (N.reaction r).source s ≠ 0 → a s ≤ b s)
    (hlt : ∃ s, (N.reaction r).source s ≠ 0 ∧ a s < b s) :
    N.hillRate P r a < N.hillRate P r b := by
  unfold hillRate
  refine mul_lt_mul_of_pos_left (Finset.prod_lt_prod₀ (fun s _ => ?_) (fun s _ => ?_) ?_)
    (P.V_pos r)
  · unfold hillSpeciesFactor
    split_ifs with h
    · exact one_pos
    · exact hillFactor_pos (P.K_pos r s) _ (hapos s h)
  · unfold hillSpeciesFactor
    split_ifs with h
    · exact le_rfl
    · exact hillFactor_monotoneOn (P.K_pos r s) _ (Set.mem_Ici.mpr (ha s))
        (Set.mem_Ici.mpr (hb s)) (hab s h)
  · obtain ⟨s, hs, hlts⟩ := hlt
    refine ⟨s, Finset.mem_univ s, ?_⟩
    unfold hillSpeciesFactor
    simp only [hs, ite_false]
    exact hillFactor_strictMonoOn (P.K_pos r s) (P.n_pos r s).ne' (Set.mem_Ici.mpr (ha s))
      (Set.mem_Ici.mpr (hb s)) hlts

/-- **Hill kinetics is weakly monotonic.** -/
theorem hillKinetics_weaklyMonotonic (N : Network S) (P : HillParameters N) :
    (N.hillKinetics P).WeaklyMonotonic := by
  intro cs css hcs hcss r hg hg'
  have hcspos : ∀ s, (N.reaction r).source s ≠ 0 → 0 < cs s := fun s hs =>
    lt_of_le_of_ne (hcs s) (Ne.symm (hg s hs))
  have hcsspos : ∀ s, (N.reaction r).source s ≠ 0 → 0 < css s := fun s hs =>
    lt_of_le_of_ne (hcss s) (Ne.symm (hg' s hs))
  simp only [hillKinetics_rate]
  constructor
  · intro hlt
    by_contra hcon
    push Not at hcon
    have := N.hillRate_le_of_source_le P r hcss hcs hcon
    linarith
  · intro heq
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨s₀, hs₀, hne⟩, hmix⟩ := hcon
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hall : ∀ s, (N.reaction r).source s ≠ 0 → cs s ≤ css s := fun s hs =>
        hmix s₀ s hs₀ hs hlt
      have := N.hillRate_lt_of_source_lt P r hcs hcss hcspos hall ⟨s₀, hs₀, hlt⟩
      linarith
    · have hall : ∀ s, (N.reaction r).source s ≠ 0 → css s ≤ cs s := by
        intro s hs
        by_contra h
        push Not at h
        have := hmix s s₀ hs hs₀ h
        linarith
      have := N.hillRate_lt_of_source_lt P r hcss hcs hcsspos hall ⟨s₀, hs₀, hgt⟩
      linarith

/-- **Concordant networks with Hill kinetics are monostationary.** -/
theorem Concordant.hill_subsingleton_steadyState {N : Network S} (hN : N.Concordant)
    (P : HillParameters N) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsKineticSteadyState (N.hillKinetics P) x)
    (hsy : N.IsKineticSteadyState (N.hillKinetics P) y) : x = y :=
  hN.subsingleton_steadyState (N.hillKinetics_weaklyMonotonic P) hx hy hsx hsy

/-- **Concordant networks with Michaelis–Menten kinetics are monostationary.** -/
theorem Concordant.michaelisMenten_subsingleton_steadyState {N : Network S}
    (hN : N.Concordant) (P : MichaelisMentenParameters N) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsKineticSteadyState (N.michaelisMentenKinetics P) x)
    (hsy : N.IsKineticSteadyState (N.michaelisMentenKinetics P) y) : x = y :=
  hN.hill_subsingleton_steadyState _ hx hy hsx hsy

end Network

end CRNT
