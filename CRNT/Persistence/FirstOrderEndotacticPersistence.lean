import CRNT.Geometry.EndotacticStandard
import CRNT.Dynamics.KnownGlobalPersistenceClasses
import CRNT.Persistence.ConservativePersistence
import CRNT.Kinetics.SpeciesProjectionMassAction
import CRNT.Dynamics.GenuineConfinement
import CRNT.LinearAlgebra.OrthogonalComplement

/-!
# Persistence of first-order endotactic networks

`firstOrderEndotacticPersistenceClaim`: a first-order network (every complex is `0` or a single
species) that is endotactic in the standard sense is structurally persistent.

* Species reachable from the complex `0` are bounded below along a path from `0`: if `y → X_i`
  is a reaction and `x^y ≥ m`, then `x_i' ≥ κ m − D_i x_i`, where `D_i` is the total outflow rate
  of `X_i`, so `x_i ≥ min(x_i(0), κ m/(D_i + 1))/2` (`exists_lower_of_deriv_ge`).
* For a species `X_s` not reachable from `0`, the set `U` of species reaching `X_s` has no
  entering reaction; by `EndotacticStd` (with `w = −𝟙_U`), no reaction leaves the strongly
  connected component `C` of `X_s`, and no reaction enters it. The `C`-coordinates then solve the
  mass-action system of `speciesProjection N C` with the same rates, which is weakly reversible
  and conservative, hence persistent (`weaklyReversible_conservative_persistentFrom`).
-/

open Filter Set
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The unit complex `X_i`. -/
abbrev unitCx (i : S) : Complex S := Pi.single i 1

theorem unitCx_apply (i j : S) : unitCx i j = if j = i then 1 else 0 := by
  simp [unitCx, Pi.single_apply]

/-- In a first-order network every complex is `0` or a unit complex. -/
theorem IsFirstOrder.cases {N : Network S} (h : N.IsFirstOrder) {c : Complex S}
    (hc : c ∈ N.complexes) : c = 0 ∨ ∃ i, c = unitCx i := by
  classical
  have hsum := h c hc
  by_cases h0 : ∀ s, c s = 0
  · exact Or.inl (funext h0)
  · push Not at h0
    obtain ⟨i, hi⟩ := h0
    right
    refine ⟨i, funext fun j => ?_⟩
    have hle : ∀ j, c j ≤ ∑ s, c s := fun j =>
      Finset.single_le_sum (fun s _ => Nat.zero_le _) (Finset.mem_univ j)
    have hci : c i = 1 := by have := hle i; omega
    rw [unitCx_apply]
    split_ifs with hji
    · rw [hji, hci]
    · have h2 : c i + c j ≤ ∑ s, c s := by
        rw [← Finset.sum_pair (f := c) (Ne.symm hji)]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      omega

theorem source_cases {N : Network S} (h : N.IsFirstOrder) (r : N.R) :
    (N.reaction r).source = 0 ∨ ∃ i, (N.reaction r).source = unitCx i :=
  h.cases (N.source_mem_complexes r)

theorem target_cases {N : Network S} (h : N.IsFirstOrder) (r : N.R) :
    (N.reaction r).target = 0 ∨ ∃ i, (N.reaction r).target = unitCx i :=
  h.cases (N.target_mem_complexes r)

theorem monomial_zero (x : Concentration S) : (0 : Complex S).massActionMonomial x = 1 := by
  simp [Complex.massActionMonomial]

theorem monomial_unitCx (i : S) (x : Concentration S) :
    (unitCx i).massActionMonomial x = x i := by
  classical
  unfold Complex.massActionMonomial
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [unitCx, Pi.single_apply, hj]
  · simp

/-- In a first-order network, `x^y · y_i = x_i · y_i`. -/
theorem monomial_mul_coord {N : Network S} (h : N.IsFirstOrder) (r : N.R) (i : S)
    (x : Concentration S) :
    (N.reaction r).source.massActionMonomial x * ((N.reaction r).source i : ℝ) =
      x i * ((N.reaction r).source i : ℝ) := by
  rcases source_cases h r with h0 | ⟨j, hj⟩
  · simp [h0]
  · rw [hj, monomial_unitCx]
    by_cases hij : i = j
    · rw [hij]
    · simp [unitCx, Pi.single_apply, hij]

/-- Total outflow rate of species `i`. -/
noncomputable def outRate (N : Network S) (κ : N.RateConstants) (i : S) : ℝ :=
  ∑ r, κ.k r * ((N.reaction r).source i : ℝ)

theorem outRate_nonneg (N : Network S) (κ : N.RateConstants) (i : S) : 0 ≤ N.outRate κ i :=
  Finset.sum_nonneg fun r _ => mul_nonneg (κ.positive r).le (Nat.cast_nonneg _)

/-- **Production lower bound.** If `r` produces `X_i` from a source not containing `X_i`, then
`κ_r x^{y_r} − D_i x_i ≤ (dx/dt)_i` on the nonnegative orthant. -/
theorem field_ge_production {N : Network S} (h : N.IsFirstOrder) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Nonnegative) {i : S} {r : N.R}
    (hsrc : (N.reaction r).source i = 0) (htgt : (N.reaction r).target i = 1) :
    κ.k r * (N.reaction r).source.massActionMonomial x - N.outRate κ i * x i ≤
      N.massActionVectorField κ x i := by
  classical
  rw [massActionVectorField_apply]
  set g : N.R → ℝ := fun r' => N.massActionRate κ r' x * N.reactionVector r' i
  set l : N.R → ℝ := fun r' => -(κ.k r' * ((N.reaction r').source i : ℝ) * x i)
  have hgl : ∀ r', l r' ≤ g r' := by
    intro r'
    simp only [g, l, massActionRate, reactionVector_apply]
    have hm := monomial_mul_coord h r' i x
    have hmon : 0 ≤ (N.reaction r').source.massActionMonomial x :=
      Finset.prod_nonneg fun s _ => pow_nonneg (hx s) _
    have ht : (0 : ℝ) ≤ ((N.reaction r').target i : ℝ) := Nat.cast_nonneg _
    have hk := (κ.positive r').le
    nlinarith [mul_nonneg (mul_nonneg hk hmon) ht]
  have hgr : g r = κ.k r * (N.reaction r).source.massActionMonomial x := by
    simp only [g, massActionRate, reactionVector_apply, hsrc, htgt]; simp
  have hlr : l r = 0 := by simp [l, hsrc]
  have hsplit : ∑ r', g r' = g r + ∑ r' ∈ Finset.univ.erase r, g r' :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ r)).symm
  have hsplitl : ∑ r', l r' = l r + ∑ r' ∈ Finset.univ.erase r, l r' :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ r)).symm
  have hle : ∑ r' ∈ Finset.univ.erase r, l r' ≤ ∑ r' ∈ Finset.univ.erase r, g r' :=
    Finset.sum_le_sum fun r' _ => hgl r'
  have hout : ∑ r', l r' = -(N.outRate κ i * x i) := by
    simp only [l, outRate, Finset.sum_neg_distrib, Finset.sum_mul]
  change κ.k r * _ - _ ≤ ∑ r', g r'
  rw [hsplit, hgr]
  rw [hsplitl, hlr, zero_add] at hout
  linarith

/-- **Barrier lemma.** If `f' ≥ c − D f` with `c > 0`, `D ≥ 0`, and `f(0) > 0`, then `f` has a
positive lower bound on `[0, ∞)`. -/
theorem exists_lower_of_deriv_ge {f f' : ℝ → ℝ} (hf : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    {c D : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hf0 : 0 < f 0)
    (hcmp : ∀ t, 0 ≤ t → c - D * f t ≤ f' t) : ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → m ≤ f t := by
  set L := min (f 0) (c / (D + 1)) / 2 with hL
  have hD1 : 0 < D + 1 := by linarith
  have hLpos : 0 < L := by positivity
  have hLf0 : L < f 0 := by
    have := min_le_left (f 0) (c / (D + 1)); rw [hL]; linarith
  have hLc : D * L < c := by
    have h1 : L ≤ c / (D + 1) / 2 := by
      have := min_le_right (f 0) (c / (D + 1)); rw [hL]; linarith
    have h2 : D * L ≤ D * (c / (D + 1) / 2) := mul_le_mul_of_nonneg_left h1 hD
    have h3 : D * (c / (D + 1) / 2) < c := by
      rw [show D * (c / (D + 1) / 2) = c * (D / (D + 1)) / 2 by field_simp]
      have : D / (D + 1) < 1 := by rw [div_lt_one hD1]; linarith
      nlinarith
    linarith
  refine ⟨L, hLpos, fun t ht => ?_⟩
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := fun τ => -f τ)
    (f' := fun τ => -f' τ) (a := 0) (b := t)
    (fun τ hτ => (hf τ hτ.1).continuousAt.neg.continuousWithinAt)
    (fun τ hτ => (hf τ hτ.1).neg.hasDerivWithinAt)
    (B := fun _ => -L) (B' := fun _ => 0) (by linarith)
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (fun τ hτ heq => by
      have hfτ : f τ = L := by linarith
      have := hcmp τ hτ.1
      rw [hfτ] at this
      linarith) (Set.right_mem_Icc.2 ht)
  linarith

/-! ## Species reachable from `0` -/

/-- Along a positive forward solution, every complex reachable from `0` has a monomial bounded
below by a positive constant. -/
theorem reachZero_lower {N : Network S} (hfo : N.IsFirstOrder) (κ : N.RateConstants)
    {Γ : ℝ → Concentration S}
    (hsol : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t)
    (hpos : ∀ t, 0 ≤ t → (Γ t).Positive) {d : Complex S} (hd : N.Reaches 0 d) :
    ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → m ≤ d.massActionMonomial (Γ t) := by
  classical
  induction hd with
  | refl => exact ⟨1, one_pos, fun t _ => by rw [monomial_zero]⟩
  | @tail e f _ hef ih =>
      obtain ⟨me, hme, hmele⟩ := ih
      obtain ⟨r, hs, ht⟩ := hef
      rcases target_cases hfo r with h0 | ⟨i, hi⟩
      · rw [← ht, h0]; exact ⟨1, one_pos, fun t _ => by rw [monomial_zero]⟩
      · rw [← ht, hi]
        by_cases hei : e = unitCx i
        · rw [← hei]; exact ⟨me, hme, hmele⟩
        · have hsrc : (N.reaction r).source i = 0 := by
            rcases source_cases hfo r with h0 | ⟨j, hj⟩
            · rw [h0]; rfl
            · have hji : j ≠ i := fun e' => hei (by rw [← hs, hj, e'])
              rw [hj, unitCx_apply, if_neg (Ne.symm hji)]
          have htgt : (N.reaction r).target i = 1 := by rw [hi, unitCx_apply, if_pos rfl]
          obtain ⟨m, hm, hle⟩ := exists_lower_of_deriv_ge (f := fun t => Γ t i)
            (f' := fun t => N.massActionVectorField κ (Γ t) i)
            (fun t ht => (hasDerivAt_pi.mp (hsol t ht)) i)
            (c := κ.k r * me) (D := N.outRate κ i) (mul_pos (κ.positive r) hme)
            (N.outRate_nonneg κ i) (hpos 0 le_rfl i) (fun t ht => by
              have h1 := field_ge_production hfo κ (hpos t ht).nonnegative hsrc htgt
              have h2 : κ.k r * me ≤ κ.k r * (N.reaction r).source.massActionMonomial (Γ t) := by
                rw [hs]; exact mul_le_mul_of_nonneg_left (hmele t ht) (κ.positive r).le
              linarith)
          exact ⟨m, hm, fun t ht => by rw [monomial_unitCx]; exact hle t ht⟩

/-! ## Species not reachable from `0` -/

theorem complexWValue_zero (w : S → ℝ) : complexWValue w (0 : Complex S) = 0 := by
  simp [complexWValue, Network.dotProduct, exponentVector]

theorem complexWValue_unitCx (w : S → ℝ) (k : S) : complexWValue w (unitCx k) = w k := by
  classical
  simp only [complexWValue, Network.dotProduct, exponentVector, unitCx_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem unitCx_injective : Function.Injective (unitCx : S → Complex S) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [unitCx, Pi.single_apply, hij] at this

/-- **No reaction leaves the component of a species not reachable from `0`.** -/
theorem target_reaches_back {N : Network S} (hfo : N.IsFirstOrder) (hend : N.EndotacticStd)
    {s : S} (h0 : ¬ N.Reaches 0 (unitCx s)) {r : N.R} (hr : (N.reaction r).source = unitCx s) :
    ∃ m, (N.reaction r).target = unitCx m ∧ N.Reaches (unitCx m) (unitCx s) := by
  classical
  by_contra hno
  push Not at hno
  set w : S → ℝ := fun k => if N.Reaches (unitCx k) (unitCx s) then -1 else 0 with hw
  have hval : ∀ c : Complex S, c ∈ N.complexes →
      complexWValue w c = 0 ∨ (∃ k, c = unitCx k ∧ N.Reaches (unitCx k) (unitCx s) ∧
        complexWValue w c = -1) := by
    intro c hc
    rcases hfo.cases hc with rfl | ⟨k, rfl⟩
    · exact Or.inl (complexWValue_zero w)
    · rw [complexWValue_unitCx]
      by_cases hk : N.Reaches (unitCx k) (unitCx s)
      · exact Or.inr ⟨k, rfl, hk, by simp [hw, hk]⟩
      · exact Or.inl (by simp [hw, hk])
  have hsrcval : complexWValue w (N.reaction r).source = -1 := by
    rw [hr, complexWValue_unitCx]; simp [hw, Reaches.refl]
  have htgtval : complexWValue w (N.reaction r).target = 0 := by
    rcases target_cases hfo r with h0' | ⟨m, hm⟩
    · rw [h0']; exact complexWValue_zero w
    · rw [hm, complexWValue_unitCx]; simp [hw, hno m hm]
  have hrate : 0 < N.wRate w r := by
    rw [N.wRate_eq_complexWValue_sub, hsrcval, htgtval]; norm_num
  obtain ⟨r', hneg, hlt⟩ := hend w r hrate
  rw [wValue_eq_complexWValue_source, wValue_eq_complexWValue_source, hsrcval] at hlt
  rw [N.wRate_eq_complexWValue_sub] at hneg
  -- the source of `r'` is outside `U`, its target inside: an entering reaction
  rcases hval _ (N.target_mem_complexes r') with ht0 | ⟨m, hm, hms, -⟩
  · rcases hval _ (N.source_mem_complexes r') with hs0 | ⟨k, -, -, hk⟩
    · linarith
    · linarith
  · rcases hval _ (N.source_mem_complexes r') with hs0 | ⟨k, -, -, hk⟩
    · -- the source is `0` or a species not reaching `X_s`
      have hedge : N.Reaches (N.reaction r').source (unitCx s) :=
        Relation.ReflTransGen.head ⟨r', rfl, hm⟩ hms
      rcases source_cases hfo r' with hz | ⟨k, hk⟩
      · rw [hz] at hedge; exact h0 hedge
      · rw [hk] at hedge hs0
        rw [complexWValue_unitCx] at hs0
        simp [hw, hedge] at hs0
    · linarith

/-- The strongly connected component of `X_s`. -/
noncomputable def compOf (N : Network S) (s : S) : Finset S := by
  classical
  exact Finset.univ.filter fun j => N.Reaches (unitCx s) (unitCx j) ∧ N.Reaches (unitCx j) (unitCx s)

theorem mem_compOf {N : Network S} {s j : S} :
    j ∈ N.compOf s ↔ N.Reaches (unitCx s) (unitCx j) ∧ N.Reaches (unitCx j) (unitCx s) := by
  classical
  unfold compOf; simp

/-- Reactions either stay inside the component of an unreachable species or avoid it entirely. -/
theorem comp_closed {N : Network S} (hfo : N.IsFirstOrder) (hend : N.EndotacticStd)
    {s : S} (h0 : ¬ N.Reaches 0 (unitCx s)) (r : N.R) :
    (∃ j ∈ N.compOf s, ∃ m ∈ N.compOf s,
        (N.reaction r).source = unitCx j ∧ (N.reaction r).target = unitCx m) ∨
      (∀ k ∈ N.compOf s, (N.reaction r).source k = 0 ∧ (N.reaction r).target k = 0) := by
  classical
  -- species of the component are not reachable from `0`
  have hunr : ∀ j ∈ N.compOf s, ¬ N.Reaches 0 (unitCx j) := fun j hj hr =>
    h0 (hr.trans (mem_compOf.mp hj).2)
  by_cases hsrc : ∃ j ∈ N.compOf s, (N.reaction r).source = unitCx j
  · obtain ⟨j, hj, hjs⟩ := hsrc
    obtain ⟨m, hm, hmj⟩ := target_reaches_back hfo hend (hunr j hj) hjs
    left
    refine ⟨j, hj, m, mem_compOf.mpr ⟨?_, hmj.trans (mem_compOf.mp hj).2⟩, hjs, hm⟩
    exact (mem_compOf.mp hj).1.tail ⟨r, hjs, hm⟩
  · right
    push Not at hsrc
    have hs0 : ∀ k ∈ N.compOf s, (N.reaction r).source k = 0 := by
      intro k hk
      rcases source_cases hfo r with h | ⟨j, hj⟩
      · rw [h]; rfl
      · rw [hj, unitCx_apply]
        have : k ≠ j := fun e => hsrc j (e ▸ hk) hj
        simp [this]
    refine fun k hk => ⟨hs0 k hk, ?_⟩
    rcases target_cases hfo r with h | ⟨m, hm⟩
    · rw [h]; rfl
    · rw [hm, unitCx_apply]
      by_cases hmk : k = m
      · exfalso
        subst hmk
        -- `r` enters the component: its source must lie in it
        rcases source_cases hfo r with hz | ⟨j, hj⟩
        · exact hunr k hk (Relation.ReflTransGen.single ⟨r, hz, hm⟩)
        · have hjunr : ¬ N.Reaches 0 (unitCx j) := fun hr0 =>
            hunr k hk (hr0.tail ⟨r, hj, hm⟩)
          obtain ⟨m', hm', hm'j⟩ := target_reaches_back hfo hend hjunr hj
          have hkm : k = m' := unitCx_injective (hm.symm.trans hm')
          subst hkm
          have hjC : j ∈ N.compOf s := mem_compOf.mpr
            ⟨(mem_compOf.mp hk).1.trans hm'j,
              (Relation.ReflTransGen.single ⟨r, hj, hm⟩).trans (mem_compOf.mp hk).2⟩
          exact hsrc j hjC hj
      · simp [hmk]

/-! ## The closed component as a subsystem -/

theorem projectComplex_unitCx_mem {P : Finset S} {j : S} (hj : j ∈ P) :
    projectComplex P (unitCx j) = unitCx (⟨j, hj⟩ : {s // s ∈ P}) := by
  funext t
  simp only [projectComplex_apply, unitCx_apply, Subtype.ext_iff]

/-- Reachability passes to species projections. -/
theorem Reaches.project {N : Network S} (P : Finset S) {c d : Complex S} (h : N.Reaches c d) :
    (N.speciesProjection P).Reaches (projectComplex P c) (projectComplex P d) := by
  induction h with
  | refl => exact Reaches.refl _ _
  | @tail e f _ hef ih =>
      obtain ⟨r, hs, ht⟩ := hef
      exact ih.tail ⟨r, by rw [← hs]; rfl, by rw [← ht]; rfl⟩

theorem sum_unitCx_subtype {P : Finset S} {m : S} (hm : m ∈ P) :
    ∑ t : {s // s ∈ P}, ((unitCx m t.1 : ℕ) : ℝ) = 1 := by
  classical
  rw [Finset.sum_eq_single ⟨m, hm⟩]
  · simp
  · intro t _ ht
    have : t.1 ≠ m := fun e => ht (Subtype.ext e)
    simp [unitCx_apply, this]
  · simp

/-- **Persistence of a closed component.** For a species not reachable from `0`, the coordinate
of a positive forward solution is bounded below by a positive constant. -/
theorem comp_lower {N : Network S} (hfo : N.IsFirstOrder) (hend : N.EndotacticStd)
    (κ : N.RateConstants) {s : S} (h0 : ¬ N.Reaches 0 (unitCx s)) {Γ : ℝ → Concentration S}
    (hsol : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t)
    (hpos : ∀ t, 0 ≤ t → (Γ t).Positive) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 ≤ t → ε ≤ Γ t s := by
  classical
  set C := N.compOf s
  have hsC : s ∈ C := mem_compOf.mpr ⟨Reaches.refl _ _, Reaches.refl _ _⟩
  set NP := N.speciesProjection C
  let κP : NP.RateConstants := ⟨κ.k, κ.positive⟩
  have hcl := comp_closed hfo hend h0
  -- the projected field
  have hfield : ∀ (x : Concentration S) (t : {s // s ∈ C}),
      NP.massActionVectorField κP (projectConcentration C x) t =
        N.massActionVectorField κ x t.1 := by
    intro x t
    rw [massActionVectorField_apply, massActionVectorField_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    change N.R at r
    rw [speciesProjection_reactionVector_apply]
    rcases hcl r with ⟨j, hj, m, hm, hsr, htr⟩ | hout
    · congr 1
      simp only [massActionRate]
      change κ.k r * (projectComplex C (N.reaction r).source).massActionMonomial
        (projectConcentration C x) = κ.k r * (N.reaction r).source.massActionMonomial x
      rw [hsr, projectComplex_unitCx_mem hj, monomial_unitCx, monomial_unitCx]
      rfl
    · have h1 := hout t.1 t.2
      rw [reactionVector_apply, h1.1, h1.2]
      simp
  -- weak reversibility of the projection
  have hwr : NP.WeaklyReversible := by
    intro r
    change N.R at r
    rcases hcl r with ⟨j, hj, m, hm, hsr, htr⟩ | hout
    · have hreach : N.Reaches (N.reaction r).target (N.reaction r).source := by
        rw [hsr, htr]; exact (mem_compOf.mp hm).2.trans (mem_compOf.mp hj).1
      exact Reaches.project C hreach
    · have heq : (NP.reaction r).target = (NP.reaction r).source := by
        funext t
        rw [speciesProjection_target_apply, speciesProjection_source_apply, (hout t.1 t.2).1,
          (hout t.1 t.2).2]
      rw [heq]
  -- conservation of the total mass of the component
  have hcons : NP.IsConservative := by
    refine ⟨fun _ => 1, ?_, fun _ => one_pos⟩
    apply mem_orthSum_span
    rintro g ⟨r, rfl⟩
    have hv : ∀ t : {s // s ∈ C}, NP.reactionVector r t =
        ((N.reaction r).target t.1 : ℝ) - (N.reaction r).source t.1 := fun t =>
      speciesProjection_reactionVector_apply N C r t
    simp only [one_mul]
    rw [Finset.sum_congr rfl fun t _ => hv t]
    rcases hcl r with ⟨j, hj, m, hm, hsr, htr⟩ | hout
    · rw [hsr, htr, Finset.sum_sub_distrib, sum_unitCx_subtype hm, sum_unitCx_subtype hj,
        sub_self]
    · exact Finset.sum_eq_zero fun t _ => by rw [(hout t.1 t.2).1, (hout t.1 t.2).2]; simp
  -- the projected trajectory
  set Γt : ℝ → Concentration {s // s ∈ C} := fun t => projectConcentration C (Γ t)
  have hsolP : ∀ t, 0 ≤ t → HasDerivAt Γt (NP.massActionVectorField κP (Γt t)) t := by
    intro t ht
    rw [hasDerivAt_pi]
    intro u
    rw [hfield]
    exact (hasDerivAt_pi.mp (hsol t ht)) u.1
  have hx₀ : (Γt 0).Positive := fun u => hpos 0 le_rfl u.1
  obtain ⟨K₀, hK₀c, hK₀pos, hK₀⟩ :=
    NP.weaklyReversible_conservative_persistentFrom κP hwr hcons hx₀
  have hin : ∀ t, 0 ≤ t → Γt t ∈ K₀ := hK₀ Γt rfl hsolP
  obtain ⟨y₀, hy₀, hmin⟩ := hK₀c.exists_isMinOn ⟨Γt 0, hin 0 le_rfl⟩
    (continuous_apply (⟨s, hsC⟩ : {s // s ∈ C})).continuousOn
  exact ⟨y₀ ⟨s, hsC⟩, hK₀pos y₀ hy₀ _, fun t ht => hmin (hin t ht)⟩

/-- **First-order endotactic networks are structurally persistent.** -/
theorem firstOrderEndotacticPersistenceClaim (N : Network S) :
    N.FirstOrderEndotacticPersistenceClaim := by
  intro hfo hend κ ϕ γ hflow x₀ hx₀ s
  obtain ⟨hzero, hϕγ, hsolf⟩ := hflow
  have hsol := hsolf x₀
  have hγ0 : (γ x₀ 0).Positive := by rw [hzero]; exact hx₀
  have hpos := N.genuineOrbit_pos κ hγ0 hsol
  by_cases hreach : N.Reaches 0 (unitCx s)
  · obtain ⟨m, hm, hle⟩ := reachZero_lower hfo κ hsol hpos hreach
    refine ⟨m, hm, fun t => ?_⟩
    rw [hϕγ x₀ t]
    have := hle t t.2
    rwa [monomial_unitCx] at this
  · obtain ⟨ε, hε, hle⟩ := comp_lower hfo hend κ hreach hsol hpos
    exact ⟨ε, hε, fun t => by rw [hϕγ x₀ t]; exact hle t t.2⟩

/-- **Persistence of first-order endotactic networks, trajectory form.** -/
theorem IsFirstOrder.persistent {N : Network S} (hfo : N.IsFirstOrder) (hend : N.EndotacticStd)
    (κ : N.RateConstants) {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → ∀ s, m ≤ Γ t s := by
  classical
  have hpos := N.genuineOrbit_pos κ hΓ0 hsol
  have hs : ∀ s : S, ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → m ≤ Γ t s := by
    intro s
    by_cases hreach : N.Reaches 0 (unitCx s)
    · obtain ⟨m, hm, hle⟩ := reachZero_lower hfo κ hsol hpos hreach
      exact ⟨m, hm, fun t ht => by have := hle t ht; rwa [monomial_unitCx] at this⟩
    · exact comp_lower hfo hend κ hreach hsol hpos
  choose mf hmf hmfle using hs
  by_cases hS : Nonempty S
  · obtain ⟨s₀, -, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) mf
    exact ⟨Finset.univ.inf' Finset.univ_nonempty mf, by rw [h]; exact hmf s₀,
      fun t ht s => (Finset.inf'_le _ (Finset.mem_univ s)).trans (hmfle s t ht)⟩
  · exact ⟨1, one_pos, fun _ _ s => absurd ⟨s⟩ hS⟩

end Network
end CRNT
