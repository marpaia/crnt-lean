import CRNT.Algebra.Patchworking

/-!
# Positively decorated simplices with conservation laws (Bihan–Dickenstein–Giaroli)

For a network with stoichiometric subspace `V`, steady states in a compatibility class are the
zeros of the augmented square system `Φ(x) = (Z F(x), L x − T)`, where `Z : ℝ^S → ℝ^{E₁}` is
injective on `V` (it records the field, which lies in `V`), `L : ℝ^S → ℝ^{E₂}` has kernel `V`
(conservation laws) and `T` is the vector of total amounts, `|E₁| + |E₂| = |S|`. Its support
consists of the reactant complexes, the unit complexes `e_i` (the linear terms of `L x`) and the
zero complex (the constants `T`); its coefficients are `augCoeff`.

Deforming the rate constants by `t^{h(y_r)}` and the totals by `t^{h(0)}`, with `h(e_i) = 0`
(the conservation coefficients are not parameters), the augmented system is exactly the deformed
system `Patchworking.sys` (`sys_augCoeff`). Hence `d` positively decorated lower cells of the
augmented system with distinct normals give `d` distinct positive steady states in one
compatibility class, each nondegenerate relative to the class (`steadyStates_of_augmentedCells`),
the general form of Bihan–Dickenstein–Giaroli's lower bound.
-/

namespace CRNT

namespace Network

open Filter Topology

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The unit complex `e_i` (one molecule of species `i`). -/
def unitComplex (i : S) : Complex S := Pi.single i 1

omit [Fintype S] in
theorem unitComplex_ne_zero (i : S) : unitComplex i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unitComplex] at this

omit [Fintype S] in
theorem unitComplex_injective : Function.Injective (unitComplex (S := S)) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [unitComplex, Pi.single_apply, hij] at this

theorem monomial_unitComplex (i : S) (x : S → ℝ) : (unitComplex i).massActionMonomial x = x i := by
  simp only [Complex.massActionMonomial, unitComplex]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

variable {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂]

/-- The coefficient vectors of the augmented system `(Z F(x), L x − T)`. -/
noncomputable def augCoeff (N : Network S) (κ : RateConstants N) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (T : E₂ → ℝ) (a : Complex S) : E₁ ⊕ E₂ → ℝ :=
  Sum.elim (Z (combinedVector N κ a))
    ((∑ i, if a = unitComplex i then L (Pi.single i 1) else 0) - if a = 0 then T else 0)

/-- The support: reactant complexes, unit complexes and the zero complex. -/
noncomputable def augSupport (N : Network S) : Finset (Complex S) :=
  Finset.univ.image (fun r => (N.reaction r).source) ∪ Finset.univ.image unitComplex ∪ {0}

/-- Rates deformed by integer heights: `κ_r t^{h(y_r)}`. -/
noncomputable def deformedRatesZ (N : Network S) (κ : RateConstants N) (h : Complex S → ℤ)
    (t : ℝ) : RateConstants N :=
  ⟨fun r => κ.k r * Real.exp ((h (N.reaction r).source : ℝ) * Real.log t),
    fun r => mul_pos (κ.positive r) (Real.exp_pos _)⟩

/-- **The augmented system is the deformed polynomial system.** With `h(e_i) = 0`, the system
`∑_{a} t^{h(a)} x^a c_a` equals `(Z F_{κ_t}(x), L x − t^{h(0)} T)`. -/
theorem sys_augCoeff (N : Network S) (κ : RateConstants N) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (T : E₂ → ℝ) (h : Complex S → ℤ)
    (hh : ∀ i, h (unitComplex i) = 0) (t : ℝ) (x : S → ℝ) :
    Patchworking.sys (augSupport N) (augCoeff N κ Z L T) h t x =
      Sum.elim (Z (N.massActionVectorField (deformedRatesZ N κ h t) x))
        (L x - Real.exp ((h 0 : ℝ) * Real.log t) • T) := by
  classical
  set A := augSupport N
  set m : Complex S → ℝ := fun a => Real.exp ((h a : ℝ) * Real.log t) * a.massActionMonomial x
    with hm
  have hsrc : ∀ r, (N.reaction r).source ∈ A := fun r => by
    simp [A, augSupport]
  have hunit : ∀ i, unitComplex i ∈ A := fun i => by simp [A, augSupport]
  have hzero : (0 : Complex S) ∈ A := by simp [A, augSupport]
  -- the field part
  have hfield : ∑ a ∈ A, m a • combinedVector N κ a =
      N.massActionVectorField (deformedRatesZ N κ h t) x := by
    have h1 : N.massActionVectorField (deformedRatesZ N κ h t) x =
        ∑ r, (m (N.reaction r).source * κ.k r) • N.reactionVector r := by
      funext s
      rw [massActionVectorField_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, massActionRate, deformedRatesZ, hm]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := A)
      (g := fun r => (N.reaction r).source) (fun r _ => hsrc r)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [combinedVector, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.mp hr).2]
  -- the conservation part
  have hcons : ∑ a ∈ A, m a • ((∑ i, if a = unitComplex i then L (Pi.single i 1) else 0) -
      if a = 0 then T else 0) = L x - Real.exp ((h 0 : ℝ) * Real.log t) • T := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    have h1 : ∀ i, ∑ a ∈ A, (if a = unitComplex i then m a • L (Pi.single i 1) else 0) =
        x i • L (Pi.single i 1) := by
      intro i
      rw [Finset.sum_ite_eq' A (unitComplex i)]; simp only [hunit i, ↓reduceIte]
      simp [hm, hh, monomial_unitComplex]
    have h2 : ∑ a ∈ A, (if a = 0 then m a • T else 0) =
        Real.exp ((h 0 : ℝ) * Real.log t) • T := by
      rw [Finset.sum_ite_eq' A 0]; simp only [hzero, ↓reduceIte]
      simp [hm, Complex.massActionMonomial]
    rw [Finset.sum_congr rfl fun i _ => h1 i, h2]
    congr 1
    conv_rhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul]; congr 2; funext j; simp [Pi.single_apply, eq_comm]
  funext e
  cases e with
  | inl e₁ =>
    simp only [Patchworking.sys, Finset.sum_apply, Pi.smul_apply, augCoeff, Sum.elim_inl]
    rw [← hfield, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]
  | inr e₂ =>
    simp only [Patchworking.sys, Finset.sum_apply, Pi.smul_apply, augCoeff, Sum.elim_inr]
    rw [← hcons]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]

theorem field_mem_stoichSubspace (N : Network S) (κ : RateConstants N) (x : Concentration S) :
    N.massActionVectorField κ x ∈ N.stoichSubspace := by
  have : N.massActionVectorField κ x = ∑ r, N.massActionRate κ r x • N.reactionVector r := by
    funext s; simp [massActionVectorField_apply, Finset.sum_apply, smul_eq_mul]
  rw [this]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- The embeddings of the two blocks of equations. -/
noncomputable def inlCLM (E₁ E₂ : Type) [Fintype E₁] [Fintype E₂] :
    (E₁ → ℝ) →L[ℝ] (E₁ ⊕ E₂ → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Sum.elim v 0
      map_add' := fun u v => by funext e; cases e <;> simp
      map_smul' := fun c v => by funext e; cases e <;> simp }

noncomputable def inrCLM (E₁ E₂ : Type) [Fintype E₁] [Fintype E₂] :
    (E₂ → ℝ) →L[ℝ] (E₁ ⊕ E₂ → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Sum.elim 0 v
      map_add' := fun u v => by funext e; cases e <;> simp
      map_smul' := fun c v => by funext e; cases e <;> simp }

/-- **Bihan–Dickenstein–Giaroli lower bound with conservation laws.** Let `Z` be injective on the
stoichiometric subspace `V`, let `L` have kernel `V`, with `|E₁| + |E₂| = |S|`, and let the heights
vanish on the unit complexes. If the augmented system `(augSupport N, augCoeff N κ̄ Z L T̄)` has
`d > 0` positively decorated lower cells with pairwise different normals, then for some rate
constants there are `d` distinct positive steady states in one compatibility class, each
nondegenerate relative to the class. -/
theorem steadyStates_of_augmentedCells (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (hZ : ∀ v ∈ N.stoichSubspace, Z v = 0 → v = 0)
    (hL : ∀ v, L v = 0 ↔ v ∈ N.stoichSubspace)
    (hcard : Fintype.card (E₁ ⊕ E₂) = Fintype.card S) (κ : RateConstants N) (T : E₂ → ℝ)
    (h : Complex S → ℤ) (hh : ∀ i, h (unitComplex i) = 0) {d : ℕ} (hd : 0 < d)
    (C : Fin d → Patchworking.SysCell (augSupport N) (augCoeff N κ Z L T) h)
    (hw : Function.Injective fun j => (C j).w) :
    ∃ (κ' : RateConstants N) (x₀ : Concentration S) (X : Fin d → Concentration S),
      (∀ j, X j ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ' (X j) ∧
        N.IsNondegenerateSteadyState κ' (X j)) ∧ Function.Injective X := by
  classical
  obtain ⟨t, ht, X, hX, hinj⟩ := Patchworking.solutions_of_cells hcard C hw
  set κ' := deformedRatesZ N κ h t
  set Tt : E₂ → ℝ := Real.exp ((h 0 : ℝ) * Real.log t) • T
  have hid := sys_augCoeff N κ Z L T h hh t
  -- the two blocks of each solution
  have hblocks : ∀ j, Z (N.massActionVectorField κ' (X j)) = 0 ∧ L (X j) = Tt := by
    intro j
    have h0 := (hX j).2.1
    rw [hid] at h0
    constructor
    · funext e₁; have := congrFun h0 (Sum.inl e₁); simpa using this
    · funext e₂; have := congrFun h0 (Sum.inr e₂); simp at this; simpa [sub_eq_zero, Tt] using this
  have hss : ∀ j, N.IsMassActionSteadyState κ' (X j) := by
    intro j s
    have := hZ _ (field_mem_stoichSubspace N κ' (X j)) (hblocks j).1
    exact congrFun this s
  set j₀ : Fin d := ⟨0, hd⟩
  refine ⟨κ', X j₀, X, fun j => ⟨⟨?_, (hX j).1⟩, hss j, ?_⟩, hinj⟩
  · -- same class: `L (X j − X j₀) = 0`
    show X j - X j₀ ∈ N.stoichSubspace
    rw [← hL, map_sub, (hblocks j).2, (hblocks j₀).2, sub_self]
  · -- nondegeneracy relative to the class
    intro u hu hJu
    set Zc := LinearMap.toContinuousLinearMap Z
    set Lc := LinearMap.toContinuousLinearMap L
    have hD : HasFDerivAt (Patchworking.sys (augSupport N) (augCoeff N κ Z L T) h t)
        (inlCLM E₁ E₂ ∘L Zc ∘L N.massActionJacobianCLM κ' (X j) + inrCLM E₁ E₂ ∘L Lc) (X j) := by
      have heq : Patchworking.sys (augSupport N) (augCoeff N κ Z L T) h t =
          fun x => inlCLM E₁ E₂ (Zc (N.massActionVectorField κ' x)) +
            inrCLM E₁ E₂ (Lc x - Tt) := by
        funext x
        rw [hid]
        funext e
        cases e
        · simp [inlCLM, inrCLM, Zc, Lc, Tt]; rfl
        · simp [inlCLM, inrCLM, Zc, Lc, Tt]
      rw [heq]
      have h1 : HasFDerivAt (fun x => inlCLM E₁ E₂ (Zc (N.massActionVectorField κ' x)))
          (inlCLM E₁ E₂ ∘L Zc ∘L N.massActionJacobianCLM κ' (X j)) (X j) :=
        (inlCLM E₁ E₂).hasFDerivAt.comp _ (Zc.hasFDerivAt.comp _
          (N.massActionVectorField_hasFDerivAt κ' (X j)))
      have h2 : HasFDerivAt (fun x => inrCLM E₁ E₂ (Lc x - Tt)) (inrCLM E₁ E₂ ∘L Lc) (X j) :=
        (inrCLM E₁ E₂).hasFDerivAt.comp _ (Lc.hasFDerivAt.sub_const Tt)
      exact h1.add h2
    have hDu : fderiv ℝ (Patchworking.sys (augSupport N) (augCoeff N κ Z L T) h t) (X j) u = 0 := by
      rw [hD.fderiv]
      have hLu : L u = 0 := (hL u).mpr hu
      simp [hJu, hLu, Zc, Lc]
    exact (hX j).2.2 (by rw [hDu, map_zero])

end Network

end CRNT
