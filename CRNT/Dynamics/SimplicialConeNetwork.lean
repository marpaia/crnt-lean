import CRNT.Dynamics.SimplicialConeMonotone
import CRNT.Dynamics.CooperativeNetworks

/-!
# A structural criterion for simplicial-cone monotonicity

## The theory

A chemical reaction network is **monotone** if the order of its solutions is preserved by the
flow.  For the *orthant* orders — the componentwise orders associated to the orthants of `ℝ^S` —
the theory is classical (Angeli & Sontag, *Monotone and nonmonotone reaction systems*,
Chemical Engineering Science 45 (1990) 939–961; Smith, *Monotone Dynamical Systems*, 1995;
Banaji 2009; Russo, di Bernardo & Sontag 2010).  A field `f` satisfies the **Kamke condition**
(quasi-monotonicity) on a set `K` when `a ≤ b`, `a i = b i` imply `f a i ≤ f b i`; Kamke's
comparison principle (Kamke 1932; Hirsch & Smith, *Monotone Dynamical Systems*, 2005) then yields
that ordered initial conditions stay ordered.  Monotonicity with respect to a *simplicial cone* —
the image `M (ℝ^S_{≥0})` of the nonnegative orthant under an invertible linear map `M` — is the
generalization of the orthant theory: the order is `x ≤_M y ↔ M⁻¹ x ≤ M⁻¹ y` and the solutions of
the mass-action ODE keep that order.  In the orthant case the sign of the reaction vectors is
decisive, and Harary's signed-graph criterion (Harary 1964) decides *which* sign pattern (i.e.
which orthant) makes a given network monotone: the interaction graph of the network must be
balanced.

## What this repository already contains

* `CRNT.Monotone.kamke_comparison` — the Kamke comparison principle for cooperative fields.
* `CRNT.Monotone.orthant_comparison` — the comparison principle for the orthant order `≤_σ`.
* `CRNT.Network.massAction_kamkeOnSign_of_orthantCooperative` and
  `CRNT.Network.massAction_orthant_preserving` — the **structural criterion** for the orthant
  order: the sign condition `σ_i σ_j (y'_r - y_r)_i ≥ 0` on the reaction vectors.
* `CRNT.Network.exists_orthantCooperative_of_balanced` and
  `CRNT.Network.massAction_orthant_preserving_of_balanced` — the Harary signed-graph criterion.
* `CRNT.Network.massAction_kamkeOn_of_cooperative` and
  `CRNT.Network.massAction_order_preserving_of_cooperative` — the cooperative case.
* `CRNT.Monotone.simplicialCone_comparison` — the **general-cone comparison principle**.

## What this module adds

The general-cone comparison principle was available, but the *structural* criterion for it was
missing: there was no mass-action criterion for simplicial-cone monotonicity analogous to
`CRNT.Network.massAction_orthant_preserving` for the orthant case.  This module supplies it.

`CRNT.Network.IsSimplicialConeMonotoneNetwork N M` is the criterion.  Reading `M` as the
change of coordinates to the cone coordinates (`M x` are the cone coordinates of `x`, so the cone
is `M⁻¹ (ℝ^S_{≥0})` and the cone order is `M x ≤ M y`), it says

* the change of coordinates is order preserving (`M` maps the nonnegative orthant into itself), so
  that the mass-action monomials stay monotone in the cone coordinates; and
* **every reaction is cone-increasing**: the vector `M (reactionVector r)` — the reaction vector
  written in the cone coordinates — is coordinatewise nonnegative, i.e. it lies in the cone.

Under this criterion the mass-action field satisfies the Kamke condition on the cone
(`CRNT.Network.massAction_kamkeOnSimplicialCone_of_criterion`) and the mass-action flow preserves
the simplicial-cone order (`CRNT.Network.massAction_simplicialCone_preserving_of_criterion`; for
a `LinearIsometryEquiv` this is the order `CRNT.Monotone.ConeLE M` of the repository, see
`CRNT.Network.massAction_coneLE_preserving_of_criterion`).

## What is *not* formalized here

The **general** cone-monotonicity theory is not formalized: we do not characterize the networks
that are monotone with respect to a *given* cone, we do not give the analogue of Harary's
criterion for simplicial cones (the graph-theoretic criterion for the existence of a cone
adapted to a network), and we do not treat the invariance of the cone under the flow or the
existence and uniqueness of equilibria inside a cone.  The criterion proved here is a
sufficient condition, not a necessary one.
-/

namespace CRNT

namespace Monotone

open Set
open scoped NNReal

variable {S : Type} [Fintype S]

/-- **Comparison principle for simplicial cones, for a general linear equivalence.**  This is
`CRNT.Monotone.simplicialCone_comparison` with the cone-defining map allowed to be an arbitrary
linear equivalence (not necessarily a linear isometry).  The order compared is
`M.symm x ≤ M.symm y`, i.e. the order of the cone `M (ℝ^S_{≥0})`. -/
theorem simplicialCone_comparison_equiv (M : (S → ℝ) ≃ₗ[ℝ] (S → ℝ)) {f : (S → ℝ) → (S → ℝ)}
    {K : Set (S → ℝ)} {L : ℝ≥0} (hlip : LipschitzOnWith L f K)
    (hsup : ∀ a ∈ K, ∀ b ∈ K, M (M.symm a ⊔ M.symm b) ∈ K)
    (hk : KamkeOn (fun z => M.symm (f (M z))) (M.symm '' K)) {T : ℝ} {x y : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (f (x t)) (Icc 0 T) t)
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (f (y t)) (Icc 0 T) t)
    (hxK : ∀ t ∈ Icc 0 T, x t ∈ K) (hyK : ∀ t ∈ Icc 0 T, y t ∈ K)
    (h0 : M.symm (x 0) ≤ M.symm (y 0)) : ∀ t ∈ Icc 0 T, M.symm (x t) ≤ M.symm (y t) := by
  have hmaps : MapsTo (fun z => M z) (M.symm '' K) K := by
    rintro _ ⟨a, ha, rfl⟩
    simpa using ha
  have hlip' : LipschitzOnWith
      (‖(M.symm.toLinearMap.toContinuousLinearMap : (S → ℝ) →L[ℝ] (S → ℝ))‖₊ *
        (L * ‖(M.toLinearMap.toContinuousLinearMap : (S → ℝ) →L[ℝ] (S → ℝ))‖₊))
      (fun z => M.symm (f (M z))) (M.symm '' K) :=
    (M.symm.toLinearMap.toContinuousLinearMap).lipschitzWith.comp_lipschitzOnWith
      (hlip.comp
        ((M.toLinearMap.toContinuousLinearMap).lipschitzWith.lipschitzOnWith) hmaps)
  have hsup' : ∀ a ∈ M.symm '' K, ∀ b ∈ M.symm '' K, a ⊔ b ∈ M.symm '' K := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨M (M.symm a ⊔ M.symm b), hsup a ha b hb, by simp⟩
  have hder : ∀ {z : ℝ → (S → ℝ)}, (∀ t ∈ Icc 0 T, HasDerivWithinAt z (f (z t)) (Icc 0 T) t) →
      ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => M.symm (z t))
        ((fun w => M.symm (f (M w))) (M.symm (z t))) (Icc 0 T) t := by
    intro z hz t ht
    have h := (M.symm.toLinearMap.toContinuousLinearMap).hasFDerivAt.comp_hasDerivWithinAt t (hz t ht)
    have h2 : (fun w => M.symm (f (M w))) (M.symm (z t)) = M.symm (f (z t)) := by simp
    rw [h2]
    exact h
  intro t ht
  exact kamke_comparison hlip' hsup' hk (hder hx) (hder hy)
    (fun t ht => ⟨x t, hxK t ht, rfl⟩) (fun t ht => ⟨y t, hyK t ht, rfl⟩) h0 t ht

end Monotone

namespace Network

open Set
open scoped BigOperators NNReal

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The linear map `M` *preserves the nonnegative orthant* when it sends nonnegative vectors to
nonnegative vectors; equivalently, when the matrix of `M` has nonnegative entries. -/
def IsOrthantPreserving (M : (S → ℝ) →ₗ[ℝ] (S → ℝ)) : Prop :=
  ∀ x : S → ℝ, 0 ≤ x → 0 ≤ M x

/-- The vector `v` is *cone-increasing* for the simplicial cone `M (ℝ^S_{≥0})` when all its cone
coordinates `M.symm v` are nonnegative; equivalently, when `v` belongs to the cone
`M (ℝ^S_{≥0})`. -/
def IsConeIncreasing (M : (S → ℝ) ≃ₗ[ℝ] (S → ℝ)) (v : S → ℝ) : Prop :=
  ∀ i : S, 0 ≤ M.symm v i

/-- **A structural criterion for simplicial-cone monotonicity.**

Let `M : (S → ℝ) ≃ₗ[ℝ] (S → ℝ)` be an invertible linear map and `N` a network.  The network is
*simplicial-cone monotone* for `M` when

* `M` preserves the nonnegative orthant (`IsOrthantPreserving`), so that the mass-action monomials
  remain monotone in the cone coordinates; and
* every reaction is *cone-increasing*: the reaction vector `N.reactionVector r`, written in the
  cone coordinates `M.symm (N.reactionVector r)`, is coordinatewise nonnegative, i.e. it belongs to
  the cone `M (ℝ^S_{≥0})`.

In the alternative convention in which `M` denotes the change of coordinates to the cone
coordinates (so that the cone is `M⁻¹ (ℝ^S_{≥0})` and the cone order is `M x ≤ M y`), the second
condition reads `∀ r i, 0 ≤ M (N.reactionVector r) i`: the vector `M (reactionVector r)` lies in
the cone and is coordinatewise nonnegative in the cone coordinates.

Under this criterion the mass-action flow preserves the simplicial-cone order. -/
def IsSimplicialConeMonotoneNetwork (N : Network S) (M : (S → ℝ) ≃ₗ[ℝ] (S → ℝ)) : Prop :=
  IsOrthantPreserving M.toLinearMap ∧ ∀ r : N.R, IsConeIncreasing M (N.reactionVector r)

/-- **The mass-action field satisfies the Kamke condition on a simplicial cone** whenever the
network satisfies the structural criterion.

The transformed field `z ↦ M.symm (f (M z))` — the field written in the cone coordinates — is
Kamke (quasi-monotone) on the box `[0, C]` of the cone coordinates, for every `C ≥ 0`. -/
theorem massAction_kamkeOnSimplicialCone_of_criterion (N : Network S) (κ : N.RateConstants)
    (M : (S → ℝ) ≃ₗ[ℝ] (S → ℝ)) (hM : N.IsSimplicialConeMonotoneNetwork M) (C : ℝ) :
    Monotone.KamkeOn (fun z => M.symm (N.massActionVectorField κ (M z)))
      (Set.Icc (0 : S → ℝ) (fun _ => C)) := by
  intro a ha b hb hab i hi
  have hMnn : ∀ x : S → ℝ, 0 ≤ x → 0 ≤ M x := hM.1
  have hMa0 : 0 ≤ M a := hMnn _ fun j => ha.1 j
  have hMab : M a ≤ M b := by
    intro j
    have h1 : M b j - M a j = M (b - a) j := by rw [map_sub]; rfl
    have h2 : 0 ≤ M (b - a) j := (hMnn _ fun k => sub_nonneg.mpr (hab k)) j
    linarith
  have hmono : ∀ r : N.R, (N.reaction r).source.massActionMonomial (M a) ≤
      (N.reaction r).source.massActionMonomial (M b) := by
    intro r
    exact massActionMonomial_mono (fun j => hMa0 j) hMab
  have hfield : ∀ x : Concentration S, ∀ j : S,
      M.symm (N.massActionVectorField κ x) j =
        ∑ r : N.R, (κ.k r * (N.reaction r).source.massActionMonomial x) *
          (M.symm (N.reactionVector r)) j := by
    intro x j
    have h1 : N.massActionVectorField κ x = ∑ r : N.R,
        (κ.k r * (N.reaction r).source.massActionMonomial x) • (N.reactionVector r) := by
      funext k
      simp only [massActionVectorField_apply, massActionRate, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [h1, map_sum]
    simp only [M.symm.map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  show M.symm (N.massActionVectorField κ (M a)) i ≤ M.symm (N.massActionVectorField κ (M b)) i
  rw [hfield, hfield]
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmono r) (κ.positive r).le) (hM.2 r i)

/-- **The mass-action flow preserves the simplicial-cone order** under the structural criterion.

Two solutions of the mass-action ODE on `[0, T]` whose cone coordinates stay in the box
`[0, C]` and which start ordered in the cone order `M.symm x ≤ M.symm y` stay ordered. -/
theorem massAction_simplicialCone_preserving_of_criterion (N : Network S) (κ : N.RateConstants)
    (M : (S → ℝ) ≃ₗ[ℝ] (S → ℝ)) (hM : N.IsSimplicialConeMonotoneNetwork M) (C : ℝ)
    {T : ℝ} {x y : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (N.massActionVectorField κ (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, M.symm (x t) ∈ Set.Icc (0 : S → ℝ) (fun _ => C))
    (hyK : ∀ t ∈ Set.Icc 0 T, M.symm (y t) ∈ Set.Icc (0 : S → ℝ) (fun _ => C))
    (h0 : M.symm (x 0) ≤ M.symm (y 0)) :
    ∀ t ∈ Set.Icc 0 T, M.symm (x t) ≤ M.symm (y t) := by
  set K : Set (S → ℝ) := M '' Set.Icc (0 : S → ℝ) (fun _ => C)
  obtain ⟨L, hL⟩ := ((N.contDiff_massActionVectorField κ).contDiffOn (s := K)).exists_lipschitzOnWith
    (by simp) (Convex.linear_image (convex_Icc _ _) M.toLinearMap)
    (IsCompact.image isCompact_Icc M.toLinearMap.toContinuousLinearMap.continuous)
  have hKmem : ∀ z : S → ℝ, z ∈ K ↔ M.symm z ∈ Set.Icc (0 : S → ℝ) (fun _ => C) := by
    intro z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := (Set.mem_image M _ _).mp hz
      simpa using hw
    · intro hz
      refine (Set.mem_image M _ _).mpr ⟨M.symm z, hz, ?_⟩
      simp
  have hsup : ∀ a ∈ K, ∀ b ∈ K, M (M.symm a ⊔ M.symm b) ∈ K := by
    intro a ha b hb
    obtain ⟨z, hz, rfl⟩ := (Set.mem_image M _ _).mp ha
    obtain ⟨w, hw, rfl⟩ := (Set.mem_image M _ _).mp hb
    refine (Set.mem_image M _ _).mpr ⟨M.symm (M (z ⊔ w)), ?_, ?_⟩
    · rw [LinearEquiv.symm_apply_apply]
      constructor
      · intro j
        exact le_sup_of_le_left (hz.1 j)
      · intro j
        exact sup_le (hz.2 j) (hw.2 j)
    · simp
  have hmem : M.symm '' K = Set.Icc (0 : S → ℝ) (fun _ => C) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, hu, rfl⟩ := (Set.mem_image M _ _).mp hw
      simpa using hu
    · intro hz
      refine (Set.mem_image M.symm _ _).mpr ⟨M z, ?_, ?_⟩
      · refine (hKmem (M z)).mpr ?_
        rw [LinearEquiv.symm_apply_apply]
        exact hz
      · rw [LinearEquiv.symm_apply_apply]
  have hk : Monotone.KamkeOn (fun z => M.symm (N.massActionVectorField κ (M z))) (M.symm '' K) := by
    rw [hmem]
    exact N.massAction_kamkeOnSimplicialCone_of_criterion κ M hM C
  exact Monotone.simplicialCone_comparison_equiv M hL hsup hk hx hy
    (fun t ht => (hKmem (x t)).mpr (hxK t ht)) (fun t ht => (hKmem (y t)).mpr (hyK t ht)) h0

/-- **Order preservation in the simplicial-cone order of the repository.**  For a linear isometry
`M` the cone order is `CRNT.Monotone.ConeLE M x y ↔ M.symm x ≤ M.symm y`; the mass-action flow of
a network satisfying the structural criterion preserves it. -/
theorem massAction_coneLE_preserving_of_criterion (N : Network S) (κ : N.RateConstants)
    (M : (S → ℝ) ≃L[ℝ] (S → ℝ)) (hM : N.IsSimplicialConeMonotoneNetwork M.toLinearEquiv) (C : ℝ)
    {T : ℝ} {x y : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (N.massActionVectorField κ (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, M.symm (x t) ∈ Set.Icc (0 : S → ℝ) (fun _ => C))
    (hyK : ∀ t ∈ Set.Icc 0 T, M.symm (y t) ∈ Set.Icc (0 : S → ℝ) (fun _ => C))
    (h0 : Monotone.ConeLE M (x 0) (y 0)) :
    ∀ t ∈ Set.Icc 0 T, Monotone.ConeLE M (x t) (y t) := by
  exact N.massAction_simplicialCone_preserving_of_criterion κ M.toLinearEquiv hM C hx hy hxK hyK h0

/-- **Worked instance: the orthant case.**  A network all of whose reaction vectors are
coordinatewise nonnegative satisfies the criterion for the identity cone, i.e. for the cone
`ℝ^S_{≥0}`; the mass-action flow then preserves the usual componentwise order. -/
theorem isSimplicialConeMonotoneNetwork_refl_of_nonneg (N : Network S)
    (h : ∀ r : N.R, ∀ i : S, 0 ≤ N.reactionVector r i) :
    N.IsSimplicialConeMonotoneNetwork (LinearEquiv.refl ℝ (S → ℝ)) := by
  constructor
  · intro x hx i
    simpa using hx i
  · intro r i
    simpa using h r i

/-- **Order preservation for networks with nonnegative reaction vectors.** -/
theorem massAction_order_preserving_of_nonneg_reactionVectors (N : Network S) (κ : N.RateConstants)
    (h : ∀ r : N.R, ∀ i : S, 0 ≤ N.reactionVector r i) (C : ℝ) {T : ℝ} {x y : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (N.massActionVectorField κ (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ Set.Icc (0 : S → ℝ) (fun _ => C))
    (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ Set.Icc (0 : S → ℝ) (fun _ => C))
    (h0 : x 0 ≤ y 0) : ∀ t ∈ Set.Icc 0 T, x t ≤ y t := by
  exact N.massAction_simplicialCone_preserving_of_criterion κ (LinearEquiv.refl ℝ (S → ℝ))
    (N.isSimplicialConeMonotoneNetwork_refl_of_nonneg h) C hx hy hxK hyK h0

namespace Example

/-- The linear equivalence of `Fin 2 → ℝ` given by `M (x₀, x₁) = (x₀ + x₁, x₁)`.  Its cone
`M (ℝ^S_{≥0})` is a genuinely non-orthant simplicial cone and its cone coordinates are
`M⁻¹ (x₀, x₁) = (x₀ - x₁, x₁)`. -/
def shearEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := fun i => if i = 0 then x 0 + x 1 else x 1
  invFun y := fun i => if i = 0 then y 0 - y 1 else y 1
  map_add' := by
    intro a b
    funext i
    fin_cases i
    · simp
      ring
    · simp
  map_smul' := by
    intro c x
    funext i
    fin_cases i
    · simp
      ring
    · simp
  left_inv := by
    intro x
    funext i
    fin_cases i
    · simp
    · simp
  right_inv := by
    intro y
    funext i
    fin_cases i
    · simp
    · simp

/-- The two-species network `∅ → X + Y`. -/
def net : Network (Fin 2) :=
  ⟨Fin 1, inferInstance, inferInstance, fun _ => ⟨fun _ => 0, fun _ => 1⟩⟩

/-- The reaction vector of `net` is `(1, 1)`. -/
theorem net_reactionVector (r : net.R) (i : Fin 2) : net.reactionVector r i = 1 := by
  show ((net.reaction r).target i : ℝ) - ((net.reaction r).source i : ℝ) = 1
  simp [net]

/-- **A genuinely non-orthant instance of the criterion.**  The network `∅ → X + Y` is
simplicial-cone monotone for the cone `M (ℝ^S_{≥0})` with `M (x₀, x₁) = (x₀ + x₁, x₁)`: the
reaction vector `(1, 1)` has cone coordinates `(0, 1) ≥ 0`. -/
theorem isSimplicialConeMonotoneNetwork_shear :
    net.IsSimplicialConeMonotoneNetwork shearEquiv := by
  constructor
  · intro x hx i
    fin_cases i
    · simp [shearEquiv]
      exact add_nonneg (hx 0) (hx 1)
    · simp [shearEquiv]
      exact hx 1
  · intro r i
    have hvec : net.reactionVector r = fun _ => 1 := funext fun j => net_reactionVector r j
    fin_cases i
    · simp [shearEquiv, hvec]
    · simp [shearEquiv, hvec]

end Example

end Network

end CRNT

#print axioms CRNT.Monotone.simplicialCone_comparison_equiv
#print axioms CRNT.Network.massAction_kamkeOnSimplicialCone_of_criterion
#print axioms CRNT.Network.massAction_simplicialCone_preserving_of_criterion
#print axioms CRNT.Network.massAction_coneLE_preserving_of_criterion
#print axioms CRNT.Network.massAction_order_preserving_of_nonneg_reactionVectors
